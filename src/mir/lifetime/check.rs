//! Loan-conflict check and region-constraint emission over MIR functions.
//!
//! Verifies per-statement access against the active loan set (emits
//! `LT-LoanConflict`), accumulates outlives constraints from ref-typed
//! assignments and call sites, and reports any that can't be discharged
//! against the function's declared outlives axioms (`LT-LifetimeMismatch`
//! and `LT-LifetimeEscape`).
//!
//! Independent of `init_state`: this pass sees a program purely as
//! borrows and accesses, without regard to the ref kind's init obligation.

use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::diagnostic_format::DiagnosticFormat;
use crate::mir::helpers::*;
use crate::mir::env::GlobalEnv;
use indexmap::IndexMap;
use std::collections::BTreeSet;

use super::constraints;
use super::constraints::ConstraintCause;
use super::loans::{
    self, consume_operand, is_compatible, is_elab_inserted_drop, paths_conflict, transfer_stmt,
    AccessKind, LoanMap,
};
use super::region::{self, Region};
use super::LifetimeCode;

pub fn check_program(program: &Program, env: &GlobalEnv, d: &mut Diagnostics) {
    check_decl_wf(env, d);
    for f in program.functions() {
        check_fn_signature_wf(f, env, d);
        check_function(env, f, d);
    }
}

fn check_function(env: &GlobalEnv, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }
    let region_ctx = region::build_region_ctx(func, env);
    let entry_states = loans::run(body);
    let mut constraints = constraints::ConstraintSet::new();
    let locals = func.locals_map();
    let mut checker = Checker {
        env,
        func,
        locals,
        region_ctx: &region_ctx,
        constraints: &mut constraints,
        d,
    };
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut loans = entry.clone();
        for (i, stmt) in block.statements.iter().enumerate() {
            let next = block.statements.get(i + 1);
            checker.check_and_transfer_stmt(block, stmt, next, &mut loans);
            checker.emit_stmt_constraints(stmt);
        }
        checker.check_and_transfer_terminator(block, &mut loans);
    }
    let escape_visible = signature_visible_regions(func, env);
    checker.check_constraints(&escape_visible);
}

/// Enforce well-formedness of every type mention in a fn's signature
/// (params, `$return`) and local decls. Runs independently of body
/// existence, so extern fn declarations with ill-formed signatures are
/// still rejected. The emitted constraints are checked against the
/// fn's own declared outlives axioms.
fn check_fn_signature_wf(func: &Function, env: &GlobalEnv, d: &mut Diagnostics) {
    let mut cs = constraints::ConstraintSet::new();
    for p in &func.params {
        emit_type_wf_constraints(&p.ty, env, &mut cs);
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            emit_type_wf_constraints(&l.ty, env, &mut cs);
        }
        for block in &body.blocks {
            for stmt in &block.statements {
                emit_stmt_wf_constraints(stmt, env, &mut cs);
            }
        }
    }
    if cs.is_empty() {
        return;
    }
    let axioms: Vec<(Region, Region)> = func
        .meta
        .params
        .outlives
        .iter()
        .map(|bound| {
            (
                name_to_region(&bound.longer),
                name_to_region(&bound.shorter),
            )
        })
        .collect();
    let closure = constraints::transitive_closure(&axioms);
    for c in cs.iter() {
        if let (Region::Named(_), Region::Named(_) | Region::Static) = (&c.outlives, &c.sub) {
            if c.outlives == c.sub || closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                continue;
            }
            d.push_error(
                missing_bound_diagnostic(c, "function", &func.meta).in_function(&func.meta.name),
            );
        }
    }
}

/// Enforce well-formedness of every declared struct/enum: field or
/// variant types that mention a generic `Custom<'x, 'y>` require the
/// containing decl's declared outlives axioms to justify the mentioned
/// type's declared outlives obligations. E.g. a field of type
/// `Wrap<'a, 'b>` where `Wrap` requires `'b: 'a` forces the outer decl
/// to declare `'b: 'a` on its own params.
fn check_decl_wf(env: &GlobalEnv, d: &mut Diagnostics) {
    for decl in env.types.values() {
        let meta = decl.meta();
        let mut cs = constraints::ConstraintSet::new();
        match decl {
            TypeDecl::Struct(s) => {
                for f in &s.fields {
                    emit_type_wf_constraints(&f.ty, env, &mut cs);
                }
            }
            TypeDecl::Enum(e) => {
                for v in &e.variants {
                    emit_type_wf_constraints(&v.ty, env, &mut cs);
                }
            }
        }
        if cs.is_empty() {
            continue;
        }
        let container_kind = match decl {
            TypeDecl::Struct(_) => "struct",
            TypeDecl::Enum(_) => "enum",
        };
        let axioms: Vec<(Region, Region)> = meta
            .params
            .outlives
            .iter()
            .map(|bound| {
                (
                    name_to_region(&bound.longer),
                    name_to_region(&bound.shorter),
                )
            })
            .collect();
        let closure = constraints::transitive_closure(&axioms);
        for c in cs.iter() {
            if let (Region::Named(_), Region::Named(_) | Region::Static) = (&c.outlives, &c.sub) {
                if c.outlives == c.sub {
                    continue;
                }
                if closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                    continue;
                }
                d.push_error(missing_bound_diagnostic(c, container_kind, meta));
            }
        }
    }
}

fn missing_bound_diagnostic(
    constraint: &constraints::Constraint,
    owner_kind: &str,
    owner: &DeclMeta,
) -> Diagnostic {
    let mut format = DiagnosticFormat::new();
    let scope = format.scope(owner);
    let bound = format!(
        "{}: {}",
        format.region(&scope, &constraint.outlives),
        format.region(&scope, &constraint.sub),
    );
    let message = format!(
        "{} requires lifetime bound {}, but it is not implied by the declared bounds on {} '{}'",
        constraint.cause.description(),
        bound,
        owner_kind,
        owner.name,
    );
    let hint = format!(
        "declare bound {} on {} '{}' or change the value flow so it is not required",
        bound, owner_kind, owner.name,
    );
    format.finish(
        Diagnostic::new(LifetimeCode::LifetimeMismatch, constraint.origin, message).with_hint(hint),
    )
}

/// Map a lifetime to its region form. The reserved name `'static`
/// becomes `Region::Static`; every other name becomes `Region::Named`.
fn name_to_region(lt: &Lifetime) -> Region {
    if lt.0 == "static" {
        Region::Static
    } else {
        Region::Named(lt.clone())
    }
}

/// Walk statement-level type mentions and emit well-formedness
/// constraints for their Custom subtrees. Covers rvalues that carry
/// explicit types: `PtrCast(_, ty)` and `EnumConstr(_, type_args, ..)`.
/// Places and operands don't carry standalone type mentions — their
/// types derive from local/param decls, already walked upstream.
fn emit_stmt_wf_constraints(stmt: &Statement, env: &GlobalEnv, cs: &mut constraints::ConstraintSet) {
    match &stmt.kind {
        StatementKind::Assign(_, rvalue) => match rvalue {
            RValue::PtrCast(op, ty) => {
                emit_operand_wf_constraints(op, env, cs);
                emit_type_wf_constraints(ty, env, cs);
            }
            RValue::EnumConstr(_, type_args, _, op) => {
                for ty in type_args {
                    emit_type_wf_constraints(ty, env, cs);
                }
                emit_operand_wf_constraints(op, env, cs);
            }
            RValue::Use(op) => emit_operand_wf_constraints(op, env, cs),
            RValue::ArrayLit(ops) => {
                for op in ops {
                    emit_operand_wf_constraints(op, env, cs);
                }
            }
            RValue::Ref(_, _) | RValue::RawRef(_) => {}
        },
        StatementKind::Call(target, args) => {
            emit_operand_wf_constraints(target, env, cs);
            for op in args {
                emit_operand_wf_constraints(op, env, cs);
            }
        }
        StatementKind::Drop(_) | StatementKind::Unborrow(_) | StatementKind::RequireUninit(_) => {}
    }
}

/// If `op` is a fn-name const with type arguments, discharge each
/// type_arg's Custom outlives obligations. FnName can appear in call
/// targets, call args, and any rvalue that consumes an operand
/// (`Use`, `PtrCast`, `EnumConstr`, `ArrayLit`).
fn emit_operand_wf_constraints(op: &Operand, env: &GlobalEnv, cs: &mut constraints::ConstraintSet) {
    if let Operand::Const(ConstVal::FnName(_, type_args)) = op {
        for ty in type_args {
            emit_type_wf_constraints(ty, env, cs);
        }
    }
}

/// Walk `ty` and, for every `TypeKind::Custom(Instance { name, .. })` mention,
/// substitute the decl's declared outlives bounds with the mention's
/// actual lifetime args and emit them into `cs`. Recurses through
/// `Ref`, `Array`, `RawPtr`, `Fn`, and nested `Custom` type args.
///
/// This is the type-level well-formedness sweep: every mention of a
/// generic type at any type-appearance position (fn param, local decl,
/// struct field, nested type arg) discharges the mentioned type's
/// declared outlives obligations against the containing scope's axioms.
/// Mirrors the fn-call instantiation pattern in `check_call_regions`
/// (which handles the analog for `fn foo<'a, 'b: 'a>(...)` calls).
fn emit_type_wf_constraints(ty: &Type, env: &GlobalEnv, cs: &mut constraints::ConstraintSet) {
    match &ty.kind {
        TypeKind::Custom(Instance { name, lifetime_args: lts, type_args: args }) => {
            if let Some(decl) = env.types.get(name) {
                let meta = decl.meta();
                if lts.len() == meta.params.lifetime_params.len() {
                    let sub: IndexMap<&Lifetime, &Lifetime> = meta
                        .params
                        .lifetime_params
                        .iter()
                        .map(|p| &p.lifetime)
                        .zip(lts.iter())
                        .collect();
                    for bound in &meta.params.outlives {
                        let a_lt = sub.get(&bound.longer).copied().unwrap_or(&bound.longer);
                        let b_lt = sub.get(&bound.shorter).copied().unwrap_or(&bound.shorter);
                        cs.emit(
                            name_to_region(a_lt),
                            name_to_region(b_lt),
                            ConstraintCause::TypeRequirement {
                                type_name: name.clone(),
                            },
                            ty.source,
                        );
                    }
                }
            }
            for a in args {
                emit_type_wf_constraints(a, env, cs);
            }
        }
        TypeKind::Ref(_, _, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            emit_type_wf_constraints(inner, env, cs);
        }
        TypeKind::Fn(inners) => {
            for i in inners {
                emit_type_wf_constraints(i, env, cs);
            }
        }
        TypeKind::Unit
        | TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Param(_) => {}
    }
}

/// Return the set of Named regions that are reachable from a
/// caller-visible slot: through `$return`, or through any
/// caller-provided `&mut` / `&out` parameter (i.e. any pointer the
/// callee can write into, whose target the caller reads back).
///
/// A Named region that only appears in body-local types (e.g. a
/// struct field of a locally-owned struct decl instantiated at
/// use-site with no lifetime args) is NOT escape-visible.
fn signature_visible_regions(func: &Function, env: &GlobalEnv) -> BTreeSet<Lifetime> {
    let mut out = BTreeSet::new();
    for p in &func.params {
        // $return is the sret slot; any &out or &mut is caller-provided
        // storage the callee writes into.
        let visible = p.name == "$return"
            || matches!(
                &p.ty.kind,
                TypeKind::Ref(RefKind::Out, _, _) | TypeKind::Ref(RefKind::Mut, _, _)
            );
        if !visible {
            continue;
        }
        // Peel off the outer ref (that ref's own lifetime is the
        // caller's storage lifetime; irrelevant to escape) and collect
        // named regions in the pointee.
        let pointee = match &p.ty.kind {
            TypeKind::Ref(_, _, inner) => inner.as_ref().clone(),
            _ => p.ty.clone(),
        };
        let mut visited = BTreeSet::new();
        collect_named_regions(&pointee, env, &mut visited, &mut out);
    }
    out
}

fn collect_named_regions(
    ty: &Type,
    env: &GlobalEnv,
    visited: &mut BTreeSet<String>,
    out: &mut BTreeSet<Lifetime>,
) {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), inner) => {
            out.insert(lt.clone());
            collect_named_regions(inner, env, visited, out);
        }
        TypeKind::Ref(_, None, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            collect_named_regions(inner, env, visited, out);
        }
        TypeKind::Custom(Instance { name, lifetime_args, type_args }) => {
            for lt in lifetime_args {
                out.insert(lt.clone());
            }
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    for f in &s.fields {
                        if let Some(sub) = s.meta.try_substitute(&f.ty, lifetime_args, type_args)
                        {
                            collect_named_regions(&sub, env, visited, out);
                        }
                    }
                }
                Some(TypeDecl::Enum(e)) => {
                    for v in &e.variants {
                        if let Some(sub) = e.meta.try_substitute(&v.ty, lifetime_args, type_args)
                        {
                            collect_named_regions(&sub, env, visited, out);
                        }
                    }
                }
                // `None`: type not registered — a type-check error is
                // already reported. Nothing more to walk.
                None => {}
            }
            visited.remove(name);
        }
        TypeKind::Fn(args) => {
            for a in args {
                collect_named_regions(a, env, visited, out);
            }
        }
        // Scalars carry no lifetimes. `TypeKind::Param` is an in-scope
        // parameter binder; its lifetime dependency (if any) is
        // introduced at the instantiation site, not this walk.
        TypeKind::Unit
        | TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Param(_) => {}
    }
}

/// Test-only: compute the outlives constraints emitted for `func`
/// without running any check. Exercises the accumulation path.
#[cfg(test)]
pub fn constraints_for(env: &GlobalEnv, func: &Function) -> constraints::ConstraintSet {
    let mut cs = constraints::ConstraintSet::new();
    // `None` here means an extern fn: no body, no statements, no
    // constraints to emit. Return the empty set.
    let Some(body) = &func.body else { return cs };
    if body.blocks.is_empty() {
        return cs;
    }
    let region_ctx = region::build_region_ctx(func, env);
    let locals = func.locals_map();
    let mut dummy_d = Diagnostics::default();
    let mut checker = Checker {
        env,
        func,
        locals,
        region_ctx: &region_ctx,
        constraints: &mut cs,
        d: &mut dummy_d,
    };
    for block in &body.blocks {
        for stmt in &block.statements {
            checker.emit_stmt_constraints(stmt);
        }
    }
    cs
}

/// Variance of a position, used to determine which direction an
/// outlives constraint is emitted at a lifetime slot.
#[derive(Copy, Clone, PartialEq)]
enum Variance {
    /// Arg position: `caller_region outlives inst_region`.
    Contravariant,
    /// Return position: `inst_region outlives caller_region`. Reached
    /// only by walking through a contravariant position — currently
    /// only fn-pointer arg positions produce that flip, and `TypeKind::Fn`
    /// isn't walked yet (see the "Call-site handling ignores fn
    /// pointers" punchlist item). `combine`'s `(Contra, Co) →
    /// Invariant` rule and `emit_variance`'s `Covariant` branch are
    /// pre-wired for that walk.
    #[allow(dead_code)]
    Covariant,
    /// Descended through an exclusive kind: emit both directions.
    Invariant,
}

impl Variance {
    fn combine(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
            (Variance::Contravariant, Variance::Covariant)
            | (Variance::Covariant, Variance::Contravariant) => Variance::Invariant,
            (a, _) => a,
        }
    }
}

fn emit_variance(
    caller: &Region,
    inst: &Region,
    v: Variance,
    constraints: &mut constraints::ConstraintSet,
    cause: ConstraintCause,
    source: SourceInfo,
) {
    match v {
        Variance::Contravariant => {
            constraints.emit(caller.clone(), inst.clone(), cause, source);
        }
        Variance::Covariant => {
            constraints.emit(inst.clone(), caller.clone(), cause, source);
        }
        Variance::Invariant => {
            constraints.emit(caller.clone(), inst.clone(), cause.clone(), source);
            constraints.emit(inst.clone(), caller.clone(), cause, source);
        }
    }
}

/// Return the first named-region-like lifetime found in `ty`,
/// substituted through `inst`. Used to identify the "returned ref's
/// region" for synthetic loan placement.
fn first_named_region(ty: &Type, inst: &IndexMap<Lifetime, Region>) -> Option<Region> {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), _) => {
            Some(inst.get(lt).cloned().unwrap_or_else(|| name_to_region(lt)))
        }
        TypeKind::Custom(Instance { lifetime_args, .. }) => {
            let lt = lifetime_args.first()?;
            Some(inst.get(lt).cloned().unwrap_or_else(|| name_to_region(lt)))
        }
        TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => first_named_region(elem, inst),
        _ => None,
    }
}

/// Get the outer ref-kind of `place` when its type is `TypeKind::Ref`.
fn ref_kind_of_place(place: &Place, locals: &IndexMap<String, Type>, env: &GlobalEnv) -> Option<RefKind> {
    match crate::mir::type_util::place_type(locals, env, place)?.kind {
        TypeKind::Ref(kind, _, _) => Some(kind),
        _ => None,
    }
}

/// Resolve the region for a `Ref` layer during a variance walk. `Some(lt)` in
/// the type wins; falling back to `place`'s outer region covers body-local
/// refs whose lifetime slot is `None`. Inner Ref layers pass `place = None`
/// because per-layer places aren't tracked.
fn ref_region(
    lt: &Option<Lifetime>,
    place: Option<&Place>,
    region_ctx: &region::RegionCtx,
    locals: &IndexMap<String, Type>,
    env: &GlobalEnv,
) -> Option<Region> {
    if let Some(lt) = lt {
        return Some(name_to_region(lt));
    }
    place.and_then(|p| region_ctx.region_of_place(p, locals, env))
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Take(_) => {
            unreachable!("lifetime check saw unresolved `take` operand; copy relaxation should have resolved it")
        }
        Operand::Const(_) => None,
    }
}

struct Checker<'a> {
    env: &'a GlobalEnv,
    func: &'a Function,
    locals: IndexMap<String, Type>,
    region_ctx: &'a region::RegionCtx,
    constraints: &'a mut constraints::ConstraintSet,
    d: &'a mut Diagnostics,
}

impl<'a> Checker<'a> {
    fn error(&self, code: LifetimeCode, source: SourceInfo, msg: String) -> Diagnostic {
        Diagnostic::new(code, source, msg).in_function(&self.func.meta.name)
    }

    /// Enforce accumulated outlives constraints. The only satisfiable
    /// inter-region relations are equality, entries in the transitive
    /// closure of declared axioms, or `Static outlives X` (Static is
    /// the top of the order). Unsatisfiable relations between two
    /// declared regions fire `LT-LifetimeMismatch`; a body-local region
    /// escaping through a caller-visible slot fires `LT-LifetimeEscape`.
    fn check_constraints(&mut self, escape_visible: &BTreeSet<Lifetime>) {
        let axioms: Vec<(Region, Region)> = self
            .func
            .meta
            .params
            .outlives
            .iter()
            .map(|bound| {
                (
                    name_to_region(&bound.longer),
                    name_to_region(&bound.shorter),
                )
            })
            .collect();
        let closure = constraints::transitive_closure(&axioms);
        let projected = self.constraints.project_inference();
        for c in projected.iter() {
            match (&c.outlives, &c.sub) {
                (Region::Named(_), Region::Named(_) | Region::Static) if c.outlives != c.sub => {
                    if closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                        continue;
                    }
                    self.d.push_error(
                        missing_bound_diagnostic(c, "function", &self.func.meta)
                            .in_function(&self.func.meta.name),
                    );
                }
                // Escape: a Free-region loan (body-local storage) flowing
                // into a caller-visible signature slot — either a Named
                // region on `$return`/`&mut`/`&out` params, or `'static`
                // (always visible; Static is the top of the order).
                (Region::Free(_), Region::Named(dst)) if escape_visible.contains(dst) => {
                    let mut format = DiagnosticFormat::new();
                    let scope = format.scope(&self.func.meta);
                    let msg = format!(
                        "borrow escapes function: value with local (unnamed) region cannot be stored into region {}",
                        format.lifetime(&scope, dst),
                    );
                    let diagnostic = self.error(LifetimeCode::LifetimeEscape, c.origin, msg);
                    self.d.push_error(format.finish(diagnostic));
                }
                (Region::Free(_), Region::Static) => {
                    let msg = format!(
                        "borrow escapes function: value with local (unnamed) region cannot be stored into region {}",
                        c.sub,
                    );
                    self.d
                        .push_error(self.error(LifetimeCode::LifetimeEscape, c.origin, msg));
                }
                // Remaining pairs are satisfiable at this phase:
                //   - (Named=Named) or (Static=Static): identical
                //     regions, trivially met.
                //   - (Named, Free): a real region flowing into a
                //     body-local temp — always OK.
                //   - (Free, Named-not-escape): flow into an internal
                //     Named region without caller visibility — OK; if
                //     the region ever becomes caller-visible the
                //     escape branch above fires instead.
                //   - (Free, Free): two body-local regions unify.
                //   - (Static, _): Static outlives everything, always;
                //     also pruned at emit but kept for exhaustiveness.
                (Region::Named(_), Region::Named(_))
                | (Region::Named(_), Region::Free(_))
                | (Region::Named(_), Region::Static)
                | (Region::Free(_), Region::Named(_))
                | (Region::Free(_), Region::Free(_))
                | (Region::Static, _) => {}
                (Region::Inference(_), _) | (_, Region::Inference(_)) => {
                    unreachable!("call inference region survived constraint projection")
                }
            }
        }
    }

    /// Emit outlives constraints for one statement. Currently covers
    /// assignment `dst = src` where both sides are ref-typed: the
    /// source's region must outlive the destination's.
    ///
    /// Silent-early-return convention throughout this fn: the `Some(...)
    /// else { return }` guards skip statements or operands that carry
    /// no lifetime obligation. In particular:
    ///   - Non-Assign statements have no ref-flow to constrain here
    ///     (call-site region flow is handled by `walk_call_regions`).
    ///   - `Operand::Const` has no source place → no source region.
    ///   - `region_of_place` and `region_of_borrow_source` returning
    ///     `None` mean the place isn't ref-typed / can't be resolved →
    ///     no constraint needed.
    fn emit_stmt_constraints(&mut self, stmt: &Statement) {
        let StatementKind::Assign(target, rvalue) = &stmt.kind else {
            return;
        };
        // `Use` copies a source place into a target place: their types are
        // structurally equal (enforced upstream by the MIR type checker), so
        // a variance-aware walk over the pair emits a constraint at every
        // Ref layer and Custom lifetime argument. Other rvalues keep the
        // outer-only special case below: `Ref` synthesizes a fresh outer
        // region with no matching source type, `EnumConstr` changes the
        // target's shape, and `PtrCast` bridges types where a parallel walk
        // isn't well-defined.
        if let RValue::Use(op) = rvalue {
            let Some(src_place) = operand_place(op) else { return };
            let Some(src_ty) =
                crate::mir::type_util::place_type(&self.locals, self.env, src_place)
            else {
                return;
            };
            let Some(tgt_ty) = crate::mir::type_util::place_type(&self.locals, self.env, target)
            else {
                return;
            };
            self.emit_use_type_constraints(
                &src_ty,
                &tgt_ty,
                Some((src_place, target)),
                Variance::Covariant,
                stmt.source,
            );
            return;
        }
        // Array literals build a `[T; N]` from N operands. Each operand
        // flows into a slot with the array element type, so per-slot
        // variance constraints must be emitted or wrong-lifetime element
        // refs would slip into a signature-visible array without a
        // diagnostic. Handled here, before the single-source `match` below.
        if let RValue::ArrayLit(ops) = rvalue {
            let Some(tgt_ty) = crate::mir::type_util::place_type(&self.locals, self.env, target)
            else {
                return;
            };
            let TypeKind::Array(elem_ty, _) = &tgt_ty.kind else {
                return;
            };
            for (k, op) in ops.iter().enumerate() {
                let Some(src_place) = operand_place(op) else { continue };
                let Some(src_ty) =
                    crate::mir::type_util::place_type(&self.locals, self.env, src_place)
                else {
                    continue;
                };
                let slot = index_place(
                    target.clone(),
                    Operand::Const(ConstVal::Int { bits: k as u64, ty: IntTy::I64 }),
                );
                self.emit_use_type_constraints(
                    &src_ty,
                    elem_ty,
                    Some((src_place, &slot)),
                    Variance::Covariant,
                    stmt.source,
                );
            }
            return;
        }
        let (src_region, target_place) = match rvalue {
            RValue::Ref(_, place) => {
                let Some(r) =
                    self.region_ctx
                        .region_of_borrow_source(place, &self.locals, self.env)
                else {
                    return;
                };
                (r, target.clone())
            }
            RValue::EnumConstr(_, _, variant, op) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, downcast_place(target.clone(), variant.clone()))
            }
            RValue::PtrCast(op, _) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, target.clone())
            }
            _ => return,
        };
        let Some(t_r) = self
            .region_ctx
            .region_of_place(&target_place, &self.locals, self.env)
        else {
            return;
        };
        // Emit variance-aware constraint. Shared refs are covariant
        // (source outlives dst is enough). Exclusive-write kinds are
        // invariant (source outlives dst AND dst outlives source).
        let target_kind = ref_kind_of_place(&target_place, &self.locals, self.env);
        self.constraints.emit(
            src_region.clone(),
            t_r.clone(),
            ConstraintCause::Assignment,
            stmt.source,
        );
        if !matches!(target_kind, Some(RefKind::Shared)) {
            self.constraints
                .emit(t_r, src_region, ConstraintCause::Assignment, stmt.source);
        }
    }

    /// Recursively emit variance-aware outlives constraints between two
    /// structurally equal types (source and target of a `Use` assignment).
    /// The optional `outer_places` argument enables `region_ctx` lookup for a
    /// body-local ref at the top of the walk; inner refs contribute a
    /// constraint only when both source and target lifetimes are named, since
    /// there is no per-inner-ref region tracking today.
    fn emit_use_type_constraints(
        &mut self,
        src_ty: &Type,
        tgt_ty: &Type,
        outer_places: Option<(&Place, &Place)>,
        variance: Variance,
        source: SourceInfo,
    ) {
        match (&src_ty.kind, &tgt_ty.kind) {
            (TypeKind::Ref(kind, s_lt, s_inner), TypeKind::Ref(_, t_lt, t_inner)) => {
                let src_region = ref_region(
                    s_lt,
                    outer_places.map(|(s, _)| s),
                    self.region_ctx,
                    &self.locals,
                    self.env,
                );
                let tgt_region = ref_region(
                    t_lt,
                    outer_places.map(|(_, t)| t),
                    self.region_ctx,
                    &self.locals,
                    self.env,
                );
                let layer_variance = variance.combine(match kind {
                    RefKind::Shared => Variance::Covariant,
                    _ => Variance::Invariant,
                });
                if let (Some(sr), Some(tr)) = (src_region, tgt_region) {
                    // emit_variance uses (caller, inst) where the caller is the
                    // outer slot; the assignment target is the outer slot and
                    // the source is the value being provided.
                    emit_variance(
                        &tr,
                        &sr,
                        layer_variance,
                        self.constraints,
                        ConstraintCause::Assignment,
                        source,
                    );
                }
                self.emit_use_type_constraints(s_inner, t_inner, None, layer_variance, source);
            }
            (TypeKind::Custom(Instance { lifetime_args: s_lts, type_args: s_args, .. }), TypeKind::Custom(Instance { lifetime_args: t_lts, type_args: t_args, .. })) => {
                let inv = variance.combine(Variance::Invariant);
                for (s_lt, t_lt) in s_lts.iter().zip(t_lts) {
                    let sr = name_to_region(s_lt);
                    let tr = name_to_region(t_lt);
                    emit_variance(
                        &tr,
                        &sr,
                        inv,
                        self.constraints,
                        ConstraintCause::Assignment,
                        source,
                    );
                }
                for (s_arg, t_arg) in s_args.iter().zip(t_args) {
                    self.emit_use_type_constraints(s_arg, t_arg, None, inv, source);
                }
            }
            (TypeKind::Array(s_el, n), TypeKind::Array(t_el, _)) => {
                // Iterate slots so a nested Ref inside the element type
                // has per-slot places to look up its region against.
                // Passing `None` here would strand elided element refs
                // without a src/tgt place and lose the outer constraint.
                for k in 0..*n {
                    let idx = || {
                        Operand::Const(ConstVal::Int { bits: k, ty: IntTy::I64 })
                    };
                    let slot_places =
                        outer_places.map(|(s, t)| (index_place(s.clone(), idx()), index_place(t.clone(), idx())));
                    self.emit_use_type_constraints(
                        s_el,
                        t_el,
                        slot_places.as_ref().map(|(s, t)| (s, t)),
                        variance,
                        source,
                    );
                }
            }
            (TypeKind::RawPtr(s_inner), TypeKind::RawPtr(t_inner)) => {
                self.emit_use_type_constraints(
                    s_inner,
                    t_inner,
                    None,
                    variance.combine(Variance::Invariant),
                    source,
                );
            }
            // Inner Ref layers with `None` lifetimes come from local declarations
            // without lifetime annotations; there is no region representation for
            // them today. Fn types don't carry lifetime metadata yet (see the
            // Fn-pointer lifetime tracking punchlist item). Scalars and Param
            // carry no lifetimes.
            _ => {}
        }
    }

    /// Check whether accessing `place` in the given way conflicts with any
    /// active loan. Uses `extract_path_with_deref` so accesses through `*r`
    /// or ancestors of `*r` (like `r` itself) can conflict with a reborrow
    /// loan on `Deref(Var(r))`.
    ///
    /// A conflict is reported when: the access root matches a loan's root
    /// (i.e. touches the same base variable) AND the access path shares a
    /// prefix with the loaned path AND the loan kind is not compatible with
    /// the access kind.
    fn check_loan_conflict(
        &mut self,
        block: &BasicBlock,
        place: &Place,
        access: AccessKind,
        source: SourceInfo,
        loans: &LoanMap,
    ) {
        let (access_root, access_path) = extract_path_with_deref(place);

        for (borrower_place, loan) in loans {
            // Ignore the borrower itself. Consumption of the borrower's own
            // storage (`move r`, `move b.p`) doesn't conflict with the loan
            // it holds — that's handled by close_ref_if_present. But an
            // *ancestor* consumption (`move b` when `b.p` holds a loan)
            // still needs to fire on `b.p`'s loan, so this skip only fires
            // when the access is exactly the borrower place.
            let (borrower_root, borrower_path) = extract_path_with_deref(borrower_place);
            if borrower_root == access_root && borrower_path == access_path {
                continue;
            }
            if is_compatible(&loan.kind, &access) {
                continue;
            }
            // Multi-loan: any place in the set may be the actual pointee.
            // Report at most one error per loan (first matching place).
            for loaned in &loan.loaned {
                let (loan_root, loan_path) = extract_path_with_deref(loaned);
                if loan_root != access_root {
                    continue;
                }
                if !paths_conflict(&access_path, &loan_path) {
                    continue;
                }
                let borrower_name = format_place(borrower_place);
                let access_temp = self.hll_temporary_kind(place);
                let borrower_temp = self.hll_temporary_kind(borrower_place);
                let access_name = match access_temp {
                    Some(HllTemporaryKind::Expression) => "temporary value".to_string(),
                    Some(HllTemporaryKind::Lowering) => "intermediate value".to_string(),
                    None => format_place(place),
                };
                let source_access = if matches!(access, AccessKind::Move)
                    && source.generated_kind() == Some(GeneratedKind::HllDesugaring)
                {
                    "use".to_string()
                } else {
                    access.to_string()
                };
                let is_expression_cleanup = access_temp == Some(HllTemporaryKind::Expression)
                    && matches!(access, AccessKind::Move)
                    && source.generated_kind() == Some(GeneratedKind::DropElaboration);
                let (msg, hint, secondary) = if is_expression_cleanup {
                    (
                        "borrow of a temporary value escapes the expression that created it"
                            .to_string(),
                        "bind the temporary value to a local before borrowing it.".to_string(),
                        "temporary value is borrowed here".to_string(),
                    )
                } else if let Some(borrower_temp) = borrower_temp {
                    let loaned_name = format_place(loaned);
                    let borrow_kind = match loan.kind {
                        RefKind::Shared => "shared borrow",
                        _ => "exclusive borrow",
                    };
                    let hint = match borrower_temp {
                        HllTemporaryKind::Expression => {
                            "the borrow remains active until the surrounding expression finishes."
                        }
                        HllTemporaryKind::Lowering => {
                            "the borrow remains active until the current operation finishes."
                        }
                    };
                    (
                        format!(
                            "cannot {} '{}': conflicts with an active {} of '{}'",
                            source_access, access_name, borrow_kind, loaned_name,
                        ),
                        hint.to_string(),
                        format!("{} of '{}' occurs here", borrow_kind, loaned_name),
                    )
                } else {
                    (
                        format!(
                            "cannot {} '{}': already borrowed by '{}'",
                            source_access, access_name, borrower_name,
                        ),
                        format!(
                            "the borrow of '{}' is active until its last use or explicit unborrow.",
                            borrower_name,
                        ),
                        format!("borrow of '{}' occurs here", access_name),
                    )
                };
                let mut diag = self
                    .error(LifetimeCode::LoanConflict, source, msg)
                    .in_block(&block.label)
                    .with_hint(hint);
                // Attach the borrow's origin as a secondary span if we
                // captured one (within-block loans have real spans;
                // cross-block dataflow-propagated loans have Span::default,
                // which renders as no snippet).
                let create_span = loan.create_source.span();
                if create_span.line != 0 || create_span.col != 0 {
                    diag = diag.with_secondary(loan.create_source, secondary);
                }
                self.d.push_error(diag);
                break;
            }
        }
    }

    fn check_operand_access(
        &mut self,
        block: &BasicBlock,
        op: &Operand,
        source: SourceInfo,
        loans: &LoanMap,
    ) {
        let (place, access) = match op {
            Operand::Copy(p) => (p, AccessKind::Read),
            Operand::Move(p) => (p, AccessKind::Move),
            Operand::Take(_) => {
                unreachable!("lifetime check saw unresolved `take` operand; copy relaxation should have resolved it")
            }
            Operand::Const(_) => return,
        };
        self.check_loan_conflict(block, place, access, source, loans);
    }

    fn hll_temporary_kind(&self, place: &Place) -> Option<HllTemporaryKind> {
        let (root, _) = extract_path_with_deref(place);
        self.func
            .body
            .as_ref()
            .and_then(|body| body.locals.iter().find(|local| local.name == root))
            .and_then(|local| match local.source.generated_kind() {
                Some(GeneratedKind::HllTemporary(kind)) => Some(kind),
                _ => None,
            })
    }

    /// Emit outlives constraints for a `call callee(args)` statement,
    /// and register synthetic loans on caller-side output slots so the
    /// loan tracker can detect aliasing of caller-side inputs through
    /// callee-returned refs.
    ///
    /// From the lifetime pass's view, all four exclusive-borrow kinds
    /// (`&mut`, `&out`, `&drop`, `&uninit`) behave the same: they're
    /// exclusive borrows whose pointee lifetimes are invariant. Init-
    /// state discipline distinguishes them; lifetime doesn't.
    ///
    /// Algorithm:
    /// 1. Look up callee's Function in env. Bail on fn-pointer /
    ///    non-fn-name callees.
    /// 2. Allocate fresh Free regions from `region_ctx.fresh()` for
    ///    each callee lifetime param.
    /// 3. Walk each (caller arg, callee param) in parallel. At each
    ///    lifetime slot emit constraints:
    ///    - Argument-position (contravariant): `caller outlives inst`.
    ///    - Return-position (covariant, i.e. inside an exclusive
    ///      pointee): `inst outlives caller`.
    ///    - Exclusive descent: emit BOTH directions (invariance).
    ///    Snapshot input arg loans by instantiated region for step 5.
    /// 4. Instantiate the callee's signature_outlives axioms.
    /// 5. Register synthetic loans on caller-side output slots: for
    ///    each arg that's `&mut T`/`&out T`/... containing an inner
    ///    ref of instantiated region R, look at the arg's own loan's
    ///    loaned places (caller-side backing storage) and place a
    ///    synthetic loan there whose `loaned` = union of input loans
    ///    sharing region R.
    fn check_call_regions(
        &mut self,
        target: &Operand,
        args: &[Operand],
        source: SourceInfo,
        loans: &mut LoanMap,
    ) {
        let Operand::Const(ConstVal::FnName(callee_name, _)) = target else {
            return;
        };
        let Some(callee) = self.env.functions.get(callee_name) else {
            return;
        };
        if callee.params.len() != args.len() {
            return;
        }

        // Fresh instantiation region per callee lifetime param.
        let inst: IndexMap<Lifetime, Region> = callee
            .meta
            .params
            .lifetime_params
            .iter()
            .map(|lt| (lt.lifetime.clone(), self.region_ctx.fresh_inference()))
            .collect();

        let mut per_output_inputs: IndexMap<Region, BTreeSet<Place>> = IndexMap::new();

        for (arg, param) in args.iter().zip(callee.params.iter()) {
            let Some(arg_place) = operand_place(arg) else {
                continue;
            };
            self.walk_call_regions(
                &param.ty,
                arg_place,
                &inst,
                Variance::Contravariant,
                loans,
                &mut per_output_inputs,
                callee_name,
                source,
            );
        }

        for bound in &callee.meta.params.outlives {
            let a_r = inst
                .get(&bound.longer)
                .cloned()
                .unwrap_or_else(|| name_to_region(&bound.longer));
            let b_r = inst
                .get(&bound.shorter)
                .cloned()
                .unwrap_or_else(|| name_to_region(&bound.shorter));
            self.constraints.emit(
                a_r,
                b_r,
                ConstraintCause::Call {
                    callee: callee_name.clone(),
                },
                source,
            );
        }

        for (arg, param) in args.iter().zip(callee.params.iter()) {
            let Some(arg_place) = operand_place(arg) else {
                continue;
            };
            let Some(arg_owned) = as_owned_path(arg_place) else {
                continue;
            };
            let TypeKind::Ref(kind, _, inner_ty) = &param.ty.kind else {
                continue;
            };
            if matches!(kind, RefKind::Shared) {
                continue;
            }
            // The value the callee writes has a region: the outermost
            // named region in the inner type.
            let Some(out_region) = first_named_region(inner_ty, &inst) else {
                continue;
            };
            let Some(input_places) = per_output_inputs.get(&out_region) else {
                continue;
            };
            if input_places.is_empty() {
                continue;
            }

            let mut merged: BTreeSet<Place> = BTreeSet::new();
            for src in input_places {
                if let Some(loan) = loans.get(src) {
                    merged.extend(loan.loaned.iter().cloned());
                }
            }
            if merged.is_empty() {
                continue;
            }

            // Synthetic loan's kind mirrors the callee's returned ref.
            let synth_kind = match &inner_ty.kind {
                TypeKind::Ref(k, _, _) => k.clone(),
                _ => kind.clone(),
            };
            let arg_loan = loans.get(&arg_owned).cloned();
            if let Some(arg_loan) = arg_loan {
                for slot in arg_loan.loaned {
                    loans.insert(
                        slot,
                        loans::Loan {
                            kind: synth_kind.clone(),
                            loaned: merged.clone(),
                            create_source: source,
                        },
                    );
                }
            }
        }
    }

    /// Walk callee param type and caller arg place in parallel, emitting
    /// outlives constraints at each lifetime slot and recording input-
    /// side loans for synthetic-loan registration on outputs.
    fn walk_call_regions(
        &mut self,
        callee_ty: &Type,
        caller_place: &Place,
        inst: &IndexMap<Lifetime, Region>,
        variance: Variance,
        loans: &LoanMap,
        per_output_inputs: &mut IndexMap<Region, BTreeSet<Place>>,
        callee_name: &str,
        source: SourceInfo,
    ) {
        match &callee_ty.kind {
            TypeKind::Ref(kind, Some(lt), inner) => {
                let inst_region = inst.get(lt).cloned().unwrap_or_else(|| name_to_region(lt));
                if let Some(caller_r) =
                    self.region_ctx
                        .region_of_place(caller_place, &self.locals, self.env)
                {
                    emit_variance(
                        &caller_r,
                        &inst_region,
                        variance,
                        self.constraints,
                        ConstraintCause::Call {
                            callee: callee_name.to_string(),
                        },
                        source,
                    );
                    if matches!(variance, Variance::Contravariant | Variance::Invariant) {
                        if let Some(owned) = as_owned_path(caller_place) {
                            if loans.contains_key(&owned) {
                                per_output_inputs
                                    .entry(inst_region.clone())
                                    .or_default()
                                    .insert(owned);
                            }
                        }
                    }
                }
                // Exclusive kinds make the pointee's lifetimes invariant.
                // Shared preserves the current variance.
                let inner_variance = match kind {
                    RefKind::Shared => variance,
                    _ => Variance::Invariant,
                };
                let inner_caller = crate::mir::helpers::deref_place(caller_place.clone());
                self.walk_call_regions(
                    inner,
                    &inner_caller,
                    inst,
                    inner_variance,
                    loans,
                    per_output_inputs,
                    callee_name,
                    source,
                );
            }
            TypeKind::Custom(Instance { lifetime_args: lts, type_args: args, .. }) => {
                // Match callee and caller lifetime args positionally, not
                // all-to-first. A generic type's lifetime slots behave
                // like container references: default to invariance
                // (conservative, safe).
                let caller_ty =
                    crate::mir::type_util::place_type(&self.locals, self.env, caller_place);
                if let Some(caller_ty) = caller_ty {
                    if let TypeKind::Custom(Instance { lifetime_args: caller_lts, .. }) = &caller_ty.kind {
                        for (callee_lt, caller_lt) in lts.iter().zip(caller_lts.iter()) {
                            let inst_region = inst
                                .get(callee_lt)
                                .cloned()
                                .unwrap_or_else(|| name_to_region(callee_lt));
                            let caller_r = name_to_region(caller_lt);
                            emit_variance(
                                &caller_r,
                                &inst_region,
                                variance.combine(Variance::Invariant),
                                self.constraints,
                                ConstraintCause::Call {
                                    callee: callee_name.to_string(),
                                },
                                source,
                            );
                        }
                    }
                }
                // Recurse into type args (invariant for now).
                for a in args {
                    self.walk_call_regions(
                        a,
                        caller_place,
                        inst,
                        variance.combine(Variance::Invariant),
                        loans,
                        per_output_inputs,
                        callee_name,
                        source,
                    );
                }
            }
            TypeKind::Array(elem, n) => {
                // Iterate constant-index slots so nested Ref layers reach
                // per-slot caller places — a whole-array `caller_place`
                // has no Ref type, so `region_of_place` at the Ref layer
                // would return None and skip the constraint emission.
                for k in 0..*n {
                    let slot = index_place(
                        caller_place.clone(),
                        Operand::Const(ConstVal::Int { bits: k, ty: IntTy::I64 }),
                    );
                    self.walk_call_regions(
                        elem,
                        &slot,
                        inst,
                        variance,
                        loans,
                        per_output_inputs,
                        callee_name,
                        source,
                    );
                }
            }
            TypeKind::RawPtr(elem) => {
                self.walk_call_regions(
                    elem,
                    caller_place,
                    inst,
                    variance,
                    loans,
                    per_output_inputs,
                    callee_name,
                    source,
                );
            }
            // Scalars and `Param` carry no lifetime — no walk needed.
            //
            // `TypeKind::Fn` is a KNOWN gap tracked in the punchlist
            // ("Call-site handling ignores fn pointers"): descending
            // into a fn-pointer type's arg/return slots would emit the
            // standard covariant-return / contravariant-arg constraints,
            // but TypeKind::Fn today carries no lifetime metadata to walk.
            // Adding that walk requires first extending TypeKind::Fn to
            // carry per-slot lifetimes. Until then, taking a &fn-pointer
            // to a ref-returning fn silently bypasses lifetime tracking
            // on that call path — the escape check and the standard
            // ref-flow constraints still fire on direct call sites.
            // `Ref` with `None` lifetime: elision assigns Free regions
            // for these before check runs, but a hand-written or
            // partially-elided signature can still reach here. No
            // named lifetime to constrain; the caller-side ref still
            // participates in the standard `region_of_place` path
            // driven from the direct-call handler above.
            TypeKind::Ref(_, None, _) => {}
            TypeKind::Unit
            | TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Never
            | TypeKind::Param(_)
            | TypeKind::Fn(_) => {}
        }
    }

    /// Check accesses in `stmt` against `loans`, then advance `loans` via
    /// `transfer_stmt`. `Call` is handled inline (not via `transfer_stmt`)
    /// so operand-by-operand consumption sees prior operands' releases —
    /// e.g. `call f(move r, copy y)` where `y` is loaned by `r` must pass.
    ///
    /// `next` is the immediately-following statement in the block, used
    /// to skip loan-conflict emission on drop-elab-inserted drops (see
    /// the Drop arm).
    fn check_and_transfer_stmt(
        &mut self,
        block: &BasicBlock,
        stmt: &Statement,
        next: Option<&Statement>,
        loans: &mut LoanMap,
    ) {
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                match rvalue {
                    RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                        self.check_operand_access(block, op, stmt.source, loans);
                    }
                    RValue::Ref(kind, place) => {
                        self.check_loan_conflict(
                            block,
                            place,
                            AccessKind::Borrow(kind.clone()),
                            stmt.source,
                            loans,
                        );
                    }
                    RValue::RawRef(_) => {
                        // Raw pointer creation is the "unsafe" escape hatch
                        // — no loan-conflict check. Aliasing with live
                        // borrows is the programmer's responsibility.
                    }
                    RValue::ArrayLit(ops) => {
                        for op in ops {
                            self.check_operand_access(block, op, stmt.source, loans);
                        }
                    }
                }
                self.check_loan_conflict(block, target, AccessKind::Write, stmt.source, loans);
                transfer_stmt(loans, stmt, stmt.source);
            }
            StatementKind::Call(target, args) => {
                self.check_operand_access(block, target, stmt.source, loans);
                self.check_call_regions(target, args, stmt.source, loans);
                consume_operand(loans, target);
                for a in args {
                    self.check_operand_access(block, a, stmt.source, loans);
                    consume_operand(loans, a);
                }
            }
            StatementKind::Drop(place) => {
                // Skip the loan-conflict emission on drop-elab-inserted
                // drops. Drop-elab rewrites `x = <rvalue>` (Init x, Drop
                // type) into `drop x; x = <rvalue>` with the inserted
                // drop carrying the *assign's* span. Both statements
                // would fire against the same borrower at the same span,
                // reporting a single user event twice. The assign
                // carries the authoritative diagnostic; the auto-drop is
                // silent but still advances the loan map.
                if !is_elab_inserted_drop(place, stmt.source, next) {
                    self.check_loan_conflict(block, place, AccessKind::Move, stmt.source, loans);
                }
                transfer_stmt(loans, stmt, stmt.source);
            }
            StatementKind::Unborrow(place) => {
                // Consumes the borrower Var. Its own loan is skipped in
                // check_loan_conflict (the "borrower == access_root with
                // empty path" case), but a *reborrow* of this borrower —
                // loan borrowed by s on `*r` — still needs to block `unborrow r`.
                self.check_loan_conflict(block, place, AccessKind::Move, stmt.source, loans);
                transfer_stmt(loans, stmt, stmt.source);
            }
            StatementKind::RequireUninit(_) => {
                // Place-state validates the assertion. It is not a runtime
                // access and therefore does not participate in loan checks.
            }
        }
    }

    fn check_and_transfer_terminator(&mut self, block: &BasicBlock, loans: &mut LoanMap) {
        let terminator_source = block.terminator.source;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                self.check_operand_access(block, cond, terminator_source, loans);
                consume_operand(loans, cond);
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                // Discriminant read.
                self.check_loan_conflict(block, place, AccessKind::Read, terminator_source, loans);
            }
            // Goto/Return/Abort/Unreachable read no operand or place;
            // there is no runtime access here. Any outstanding loan
            // that must be closed at `return` is surfaced by the
            // place-state ref-obligation check on the elaborated MIR
            // (NLL inserts `unborrow` at last-use; whatever remains
            // active at return fires from that pass).
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::parser::Parser;

    #[test]
    fn loan_conflict_hides_hll_temporary_borrower_name() {
        let mut program = Parser::parse_or_panic(
            r#"
            fn f(x: i64) {
              _temp_0: & i64;
              entry:
                _temp_0 = & x;
                x = 1;
                unborrow _temp_0;
                drop x;
                return
            }
            "#,
        );
        let Declaration::Fn(func) = &mut program.declarations[0] else {
            panic!("expected function declaration");
        };
        let body = func.body.as_mut().expect("expected function body");
        body.locals[0].source = SourceInfo::generated(
            GeneratedKind::HllTemporary(HllTemporaryKind::Expression),
            body.locals[0].span(),
        );
        for stmt in &mut body.blocks[0].statements {
            stmt.source = SourceInfo::generated(GeneratedKind::HllDesugaring, stmt.span());
        }

        let (env, env_errors) = GlobalEnv::build(&program);
        assert!(env_errors.is_empty());
        let mut diagnostics = Diagnostics::default();
        check_program(&program, &env, &mut diagnostics);

        let conflict = diagnostics
            .errors()
            .find(|diag| diag.message().contains("active shared borrow"))
            .expect("expected loan conflict");
        assert_eq!(
            conflict.message(),
            "cannot write to 'x': conflicts with an active shared borrow of 'x'"
        );
        assert!(!conflict.message().contains("_temp_0"));
    }

    #[test]
    fn ordinary_access_to_expression_temp_is_not_misreported_as_escape() {
        let mut program = Parser::parse_or_panic(
            r#"
            fn f() {
              _temp_0: i64;
              r: & i64;
              entry:
                _temp_0 = 1;
                r = & _temp_0;
                _temp_0 = 2;
                unborrow r;
                drop _temp_0;
                return
            }
            "#,
        );
        let Declaration::Fn(func) = &mut program.declarations[0] else {
            panic!("expected function declaration");
        };
        let body = func.body.as_mut().expect("expected function body");
        body.locals[0].source = SourceInfo::generated(
            GeneratedKind::HllTemporary(HllTemporaryKind::Expression),
            body.locals[0].span(),
        );
        for stmt in &mut body.blocks[0].statements {
            stmt.source = SourceInfo::generated(GeneratedKind::HllDesugaring, stmt.span());
        }

        let (env, env_errors) = GlobalEnv::build(&program);
        assert!(env_errors.is_empty());
        let mut diagnostics = Diagnostics::default();
        check_program(&program, &env, &mut diagnostics);

        let conflict = diagnostics
            .errors()
            .find(|diagnostic| diagnostic.message().contains("cannot write"))
            .expect("expected loan conflict");
        assert_eq!(
            conflict.message(),
            "cannot write to 'temporary value': already borrowed by 'r'"
        );
        assert!(!conflict.message().contains("escapes"));
        assert!(!conflict.message().contains("_temp_0"));
    }
}
