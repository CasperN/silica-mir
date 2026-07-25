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
use crate::mir::helpers::*;
use crate::mir::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::BTreeSet;

use super::constraints;
use super::loans::{
    self, consume_operand, is_compatible, is_elab_inserted_drop, paths_conflict, transfer_stmt,
    AccessKind, LoanMap,
};
use super::region::{self, Region};
use super::LifetimeCode;

pub fn check_program(program: &Program, env: &Env, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }
    let region_ctx = region::build_region_ctx(func, env);
    let entry_states = loans::run(body, &region_ctx);
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

/// Return the set of Named regions that are reachable from a
/// caller-visible slot: through `$return`, or through any
/// caller-provided `&mut` / `&out` parameter (i.e. any pointer the
/// callee can write into, whose target the caller reads back).
///
/// A Named region that only appears in body-local types (e.g. a
/// struct field of a locally-owned struct decl instantiated at
/// use-site with no lifetime args) is NOT escape-visible.
fn signature_visible_regions(func: &Function, env: &Env) -> BTreeSet<Lifetime> {
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
    env: &Env,
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
        TypeKind::Custom(name, lifetime_args, type_args) => {
            for lt in lifetime_args {
                out.insert(lt.clone());
            }
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    for f in &s.fields {
                        let sub = s.meta.substitute(&f.ty, lifetime_args, type_args);
                        collect_named_regions(&sub, env, visited, out);
                    }
                }
                Some(TypeDecl::Enum(e)) => {
                    for v in &e.variants {
                        let sub = e.meta.substitute(&v.ty, lifetime_args, type_args);
                        collect_named_regions(&sub, env, visited, out);
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
pub fn constraints_for(env: &Env, func: &Function) -> constraints::ConstraintSet {
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
    /// only fn-pointer arg positions produce that flip, and `Type::Fn`
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
    span: Span,
) {
    match v {
        Variance::Contravariant => {
            constraints.emit(caller.clone(), inst.clone(), span);
        }
        Variance::Covariant => {
            constraints.emit(inst.clone(), caller.clone(), span);
        }
        Variance::Invariant => {
            constraints.emit(caller.clone(), inst.clone(), span);
            constraints.emit(inst.clone(), caller.clone(), span);
        }
    }
}

/// Return the first named-region-like lifetime found in `ty`,
/// substituted through `inst`. Used to identify the "returned ref's
/// region" for synthetic loan placement.
fn first_named_region(ty: &Type, inst: &IndexMap<Lifetime, Region>) -> Option<Region> {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), _) => {
            Some(inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone())))
        }
        TypeKind::Custom(_, lts, _) => {
            let lt = lts.first()?;
            Some(inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone())))
        }
        TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => first_named_region(elem, inst),
        _ => None,
    }
}

/// Get the outer ref-kind of `place` when its type is `TypeKind::Ref`.
fn ref_kind_of_place(place: &Place, locals: &IndexMap<String, Type>, env: &Env) -> Option<RefKind> {
    match crate::mir::type_util::place_type(locals, env, place)?.kind {
        TypeKind::Ref(kind, _, _) => Some(kind),
        _ => None,
    }
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
    env: &'a Env,
    func: &'a Function,
    locals: IndexMap<String, Type>,
    region_ctx: &'a region::RegionCtx,
    constraints: &'a mut constraints::ConstraintSet,
    d: &'a mut Diagnostics,
}

impl<'a> Checker<'a> {
    fn error(&self, code: LifetimeCode, span: Span, msg: String) -> Diagnostic {
        Diagnostic::new(code, span, msg).in_function(&self.func.meta.name)
    }

    /// Enforce accumulated outlives constraints. Without `where`-clause
    /// bounds in scope, the only satisfiable inter-named-region relation
    /// is equality (or `Static outlives anything`, already pruned at
    /// emit). Any constraint pairing two distinct Named regions fires
    /// `LT-LifetimeMismatch`. Free ↔ Named or Free ↔ Free are treated as
    /// unifiable at this phase (escape checking handles the interesting
    /// Free ↔ signature-visible case in phase 5).
    fn check_constraints(&mut self, escape_visible: &BTreeSet<Lifetime>) {
        // Reserved lifetime `'static` maps to `Region::Static` in the
        // axiom set so that `<'a: 'static>` (a demanding-'static bound)
        // enters the transitive closure with Static on the RHS.
        let name_to_region = |lt: &Lifetime| {
            if lt.0 == "static" {
                Region::Static
            } else {
                Region::Named(lt.clone())
            }
        };
        let axioms: Vec<(Region, Region)> = self
            .func
            .meta
            .outlives
            .iter()
            .map(|(a, b)| (name_to_region(a), name_to_region(b)))
            .collect();
        let closure = constraints::transitive_closure(&axioms);
        for c in self.constraints.iter() {
            match (&c.outlives, &c.sub) {
                (Region::Named(_), Region::Named(_)) if c.outlives != c.sub => {
                    if closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                        continue;
                    }
                    let msg = format!(
                        "lifetime mismatch: expected value with region {}, found value with region {}",
                        c.sub, c.outlives,
                    );
                    self.d
                        .push_error(self.error(LifetimeCode::LifetimeMismatch, c.origin, msg));
                }
                // Escape: a Free-region loan (body-local storage) flowing
                // into a Named region that's actually reachable through a
                // caller-visible output ($return or &out/&mut param).
                (Region::Free(_), Region::Named(dst)) if escape_visible.contains(dst) => {
                    let msg = format!(
                        "borrow escapes function: value with local (unnamed) region cannot be stored into region {}",
                        dst,
                    );
                    self.d
                        .push_error(self.error(LifetimeCode::LifetimeEscape, c.origin, msg));
                }
                // Named outlives Free: source is a real (signature)
                // region, dst is a body-local. Always satisfiable — a
                // named region outlives any local temp.
                (Region::Named(_), Region::Free(_)) => {}
                // Remaining pairs are satisfiable at this phase:
                //   - (Named=Named): identical regions, trivially met.
                //   - (Free, Named-not-escape): flow into an internal
                //     Named region without caller visibility — OK; if
                //     the region ever becomes caller-visible the
                //     escape_visible branch above fires instead.
                //   - (Free, Free): two body-local regions unify.
                //   - Anything paired with Region::Static: Static
                //     outlives everything and is outlived by nothing
                //     stricter, so pairings resolve trivially.
                (Region::Named(_), Region::Named(_))
                | (Region::Free(_), Region::Named(_))
                | (Region::Free(_), Region::Free(_))
                | (Region::Static, _)
                | (_, Region::Static) => {}
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
    ///   - Ref rvalues on projected places (non-owned) resolve to
    ///     `Region::Free(u32::MAX)` (sentinel) rather than bailing —
    ///     the sentinel keeps the constraint emission live.
    ///   - `region_of_place` returning `None` means the place isn't
    ///     ref-typed → no constraint needed.
    fn emit_stmt_constraints(&mut self, stmt: &Statement) {
        let StatementKind::Assign(target, rvalue) = &stmt.kind else {
            return;
        };
        let (src_region, target_place) = match rvalue {
            RValue::Use(op) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, target.clone())
            }
            RValue::Ref(_, place) => {
                let r = if let Some(owned) = as_owned_path(place) {
                    self.region_ctx
                        .get(&owned)
                        .cloned()
                        .unwrap_or(Region::Free(u32::MAX))
                } else {
                    let mut cur = place;
                    while let Place::Field(inner, _)
                    | Place::Downcast(inner, _)
                    | Place::Index(inner, _) = cur
                    {
                        cur = inner;
                    }
                    if let Place::Deref(inner) = cur {
                        self.region_ctx
                            .region_of_place(inner, &self.locals, self.env)
                            .unwrap_or(Region::Free(u32::MAX))
                    } else {
                        Region::Free(u32::MAX)
                    }
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
        self.constraints
            .emit(src_region.clone(), t_r.clone(), stmt.span);
        if !matches!(target_kind, Some(RefKind::Shared)) {
            self.constraints.emit(t_r, src_region, stmt.span);
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
        span: Span,
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
                let hint = format!(
                    "the borrow of '{}' is active until its last use or explicit unborrow.",
                    borrower_name,
                );
                let msg = format!(
                    "cannot {} '{}': already borrowed by '{}'",
                    access,
                    format_place(place),
                    borrower_name,
                );
                let mut diag = self
                    .error(LifetimeCode::LoanConflict, span, msg)
                    .in_block(&block.label)
                    .with_hint(hint);
                // Attach the borrow's origin as a secondary span if we
                // captured one (within-block loans have real spans;
                // cross-block dataflow-propagated loans have Span::default,
                // which renders as no snippet).
                if loan.create_span.line != 0 || loan.create_span.col != 0 {
                    diag = diag.with_secondary(
                        loan.create_span,
                        format!("borrow of '{}' occurs here", format_place(place)),
                    );
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
        span: Span,
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
        self.check_loan_conflict(block, place, access, span, loans);
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
        span: Span,
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
            .lifetime_params
            .iter()
            .map(|lt| (lt.clone(), self.region_ctx.fresh()))
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
                span,
            );
        }

        for (a, b) in &callee.meta.outlives {
            let a_r = inst.get(a).cloned().unwrap_or(Region::Named(a.clone()));
            let b_r = inst.get(b).cloned().unwrap_or(Region::Named(b.clone()));
            self.constraints.emit(a_r, b_r, span);
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
                            region: out_region.clone(),
                            loaned: merged.clone(),
                            create_span: span,
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
        span: Span,
    ) {
        match &callee_ty.kind {
            TypeKind::Ref(kind, Some(lt), inner) => {
                let inst_region = inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone()));
                if let Some(caller_r) =
                    self.region_ctx
                        .region_of_place(caller_place, &self.locals, self.env)
                {
                    emit_variance(&caller_r, &inst_region, variance, self.constraints, span);
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
                    span,
                );
            }
            TypeKind::Custom(_, lts, args) => {
                // A generic type's lifetime args behave like a container
                // reference: default to invariance (conservative, safe).
                for lt in lts {
                    let inst_region = inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone()));
                    let caller_ty =
                        crate::mir::type_util::place_type(&self.locals, self.env, caller_place);
                    if let Some(caller_ty) = caller_ty {
                        if let TypeKind::Custom(_, caller_lts, _) = &caller_ty.kind {
                            if let Some(caller_lt) = caller_lts.first() {
                                let caller_r = Region::Named(caller_lt.clone());
                                emit_variance(
                                    &caller_r,
                                    &inst_region,
                                    variance.combine(Variance::Invariant),
                                    self.constraints,
                                    span,
                                );
                            }
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
                        span,
                    );
                }
            }
            TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => {
                self.walk_call_regions(
                    elem,
                    caller_place,
                    inst,
                    variance,
                    loans,
                    per_output_inputs,
                    span,
                );
            }
            // Scalars and `Param` carry no lifetime — no walk needed.
            //
            // `TypeKind::Fn` is a KNOWN gap tracked in the punchlist
            // ("Call-site handling ignores fn pointers"): descending
            // into a fn-pointer type's arg/return slots would emit the
            // standard covariant-return / contravariant-arg constraints,
            // but Type::Fn today carries no lifetime metadata to walk.
            // Adding that walk requires first extending Type::Fn to
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
                        self.check_operand_access(block, op, stmt.span, loans);
                    }
                    RValue::Ref(kind, place) => {
                        self.check_loan_conflict(
                            block,
                            place,
                            AccessKind::Borrow(kind.clone()),
                            stmt.span,
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
                            self.check_operand_access(block, op, stmt.span, loans);
                        }
                    }
                }
                self.check_loan_conflict(block, target, AccessKind::Write, stmt.span, loans);
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::Call(target, args) => {
                self.check_operand_access(block, target, stmt.span, loans);
                self.check_call_regions(target, args, stmt.span, loans);
                consume_operand(loans, target);
                for a in args {
                    self.check_operand_access(block, a, stmt.span, loans);
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
                if !is_elab_inserted_drop(place, stmt.span, next) {
                    self.check_loan_conflict(block, place, AccessKind::Move, stmt.span, loans);
                }
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::Unborrow(place) => {
                // Consumes the borrower Var. Its own loan is skipped in
                // check_loan_conflict (the "borrower == access_root with
                // empty path" case), but a *reborrow* of this borrower —
                // loan borrowed by s on `*r` — still needs to block `unborrow r`.
                self.check_loan_conflict(block, place, AccessKind::Move, stmt.span, loans);
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::RequireUninit(_) => {
                // Place-state validates the assertion. It is not a runtime
                // access and therefore does not participate in loan checks.
            }
        }
    }

    fn check_and_transfer_terminator(&mut self, block: &BasicBlock, loans: &mut LoanMap) {
        let terminator_span = block.terminator.span;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                self.check_operand_access(block, cond, terminator_span, loans);
                consume_operand(loans, cond);
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                // Discriminant read.
                self.check_loan_conflict(block, place, AccessKind::Read, terminator_span, loans);
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
