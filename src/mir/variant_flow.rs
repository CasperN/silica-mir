//! Enum-variant reachability analysis for `switchEnum`. Enforces:
//!
//!   - Every declared variant of the switched enum must appear as an arm.
//!   - No duplicate arm for the same variant.
//!   - An arm whose target block terminates in `unreachable` is valid only if
//!     the variant is provably unreachable at the switch point. Conversely, an
//!     arm targeting real code for a provably-unreachable variant is dead code
//!     — a warning, not an error.
//!
//! State lattice per (block-entry, place):
//!   * Absent from the map          = ⊤ (any variant possible)
//!   * `Some(subset)`               = tracked subset
//!   * The whole block unvisited by the fixed-point = ⊥ (skip; unreachable)
//!
//! We only track `Place::Var(_)`. Downcasts on projection paths
//! (`x.f as V`, `(x as U).f as V`, etc.) are rejected at check time —
//! nothing in this analysis proves the projection is the required
//! variant, so requiring an extract-to-local first keeps the checker
//! honest. Exclusive borrows (`&mut`/`&out`/`&drop`/`&uninit`) of a
//! tracked Var clobber that Var back to ⊤ for the rest of its
//! lifetime, since we can't see what the borrower does.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction, WalkPoint};
use crate::mir::helpers::*;
use crate::mir::type_check::{Env, TypeDecl};
use crate::mir::type_util::is_type_uninhabited;
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// Machine-readable diagnostic codes emitted by the variant-flow pass.
///
/// Multiple push sites that surface the same conceptual failure share
/// a code (e.g. every "declared variant missing" arm produces one
/// `SwitchNotExhaustive` diagnostic).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantFlowCode {
    /// `place as V` where flow analysis hasn't refined `place`'s
    /// variant set to (a subset containing only) `V`. Usually needs a
    /// preceding `switchEnum` arm to narrow the state.
    DowncastVariantNotRefined,
    /// Downcast applied to a projection like `s.e as V`. Variant flow
    /// only tracks root `Var`s — copy through a local first.
    DowncastOnProjection,
    /// `switchEnum` with zero arms — no control-flow successor.
    SwitchNoArms,
    /// `switchEnum` doesn't cover every declared variant of the enum.
    /// Each missing variant reports its own diagnostic.
    SwitchNotExhaustive,
    /// `switchEnum` names the same variant twice. Each repeat reports
    /// its own diagnostic.
    SwitchDuplicateArm,
    /// A `switchEnum` arm targets a block whose terminator is
    /// `unreachable`, but flow analysis proves the variant IS
    /// reachable at the switch. Declaring an arm `unreachable` is
    /// only sound when the analysis actually rules it out.
    SwitchArmFalselyUnreachable,
    /// (warning) A `switchEnum` arm exists for a variant that flow
    /// analysis proves cannot occur at this point — dead code.
    SwitchArmDeadCode,
}

impl From<VariantFlowCode> for DiagCode {
    fn from(code: VariantFlowCode) -> DiagCode {
        DiagCode::VariantFlow(code)
    }
}
use VariantFlowCode::*;

/// Build a diagnostic with the standard function/block context set.
/// Local shorthand for the builder chain used at every push site.
fn diag(
    code: impl Into<DiagCode>,
    span: Span,
    func: &Function,
    block: &BasicBlock,
    msg: String,
) -> Diagnostic {
    Diagnostic::new(code, span, msg)
        .in_function(&func.meta.name)
        .in_block(&block.label)
}

/// State at one program point: per-Var variant set. Absent = ⊤.
type PointState = IndexMap<String, BTreeSet<String>>;

struct VariantFlow;

impl Analysis for VariantFlow {
    type State = PointState;
    fn direction(&self) -> Direction {
        Direction::Forward
    }
    fn initial_state(&self) -> Self::State {
        PointState::new()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join(a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, _span: Span) {
        transfer_stmt(stmt, state);
    }
    fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
    fn refine_edge(&self, state: &mut Self::State, block: &BasicBlock, succ: &str) {
        // switchEnum arm edges refine the switched Var to the matched variant.
        let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind else {
            return;
        };
        let Some(root) = root_var(place) else {
            return;
        };
        for (variant, label) in cases {
            if label == succ {
                let mut singleton = BTreeSet::new();
                singleton.insert(variant.clone());
                state.insert(root.to_string(), singleton);
                return;
            }
        }
    }
}

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
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

    let locals = func.locals_map();
    let entry_states = dataflow::run(&VariantFlow, body);

    // `check_switch` needs the whole `body` for target-block lookups; the
    // walker only surfaces the current block, so we do the switch check in
    // a separate pass alongside the per-point downcast refinement.
    dataflow::walk_forward(&VariantFlow, body, &entry_states, |pt| match pt {
        WalkPoint::Stmt {
            state,
            block,
            stmt,
            span,
        } => {
            check_places_in_stmt(env, func, &locals, block, stmt, span, state, d);
        }
        WalkPoint::Terminator { state, block, .. } => {
            check_places_in_terminator(env, func, &locals, block, state, d);
            if let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind {
                check_switch(env, func, body, &locals, block, place, cases, state, d);
            }
        }
    });
}

/// Strict Var-only extraction. Unlike `ast::extract_path`, this returns
/// `None` for any projection (field, downcast) — enum_variants tracks only
/// top-level Var variant sets, so refinement/clobbering must not attribute
/// sub-place operations to the root.
fn root_var(place: &Place) -> Option<&str> {
    match place {
        Place::Var(name) => Some(name.as_str()),
        _ => None,
    }
}

fn check_places_in_stmt(
    env: &Env,
    func: &Function,
    locals: &IndexMap<String, Type>,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            check_downcast_refinement(env, func, locals, block, target, span, state, d);
            match rvalue {
                RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                    if let Some(p) = operand_place(op) {
                        check_downcast_refinement(env, func, locals, block, p, span, state, d);
                    }
                }
                RValue::Ref(_, p) | RValue::RawRef(p) => {
                    check_downcast_refinement(env, func, locals, block, p, span, state, d);
                }
                RValue::ArrayLit(ops) => {
                    for op in ops {
                        if let Some(p) = operand_place(op) {
                            check_downcast_refinement(env, func, locals, block, p, span, state, d);
                        }
                    }
                }
            }
        }
        StatementKind::Call(target, args) => {
            if let Some(p) = operand_place(target) {
                check_downcast_refinement(env, func, locals, block, p, span, state, d);
            }
            for a in args {
                if let Some(p) = operand_place(a) {
                    check_downcast_refinement(env, func, locals, block, p, span, state, d);
                }
            }
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            check_downcast_refinement(env, func, locals, block, place, span, state, d);
        }
    }
}

fn check_places_in_terminator(
    env: &Env,
    func: &Function,
    locals: &IndexMap<String, Type>,
    block: &BasicBlock,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let ts = block.terminator.span;
    match &block.terminator.kind {
        TerminatorKind::Branch { cond, .. } => {
            if let Some(p) = operand_place(cond) {
                check_downcast_refinement(env, func, locals, block, p, ts, state, d);
            }
        }
        TerminatorKind::SwitchEnum { place, .. } => {
            check_downcast_refinement(env, func, locals, block, place, ts, state, d);
        }
        _ => {}
    }
}

/// Verify that every `Downcast(V)` step in `place` sits at a program
/// point where the enclosing enum is proven to hold variant `V`.
///
/// Coverage:
/// - `x as V` where `x` is an enum Var: refined via preceding
///   `switchEnum(x) → V` edge.
/// - `x.f as V`, `x.f.g as V`, `(x as U).f as V`, and any Downcast at a
///   deeper path position: rejected — variant_flow only tracks state on
///   root Vars, so nothing proves the projection is the required variant.
fn check_downcast_refinement(
    env: &Env,
    func: &Function,
    locals: &IndexMap<String, Type>,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else {
        return;
    };

    for (i, step) in path.iter().enumerate() {
        let PathStep::Downcast(v) = step else {
            continue;
        };

        // Track-able case: Downcast at path[0] and root is a Var of enum
        // type. Anything else (deeper Downcast, non-enum root) is beyond
        // the current analysis and treated as unprovable.
        if i == 0 && root_is_enum_ty(&root, locals, env) {
            let known = state.get(&root);
            let refined = match known {
                // ⊥: variant set empty means the point is proven unreachable.
                // Vacuously refined; any downcast satisfies.
                Some(set) if set.is_empty() => true,
                Some(set) => set.len() == 1 && set.contains(v),
                None => false, // ⊤: any declared variant possible
            };
            if !refined {
                d.push_error(diag(
                    DowncastVariantNotRefined,
                    span,
                    func,
                    block,
                    format!(
                        "cannot downcast '{} as {}' here: '{}' is not refined to variant '{}'",
                        root, v, root, v
                    ),
                ));
            }
        } else {
            let prefix = format_place(&build_place(&root, &path[..i]));
            d.push_error(diag(
                DowncastOnProjection,
                span,
                func,
                block,
                format!(
                    "cannot downcast '{} as {}' here: variant flow only tracks root Vars, and '{}' is a projection — extract into a local first",
                    prefix, v, prefix
                ),
            ));
        }
    }
}

fn root_is_enum_ty(root: &str, locals: &IndexMap<String, Type>, env: &Env) -> bool {
    let Some(root_ty) = locals.get(root) else {
        return false;
    };
    matches!(
        &root_ty.kind,
        TypeKind::Custom(n, _, _) if matches!(env.types.get(n), Some(TypeDecl::Enum(_)))
    )
}

/// Rebuild a `Place` from `(root, steps)` — inverse of extract_path/
/// extract_path_with_deref. Used to feed `format_place` a place value
/// when the caller only has the decomposed form.
fn build_place(root: &str, steps: &[PathStep]) -> Place {
    let mut p = var_place(root);
    for step in steps {
        p = match step {
            PathStep::Field(f) => field_place(p, f.clone()),
            PathStep::Downcast(v) => downcast_place(p, v.clone()),
            PathStep::Index(Some(k)) => index_place(p, const_op(int_const(*k, IntTy::I64))),
            PathStep::Index(None) => {
                // Sentinel: dynamic-index steps only appear via
                // extract_path_with_deref, which variant_flow doesn't
                // feed into build_place. Panic if we somehow get here.
                unreachable!("variant_flow shouldn't rebuild dynamic-index paths")
            }
            PathStep::Deref => deref_place(p),
        };
    }
    p
}

fn transfer_stmt(stmt: &Statement, state: &mut PointState) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // Exclusive borrow of a tracked Var → clobber it: we can't see
            // what the borrower does. Raw pointer creation clobbers
            // for the same reason (aliasing writes possible).
            let clobber_borrowed: Option<&Place> = match rvalue {
                RValue::Ref(kind, borrowed) if !matches!(kind, RefKind::Shared) => Some(borrowed),
                RValue::RawRef(borrowed) => Some(borrowed),
                _ => None,
            };
            if let Some(borrowed) = clobber_borrowed {
                if let Some(root) = root_var(borrowed) {
                    state.shift_remove(root);
                }
            }

            // Update state[target] iff target is a Var. Writes through
            // non-Var places don't refine any tracked Var (we don't do
            // aliasing here).
            let Place::Var(t) = target else {
                return;
            };
            match rvalue {
                RValue::EnumConstr(_, _, variant, _) => {
                    let mut set = BTreeSet::new();
                    set.insert(variant.clone());
                    state.insert(t.clone(), set);
                }
                RValue::Use(op) => match op {
                    Operand::Copy(Place::Var(src)) | Operand::Move(Place::Var(src)) => {
                        if let Some(set) = state.get(src).cloned() {
                            state.insert(t.clone(), set);
                        } else {
                            state.shift_remove(t);
                        }
                    }
                    _ => {
                        state.shift_remove(t);
                    }
                },
                _ => {
                    state.shift_remove(t);
                }
            }
        }
        StatementKind::Call(_, _) => {
            // Return values flow through `&out` params; those references were
            // borrowed at some earlier assignment (which already clobbered
            // the underlying Var). Nothing to do here.
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            // Consumes the place — kill any variant refinement.
            if let Some(root) = root_var(place) {
                state.shift_remove(root);
            }
        }
    }
}

fn join(a: &PointState, b: &PointState) -> PointState {
    let mut out = PointState::new();
    for (var, va) in a {
        if let Some(vb) = b.get(var) {
            let mut u = va.clone();
            u.extend(vb.iter().cloned());
            out.insert(var.clone(), u);
        }
        // absent from b → ⊤ in b → ⊤ in join → omit
    }
    // vars only in b → ⊤ in a → ⊤ in join → omit
    out
}

fn check_switch(
    env: &Env,
    func: &Function,
    body: &FunctionBody,
    locals: &IndexMap<String, Type>,
    block: &BasicBlock,
    place: &Place,
    cases: &[(String, String)],
    state: &PointState,
    d: &mut Diagnostics,
) {
    let terminator_span = block.terminator.span;
    if cases.is_empty() {
        d.push_error(diag(
            SwitchNoArms,
            terminator_span,
            func,
            block,
            "switchEnum requires at least one arm".to_string(),
        ));
    }

    let Some(enum_decl) = resolve_enum_of_place(env, locals, place) else {
        // Non-enum place (or unresolvable local) — tc reports it. Skip flow.
        return;
    };

    let declared: Vec<&str> = enum_decl.variants.iter().map(|v| v.name.as_str()).collect();
    let handled: BTreeSet<&str> = cases.iter().map(|(v, _)| v.as_str()).collect();

    // Exhaustiveness — report missing variants in declaration order.
    for variant in &declared {
        if !handled.contains(variant) {
            d.push_error(diag(
                SwitchNotExhaustive,
                terminator_span,
                func,
                block,
                format!(
                    "switchEnum on '{}' does not handle variant '{}'",
                    enum_decl.meta.name, variant
                ),
            ));
        }
    }

    // Duplicate arms — report each repeat, in occurrence order.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (variant, _) in cases {
        if !seen.insert(variant.as_str()) {
            d.push_error(diag(
                SwitchDuplicateArm,
                terminator_span,
                func,
                block,
                format!("switchEnum has duplicate arm for variant '{}'", variant),
            ));
        }
    }

    // Per-arm flow check.
    let root = root_var(place);
    let known: Option<&BTreeSet<String>> = root.and_then(|r| state.get(r));

    let blocks_by_label = body.blocks_by_label();

    for (variant, label) in cases {
        // Skip arms for variants that don't belong to this enum (tc reports
        // that separately) and skip arms with undefined targets.
        if !declared.contains(&variant.as_str()) {
            continue;
        }
        let Some(target) = blocks_by_label.get(label.as_str()) else {
            continue;
        };
        let target_unreachable = matches!(target.terminator.kind, TerminatorKind::Unreachable);

        let variant_reachable = match known {
            Some(set) => set.contains(variant),
            None => {
                // ⊤ over declared variants, but uninhabited variants
                // (whose payload type can't be constructed) never
                // occur at runtime — treat as unreachable so an
                // `unreachable` arm for `N: never` is valid without
                // requiring prior refinement.
                let payload_ty = enum_decl
                    .variants
                    .iter()
                    .find(|v| v.name == *variant)
                    .map(|v| &v.ty);
                match payload_ty {
                    Some(ty) => !is_type_uninhabited(ty, env),
                    None => true,
                }
            }
        };

        match (target_unreachable, variant_reachable) {
            (true, true) => d.push_error(diag(
                SwitchArmFalselyUnreachable,
                terminator_span,
                func,
                block,
                format!(
                    "switchEnum arm for variant '{}' claims unreachable but variant is reachable at this point",
                    variant
                ),
            )),
            (false, false) => d.push_warning(diag(
                SwitchArmDeadCode,
                terminator_span,
                func,
                block,
                format!(
                    "switchEnum arm for variant '{}' is dead code (variant is unreachable at this point)",
                    variant
                ),
            )),
            _ => {}
        }
    }
}

fn resolve_enum_of_place<'a>(
    env: &'a Env,
    locals: &IndexMap<String, Type>,
    place: &Place,
) -> Option<&'a EnumDecl> {
    // We only need the successful branch; span doesn't matter since
    // any error is discarded.
    let ty = env
        .type_of_place(place, crate::mir::ast::Span::default(), locals)
        .ok()?;
    let TypeKind::Custom(name, _, _) = ty.kind else {
        return None;
    };
    match env.types.get(&name) {
        Some(TypeDecl::Enum(e)) => Some(e),
        _ => None,
    }
}
