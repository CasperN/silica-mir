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
//! We only track `Place::Var(_)`. Field paths and derefs are always ⊤ — the
//! first-pass analysis doesn't try to alias-track through references or into
//! aggregates. Exclusive borrows (`&mut`/`&out`/`&drop`/`&uninit`) of a tracked
//! Var clobber that Var back to ⊤ for the rest of its lifetime, since we can't
//! see what the borrower does.

use crate::ast::*;
use crate::dataflow::{self, Analysis, Direction, WalkPoint};
use crate::diagnostics::Diagnostics;
use crate::type_check::{Env, TypeDecl};
use crate::{push_error, push_warning};
use indexmap::IndexMap;
use std::collections::BTreeSet;

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
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement) {
        transfer_stmt(stmt, state);
    }
    fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
    fn refine_edge(&self, state: &mut Self::State, block: &BasicBlock, succ: &str) {
        // switchEnum arm edges refine the switched Var to the matched variant.
        let Terminator::SwitchEnum { place, cases } = &block.terminator else {
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
            if let Terminator::SwitchEnum { place, cases } = &block.terminator {
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
    match stmt {
        Statement::Assign(target, rvalue) => {
            check_downcast_refinement(env, func, locals, block, target, span, state, d);
            match rvalue {
                RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
                    if let Some(p) = operand_place(op) {
                        check_downcast_refinement(env, func, locals, block, p, span, state, d);
                    }
                }
                RValue::Ref(_, p) => {
                    check_downcast_refinement(env, func, locals, block, p, span, state, d);
                }
            }
        }
        Statement::Call(target, args) => {
            if let Some(p) = operand_place(target) {
                check_downcast_refinement(env, func, locals, block, p, span, state, d);
            }
            for a in args {
                if let Some(p) = operand_place(a) {
                    check_downcast_refinement(env, func, locals, block, p, span, state, d);
                }
            }
        }
        Statement::Drop(place) | Statement::Unborrow(place) => {
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
    let ts = block.terminator_span;
    match &block.terminator {
        Terminator::Branch { cond, .. } => {
            if let Some(p) = operand_place(cond) {
                check_downcast_refinement(env, func, locals, block, p, ts, state, d);
            }
        }
        Terminator::SwitchEnum { place, .. } => {
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
                push_error!(
                    d,
                    span,
                    func,
                    block,
                    "cannot downcast '{} as {}' here: '{}' is not refined to variant '{}'",
                    root,
                    v,
                    root,
                    v
                );
            }
        } else {
            let prefix = format_place_up_to(&root, &path[..i]);
            push_error!(
                d,
                span,
                func,
                block,
                "cannot downcast '{} as {}' here: variant flow only tracks root Vars, and '{}' is a projection — extract into a local first",
                prefix,
                v,
                prefix
            );
        }
    }
}

fn root_is_enum_ty(root: &str, locals: &IndexMap<String, Type>, env: &Env) -> bool {
    let Some(root_ty) = locals.get(root) else {
        return false;
    };
    matches!(
        root_ty,
        Type::Custom(n) if matches!(env.types.get(n), Some(TypeDecl::Enum(_)))
    )
}

fn format_place_up_to(root: &str, prefix: &[PathStep]) -> String {
    let mut s = root.to_string();
    for step in prefix {
        match step {
            PathStep::Field(f) => {
                s.push('.');
                s.push_str(f);
            }
            PathStep::Downcast(v) => {
                s.push_str(" as ");
                s.push_str(v);
            }
            PathStep::Deref => {
                s = format!("*{}", s);
            }
        }
    }
    s
}

fn transfer_stmt(stmt: &Statement, state: &mut PointState) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            // Exclusive borrow of a tracked Var → clobber it: we can't see
            // what the borrower does.
            if let RValue::Ref(kind, borrowed) = rvalue {
                if !matches!(kind, RefKind::Shared) {
                    if let Some(root) = root_var(borrowed) {
                        state.shift_remove(root);
                    }
                }
            }

            // Update state[target] iff target is a Var. Writes through
            // non-Var places don't refine any tracked Var (we don't do
            // aliasing here).
            let Place::Var(t) = target else {
                return;
            };
            match rvalue {
                RValue::EnumConstr(_, variant, _) => {
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
        Statement::Call(_, _) => {
            // Return values flow through `&out` params; those references were
            // borrowed at some earlier assignment (which already clobbered
            // the underlying Var). Nothing to do here.
        }
        Statement::Drop(place) | Statement::Unborrow(place) => {
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
    let ts = block.terminator_span;
    if cases.is_empty() {
        push_error!(d, ts, func, block, "switchEnum requires at least one arm");
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
            push_error!(
                d,
                ts,
                func,
                block,
                "switchEnum on '{}' does not handle variant '{}'",
                enum_decl.name,
                variant
            );
        }
    }

    // Duplicate arms — report each repeat, in occurrence order.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (variant, _) in cases {
        if !seen.insert(variant.as_str()) {
            push_error!(
                d,
                ts,
                func,
                block,
                "switchEnum has duplicate arm for variant '{}'",
                variant
            );
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
        let target_unreachable = matches!(target.terminator, Terminator::Unreachable);

        let variant_reachable = match known {
            Some(set) => set.contains(variant),
            None => true, // ⊤
        };

        match (target_unreachable, variant_reachable) {
            (true, true) => push_error!(
                d, ts, func, block,
                "switchEnum arm for variant '{}' claims unreachable but variant is reachable at this point",
                variant
            ),
            (false, false) => push_warning!(
                d, ts, func, block,
                "switchEnum arm for variant '{}' is dead code (variant is unreachable at this point)",
                variant
            ),
            _ => {}
        }
    }
}

fn resolve_enum_of_place<'a>(
    env: &'a Env,
    locals: &IndexMap<String, Type>,
    place: &Place,
) -> Option<&'a EnumDecl> {
    let ty = env.infer_place_type(place, locals).ok()?;
    let Type::Custom(name) = ty else {
        return None;
    };
    match env.types.get(&name) {
        Some(TypeDecl::Enum(e)) => Some(e),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Coverage ----------

    #[test]
    fn coverage_all_variants_handled_ok() {
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: s]
              n: return
              s: return
            }
            ",
        );
    }

    #[test]
    fn coverage_missing_variant_error() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: end]
              end: return
            }
            ");
        assert_errors_contain(&errs, &["does not handle variant 'Some'"]);
    }

    #[test]
    fn coverage_multiple_missing_reported() {
        let (errs, _) = run("
            enum E { A: number B: number C: number }
            fn f(e: E) {
              entry:
                switchEnum(e) [A: end]
              end: return
            }
            ");
        assert_errors_contain(
            &errs,
            &["does not handle variant 'B'", "does not handle variant 'C'"],
        );
    }

    #[test]
    fn coverage_duplicate_arm_error() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: a, None: b, Some: c]
              a: return
              b: return
              c: return
            }
            ");
        assert_errors_contain(&errs, &["duplicate arm for variant 'None'"]);
    }

    #[test]
    fn coverage_unknown_variant_still_reported_and_missing_still_fires() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [Wat: end]
              end: return
            }
            ");
        // tc reports the unknown variant; flow reports the two missing ones.
        assert_errors_contain(
            &errs,
            &[
                "variant 'Wat' is not part of enum 'Option'",
                "does not handle variant 'None'",
                "does not handle variant 'Some'",
            ],
        );
    }

    // ---------- Flow: provable unreachable arms ----------

    #[test]
    fn flow_unreachable_after_construction_ok() {
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
    }

    #[test]
    fn flow_unreachable_after_prior_switch_ok() {
        // Inside the Some arm, o is refined to {Some}; the nested switch can
        // then claim None is unreachable.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n_arm, Some: s_arm]
              n_arm: return
              s_arm:
                switchEnum(o) [None: nested_dead, Some: s_body]
              s_body: return
              nested_dead: unreachable
            }
            ",
        );
    }

    #[test]
    fn flow_unreachable_after_abort_join_ok() {
        // One predecessor of `join` aborts; the other assigns None. At `join`,
        // o is refined to {None} — Some arm is provably unreachable.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(b: boolean) {
              o: Option;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                o = Option::None(unit);
                goto join
              fbr:
                abort
              join:
                switchEnum(o) [None: end, Some: dead]
              end: return
              dead: unreachable
            }
            ",
        );
    }

    #[test]
    fn flow_unreachable_target_may_contain_statements_ok() {
        // A block that terminates in `unreachable` may carry debug/printf
        // statements; still counts as an unreachable-terminated arm target.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              x: number;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead:
                x = 999;
                unreachable
            }
            ",
        );
    }

    // ---------- Flow: unprovable claims ----------

    #[test]
    fn flow_unreachable_arm_on_parameter_error() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_unreachable_arm_after_reassign_error() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o1: Option) {
              o: Option;
              entry:
                o = Option::None(unit);
                o = move o1;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_unreachable_arm_after_ambiguous_join_error() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(b: boolean) {
              o: Option;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                o = Option::None(unit);
                goto join
              fbr:
                o = Option::Some(42);
                goto join
              join:
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    // ---------- Dead-code warning ----------

    #[test]
    fn flow_dead_code_variant_real_target_warning() {
        // o is provably None, but the Some arm still targets real code. That's
        // dead code — a warning, not an error.
        let (errs, warns) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: s]
              n: return
              s: return
            }
            ");
        assert!(errs.is_empty(), "did not expect errors, got: {:?}", errs);
        assert_warnings_contain(&warns, &["variant 'Some' is dead code"]);
    }

    // ---------- Conservative places ----------

    #[test]
    fn flow_deref_switch_place_treated_as_top() {
        // switchEnum on *r treats state as ⊤ — an unreachable arm claim fails
        // even if a preceding assignment through the ref narrowed the value.
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(r: &mut Option) {
              entry:
                *r = Option::None(unit);
                switchEnum(*r) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_field_switch_place_treated_as_top() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            struct S { o: Option }
            fn f(s: S) {
              entry:
                switchEnum(s.o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_exclusive_borrow_clobbers_refinement() {
        // After `r = &mut o`, o's variant tracking is clobbered even though
        // r isn't used before the switch.
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              r: &mut Option;
              entry:
                o = Option::None(unit);
                r = &mut o;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_shared_borrow_does_not_clobber() {
        // Shared borrow can't mutate; refinement survives.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              r: &Option;
              entry:
                o = Option::None(unit);
                r = &o;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
    }

    #[test]
    fn flow_out_borrow_clobbers_refinement() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              r: &out Option;
              entry:
                o = Option::None(unit);
                r = &out o;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_drop_borrow_clobbers_refinement() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              r: &drop Option;
              entry:
                o = Option::None(unit);
                r = &drop o;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_uninit_borrow_clobbers_refinement() {
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              r: &uninit Option;
              entry:
                o = Option::None(unit);
                r = &uninit o;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_arm_target_with_abort_is_not_an_impossibility_marker() {
        // `abort` terminates the block but isn't the "impossible" marker —
        // only `unreachable` is. So a variant provably-dead whose arm points
        // at an `abort` block should be surfaced as dead-code (warning),
        // not silently accepted as a proof of impossibility.
        let (errs, warns) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: trap]
              n: return
              trap: abort
            }
            ");
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(&warns, &["variant 'Some' is dead code"]);
    }

    // ---------- Downcast refinement (read-site) ----------

    #[test]
    fn downcast_read_without_refinement_error() {
        // `o as Some` in a block where `o` is still ⊤ — the read might see
        // the None variant's payload, so this is unsound.
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                x = copy o as Some;
                return
            }
            ");
        assert_errors_contain(
            &errs,
            &["cannot downcast 'o as Some' here: 'o' is not refined to variant 'Some'"],
        );
    }

    #[test]
    fn downcast_read_in_refined_arm_ok() {
        // Inside the `Some` arm of a switchEnum on o, o is refined to {Some}
        // and `o as Some` is valid.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                switchEnum(o) [None: n, Some: s]
              s:
                x = copy o as Some;
                return
              n: return
            }
            ",
        );
    }

    #[test]
    fn downcast_on_field_of_struct_errors() {
        // `switchEnum(w.e as A)`: variant_flow can't prove w.e is variant A,
        // since it only tracks root Vars. Rejected.
        let (errs, _) = run("
            enum Copy Drop Sub { S1: unit S2: unit }
            enum Copy Drop Inner { A: Sub B: unit }
            struct Copy Drop Wrap { e: Inner }
            fn f(w: Wrap) {
              entry:
                switchEnum(w.e as A) [S1: s1, S2: s2]
              s1: return
              s2: return
            }
            ");
        assert_errors_contain(
            &errs,
            &["cannot downcast 'w.e as A' here"],
        );
    }

    #[test]
    fn nested_downcast_after_refinement_ok() {
        // `switchEnum(o as X.inner)` where o is refined to X: the outer
        // Downcast is at path[0] and root o is enum-typed → tracked.
        // The trailing `.inner` field access doesn't add a Downcast.
        assert_no_diagnostics(
            "
            enum Copy Drop Sub { S1: unit S2: unit }
            struct Copy Drop Wrap { inner: Sub }
            enum Copy Drop Outer { X: Wrap Y: unit }
            fn f(o: Outer) {
              entry:
                switchEnum(o) [X: x_lbl, Y: y_lbl]
              x_lbl:
                switchEnum(o as X.inner) [S1: s1, S2: s2]
              y_lbl: return
              s1: return
              s2: return
            }
            ",
        );
    }

    #[test]
    fn downcast_in_switch_place_without_refinement_error() {
        // switchEnum(o as X) itself is a read of `o as X` — refinement
        // required.
        let (errs, _) = run("
            enum Inner { P: unit Q: unit }
            enum Outer { X: Inner Y: unit }
            fn f(o: Outer) {
              entry:
                switchEnum(o as X) [P: pb, Q: qb]
              pb: return
              qb: return
            }
            ");
        assert_errors_contain(
            &errs,
            &["cannot downcast 'o as X' here: 'o' is not refined to variant 'X'"],
        );
    }

    // ---------- Loops ----------

    #[test]
    fn flow_switch_in_loop_widens_variant_correctly() {
        // In the loop body, o is reassigned to Some; on next iteration head,
        // o could be None (initial) or Some (from prior iteration). Any
        // unreachable arm claim should fail.
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(b: boolean) {
              o: Option;
              entry:
                o = Option::None(unit);
                goto head
              head:
                switchEnum(o) [None: body, Some: dead]
              body:
                o = Option::Some(42);
                branch(copy b) [true: head, false: done]
              done:
                return
              dead: unreachable
            }
            ");
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    // ---------- Corner cases ----------

    #[test]
    fn switch_with_no_arms_error() {
        // `switchEnum(x) [ ]` doesn't terminate the block (no successors) —
        // use `unreachable` instead. Values of zero-variant enums are
        // uninspectable, which naturally follows.
        let (errs, _) = run("
            enum Void { }
            fn f(v: Void) {
              entry:
                switchEnum(v) [ ]
            }
            ");
        assert_errors_contain(&errs, &["switchEnum requires at least one arm"]);
    }

    #[test]
    fn flow_single_variant_enum_requires_single_arm() {
        assert_no_diagnostics(
            "
            enum Copy Drop One { Only: number }
            fn f(o: One) {
              entry:
                switchEnum(o) [Only: end]
              end: return
            }
            ",
        );
    }

    #[test]
    fn flow_switch_in_dead_block_is_skipped() {
        // The block `dead_switch` is unreachable from entry, so the flow
        // analysis skips it — including its non-exhaustive switch. tc's
        // structural checks still run and might complain, but our flow-only
        // errors (missing-variant, unreachable-claim) should not appear here.
        let (errs, _) = run("
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                return
              dead_switch:
                switchEnum(o) [None: dead_switch]
            }
            ");
        assert!(
            errs.iter().all(|e| !e.contains("does not handle variant")),
            "unexpected exhaustiveness error in dead block: {:?}",
            errs,
        );
    }
}
