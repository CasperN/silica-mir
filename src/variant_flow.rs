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
use crate::diagnostics::Diagnostics;
use crate::type_check::{Env, TypeDecl};
use crate::{push_error, push_warning};
use std::collections::{BTreeSet, HashMap, VecDeque};

/// State at one program point: per-Var variant set. Absent = ⊤.
type PointState = HashMap<String, BTreeSet<String>>;

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    if body.blocks.is_empty() {
        return;
    }

    let locals = collect_locals(func, body);
    let entry_states = compute_entry_states(body);

    for block in &body.blocks {
        // Unvisited (dead) blocks: skip entirely. Their state is ⊥ so every
        // arm is trivially "provably unreachable" and the whole switch is
        // vacuous; noisy to complain.
        let Some(entry) = entry_states.get(&block.label) else { continue; };

        let mut state = entry.clone();
        for (stmt, span) in &block.statements {
            check_places_in_stmt(env, func, &locals, block, stmt, *span, &state, d);
            transfer_stmt(stmt, &mut state);
        }
        check_places_in_terminator(env, func, &locals, block, &state, d);
        if let Terminator::SwitchEnum { place, cases } = &block.terminator {
            check_switch(env, func, body, &locals, block, place, cases, &state, d);
        }
    }
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
    locals: &HashMap<String, Type>,
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
        Statement::Drop(place) => {
            check_downcast_refinement(env, func, locals, block, place, span, state, d);
        }
    }
}

fn check_places_in_terminator(
    env: &Env,
    func: &Function,
    locals: &HashMap<String, Type>,
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

/// Verify that every `Downcast(V)` step at the root position of `place` sits
/// at a program point where the tracked variant set of the root is exactly
/// `{V}` (i.e. refined by a preceding `switchEnum` → V edge).
/// Deeper downcasts (`x.f as V`) require sub-place variant tracking and are
/// silently skipped in this phase.
fn check_downcast_refinement(
    env: &Env,
    func: &Function,
    locals: &HashMap<String, Type>,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = locals.get(&root) else { return; };
    let root_is_enum = matches!(
        root_ty,
        Type::Custom(n) if matches!(env.types.get(n), Some(TypeDecl::Enum(_)))
    );
    if !root_is_enum { return; }

    for (i, step) in path.iter().enumerate() {
        if let PathStep::Downcast(v) = step {
            if i > 0 { continue; } // deeper — not yet tracked
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
                    d, span, func, block,
                    "cannot downcast '{} as {}' here: '{}' is not refined to variant '{}'",
                    root, v, root, v
                );
            }
        }
    }
}

fn collect_locals(func: &Function, body: &FunctionBody) -> HashMap<String, Type> {
    let mut locals = HashMap::new();
    for p in &func.params {
        locals.insert(p.name.clone(), p.ty.clone());
    }
    for l in &body.locals {
        locals.insert(l.name.clone(), l.ty.clone());
    }
    locals
}

fn compute_entry_states(body: &FunctionBody) -> HashMap<String, PointState> {
    let mut states: HashMap<String, PointState> = HashMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();

    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), PointState::new());
    worklist.push_back(entry_label);

    let blocks_by_label = body.blocks_by_label();

    while let Some(label) = worklist.pop_front() {
        let entry_state = states.get(&label).cloned().unwrap_or_default();
        let block = blocks_by_label[label.as_str()];

        let mut state = entry_state;
        for (stmt, _) in &block.statements {
            transfer_stmt(stmt, &mut state);
        }

        for (succ_label, refinement) in successor_edges(&block.terminator) {
            if !blocks_by_label.contains_key(succ_label.as_str()) {
                // Undefined block; tc reports this. Just skip the edge.
                continue;
            }
            let mut succ_new = state.clone();
            if let Some((var, variant)) = refinement {
                let mut singleton = BTreeSet::new();
                singleton.insert(variant);
                succ_new.insert(var, singleton);
            }
            let joined = match states.get(&succ_label) {
                None => succ_new,
                Some(existing) => join(existing, &succ_new),
            };
            if states.get(&succ_label).map_or(true, |cur| cur != &joined) {
                states.insert(succ_label.clone(), joined);
                worklist.push_back(succ_label);
            }
        }
    }

    states
}

fn successor_edges(term: &Terminator) -> Vec<(String, Option<(String, String)>)> {
    match term {
        Terminator::Goto(label) => vec![(label.clone(), None)],
        Terminator::Return | Terminator::Abort | Terminator::Unreachable => vec![],
        Terminator::Branch { true_label, false_label, .. } => vec![
            (true_label.clone(), None),
            (false_label.clone(), None),
        ],
        Terminator::SwitchEnum { place, cases } => {
            let root = root_var(place).map(|s| s.to_string());
            cases
                .iter()
                .map(|(variant, label)| {
                    let refinement = root
                        .as_ref()
                        .map(|r| (r.clone(), variant.clone()));
                    (label.clone(), refinement)
                })
                .collect()
        }
    }
}

fn transfer_stmt(stmt: &Statement, state: &mut PointState) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            // Exclusive borrow of a tracked Var → clobber it: we can't see
            // what the borrower does.
            if let RValue::Ref(kind, borrowed) = rvalue {
                if !matches!(kind, RefKind::Shared) {
                    if let Some(root) = root_var(borrowed) {
                        state.remove(root);
                    }
                }
            }

            // Update state[target] iff target is a Var. Writes through
            // non-Var places don't refine any tracked Var (we don't do
            // aliasing here).
            let Place::Var(t) = target else { return; };
            match rvalue {
                RValue::EnumConstr(_, variant, _) => {
                    let mut set = BTreeSet::new();
                    set.insert(variant.clone());
                    state.insert(t.clone(), set);
                }
                RValue::Use(op) => {
                    match op {
                        Operand::Copy(Place::Var(src))
                        | Operand::Move(Place::Var(src)) => {
                            if let Some(set) = state.get(src).cloned() {
                                state.insert(t.clone(), set);
                            } else {
                                state.remove(t);
                            }
                        }
                        _ => {
                            state.remove(t);
                        }
                    }
                }
                _ => {
                    state.remove(t);
                }
            }
        }
        Statement::Call(_, _) => {
            // Return values flow through `&out` params; those references were
            // borrowed at some earlier assignment (which already clobbered
            // the underlying Var). Nothing to do here.
        }
        Statement::Drop(place) => {
            // Drop consumes the place — kill any variant refinement.
            if let Some(root) = root_var(place) {
                state.remove(root);
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
    locals: &HashMap<String, Type>,
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
                d, ts, func, block,
                "switchEnum on '{}' does not handle variant '{}'", enum_decl.name, variant
            );
        }
    }

    // Duplicate arms — report each repeat, in occurrence order.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (variant, _) in cases {
        if !seen.insert(variant.as_str()) {
            push_error!(
                d, ts, func, block,
                "switchEnum has duplicate arm for variant '{}'", variant
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
        let Some(target) = blocks_by_label.get(label.as_str()) else { continue; };
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
    locals: &HashMap<String, Type>,
    place: &Place,
) -> Option<&'a EnumDecl> {
    let ty = env.infer_place_type(place, locals).ok()?;
    let Type::Custom(name) = ty else { return None; };
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
            enum Option { None: unit Some: number }
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
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: end]
              end: return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["does not handle variant 'Some'"],
        );
    }

    #[test]
    fn coverage_multiple_missing_reported() {
        let (errs, _) = run(
            "
            enum E { A: number B: number C: number }
            fn f(e: E) {
              entry:
                switchEnum(e) [A: end]
              end: return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["does not handle variant 'B'", "does not handle variant 'C'"],
        );
    }

    #[test]
    fn coverage_duplicate_arm_error() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: a, None: b, Some: c]
              a: return
              b: return
              c: return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["duplicate arm for variant 'None'"],
        );
    }

    #[test]
    fn coverage_unknown_variant_still_reported_and_missing_still_fires() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [Wat: end]
              end: return
            }
            ",
        );
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
            enum Option { None: unit Some: number }
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
            enum Option { None: unit Some: number }
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
            enum Option { None: unit Some: number }
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
            enum Option { None: unit Some: number }
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
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_unreachable_arm_after_reassign_error() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o1: Option) {
              o: Option;
              entry:
                o = Option::None(unit);
                o = move o1;
                switchEnum(o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_unreachable_arm_after_ambiguous_join_error() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
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
        let (errs, warns) = run(
            "
            enum Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: s]
              n: return
              s: return
            }
            ",
        );
        assert!(errs.is_empty(), "did not expect errors, got: {:?}", errs);
        assert_warnings_contain(
            &warns,
            &["variant 'Some' is dead code"],
        );
    }

    // ---------- Conservative places ----------

    #[test]
    fn flow_deref_switch_place_treated_as_top() {
        // switchEnum on *r treats state as ⊤ — an unreachable arm claim fails
        // even if a preceding assignment through the ref narrowed the value.
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(r: &mut Option) {
              entry:
                *r = Option::None(unit);
                switchEnum(*r) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_field_switch_place_treated_as_top() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            struct S { o: Option }
            fn f(s: S) {
              entry:
                switchEnum(s.o) [None: n, Some: dead]
              n: return
              dead: unreachable
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_exclusive_borrow_clobbers_refinement() {
        // After `r = &mut o`, o's variant tracking is clobbered even though
        // r isn't used before the switch.
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
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
            enum Option { None: unit Some: number }
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
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_drop_borrow_clobbers_refinement() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
        assert_errors_contain(
            &errs,
            &["variant 'Some' claims unreachable but variant is reachable"],
        );
    }

    #[test]
    fn flow_uninit_borrow_clobbers_refinement() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
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
        let (errs, warns) = run(
            "
            enum Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::None(unit);
                switchEnum(o) [None: n, Some: trap]
              n: return
              trap: abort
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(&warns, &["variant 'Some' is dead code"]);
    }

    // ---------- Downcast refinement (read-site) ----------

    #[test]
    fn downcast_read_without_refinement_error() {
        // `o as Some` in a block where `o` is still ⊤ — the read might see
        // the None variant's payload, so this is unsound.
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                x = copy o as Some;
                return
            }
            ",
        );
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
            enum Option { None: unit Some: number }
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
    fn downcast_in_switch_place_without_refinement_error() {
        // switchEnum(o as X) itself is a read of `o as X` — refinement
        // required.
        let (errs, _) = run(
            "
            enum Inner { P: unit Q: unit }
            enum Outer { X: Inner Y: unit }
            fn f(o: Outer) {
              entry:
                switchEnum(o as X) [P: pb, Q: qb]
              pb: return
              qb: return
            }
            ",
        );
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
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
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
            ",
        );
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
        let (errs, _) = run(
            "
            enum Void { }
            fn f(v: Void) {
              entry:
                switchEnum(v) [ ]
            }
            ",
        );
        assert_errors_contain(&errs, &["switchEnum requires at least one arm"]);
    }

    #[test]
    fn flow_single_variant_enum_requires_single_arm() {
        assert_no_diagnostics(
            "
            enum One { Only: number }
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
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                return
              dead_switch:
                switchEnum(o) [None: dead_switch]
            }
            ",
        );
        assert!(
            errs.iter().all(|e| !e.contains("does not handle variant")),
            "unexpected exhaustiveness error in dead block: {:?}",
            errs,
        );
    }
}
