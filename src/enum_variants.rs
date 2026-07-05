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
use crate::tc::{Env, TypeDecl};
use std::collections::{BTreeSet, HashMap, VecDeque};

#[derive(Debug, Default)]
pub struct Diagnostics {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl Diagnostics {
    fn extend(&mut self, other: Diagnostics) {
        self.errors.extend(other.errors);
        self.warnings.extend(other.warnings);
    }
}

/// State at one program point: per-Var variant set. Absent = ⊤.
type PointState = HashMap<String, BTreeSet<String>>;

pub fn check_program(env: &Env) -> Diagnostics {
    let mut d = Diagnostics::default();
    for f in env.functions.values() {
        d.extend(check_function(env, f));
    }
    d
}

fn check_function(env: &Env, func: &Function) -> Diagnostics {
    let mut d = Diagnostics::default();
    let Some(body) = &func.body else { return d; };
    if body.blocks.is_empty() {
        return d;
    }

    let locals = collect_locals(func, body);
    let entry_states = compute_entry_states(body);

    for block in &body.blocks {
        // Unvisited (dead) blocks: skip entirely. Their state is ⊥ so every
        // arm is trivially "provably unreachable" and the whole switch is
        // vacuous; noisy to complain.
        let Some(entry) = entry_states.get(&block.label) else { continue; };

        let mut state = entry.clone();
        for stmt in &block.statements {
            transfer_stmt(stmt, &mut state);
        }

        if let Terminator::SwitchEnum { place, cases } = &block.terminator {
            check_switch(env, func, body, &locals, block, place, cases, &state, &mut d);
        }
    }

    d
}

fn collect_locals(func: &Function, body: &FunctionBody) -> HashMap<String, Type> {
    let mut locals = HashMap::new();
    for (n, t) in &func.params {
        locals.insert(n.clone(), t.clone());
    }
    for (n, t) in &body.locals {
        locals.insert(n.clone(), t.clone());
    }
    locals
}

fn compute_entry_states(body: &FunctionBody) -> HashMap<String, PointState> {
    let mut states: HashMap<String, PointState> = HashMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();

    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), PointState::new());
    worklist.push_back(entry_label);

    let blocks_by_label: HashMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();

    while let Some(label) = worklist.pop_front() {
        let entry_state = states.get(&label).cloned().unwrap_or_default();
        let block = blocks_by_label[label.as_str()];

        let mut state = entry_state;
        for stmt in &block.statements {
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

fn root_var(place: &Place) -> Option<&str> {
    match place {
        Place::Var(name) => Some(name.as_str()),
        _ => None,
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
    let Some(enum_decl) = resolve_enum_of_place(env, locals, place) else {
        // Non-enum place (or unresolvable local) — tc reports it. Skip flow.
        return;
    };

    let declared: Vec<&str> = enum_decl.variants.iter().map(|(v, _)| v.as_str()).collect();
    let handled: BTreeSet<&str> = cases.iter().map(|(v, _)| v.as_str()).collect();

    // Exhaustiveness — report missing variants in declaration order.
    for variant in &declared {
        if !handled.contains(variant) {
            d.errors.push(format!(
                "In function '{}', block '{}': switchEnum on '{}' does not handle variant '{}'",
                func.name, block.label, enum_decl.name, variant
            ));
        }
    }

    // Duplicate arms — report each repeat, in occurrence order.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (variant, _) in cases {
        if !seen.insert(variant.as_str()) {
            d.errors.push(format!(
                "In function '{}', block '{}': switchEnum has duplicate arm for variant '{}'",
                func.name, block.label, variant
            ));
        }
    }

    // Per-arm flow check.
    let root = root_var(place);
    let known: Option<&BTreeSet<String>> = root.and_then(|r| state.get(r));

    let blocks_by_label: HashMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();

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
            (true, true) => d.errors.push(format!(
                "In function '{}', block '{}': switchEnum arm for variant '{}' claims unreachable but variant is reachable at this point",
                func.name, block.label, variant
            )),
            (false, false) => d.warnings.push(format!(
                "In function '{}', block '{}': switchEnum arm for variant '{}' is dead code (variant is unreachable at this point)",
                func.name, block.label, variant
            )),
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
    use super::*;
    use crate::parser::Parser;
    use crate::tc;

    fn run(src: &str) -> (Vec<String>, Vec<String>) {
        let program = Parser::new(src.to_string()).parse().unwrap_or_else(|e| {
            panic!("parse error: {}\n--- source ---\n{}", e, src)
        });
        let (env, mut errors) = tc::Env::build(&program);
        errors.extend(env.typecheck());
        let diag = check_program(&env);
        errors.extend(diag.errors);
        (errors, diag.warnings)
    }

    #[track_caller]
    fn assert_no_warnings(src: &str) {
        let (errors, warnings) = run(src);
        if !errors.is_empty() || !warnings.is_empty() {
            panic!(
                "expected success with no warnings, got:\nerrors:\n  {}\nwarnings:\n  {}\n--- source ---\n{}",
                errors.join("\n  "),
                warnings.join("\n  "),
                src
            );
        }
    }

    #[track_caller]
    fn assert_errors_contain(errors: &[String], needles: &[&str]) {
        let missing: Vec<&str> = needles
            .iter()
            .copied()
            .filter(|n| !errors.iter().any(|e| e.contains(n)))
            .collect();
        if !missing.is_empty() {
            let missing_str = missing
                .iter()
                .map(|n| format!("  {:?}", n))
                .collect::<Vec<_>>()
                .join("\n");
            let errs_str = if errors.is_empty() {
                "  (no errors)".to_string()
            } else {
                errors
                    .iter()
                    .map(|e| format!("  {}", e))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            panic!(
                "missing expected error substrings:\n{}\ngot {} error(s):\n{}",
                missing_str,
                errors.len(),
                errs_str
            );
        }
    }

    #[track_caller]
    fn assert_warnings_contain(warnings: &[String], needles: &[&str]) {
        let missing: Vec<&str> = needles
            .iter()
            .copied()
            .filter(|n| !warnings.iter().any(|w| w.contains(n)))
            .collect();
        if !missing.is_empty() {
            panic!(
                "missing expected warning substrings:\n  {}\ngot {} warning(s):\n  {}",
                missing
                    .iter()
                    .map(|n| format!("{:?}", n))
                    .collect::<Vec<_>>()
                    .join("\n  "),
                warnings.len(),
                warnings.join("\n  ")
            );
        }
    }

    // ---------- Coverage ----------

    #[test]
    fn coverage_all_variants_handled_ok() {
        assert_no_warnings(
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
        assert_no_warnings(
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
        assert_no_warnings(
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
        assert_no_warnings(
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
        assert_no_warnings(
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
        assert_no_warnings(
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
    fn flow_zero_variant_enum_ok() {
        // An enum with no variants must be switched with no arms — vacuous.
        assert_no_warnings(
            "
            enum Void { }
            fn f(v: Void) {
              entry:
                switchEnum(v) [ ]
            }
            ",
        );
    }

    #[test]
    fn flow_single_variant_enum_requires_single_arm() {
        assert_no_warnings(
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
