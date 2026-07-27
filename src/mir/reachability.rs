//! Per-function reachability analysis. Combines two concerns:
//!
//!   - Block reachability: any block that cannot be reached from the
//!     entry block via terminator successor edges is dead code
//!     (warning). Constant-folded `branch(true)`/`branch(false)` prune
//!     the untaken arm from the successor set, so blocks only
//!     reachable through a folded branch also fire the warning.
//!   - `switchEnum` arm reachability: an arm whose block terminates in
//!     `unreachable` must have its variant proven unreachable at the
//!     switch point; conversely, an arm targeting real code for a
//!     provably-unreachable variant is dead code (warning). Consumes
//!     `place_state`'s per-block variant refinement.
//!
//! The block-reachability filter runs first; arm-reachability checks
//! are skipped on unreachable blocks (dead code doesn't need per-arm
//! diagnostics on top of the block-level warning).

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::helpers::diag;
use crate::mir::place_state::analysis::{block_entry_states, InitSlot, InitState, PointState};
use crate::mir::type_check::{Env, TypeDecl};
use crate::mir::type_util::is_type_uninhabited;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Machine-readable codes emitted by the reachability pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReachabilityCode {
    /// (warning) A basic block is unreachable from the function's
    /// entry block via terminator successor edges — dead code.
    BlockUnreachable,
    /// A `switchEnum` arm targets a block whose terminator is
    /// `unreachable`, but flow analysis proves the variant IS
    /// reachable at the switch. Declaring an arm `unreachable` is
    /// only sound when the analysis actually rules it out.
    SwitchArmFalselyUnreachable,
    /// (warning) A `switchEnum` arm exists for a variant that flow
    /// analysis proves cannot occur at this point — dead code.
    SwitchArmDeadCode,
}

impl From<ReachabilityCode> for DiagCode {
    fn from(code: ReachabilityCode) -> DiagCode {
        DiagCode::Reachability(code)
    }
}

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

    let reached = compute_reachable(body);
    for block in &body.blocks {
        if !reached.contains(block.label.as_str()) {
            d.push_warning(
                Diagnostic::new(
                    ReachabilityCode::BlockUnreachable,
                    block.label_source,
                    format!("block '{}' is unreachable from entry", block.label),
                )
                .in_function(&func.meta.name),
            );
        }
    }

    // Arm reachability needs place_state's per-block variant
    // refinement; skip it for functions type_check has already
    // rejected (we may not have a well-typed enum to consult).
    let entry_states = block_entry_states(env, func);
    for block in &body.blocks {
        if !reached.contains(block.label.as_str()) {
            continue;
        }
        let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind else {
            continue;
        };
        let Some(state) = entry_states.get(&block.label) else {
            continue;
        };
        // Advance state through the block's statements so the check
        // sees the state at the terminator, not the block entry.
        let mut term_state = state.clone();
        for stmt in &block.statements {
            crate::mir::place_state::analysis::transfer_stmt_silent(env, func, stmt, &mut term_state);
        }
        check_switch_arms(env, func, body, block, place, cases, &term_state, d);
    }
}

/// BFS from the entry block, following each terminator's successors
/// but treating `branch(Const::Bool(_))` as taking only the constant's
/// arm. Blocks not visited during the traversal are unreachable.
fn compute_reachable<'a>(body: &'a FunctionBody) -> BTreeSet<&'a str> {
    let mut visited: BTreeSet<&str> = BTreeSet::new();
    let mut queue: VecDeque<&str> = VecDeque::new();
    let by_label: BTreeMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();
    let entry = body.blocks[0].label.as_str();
    visited.insert(entry);
    queue.push_back(entry);
    while let Some(label) = queue.pop_front() {
        let Some(block) = by_label.get(label) else {
            continue;
        };
        for succ in effective_successors(&block.terminator) {
            if by_label.contains_key(succ) && visited.insert(succ) {
                queue.push_back(succ);
            }
        }
    }
    visited
}

/// Terminator successors with `branch(Const::Bool(_))` folded to the
/// taken arm only. All other terminators pass through unchanged.
fn effective_successors(term: &Terminator) -> Vec<&str> {
    if let TerminatorKind::Branch {
        cond,
        true_label,
        false_label,
    } = &term.kind
    {
        if let Operand::Const(ConstVal::Bool(b)) = cond {
            return vec![if *b { true_label.as_str() } else { false_label.as_str() }];
        }
    }
    terminator_successors(term)
}

fn check_switch_arms(
    env: &Env,
    func: &Function,
    body: &FunctionBody,
    block: &BasicBlock,
    place: &Place,
    cases: &[(String, String)],
    state: &PointState,
    d: &mut Diagnostics,
) {
    let terminator_source = block.terminator.source;
    let Some(enum_decl) = resolve_enum_of_place(env, func, place) else {
        return;
    };
    let declared: BTreeSet<&str> = enum_decl.variants.iter().map(|v| v.name.as_str()).collect();
    let blocks_by_label = body.blocks_by_label();
    let known_variants = tracked_variants(state, place);

    for (variant, label) in cases {
        if !declared.contains(variant.as_str()) {
            continue;
        }
        let Some(target) = blocks_by_label.get(label.as_str()) else {
            continue;
        };
        let target_unreachable = matches!(target.terminator.kind, TerminatorKind::Unreachable);
        let variant_reachable = match &known_variants {
            Some(set) => set.contains(variant.as_str()),
            None => {
                // ⊤ over declared variants, but an uninhabited variant
                // never occurs at runtime — treat as unreachable so an
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
                ReachabilityCode::SwitchArmFalselyUnreachable,
                terminator_source,
                func,
                block,
                format!(
                    "switchEnum arm for variant '{}' claims unreachable but variant is reachable at this point",
                    variant
                ),
            )),
            (false, false) => d.push_warning(diag(
                ReachabilityCode::SwitchArmDeadCode,
                terminator_source,
                func,
                block,
                format!(
                    "switchEnum arm for variant '{}' is dead code (variant is unreachable at this point)",
                    variant
                ),
            )),
            (true, false) | (false, true) => {}
        }
    }
}

/// The set of variants that `place`'s state proves the enum might
/// currently hold, or `None` when the state carries no refinement
/// (opaque `Init`, or `place` isn't tracked).
fn tracked_variants(state: &PointState, place: &Place) -> Option<BTreeSet<String>> {
    let (root, path) = crate::mir::ast::extract_path(place)?;
    let root_state = state.locals.get(&root)?;
    let leaf = read_state_at_path(root_state, &path);
    match leaf {
        InitState::Partial(map) => {
            let variants: BTreeSet<String> = map
                .keys()
                .filter_map(|k| match k {
                    InitSlot::Variant(v) => Some(v.clone()),
                    _ => None,
                })
                .collect();
            (!variants.is_empty()).then_some(variants)
        }
        _ => None,
    }
}

fn read_state_at_path(state: &InitState, path: &[PathStep]) -> InitState {
    if path.is_empty() {
        return state.clone();
    }
    match &path[0] {
        PathStep::Field(f) => match state {
            InitState::Partial(map) => {
                let sub = map
                    .get(&InitSlot::Field(f.clone()))
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Index(Some(k)) => match state {
            InitState::Partial(map) => {
                let sub = map
                    .get(&InitSlot::Index(*k))
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Downcast(v) => match state {
            InitState::Partial(map) => map
                .get(&InitSlot::Variant(v.clone()))
                .cloned()
                .unwrap_or(InitState::Init),
            other => other.clone(),
        },
        PathStep::Deref | PathStep::Index(None) => state.clone(),
    }
}

fn resolve_enum_of_place<'a>(
    env: &'a Env,
    func: &Function,
    place: &Place,
) -> Option<&'a EnumDecl> {
    let locals = func.locals_map();
    let ty = env.type_of_place(place, &locals).ok()?;
    let TypeKind::Custom(name, _, _) = ty.kind else {
        return None;
    };
    match env.types.get(&name) {
        Some(TypeDecl::Enum(e)) => Some(e),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::mir::test_util::*;

    #[test]
    fn single_block_is_reachable() {
        assert_no_diagnostics("fn f() { entry: return }");
    }

    #[test]
    fn goto_chain_all_reachable() {
        assert_no_diagnostics(
            "
            fn f() {
              entry:
                goto middle
              middle:
                goto end
              end:
                return
            }
            ",
        );
    }

    #[test]
    fn branch_both_arms_reachable() {
        assert_no_diagnostics(
            "
            fn f(b: bool) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        );
    }

    #[test]
    fn switch_enum_arms_reachable() {
        assert_no_diagnostics(
            "
            enum Option: Copy + Drop { None: unit Some: i64 }
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
    fn loop_body_reachable_via_backedge() {
        assert_no_diagnostics(
            "
            fn f(b: bool) {
              entry:
                goto head
              head:
                branch(copy b) [true: head, false: done]
              done:
                return
            }
            ",
        );
    }

    #[test]
    fn isolated_block_is_unreachable() {
        let (errs, warns) = run("
            fn f() {
              entry:
                return
              dead:
                return
            }
            ");
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(
            &warns,
            &["In function 'f': block 'dead' is unreachable from entry"],
        );
    }

    #[test]
    fn multiple_unreachable_blocks_each_reported() {
        let (errs, warns) = run("
            fn f() {
              entry:
                return
              dead1:
                goto dead2
              dead2:
                return
            }
            ");
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(
            &warns,
            &[
                "block 'dead1' is unreachable",
                "block 'dead2' is unreachable",
            ],
        );
    }

    #[test]
    fn unreachable_terminator_still_yields_reachable_block() {
        // A block terminated by `unreachable` is still reachable if the entry
        // points to it — we only care about *predecessors*, not what the block
        // does at its end.
        assert_no_diagnostics(
            "
            fn f() {
              entry:
                goto dead
              dead:
                unreachable
            }
            ",
        );
    }

    #[test]
    fn abort_and_return_prune_successors() {
        // `abort` and `return` have no successors — anything only reachable
        // through such a block is dead.
        let (errs, warns) = run("
            fn f() {
              entry:
                abort
              orphan:
                return
            }
            ");
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(&warns, &["block 'orphan' is unreachable"]);
    }

    #[test]
    fn warning_carries_label_span() {
        // The warning's `at L:C:` points at the dead block's label, not entry.
        // With this exact source, `dead:` sits on line 4, col 1.
        let src = "fn f() {\nentry:\nreturn\ndead:\nreturn\n}";
        let (_, warns) = run(src);
        assert_warnings_contain(&warns, &["at 4:1:", "block 'dead' is unreachable"]);
    }

    #[test]
    fn branch_true_folds_false_arm_dead() {
        let (errs, warns) = run(
            "
            fn f() {
              entry:
                branch(true) [true: t, false: dead]
              t: return
              dead: return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(&warns, &["block 'dead' is unreachable"]);
    }

    #[test]
    fn branch_false_folds_true_arm_dead() {
        let (errs, warns) = run(
            "
            fn f() {
              entry:
                branch(false) [true: dead, false: fbr]
              dead: return
              fbr: return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(&warns, &["block 'dead' is unreachable"]);
    }

    #[test]
    fn folded_arm_still_reachable_via_other_pred() {
        // `shared` is the folded-out `false` arm of the branch, but a
        // live goto also targets it. Bool folding removes one edge, not
        // the block.
        assert_no_diagnostics(
            "
            fn f() {
              entry:
                branch(true) [true: mid, false: shared]
              mid:
                goto shared
              shared:
                return
            }
            ",
        );
    }
}
