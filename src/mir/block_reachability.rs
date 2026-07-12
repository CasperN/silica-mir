//! Per-function block reachability. Any block that cannot be reached from
//! the entry block via terminator successor edges is dead code — reported
//! as a warning (not an error: unsound code is caught elsewhere; dead code
//! is only suspicious).
//!
//! Implemented as a trivial forward `dataflow::Analysis` with unit state.
//! A block is reachable iff the fixpoint records a state for it.

use crate::ast::*;
use crate::dataflow::{self, Analysis, Direction};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::type_check::Env;

/// Machine-readable codes emitted by the block-reachability pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockReachabilityCode {
    /// (warning) A basic block is unreachable from the function's
    /// entry block via terminator successor edges — dead code.
    BlockUnreachable,
}

impl From<BlockReachabilityCode> for DiagCode {
    fn from(code: BlockReachabilityCode) -> DiagCode {
        DiagCode::BlockReachability(code)
    }
}

struct Reachability;

impl Analysis for Reachability {
    type State = ();
    fn direction(&self) -> Direction {
        Direction::Forward
    }
    fn initial_state(&self) -> Self::State {}
    fn join(&self, _: &Self::State, _: &Self::State) -> Self::State {}
    fn transfer_stmt(&self, _: &mut Self::State, _: &Statement) {}
    fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
}

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(f, d);
    }
}

fn check_function(func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let reached = dataflow::run(&Reachability, body);
    for block in &body.blocks {
        if !reached.contains_key(&block.label) {
            d.push_warning(
                Diagnostic::new(
                    BlockReachabilityCode::BlockUnreachable,
                    block.label_span,
                    format!("block '{}' is unreachable from entry", block.label),
                )
                .in_function(&func.name),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

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
            enum Copy Drop Option { None: unit Some: i64 }
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
}
