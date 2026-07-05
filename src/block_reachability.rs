//! Per-function block reachability. Any block that cannot be reached from
//! the entry block via terminator successor edges is dead code — reported
//! as a warning (not an error: unsound code is caught elsewhere; dead code
//! is only suspicious).

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::tc::Env;
use std::collections::{HashMap, HashSet, VecDeque};

pub fn check_program(env: &Env) -> Diagnostics {
    let mut d = Diagnostics::default();
    for f in env.functions.values() {
        d.extend(check_function(f));
    }
    d
}

fn check_function(func: &Function) -> Diagnostics {
    let mut d = Diagnostics::default();
    let Some(body) = &func.body else { return d; };
    if body.blocks.is_empty() { return d; }

    let blocks_by_label: HashMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();

    let entry = body.blocks[0].label.as_str();
    let mut visited: HashSet<String> = HashSet::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    visited.insert(entry.to_string());
    worklist.push_back(entry.to_string());

    while let Some(label) = worklist.pop_front() {
        let Some(block) = blocks_by_label.get(label.as_str()) else { continue; };
        for succ in successors(&block.terminator) {
            if blocks_by_label.contains_key(succ) && visited.insert(succ.to_string()) {
                worklist.push_back(succ.to_string());
            }
        }
    }

    for block in &body.blocks {
        if !visited.contains(&block.label) {
            d.warnings.push(format!(
                "at {}: In function '{}': block '{}' is unreachable from entry",
                block.label_span, func.name, block.label
            ));
        }
    }

    d
}

fn successors(term: &Terminator) -> Vec<&str> {
    match term {
        Terminator::Goto(label) => vec![label.as_str()],
        Terminator::Return | Terminator::Abort | Terminator::Unreachable => vec![],
        Terminator::Branch { true_label, false_label, .. } => {
            vec![true_label.as_str(), false_label.as_str()]
        }
        Terminator::SwitchEnum { cases, .. } => {
            cases.iter().map(|(_, label)| label.as_str()).collect()
        }
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
        let d = check_program(&env);
        errors.extend(d.errors);
        (errors, d.warnings)
    }

    #[track_caller]
    fn assert_no_diagnostics(src: &str) {
        let (errors, warnings) = run(src);
        if !errors.is_empty() || !warnings.is_empty() {
            panic!(
                "expected clean run, got:\nerrors:\n  {}\nwarnings:\n  {}\n--- source ---\n{}",
                errors.join("\n  "),
                warnings.join("\n  "),
                src
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
            fn f(b: boolean) {
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
    fn loop_body_reachable_via_backedge() {
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
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
        let (errs, warns) = run(
            "
            fn f() {
              entry:
                return
              dead:
                return
            }
            ",
        );
        assert!(errs.is_empty(), "unexpected errors: {:?}", errs);
        assert_warnings_contain(
            &warns,
            &["In function 'f': block 'dead' is unreachable from entry"],
        );
    }

    #[test]
    fn multiple_unreachable_blocks_each_reported() {
        let (errs, warns) = run(
            "
            fn f() {
              entry:
                return
              dead1:
                goto dead2
              dead2:
                return
            }
            ",
        );
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
        let (errs, warns) = run(
            "
            fn f() {
              entry:
                abort
              orphan:
                return
            }
            ",
        );
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
