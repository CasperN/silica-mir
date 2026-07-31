//! NLL elaboration tests that resist promotion to fixtures.
//!
//! - **Idempotence**: elaborate twice, verify the second run adds
//!   nothing. Requires calling NLL twice from Rust; no fixture surface.
//! - **Negative**: pipeline-level errors from unfulfilled `&out`
//!   obligations. Fixture cells assert one program per file; these
//!   assertions ("some error occurred") are looser and are checked here.

use crate::mir::lifetime::nll::elaborate;
use crate::mir::parser::Parser;
use crate::mir::pretty_print::pretty_print;
use crate::mir::test_util::*;
use crate::mir::env::GlobalEnv;

// ---------- Idempotence ----------

#[test]
fn idempotent_second_run_is_noop() {
    let src = "
        fn f(x: i64) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy r.*;
            x = 42;
            return
        }
        ";
    let mut program = Parser::parse_or_panic(src);
    let env = GlobalEnv::build(&program).0;
    elaborate(&mut program, &env);
    let after_first = pretty_print(&program);

    // Rebuild env against the elaborated program and run NLL again.
    let env2 = GlobalEnv::build(&program).0;
    elaborate(&mut program, &env2);
    let after_second = pretty_print(&program);

    assert_eq!(
        after_first, after_second,
        "second NLL run changed the program; expected idempotence"
    );
}

// ---------- Negative: obligation not fulfilled ----------

#[test]
fn out_param_never_written_still_leaks() {
    // NLL inserts unborrow x at the last-use point... but there IS no
    // use. Or is there? The param is at least "alive" via signature.
    // If NLL doesn't insert anywhere, the leak-check fires. If NLL
    // inserts at entry, the unborrow itself errors on obligation.
    // Either way: error expected.
    let (errs, _) = run("
        fn f(x: &out i64) {
          entry:
            return
        }
        ");
    assert!(
        !errs.is_empty(),
        "expected some error for unfulfilled &out obligation"
    );
}

// ---------- Return-reachability waiver ----------
//
// Elaboration only inserts cleanup on paths that reach `return`. Blocks
// that only lead to `abort` or `unreachable` waive linear obligations —
// the program dies before the caller could observe missing init.

#[test]
fn mixed_branch_return_arm_still_leaks_error() {
    // Return arm does NOT init r; abort arm doesn't either. The
    // return path fails the obligation check; the abort path is
    // waived. Error is still reported for the return side.
    let (errs, _) = run("
        fn f(r: &out i64, b: bool) {
          entry:
            branch(copy b) [true: return_arm, false: die_arm]
          return_arm:
            return
          die_arm:
            abort
        }
        ");
    assert!(
        !errs.is_empty(),
        "expected an error for the return-arm's unfulfilled obligation"
    );
}
