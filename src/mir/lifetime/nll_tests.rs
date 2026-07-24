//! NLL elaboration tests.
//!
//! Test strategy:
//! - **Snapshot**: `assert_elab_eq(input, expected)` pretty-prints the
//!   post-NLL program and compares exactly. Pins the insertion sites.
//! - **Round-trip**: input MIR without `unborrow` → `elaborate_and_check_mir`
//!   should succeed (NLL inserts on our behalf, drop-elab handles the
//!   rest). Complements snapshot by testing the whole pipeline together.
//! - **Idempotence**: elaborate twice; second run adds nothing.
//! - **Negative**: programs with unfulfilled `&out` obligations still
//!   fail after elaboration (NLL inserts naively; check surfaces error).

use crate::mir::lifetime::nll::elaborate;
use crate::mir::parser::Parser;
use crate::mir::pretty_print::pretty_print;
use crate::mir::test_util::*;
use crate::mir::type_check::Env;

/// Parse `src`, run NLL elaboration only (no other passes), and return
/// the pretty-printed result.
fn elaborate_only(src: &str) -> String {
    let mut program = Parser::new(src.to_string()).parse().expect("parse");
    let env = Env::build(&program).0;
    elaborate(&mut program, &env);
    pretty_print(&program)
}

/// Assert that NLL-elaborating `before` produces the exact
/// pretty-printed program `expected` (leading/trailing whitespace
/// trimmed). Pins insertion positions, ordering, and split-block
/// naming so an unintended change fails loudly.
#[track_caller]
fn assert_elab_eq(before: &str, expected: &str) {
    let got = elaborate_only(before);
    let a = got.trim();
    let b = expected.trim();
    if a != b {
        panic!(
            "elaborated output differs\n--- expected ---\n{}\n--- got ---\n{}",
            b, a
        );
    }
}

// ---------- Round-trip: no-`unborrow` variants of existing programs ----------

#[test]
fn roundtrip_mut_ref_read_last_use_ok() {
    // Same as unborrow_of_mut_ref_ok but without the explicit unborrow.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy r.*;
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_out_write_last_use_ok() {
    // `*r = 42` is the last use of r; unborrow should be inserted after.
    assert_no_diagnostics(
        "
        fn f() {
          x: i64;
          r: &out i64;
          entry:
            r = &out x;
            r.* = 42;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_reborrow_same_place_ok() {
    // After the first r's last use, unborrow r inserted → x thaws → s
    // can freshly borrow x.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          s: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy r.*;
            s = &mut x;
            y = copy s.*;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_field_borrow_last_use_ok() {
    assert_no_diagnostics(
        "
        struct P: Copy + Drop { a: i64 b: i64 }
        fn f(p: P) {
          r: &mut i64;
          entry:
            r = &mut p.a;
            p.a = 42;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_loop_last_use_after_loop_ok() {
    // Borrow taken before loop, used inside loop, unborrow inserted
    // after loop exit.
    assert_no_diagnostics(
        "
        extern fn use_num(n: i64);
        fn f(x: i64, b: bool) {
          r: &mut i64;
          entry:
            r = &mut x;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            call use_num(copy r.*);
            goto head
          done:
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_multi_loan_branch_of_borrows_ok() {
    // Branch of borrows: r loans {a, b}. NLL inserts one unborrow r
    // at the merge (before the direct writes).
    assert_no_diagnostics(
        "
        fn f(a: i64, b: i64, c: bool) {
          r: &mut i64;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            a = 1;
            b = 2;
            return
        }
        ",
    );
}

#[test]
fn roundtrip_natural_close_by_call_no_insert() {
    // call sink(move r) naturally closes; NLL should NOT insert an
    // extra unborrow. Program is valid either way but the pretty-
    // printed form should not have unborrow.
    let out = elaborate_only(
        "
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            call sink(move r);
            return
        }
        ",
    );
    assert!(
        !out.contains("unborrow"),
        "expected no unborrow inserted; got:\n{}",
        out
    );
}

#[test]
fn roundtrip_natural_close_by_drop_no_insert() {
    let out = elaborate_only(
        "
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            drop r;
            return
        }
        ",
    );
    assert!(
        !out.contains("unborrow"),
        "expected no unborrow inserted; got:\n{}",
        out
    );
}

// ---------- Snapshot: insertion shape ----------

#[test]
fn snapshot_intra_block_last_use_of_mut() {
    assert_elab_eq(
        "
        fn f(x: i64) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy r.*;
            x = 42;
            return
        }
        ",
        "fn f(x: i64) {
  r: &mut i64;
  y: i64;
  entry:
    r = &mut x;
    y = copy r.*;
    unborrow r;
    x = 42;
    return
}",
    );
}

#[test]
fn snapshot_out_write_last_use() {
    // `*r = 42` fulfills the &out obligation; NLL inserts unborrow
    // right after, before the return.
    assert_elab_eq(
        "
        fn f() {
          x: i64;
          r: &out i64;
          entry:
            r = &out x;
            r.* = 42;
            return
        }
        ",
        "fn f() {
  x: i64;
  r: &out i64;
  entry:
    r = &out x;
    r.* = 42;
    unborrow r;
    return
}",
    );
}

#[test]
fn snapshot_multi_loan_bind_rule() {
    // Both arms create r but never use it — bind rule fires per arm.
    // At merge, r is Moved on both sides; direct writes to a and b
    // are legal because loans are closed pre-merge.
    assert_elab_eq(
        "
        fn f(a: i64, b: i64, c: bool) {
          r: &mut i64;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            a = 1;
            b = 2;
            return
        }
        ",
        "fn f(a: i64, b: i64, c: bool) {
  r: &mut i64;
  entry:
    branch(copy c) [true: t, false: fbr]
  t:
    r = &mut a;
    unborrow r;
    goto merge
  fbr:
    r = &mut b;
    unborrow r;
    goto merge
  merge:
    a = 1;
    b = 2;
    return
}",
    );
}

#[test]
fn snapshot_cross_edge_split() {
    // r used in `t` but not in `fbr` — split entry→fbr, place
    // unborrow r on the split. In `t`, insert after the last use.
    assert_elab_eq(
        "
        extern fn use_num(n: i64);
        fn f(x: i64, b: bool) {
          r: &mut i64;
          entry:
            r = &mut x;
            branch(copy b) [true: t, false: fbr]
          t:
            call use_num(copy r.*);
            goto end
          fbr:
            goto end
          end:
            x = 42;
            return
        }
        ",
        "extern fn use_num(n: i64);

fn f(x: i64, b: bool) {
  r: &mut i64;
  entry:
    r = &mut x;
    branch(copy b) [true: t, false: entry__to__fbr]
  entry__to__fbr:
    unborrow r;
    goto fbr
  t:
    call use_num(copy r.*);
    unborrow r;
    goto end
  fbr:
    goto end
  end:
    x = 42;
    return
}",
    );
}

#[test]
fn snapshot_refparam_last_use() {
    assert_elab_eq(
        "
        fn f(x: &mut i64) {
          y: i64;
          entry:
            y = copy x.*;
            return
        }
        ",
        "fn f(x: &mut i64) {
  y: i64;
  entry:
    y = copy x.*;
    unborrow x;
    return
}",
    );
}

#[test]
fn snapshot_natural_close_no_insert() {
    // `call sink(move r)` naturally consumes r; NLL inserts nothing.
    assert_elab_eq(
        "
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            call sink(move r);
            return
        }
        ",
        "extern fn sink(r: &mut i64);

fn f(x: i64) {
  r: &mut i64;
  entry:
    r = &mut x;
    call sink(move r);
    return
}",
    );
}

#[test]
fn snapshot_reborrow_child_before_parent() {
    // r is a &out param, s reborrows it as &out r.*. Both die at
    // return; NLL must emit unborrow s BEFORE unborrow r (deepest
    // reborrow first) so s's loan is closed before r is consumed.
    assert_elab_eq(
        "
        fn f(r: &out i64) {
          s: &out i64;
          entry:
            s = &out r.*;
            s.* = 42;
            return
        }
        ",
        "fn f(r: &out i64) {
  s: &out i64;
  entry:
    s = &out r.*;
    s.* = 42;
    unborrow s;
    unborrow r;
    return
}",
    );
}

#[test]
fn snapshot_chained_reborrow_insertion_order() {
    // Three-level: r loans x, s reborrows r, t reborrows s. t is
    // consumed by call; NLL then closes s, then r.
    assert_elab_eq(
        "
        extern fn sink(t: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          s: &mut i64;
          t: &mut i64;
          entry:
            r = &mut x;
            s = &mut r.*;
            t = &mut s.*;
            call sink(move t);
            return
        }
        ",
        "extern fn sink(t: &mut i64);

fn f(x: i64) {
  r: &mut i64;
  s: &mut i64;
  t: &mut i64;
  entry:
    r = &mut x;
    s = &mut r.*;
    t = &mut s.*;
    call sink(move t);
    unborrow s;
    unborrow r;
    return
}",
    );
}

#[test]
fn snapshot_refparam_never_used_gets_entry_unborrow() {
    // A ref param that's never mentioned in the body — NLL inserts
    // unborrow at the very start of entry (position 0).
    assert_elab_eq(
        "
        fn f(x: &mut i64) {
          entry:
            return
        }
        ",
        "fn f(x: &mut i64) {
  entry:
    unborrow x;
    return
}",
    );
}

// ---------- Cross-edge insertion ----------

#[test]
fn cross_edge_insertion_when_borrower_dies_on_one_arm() {
    // r is used in `t` but not in `fbr`. NLL should split the entry→fbr
    // edge and insert unborrow r there. `t` gets an intra-block insert
    // after its last use. Direct access to x after the merge exercises
    // that the loan is fully released on both edges before end.
    assert_no_diagnostics(
        "
        extern fn use_num(n: i64);
        fn f(x: i64, b: bool) {
          r: &mut i64;
          entry:
            r = &mut x;
            branch(copy b) [true: t, false: fbr]
          t:
            call use_num(copy r.*);
            goto end
          fbr:
            goto end
          end:
            x = 42;
            return
        }
        ",
    );
}

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
    let mut program = Parser::new(src.to_string()).parse().unwrap();
    let env = Env::build(&program).0;
    elaborate(&mut program, &env);
    let after_first = pretty_print(&program);

    // Rebuild env against the elaborated program and run NLL again.
    let env2 = Env::build(&program).0;
    elaborate(&mut program, &env2);
    let after_second = pretty_print(&program);

    assert_eq!(
        after_first, after_second,
        "second NLL run changed the program; expected idempotence"
    );
}

// ---------- Reference parameters ----------

#[test]
fn reference_param_last_use_gets_unborrow() {
    // The &mut param x has cur=post=Init, so unborrowing it discharges
    // the signature obligation.
    assert_no_diagnostics(
        "
        fn f(x: &mut i64) {
          y: i64;
          entry:
            y = copy x.*;
            return
        }
        ",
    );
}

#[test]
fn out_param_written_then_unborrow_ok() {
    // &out param: obligation fulfilled by *x = ..., then last use.
    // NLL inserts unborrow x; discharges the signature obligation.
    assert_no_diagnostics(
        "
        fn f(x: &out i64) {
          entry:
            x.* = 42;
            return
        }
        ",
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
fn out_param_unused_with_abort_ok() {
    // Without the waiver: NLL would insert `unborrow r` at entry,
    // erroring on the unfulfilled &out obligation.
    assert_no_diagnostics(
        "
        fn f(r: &out i64) {
          entry:
            abort
        }
        ",
    );
}

#[test]
fn mut_move_out_then_abort_ok() {
    // After `x = move r.*`, r's cur=Uninit, but the block aborts.
    // Obligation is waived; no unborrow inserted.
    assert_no_diagnostics(
        "
        fn f(r: &mut i64) {
          x: i64;
          entry:
            x = move r.*;
            abort
        }
        ",
    );
}

#[test]
fn out_param_unused_with_unreachable_ok() {
    // Same as abort — `unreachable` also has no return-reachable path.
    assert_no_diagnostics(
        "
        fn f(r: &out i64) {
          entry:
            unreachable
        }
        ",
    );
}

#[test]
fn mixed_branch_return_arm_fulfills_ok() {
    // Return arm inits r; abort arm doesn't. NLL emits `unborrow r`
    // only on the return path.
    assert_no_diagnostics(
        "
        fn f(r: &out i64, b: bool) {
          entry:
            branch(copy b) [true: init_arm, false: die_arm]
          init_arm:
            r.* = 42;
            return
          die_arm:
            abort
        }
        ",
    );
}

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

#[test]
fn mixed_branch_snapshot_only_return_arm_gets_unborrow() {
    // The elaborated form should have unborrow only on the return
    // arm, not on the abort arm.
    let out = elaborate_only(
        "
        fn f(r: &out i64, b: bool) {
          entry:
            branch(copy b) [true: init_arm, false: die_arm]
          init_arm:
            r.* = 42;
            return
          die_arm:
            abort
        }
        ",
    );
    assert!(
        out.contains("r.* = 42") && out.contains("unborrow r"),
        "expected unborrow on the return arm; got:\n{}",
        out
    );
    // Count unborrow occurrences — should be exactly one.
    assert_eq!(
        out.matches("unborrow").count(),
        1,
        "expected exactly one unborrow (return arm only); got:\n{}",
        out
    );
}
