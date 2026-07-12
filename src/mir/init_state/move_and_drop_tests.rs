//! Init state — moves, drops, reads, writes on whole values.
//!
//! Covers the basic per-place operations: read of a param, write-then-
//! read, move-then-read (error), reassignment after move, double-move
//! (error), operand ordering (`call f(copy x, move x)` vs.
//! `call f(move x, copy x)`), `drop` statement semantics, and read of
//! empty-struct locals.

use crate::test_util::*;

// ---------- Baseline reads/writes/moves ----------

#[test]
fn param_starts_init_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          y: i64;
          entry:
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn write_then_read_ok() {
    // After a write, `x` is Init and can be read. Sink via a
    // different local so the test isn't just `x = copy x` (which
    // is useless — nobody writes it — and, with pre-overwrite
    // drop-elab, would spuriously fail because the inserted
    // `drop x` moves `x` before the RHS gets to read it).
    assert_no_diagnostics(
        "
        fn f() {
          x: i64;
          y: i64;
          entry:
            x = 42;
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn read_of_uninit_local_error() {
    let (errs, _) = run("
        fn f() {
          x: i64;
          y: i64;
          entry:
            y = copy x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
}

#[test]
fn read_after_move_error() {
    let (errs, _) = run("
        fn f(x: i64) {
          y: i64;
          z: i64;
          entry:
            y = move x;
            z = copy x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

// ---------- Reassignment / move ordering ----------

#[test]
fn reassign_after_move_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          y: i64;
          z: i64;
          entry:
            y = move x;
            x = 42;
            z = copy x;
            return
        }
        ",
    );
}

#[test]
fn move_then_move_error() {
    let (errs, _) = run("
        fn f(x: i64) {
          y: i64;
          z: i64;
          entry:
            y = move x;
            z = move x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

#[test]
fn call_args_copy_then_move_ok() {
    // Copy first, then move — the copy sees Init, the move consumes.
    assert_no_diagnostics(
        "
        extern fn take_two(a: i64, b: i64);
        fn f(x: i64) {
          entry:
            call take_two(copy x, move x);
            return
        }
        ",
    );
}

#[test]
fn call_args_move_then_copy_error() {
    // Left-to-right operand evaluation: the second `copy` sees the
    // already-moved state and errors.
    let (errs, _) = run("
        extern fn take_two(a: i64, b: i64);
        fn f(x: i64) {
          entry:
            call take_two(move x, copy x);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

// ---------- Call target / arg init checks ----------

#[test]
fn call_target_of_uninit_error() {
    let (errs, _) = run("
        fn f() {
          g: fn(i64);
          entry:
            call copy g(1);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'g' is used before initialization"]);
}

#[test]
fn call_arg_read_of_uninit_error() {
    let (errs, _) = run("
        extern fn takes_num(a: i64);
        fn f() {
          x: i64;
          entry:
            call takes_num(copy x);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
}

// ---------- Drop statement ----------

#[test]
fn drop_consumes_like_move() {
    // `drop x` behaves like a move for init tracking: subsequent read errors.
    let (errs, _) = run("
        fn f(x: i64) {
          y: i64;
          entry:
            drop x;
            y = copy x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

#[test]
fn drop_of_uninit_error() {
    let (errs, _) = run("
        fn f() {
          x: i64;
          entry:
            drop x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
}

// ---------- Empty struct ----------

#[test]
fn empty_struct_local_starts_init() {
    // A struct with zero fields has no components to write, so a
    // declared local of that type is trivially usable. Marked
    // `Copy Drop` so the substructural checker permits the copy.
    assert_no_diagnostics(
        "
        struct Copy Drop Unit0 { }
        fn f() {
          u: Unit0;
          v: Unit0;
          entry:
            v = copy u;
            return
        }
        ",
    );
}
