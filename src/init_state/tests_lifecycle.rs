//! Init state dataflow — value lifecycle tests.
//!
//! Covers baseline reads/writes/moves, partial init, joins, terminator
//! reads, projections, downcast writes, empty struct, calls, drop
//! statement, reassignment, and loop convergence.

use crate::test_util::*;

// ---------- Baseline (unchanged from phase 1) ----------

#[test]
fn param_starts_init_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          y: number;
          entry:
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn write_then_read_ok() {
    assert_no_diagnostics(
        "
        fn f() {
          x: number;
          entry:
            x = 42;
            x = copy x;
            return
        }
        ",
    );
}

#[test]
fn read_of_uninit_local_error() {
    let (errs, _) = run("
        fn f() {
          x: number;
          y: number;
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
        fn f(x: number) {
          y: number;
          z: number;
          entry:
            y = move x;
            z = copy x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

#[test]
fn join_disagreement_produces_diverged_error() {
    let (errs, _) = run("
        fn f(b: boolean) {
          x: number;
          y: number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            x = 1;
            goto merge
          fbr:
            goto merge
          merge:
            y = copy x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
}

// ---------- Partial init ----------

#[test]
fn field_writes_complete_init_ok() {
    // Writing every declared field of a struct-typed local promotes it
    // to fully Init.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          a: number;
          entry:
            p.x = 1;
            p.y = 2;
            a = copy p.x;
            return
        }
        ",
    );
}

#[test]
fn partial_field_write_leaves_root_partial_error() {
    // Only one field written; the whole struct is not fully init and
    // reading it errors.
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f() {
          p: P;
          q: P;
          entry:
            p.x = 1;
            q = copy p;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is not fully initialized here"]);
}

#[test]
fn read_uninit_field_of_partial_struct_error() {
    // Field-granular: writing p.x doesn't init p.y — reading p.y errors.
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f() {
          p: P;
          a: number;
          entry:
            p.x = 1;
            a = copy p.y;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is used before initialization"]);
}

#[test]
fn move_of_field_leaves_other_fields_init_ok() {
    // Struct comes in fully-init from a param; moving one field must
    // leave the other still readable. Elaboration inserts the drop
    // for the remaining p.y automatically.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f(p: P) {
          a: number;
          b: number;
          entry:
            a = move p.x;
            b = copy p.y;
            return
        }
        ",
    );
}

#[test]
fn move_of_field_then_read_that_field_error() {
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f(p: P) {
          a: number;
          b: number;
          entry:
            a = move p.x;
            b = copy p.x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is used after move"]);
}

#[test]
fn nested_field_writes_complete_init_ok() {
    // Inner struct fields inited via nested paths; the whole outer
    // struct collapses to Init once every leaf is written.
    assert_no_diagnostics(
        "
        struct Copy Drop Inner { a: number b: number }
        struct Copy Drop Outer { i: Inner c: number }
        fn f() {
          o: Outer;
          n: number;
          entry:
            o.i.a = 1;
            o.i.b = 2;
            o.c = 3;
            n = copy o.i.a;
            return
        }
        ",
    );
}

#[test]
fn nested_partial_read_of_uninit_inner_field_error() {
    let (errs, _) = run("
        struct Inner { a: number b: number }
        struct Outer { i: Inner c: number }
        fn f() {
          o: Outer;
          n: number;
          entry:
            o.i.a = 1;
            o.c = 3;
            n = copy o.i.b;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

#[test]
fn whole_struct_assign_after_partial_ok() {
    // Even if we partially init, a whole-struct assign resets to Init.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f(src: P) {
          p: P;
          a: number;
          entry:
            p.x = 1;
            p = move src;
            a = copy p.y;
            return
        }
        ",
    );
}

// ---------- Joins ----------

#[test]
fn join_agree_init_ok() {
    assert_no_diagnostics(
        "
        fn f(b: boolean) {
          x: number;
          y: number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            x = 1;
            goto merge
          fbr:
            x = 2;
            goto merge
          merge:
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn aborting_predecessor_doesnt_pollute_join() {
    assert_no_diagnostics(
        "
        fn f(b: boolean) {
          x: number;
          y: number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            x = 1;
            goto merge
          fbr:
            abort
          merge:
            y = copy x;
            return
        }
        ",
    );
}

// ---------- Terminator reads ----------

#[test]
fn branch_reads_cond() {
    let (errs, _) = run("
        fn f() {
          b: boolean;
          entry:
            branch(copy b) [true: t, false: fbr]
          t: return
          fbr: return
        }
        ");
    assert_errors_contain(&errs, &["variable 'b' is used before initialization"]);
}

#[test]
fn switch_enum_reads_place() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: number }
        fn f() {
          o: Option;
          entry:
            switchEnum(o) [None: end, Some: end]
          end:
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

// ---------- Projections ----------

#[test]
fn downcast_read_checks_root_var() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: number }
        fn f() {
          o: Option;
          a: number;
          entry:
            a = copy o as Some;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

#[test]
fn deref_read_is_not_checked() {
    assert_no_diagnostics(
        "
        fn f(r: &number) {
          a: number;
          entry:
            a = copy *r;
            return
        }
        ",
    );
}

// ---------- Downcast writes ----------

#[test]
fn downcast_write_on_init_enum_ok() {
    // Writing through a variant projection is fine when the enum is
    // Init AND refined to the correct variant.
    assert_no_diagnostics(
        "
        enum Copy Drop Option { None: unit Some: number }
        fn f(o: Option) {
          entry:
            switchEnum(o) [None: n, Some: s]
          s:
            o as Some = 7;
            return
          n: return
        }
        ",
    );
}

#[test]
fn downcast_write_on_uninit_enum_error() {
    // Enum construction goes via `Name::V(...)`; refining an uninit
    // enum by writing a variant payload is not allowed.
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: number }
        fn f() {
          o: Option;
          entry:
            o as Some = 7;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot write through variant projection: 'o' is not initialized here"],
    );
}

#[test]
fn downcast_write_on_moved_enum_error() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: number }
        fn f(o: Option) {
          sink: Option;
          entry:
            sink = move o;
            o as Some = 7;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot write through variant projection: 'o' is not initialized here"],
    );
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

// ---------- Calls ----------

#[test]
fn call_target_of_uninit_error() {
    let (errs, _) = run("
        fn f() {
          g: fn(number);
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
        extern fn takes_num(a: number);
        fn f() {
          x: number;
          entry:
            call takes_num(copy x);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
}

// ---------- Loops ----------

#[test]
fn loop_backedge_agrees_ok() {
    assert_no_diagnostics(
        "
        fn f(b: boolean) {
          x: number;
          entry:
            x = 0;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            x = 1;
            goto head
          done:
            return
        }
        ",
    );
}

// ---------- Drop statement ----------

#[test]
fn drop_consumes_like_move() {
    // `drop x` behaves like a move for init tracking: subsequent read errors.
    let (errs, _) = run("
        fn f(x: number) {
          y: number;
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
          x: number;
          entry:
            drop x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
}

// ---------- Reassignment / move ordering ----------

#[test]
fn reassign_after_move_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          y: number;
          z: number;
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
        fn f(x: number) {
          y: number;
          z: number;
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
        extern fn take_two(a: number, b: number);
        fn f(x: number) {
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
        extern fn take_two(a: number, b: number);
        fn f(x: number) {
          entry:
            call take_two(move x, copy x);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

// ---------- Loops ----------

#[test]
fn loop_may_reach_uninit_error() {
    let (errs, _) = run("
        fn f(b: boolean) {
          x: number;
          y: number;
          entry:
            branch(copy b) [true: body, false: done]
          body:
            y = copy x;
            x = 1;
            branch(copy b) [true: body, false: done]
          done:
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
}
