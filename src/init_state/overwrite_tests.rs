//! Overwrite check tests.
//!
//! When `p = ...` fires and `p` is currently `Init` (or `Partial` with
//! Init leaves), the old value would be silently forgotten. Each Init
//! leaf's type must be `Drop`, or the caller must have consumed it first.

use crate::test_util::*;

// ---------- Allowed: scalars and Copy Drop types ----------

#[test]
fn overwrite_scalar_ok() {
    // `number` is Copy Drop — bit-copies are cheap to forget.
    assert_no_diagnostics(
        "
        fn f() {
          x: number;
          entry:
            x = 1;
            x = 2;
            return
        }
        ",
    );
}

#[test]
fn overwrite_copy_drop_struct_ok() {
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: number b: number }
        extern fn use_p(p: P);
        fn f(p1: P, p2: P) {
          x: P;
          entry:
            x = move p1;
            x = move p2;
            call use_p(move x);
            return
        }
        ",
    );
}

#[test]
fn overwrite_after_explicit_drop_ok() {
    // Manual `drop x` before overwrite makes it uncontroversial.
    assert_no_diagnostics(
        "
        struct Move Drop D { a: number }
        extern fn use_d(d: D);
        fn f(d1: D, d2: D) {
          x: D;
          entry:
            x = move d1;
            drop x;
            x = move d2;
            call use_d(move x);
            return
        }
        ",
    );
}

#[test]
fn overwrite_never_init_ok() {
    // First assignment isn't an overwrite.
    assert_no_diagnostics(
        "
        struct Move Linear { r: &out number }
        extern fn take(l: Linear);
        fn f(x: Linear) {
          y: Linear;
          entry:
            y = move x;
            call take(move y);
            return
        }
        ",
    );
}

// ---------- Rejected: overwrite of live non-Drop value ----------

#[test]
fn overwrite_non_drop_linear_errors() {
    let (errs, _) = run("
        struct Move Linear { r: &out number }
        extern fn take(l: Linear);
        fn f(x1: Linear, x2: Linear) {
          y: Linear;
          entry:
            y = move x1;
            y = move x2;
            call take(move y);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot overwrite 'y': type Custom(\"Linear\") is not Drop"],
    );
}

#[test]
fn overwrite_non_drop_move_only_errors() {
    // `struct Move A` is not Drop (Move alone doesn't imply Drop).
    let (errs, _) = run("
        struct Move A { r: &out number }
        extern fn take(a: A);
        fn f(a1: A, a2: A) {
          y: A;
          entry:
            y = move a1;
            y = move a2;
            call take(move y);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot overwrite 'y'"]);
}

// ---------- Partial state ----------

#[test]
fn overwrite_field_of_scalar_struct_ok() {
    // p.a: number is Copy Drop; overwriting p.a is fine.
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: number b: number }
        fn f() {
          p: P;
          entry:
            p.a = 1;
            p.b = 2;
            p.a = 3;
            return
        }
        ",
    );
}

#[test]
fn overwrite_non_drop_field_errors() {
    // Overwriting a live non-Drop field.
    let (errs, _) = run("
        struct Move Wrap { r: &out number }
        struct Move Container { w1: Wrap w2: Wrap }
        extern fn take_wrap(w: Wrap);
        extern fn take(c: Container);
        fn f(w0: Wrap, w1: Wrap) {
          c: Container;
          entry:
            c.w1 = move w0;
            c.w1 = move w1;
            return
        }
        ");
    assert!(
        errs.iter().any(|e| e.contains("cannot overwrite 'c.w1'")),
        "expected overwrite error on c.w1, got: {:?}",
        errs
    );
}

// ---------- Path-granular obligation cross-check ----------

#[test]
fn overwrite_ref_typed_field_with_unfulfilled_obligation_errors() {
    // b.p is a &mut number bound to x. After `y = move *b.p`, b.p is
    // (Uninit, Init) — obligation unfulfilled. Overwriting b.p would
    // silently forget the pending re-init. Overwrite check catches it
    // (via close_ref_if_present, which cascades to ref-typed fields).
    let (errs, _) = run("
        struct Move RefBox { p: &mut number }
        fn f(x: number, x2: number) {
          b: RefBox;
          y: number;
          entry:
            b.p = &mut x;
            y = move *b.p;
            b.p = &mut x2;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'b.p' has unfulfilled obligation"],
    );
}

// ---------- Move source & target the same shape ----------

#[test]
fn overwrite_after_move_out_ok() {
    // After `y = move x`, y is Init but x is Moved. Now `x = ...`
    // isn't an overwrite (x is Moved), so no error.
    assert_no_diagnostics(
        "
        struct Move Linear { r: &out number }
        extern fn take(l: Linear);
        fn f(x1: Linear, x2: Linear) {
          y: Linear;
          entry:
            y = move x1;
            call take(move y);
            y = move x2;
            call take(move y);
            return
        }
        ",
    );
}
