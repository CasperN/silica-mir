//! Lifetime pass — `unborrow` statement tests.
//!
//! Covers the explicit end-of-loan primitive: obligation check on the
//! borrower, loan release, and interactions with multi-loan, joins,
//! reborrow, field granularity, and loops.

use crate::test_util::*;

// ---------- unborrow statement ----------

#[test]
fn unborrow_of_mut_ref_ok() {
    // &mut is (Init, Init) — obligation trivially fulfilled at any
    // point where cur=Init. Unborrow closes the loan.
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &mut number;
          y: number;
          entry:
            r = &mut x;
            y = copy *r;
            unborrow r;
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn unborrow_releases_loan() {
    // After `unborrow r`, direct access to the previously-borrowed
    // place is legal.
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &mut number;
          y: number;
          entry:
            r = &mut x;
            unborrow r;
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn unborrow_with_unfulfilled_obligation_error() {
    // &mut is (Init, Init) but we moved *r out (cur=Uninit).
    // Unborrow requires cur == post; this errors.
    let (errs, _) = run("
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            unborrow r;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

#[test]
fn unborrow_of_uninit_error() {
    // Can't unborrow a never-initialized ref var.
    let (errs, _) = run("
        fn f() {
          r: &mut number;
          entry:
            unborrow r;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'r' is used before initialization"]);
}

#[test]
fn unborrow_after_move_error() {
    // r was moved to a call — can't unborrow a Moved ref.
    let (errs, _) = run("
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            call sink(move r);
            unborrow r;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'r' is used after move"]);
}

#[test]
fn unborrow_of_shared_ref_ok() {
    // Shared refs have no obligation; unborrow just consumes them.
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &number;
          entry:
            r = &x;
            unborrow r;
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn unborrow_of_non_ref_type_error() {
    // Unborrow only makes sense on reference-typed places.
    let (errs, _) = run("
        fn f(x: number) {
          entry:
            unborrow x;
            return
        }
        ");
    assert_errors_contain(&errs, &["unborrow requires a reference-typed place"]);
}

#[test]
fn unborrow_out_ref_after_write_ok() {
    // &out with cur=Init after `*r = v` reaches post; unborrow OK.
    assert_no_diagnostics(
        "
        fn f(r: &out number) {
          entry:
            *r = 42;
            unborrow r;
            return
        }
        ",
    );
}

#[test]
fn unborrow_of_multi_loan_releases_all_places_ok() {
    // Branch-of-borrows unified into r loaning {a, b}. `unborrow r`
    // must release both places at the merge point, so direct writes
    // to a and b downstream succeed.
    assert_no_diagnostics(
        "
        fn f(a: number, b: number, c: boolean) {
          r: &mut number;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            unborrow r;
            a = 1;
            b = 2;
            return
        }
        ",
    );
}

#[test]
fn unborrow_in_both_arms_merges_clean_ok() {
    // Symmetric unborrow in both branches: at the merge, r is Moved
    // on both sides (no divergence), and x is unloaned on both sides
    // — direct access to x is legal downstream.
    assert_no_diagnostics(
        "
        fn f(x: number, b: boolean) {
          r: &mut number;
          y: number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            r = &mut x;
            unborrow r;
            goto merge
          fbr:
            r = &mut x;
            unborrow r;
            goto merge
          merge:
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn unborrow_then_reborrow_same_place_ok() {
    // After `unborrow r`, x is unfrozen; taking a fresh &mut of x is
    // legal. Second unborrow closes the new loan.
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          y: number;
          entry:
            r = &mut x;
            unborrow r;
            s = &mut x;
            y = copy *s;
            unborrow s;
            return
        }
        ",
    );
}

#[test]
fn unborrow_of_field_borrower_thaws_field_ok() {
    // &mut p.a freezes p.a; `unborrow r` thaws it, so writing to
    // p.a directly afterward succeeds.
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: number b: number }
        fn f(p: P) {
          r: &mut number;
          entry:
            r = &mut p.a;
            unborrow r;
            p.a = 42;
            return
        }
        ",
    );
}

#[test]
fn unborrow_across_loop_ok() {
    // Borrow taken before the loop, used through the loop, unborrowed
    // after. Verifies the loan persists across back-edges and is
    // cleanly closable at loop exit.
    assert_no_diagnostics(
        "
        extern fn use_num(n: number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            r = &mut x;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            call use_num(copy *r);
            goto head
          done:
            unborrow r;
            x = 42;
            return
        }
        ",
    );
}
