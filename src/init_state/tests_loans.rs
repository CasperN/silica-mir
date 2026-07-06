//! Init state dataflow — loan conflict tests.
//!
//! Covers single-loan conflicts (exclusive vs shared vs mutable-reborrow),
//! field-level precision, ref transfer through moves, and multi-loan
//! (branch-of-borrows) conflicts.

use crate::test_util::*;

// ---------- Loan conflicts ----------
//
// Slice 1: a borrow of a place freezes it (whole-function
// conservative lifetime — the loan lasts until the borrower is
// consumed). Any direct access to the loaned place is a conflict,
// with the shared/shared exception for reads and shared reborrows.

// === Exclusive loan blocks direct access ===

#[test]
fn mut_loan_blocks_direct_write() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            x = 1;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write to 'x': already borrowed by 'r'"],
    );
}

#[test]
fn mut_loan_blocks_direct_read() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          y: number;
          entry:
            r = &mut x;
            y = copy x;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot read 'x': already borrowed by 'r'"],
    );
}

#[test]
fn mut_loan_blocks_direct_move() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        extern fn use_num(y: number);
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            call use_num(move x);
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot move from 'x': already borrowed by 'r'"],
    );
}

// === Shared loans permit reads and shared reborrows ===

#[test]
fn shared_loan_permits_read_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &number;
          y: number;
          entry:
            r = &x;
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn shared_loan_permits_shared_reborrow_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &number;
          s: &number;
          entry:
            r = &x;
            s = &x;
            return
        }
        ",
    );
}

#[test]
fn shared_loan_blocks_write() {
    let (errs, _) = run(
        "
        fn f(x: number) {
          r: &number;
          entry:
            r = &x;
            x = 1;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write to 'x': already borrowed by 'r'"],
    );
}

#[test]
fn shared_loan_blocks_move() {
    let (errs, _) = run(
        "
        extern fn take(y: number);
        fn f(x: number) {
          r: &number;
          entry:
            r = &x;
            call take(move x);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot move from 'x': already borrowed by 'r'"],
    );
}

#[test]
fn shared_loan_blocks_mut_reborrow() {
    let (errs, _) = run(
        "
        fn f(x: number) {
          r: &number;
          s: &mut number;
          entry:
            r = &x;
            s = &mut x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot borrow as &mut 'x': already borrowed by 'r'"],
    );
}

#[test]
fn mut_loan_blocks_shared_reborrow() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &number;
          entry:
            r = &mut x;
            s = &x;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot borrow as & 'x': already borrowed by 'r'"],
    );
}

#[test]
fn mut_loan_blocks_mut_reborrow() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          s: &mut number;
          entry:
            r = &mut x;
            s = &mut x;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot borrow as &mut 'x': already borrowed by 'r'"],
    );
}

// === Loan ends when borrower is consumed ===

#[test]
fn access_ok_after_borrower_moved_to_call() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            call sink(move r);
            x = 1;
            return
        }
        ",
    );
}

// === Field-level precision ===

#[test]
fn disjoint_field_borrows_ok() {
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: number b: number }
        extern fn sink(r: &mut number);
        fn f(p: P) {
          r: &mut number;
          y: number;
          entry:
            r = &mut p.a;
            y = copy p.b;
            call sink(move r);
            return
        }
        ",
    );
}

#[test]
fn same_field_borrow_conflicts() {
    let (errs, _) = run(
        "
        struct Copy Drop P { a: number b: number }
        extern fn sink(r: &mut number);
        fn f(p: P) {
          r: &mut number;
          y: number;
          entry:
            r = &mut p.a;
            y = copy p.a;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot read 'p.a': already borrowed by 'r'"],
    );
}

#[test]
fn access_to_parent_of_borrowed_field_conflicts() {
    // Borrowing a field freezes the whole path from that field
    // upward — moving the parent p would move the borrowed field.
    let (errs, _) = run(
        "
        struct Copy Drop P { a: number b: number }
        extern fn sink(r: &mut number);
        extern fn takep(p: P);
        fn f(p: P) {
          r: &mut number;
          entry:
            r = &mut p.a;
            call takep(move p);
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot move from 'p': already borrowed by 'r'"],
    );
}

// === Access through borrower still allowed ===

#[test]
fn read_through_borrower_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &mut number;
          y: number;
          entry:
            r = &mut x;
            y = copy *r;
            return
        }
        ",
    );
}

// === Ref transfer via `dst = move src` ===

#[test]
fn ref_transfer_carries_obligation_ok() {
    // Moving an &out param to a local: the local inherits the
    // pointee obligation, satisfies it via *z = 42.
    assert_no_diagnostics(
        "
        fn f(x: &out number) {
          z: &out number;
          entry:
            z = move x;
            *z = 42;
            return
        }
        ",
    );
}

#[test]
fn ref_transfer_leaves_source_moved_error_on_reuse() {
    // After transfer, x is Moved — can't use it again.
    let (errs, _) = run(
        "
        extern fn sink(r: &out number);
        fn f(x: &out number) {
          z: &out number;
          entry:
            z = move x;
            *z = 1;
            call sink(move x);
            return
        }
        ",
    );
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

#[test]
fn ref_transfer_preserves_loan_conflict() {
    // Local borrower r loans a. Transfer r to s. s still loans a;
    // direct access to a should still conflict.
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
        fn f(a: number) {
          r: &mut number;
          s: &mut number;
          entry:
            r = &mut a;
            s = move r;
            a = 1;
            call sink(move s);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write to 'a': already borrowed by 's'"],
    );
}

#[test]
fn branch_of_ref_moves_both_params_leak() {
    // Program from a design discussion: which of x/y is initialized
    // depends on b. In each branch we init only one of them via z,
    // so the OTHER is a leak (its &out obligation is unmet on that
    // path). This program should be rejected.
    let (errs, _) = run(
        "
        fn f(x: &out number, y: &out number, b: boolean) {
          z: &out number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            z = move x;
            *z = 1;
            goto end
          fbr:
            z = move y;
            *z = 2;
            goto end
          end:
            return
        }
        ",
    );
    // In `t`, y is untouched — unfulfilled obligation.
    // In `fbr`, x is untouched — unfulfilled obligation.
    // Both branches merge into `end` where refs are dropped from
    // the join (each side has different entries) but the linear-
    // leak scan catches Diverged params.
    let has_leak = errs.iter().any(|e| e.contains("not consumed at return")
        || e.contains("has unfulfilled obligation at return"));
    assert!(
        has_leak,
        "expected some kind of leak/obligation error, got: {:?}",
        errs
    );
}


// ---------- Multi-loan (branch of borrows) ----------

#[test]
fn multi_loan_branch_of_borrows_a_or_b_ok() {
    // A branch-of-borrows: after the merge, r loans {a, b}. Both
    // are frozen. Consuming r via a call releases both. Direct
    // access to a or b after that is fine.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
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
            call sink(move r);
            a = 1;
            b = 2;
            return
        }
        ",
    );
}

#[test]
fn multi_loan_conflict_on_a_after_join() {
    // After the merge, r loans {a, b}. Writing directly to `a` is
    // a conflict — r may loan a.
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
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
            a = 1;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write to 'a': already borrowed by 'r'"],
    );
}

#[test]
fn multi_loan_conflict_on_b_after_join() {
    let (errs, _) = run(
        "
        extern fn sink(r: &mut number);
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
            b = 2;
            call sink(move r);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write to 'b': already borrowed by 'r'"],
    );
}

#[test]
fn multi_loan_disjoint_third_place_ok() {
    // r may loan {a, b}, but neither is c. Direct access to c is
    // fine.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(a: number, b: number, c: number, cond: boolean) {
          r: &mut number;
          entry:
            branch(copy cond) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            c = 3;
            call sink(move r);
            return
        }
        ",
    );
}

