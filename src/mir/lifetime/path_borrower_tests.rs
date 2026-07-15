//! Path-granular borrower tests: ref-typed struct fields, reborrow
//! through fields, boundary invariant.
//!
//! These programs would silently pass (unsound) under the older
//! Var-only borrower tracking. They now behave correctly because
//! RefState/LoanMap are keyed by owned path.

use crate::mir::test_util::*;

// ---------- Ref-typed struct field as borrower ----------

#[test]
fn field_borrower_blocks_direct_access_to_loaned_place() {
    let (errs, _) = run("
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          entry:
            b.p = &mut x;
            x = 42;
            call take_box(move b);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'b.p'"]);
}

#[test]
fn field_borrower_survives_call_taking_whole_struct() {
    // The whole b is consumed by take_box; b.p's loan on x closes
    // naturally via the ancestor consume. After that, x is writable
    // (but drop-elab will handle the cleanup).
    assert_no_diagnostics(
        "
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          entry:
            b.p = &mut x;
            call take_box(move b);
            return
        }
        ",
    );
}

// ---------- Reborrow through a field ----------

#[test]
fn reborrow_through_field_ok() {
    assert_no_diagnostics(
        "
        struct Move RefBox { p: &mut i64 }
        extern fn sink(r: &mut i64);
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          s: &mut i64;
          entry:
            b.p = &mut x;
            s = &mut b.p.*;
            call sink(move s);
            call take_box(move b);
            return
        }
        ",
    );
}

#[test]
fn access_through_field_ref_while_reborrow_live_conflicts() {
    let (errs, _) = run("
        struct Move RefBox { p: &mut i64 }
        extern fn sink(r: &mut i64);
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          s: &mut i64;
          y: i64;
          entry:
            b.p = &mut x;
            s = &mut b.p.*;
            y = copy b.p.*;
            call sink(move s);
            call take_box(move b);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'b.p.*': already borrowed by 's'"]);
}

// ---------- Split borrows across disjoint fields ----------

#[test]
fn split_field_borrows_coexist() {
    // b.q and b.r are disjoint. Moving both refs out independently is
    // fine; b is Moved (Partial) after both moves.
    assert_no_diagnostics(
        "
        struct Move RefBox2 { q: &mut i64 r: &mut i64 }
        extern fn use_mut(r: &mut i64);
        fn f(x: i64, y: i64) {
          b: RefBox2;
          entry:
            b.q = &mut x;
            b.r = &mut y;
            call use_mut(move b.q);
            call use_mut(move b.r);
            return
        }
        ",
    );
}

// ---------- Ancestor consume closes descendants ----------

#[test]
fn move_ancestor_closes_field_loans() {
    // Moving b to a callee closes b.p's loan on x — direct access to
    // x afterward is OK.
    assert_no_diagnostics(
        "
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          entry:
            b.p = &mut x;
            call take_box(move b);
            x = 1;
            return
        }
        ",
    );
}

// ---------- Boundary invariant ----------

#[test]
fn move_struct_with_unfulfilled_field_ref_obligation_errors() {
    // b.p's ref was moved out via b.p.*, leaving b.p (is_init=false,
    // ends_init=true). Moving b to a callee would silently violate
    // the obligation. Boundary check catches it.
    let (errs, _) = run("
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64) {
          b: RefBox;
          y: i64;
          entry:
            b.p = &mut x;
            y = move b.p.*;
            call take_box(move b);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot move 'b': contained reference 'b.p' has unfulfilled obligation"],
    );
}

#[test]
fn move_struct_with_fulfilled_field_ref_ok() {
    // Same shape but the ref is properly re-initialized before the
    // outer move — obligation fulfilled.
    assert_no_diagnostics(
        "
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64, z: i64) {
          b: RefBox;
          y: i64;
          entry:
            b.p = &mut x;
            y = move b.p.*;
            b.p.* = 7;
            call take_box(move b);
            return
        }
        ",
    );
}

// ---------- Ref-typed parameter passing ----------

#[test]
fn move_of_struct_with_ref_typed_field_ok() {
    // Baseline: moving a Linear (with &out field) directly through
    // to a callee — the callee's signature accepts the same type.
    assert_no_diagnostics(
        "
        struct Move Linear { r: &out i64 }
        extern fn sink(y: Linear);
        fn f(x: Linear) {
          y: Linear;
          entry:
            y = move x;
            call sink(move y);
            return
        }
        ",
    );
}

// ---------- Dynamic borrow into a field ----------

#[test]
fn dynamic_field_borrow_multi_loan() {
    // Both branches bind the same field b.p; merge unions the loan
    // targets. Writing to y at merge conflicts.
    let (errs, _) = run("
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(y: i64, z: i64, cond: bool) {
          b: RefBox;
          entry:
            branch(copy cond) [true: t, false: fbr]
          t:
            b.p = &mut y;
            goto merge
          fbr:
            b.p = &mut z;
            goto merge
          merge:
            y = 1;
            call take_box(move b);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'y': already borrowed by 'b.p'"]);
}
