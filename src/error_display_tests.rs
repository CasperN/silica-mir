//! End-to-end HLL diagnostic rendering tests.
//!
//! These pin the exact rendered output — code tag, position, function/
//! block context, source snippet with caret, and hint — for a handful
//! of common errors reached via the HLL pipeline. If an assertion
//! fails, first check whether the *observed* output is a legitimate
//! improvement (span shift, better message, added hint) before adjusting
//! either the compiler or the expected string.

use crate::diagnostics::Diagnostics;

fn run_hll_pipeline(source: &str) -> Diagnostics {
    let source_arc = std::sync::Arc::new(source.to_string());
    let mut d = Diagnostics::default()
        .with_source(source_arc)
        .with_source_kind(crate::diagnostics::SourceKind::Hll);
    if let Some(program) = crate::lower_hll_to_mir(source, &mut d) {
        crate::elaborate_and_check_mir(&program, &mut d);
    }
    d
}

#[track_caller]
fn assert_first_error(src: &str, expected: &str) {
    let d = run_hll_pipeline(src);
    assert!(!d.is_clean(), "expected an error, got clean run");
    let errs = d.errors_str();
    assert_eq!(errs[0], expected);
}

#[test]
fn test_hll_use_after_move_display() {
    // Every HLL `let y = x` lowers to a move, so re-reading `x` on the
    // next line is a use-after-move regardless of whether the type is
    // Copy at the surface level.
    let src = "
        struct Box { val: i64 }
        fn f() {
            let x = Box { val: 1 };
            let y = x;
            let z = x;
        }
    ";
    let expected = "\
at 6:21: [INIT-UseAfterMove] In function 'f': variable 'x' is used after move
   |
 6 |             let z = x;
   |                     ^";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_loan_conflict_display() {
    // `r` is kept live past the conflicting write to `x` by reading
    // through it on the next line, so the loan check reaches `x = 20;`.
    let src = "
        fn f() {
            let mut x: i64 = 10;
            let r = &mut x;
            x = 20;
            let y = r.*;
        }
    ";
    let expected = "\
at 5:13: [LT-LoanConflict] In function 'f': cannot move from 'x': already borrowed by 'r'
   |
 5 |             x = 20;
   |             ^^^^^^
  = note: borrow of 'x' occurs here
   |
 4 |             let r = &mut x;
   |                     ^^^^^^
  hint: the borrow of 'r' is active until its last use or explicit unborrow.";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_out_obligation_unfulfilled_display() {
    // `&out i64` obliges the callee to initialize the pointee before
    // return. Doing nothing with `r` leaves the obligation live.
    let src = "
        fn f(r: &out i64) {
        }
    ";
    let expected = "\
at 2:27: [INIT-RefObligationUnfulfilled] In function 'f': reference 'r' has unfulfilled obligation here (is_init=false, ends_init=true)
   |
 2 |         fn f(r: &out i64) {
   |                           ^";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_undeclared_variable_display() {
    // Reference to a name not in scope — caught in `hll::type_check`,
    // renders with the HTC-UndeclaredVariable code tag.
    let src = "
        fn f() -> i64 {
            let x = y;
            x
        }
    ";
    let expected = "\
at 3:21: [HTC-UndeclaredVariable] In function 'f': undeclared variable 'y'
   |
 3 |             let x = y;
   |                     ^";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_type_mismatch_display() {
    // Return-type unification failure — HTC-TypeMismatch. The block's
    // trailing expression is a `bool`; the declared return type is `i64`.
    let src = "
        fn f() -> i64 {
            true
        }
    ";
    let d = run_hll_pipeline(src);
    assert!(!d.is_clean());
    let errs = d.errors_str();
    assert!(
        errs[0].contains("[HTC-TypeMismatch]"),
        "expected TypeMismatch tag, got: {}",
        errs[0]
    );
    assert!(
        errs[0].contains("type mismatch"),
        "expected substring, got: {}",
        errs[0]
    );
}

#[test]
fn test_hll_immutable_assign_display() {
    // Reassigning a non-mut binding — HMC-AssignToImmutable.
    let src = "
        fn f() -> i64 {
            let x: i64 = 1;
            x = 2;
            x
        }
    ";
    let expected = "\
at 4:13: [HMC-AssignToImmutable] In function 'f': cannot assign to immutable binding 'x'
   |
 4 |             x = 2;
   |             ^";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_immutable_borrow_display() {
    // Taking `&mut` of a non-mut binding — HMC-BorrowImmutableAsMut.
    let src = "
        fn f() {
            let x: i64 = 1;
            let r = &mut x;
        }
    ";
    let expected = "\
at 4:26: [HMC-BorrowImmutableAsMut] In function 'f': cannot borrow immutable binding 'x' as mutable
   |
 4 |             let r = &mut x;
   |                          ^";
    assert_first_error(src, expected);
}

#[test]
fn test_hll_copy_of_non_copy_display() {
    // `&mut i64` isn't Copy — assigning it into a fresh binding tries
    // to copy the reference and fails.
    let src = "
        fn f(r: &mut i64) {
            let y = r;
            let z = r;
        }
    ";
    let expected = "\
at 3:21: [SUB-CopyOfNonCopy] In function 'f': cannot copy non-Copy type &mut i64
   |
 3 |             let y = r;
   |                     ^
  hint: since the type is not Copy, try moving it instead using 'move'";
    assert_first_error(src, expected);
}
