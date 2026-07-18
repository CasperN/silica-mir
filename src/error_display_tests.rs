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
        crate::elaborate_and_check_mir(program, &mut d);
    }
    d
}

#[track_caller]
fn assert_first_error(src: &str, expected: &str) {
    let d = run_hll_pipeline(src);
    crate::mir::test_util::maybe_write_fixture_ext(src, d.has_errors(), "si");
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
        struct Box: Copy + Drop { val: i64 }
        fn f() {
            let x = Box { val: 1 };
            let y = x;
            let z = x;
        }
    ";
    let expected = r#"at 6:21: [INIT-UseAfterMove] In function 'f': variable 'x' is used after move
   |
 5 |             let y = x;
 6 |             let z = x;
   |                     ^
 7 |         }
   |"#;
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
    let expected = r#"at 5:13: [LT-LoanConflict] In function 'f': cannot write to 'x': already borrowed by 'r'
   |
 3 |             let mut x: i64 = 10;
 4 |             let r = &mut x;
   |                     ------ borrow of 'x' occurs here
 5 |             x = 20;
   |             ^^^^^^
 6 |             let y = r.*;
   |
  hint: the borrow of 'r' is active until its last use or explicit unborrow."#;
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
    let expected = r#"at 2:27: [INIT-RefObligationUnfulfilled] In function 'f': reference 'r' has unfulfilled obligation: pointee is uninitialized, but must be initialized before the reference expires
   |
 1 | 
 2 |         fn f(r: &out i64) {
   |              -----------  ^ reference declared here
 3 |         }
   |"#;
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
    let expected = r#"at 3:21: [HTC-UndeclaredVariable] In function 'f': undeclared variable 'y'
   |
 2 |         fn f() -> i64 {
 3 |             let x = y;
   |                     ^
 4 |             x
   |"#;
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
    let expected = r#"at 4:13: [HMC-AssignToImmutable] In function 'f': cannot assign to immutable binding 'x'
   |
 2 |         fn f() -> i64 {
 3 |             let x: i64 = 1;
   |             --------------- variable declared as immutable here
 4 |             x = 2;
   |             ^
 5 |             x
   |"#;
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
    let expected = r#"at 4:26: [HMC-BorrowImmutableAsMut] In function 'f': cannot borrow immutable binding 'x' as mutable
   |
 2 |         fn f() {
 3 |             let x: i64 = 1;
   |             --------------- variable declared as immutable here
 4 |             let r = &mut x;
   |                          ^
 5 |         }
   |"#;
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
    let expected = r#"at 3:21: [SUB-CopyOfNonCopy] In function 'f': cannot copy non-Copy type &mut i64
   |
 2 |         fn f(r: &mut i64) {
 3 |             let y = r;
   |                     ^
 4 |             let z = r;
   |
  hint: since the type is not Copy, try moving it instead using 'move'"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_mutability() {
    let src = "
        fn f() {
            let x = 1;
            defer x = 2;
        }
    ";
    let expected = r#"at 4:19: [HMC-AssignToImmutable] In function 'f': cannot assign to immutable binding 'x'
   |
 2 |         fn f() {
 3 |             let x = 1;
   |             ---------- variable declared as immutable here
 4 |             defer x = 2;
   |                   ^
 5 |         }
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_type_check() {
    let src = "
        fn f() {
            defer 42;
        }
    ";
    let expected = r#"at 3:19: [HTC-TypeMismatch] In function 'f': type mismatch: expected integer type, found unit
   |
 2 |         fn f() {
 3 |             defer 42;
   |                   ^^
 4 |         }
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_double_drop() {
    let src = "
        struct Box: Drop + Move { val: i64 }
        fn f(b: Box) {
            defer { let x = b; };
            let y = b;
        }
    ";
    let expected = r#"at 4:29: [INIT-UseAfterMove] In function 'f': variable 'b' is used after move
   |
 3 |         fn f(b: Box) {
 4 |             defer { let x = b; };
   |                             ^
 5 |             let y = b;
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_use_after_move() {
    let src = "
        struct Box: Copy + Drop { val: i64 }
        fn f(b: Box, out: &out Box) {
            defer out.* = b;
            let c = b;
        }
    ";
    let expected = r#"at 4:19: [INIT-UseAfterMove] In function 'f': variable 'b' is used after move
   |
 3 |         fn f(b: Box, out: &out Box) {
 4 |             defer out.* = b;
   |                   ^^^^^^^^^
 5 |             let c = b;
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_ref_obligation_unfulfilled() {
    let src = "
        struct Box: Drop + Move { val: i64 }
        fn f(r: &drop Box) {
            let x = r.*;
            defer r.* = Box { val: 5 };
        }
    ";
    let expected = r#"at 5:19: [INIT-RefObligationUnfulfilled] In function 'f': reference 'r' has unfulfilled obligation: pointee is initialized, but must be consumed before the reference expires
   |
 2 |         struct Box: Drop + Move { val: i64 }
 3 |         fn f(r: &drop Box) {
   |              ------------ reference declared here
 4 |             let x = r.*;
 5 |             defer r.* = Box { val: 5 };
   |                   ^^^^^^^^^^^^^^^^^^^^
 6 |         }
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_loan_conflict() {
    let src = "
        fn f() {
            let mut x = 1;
            let r = &x;
            defer { let y = r.*; };
            x = 2;
        }
    ";
    let expected = r#"at 6:13: [LT-LoanConflict] In function 'f': cannot write to 'x': already borrowed by 'r'
   |
 3 |             let mut x = 1;
 4 |             let r = &x;
   |                     -- borrow of 'x' occurs here
 5 |             defer { let y = r.*; };
 6 |             x = 2;
   |             ^^^^^
 7 |         }
   |
  hint: the borrow of 'r' is active until its last use or explicit unborrow."#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_reject_break() {
    let src = "
        fn f() {
            loop {
                defer { break; };
            };
        }
    ";
    let expected = r#"at 4:25: [HTC-ControlFlowInDefer] In function 'f': break is not allowed inside defer
   |
 3 |             loop {
 4 |                 defer { break; };
   |                         ^^^^^
 5 |             };
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_reject_continue() {
    let src = "
        fn f() {
            loop {
                defer { continue; };
            };
        }
    ";
    let expected = r#"at 4:25: [HTC-ControlFlowInDefer] In function 'f': continue is not allowed inside defer
   |
 3 |             loop {
 4 |                 defer { continue; };
   |                         ^^^^^^^^
 5 |             };
   |"#;
    assert_first_error(src, expected);
}

#[test]
fn test_hll_defer_reject_return() {
    let src = "
        fn f() {
            defer { return; };
        }
    ";
    let expected = r#"at 3:21: [HTC-ControlFlowInDefer] In function 'f': return is not allowed inside defer
   |
 2 |         fn f() {
 3 |             defer { return; };
   |                     ^^^^^^
 4 |         }
   |"#;
    assert_first_error(src, expected);
}

