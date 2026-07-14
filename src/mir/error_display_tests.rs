use crate::mir::test_util::run;

#[test]
fn test_type_mismatch_display() {
    let src = "
        fn main(exit: &out i32) {
            x: bool;
            entry:
            exit.* = copy x;
            return
        }
    ";
    let (errs, _) = run(src);
    assert!(!errs.is_empty(), "expected error");
    let err = &errs[0];
    assert!(
        err.contains("[TC-AssignmentTypeMismatch]"),
        "missing code tag, got: {}",
        err
    );
    assert!(
        err.contains("LHS is i32, RHS is bool"),
        "missing clean types, got: {}",
        err
    );
}

#[test]
fn test_drop_non_drop_display() {
    let src = "
        fn f(r: &out i64) {
            entry:
            drop r;
            return
        }
    ";
    let (errs, _) = run(src);
    assert!(!errs.is_empty(), "expected error");
    let err = &errs[0];
    assert!(
        err.contains("[SUB-DropOfNonDrop]"),
        "missing code tag, got: {}",
        err
    );
    assert!(
        err.contains("cannot drop non-Drop type &out i64"),
        "missing message details, got: {}",
        err
    );
    assert!(
        err.contains("hint: only types implementing the Drop class can be explicitly dropped"),
        "missing hint, got: {}",
        err
    );
}

#[test]
fn test_copy_non_copy_display() {
    let src = "
        extern fn take(r: &out i64);
        fn f(r: &out i64) {
            entry:
            call take(copy r);
            return
        }
    ";
    let (errs, _) = run(src);
    assert!(!errs.is_empty(), "expected error");
    let err = &errs[0];
    assert!(
        err.contains("[SUB-CopyOfNonCopy]"),
        "missing code tag, got: {}",
        err
    );
    assert!(
        err.contains("cannot copy non-Copy type &out i64"),
        "missing message details, got: {}",
        err
    );
    assert!(
        err.contains("hint: since the type is not Copy, try moving it instead using 'move'"),
        "missing hint, got: {}",
        err
    );
}

#[test]
fn test_leak_display() {
    let src = "
        struct L { r: &out i64 }
        fn f(x: L) {
            entry:
            return
        }
    ";
    let (errs, _) = run(src);
    assert!(!errs.is_empty(), "expected error");
    let err = &errs[0];
    assert!(
        err.contains("[SUB-ReturnValueLeak]"),
        "missing code tag, got: {}",
        err
    );
    assert!(
        err.contains("value 'x' of type L is not consumed at return"),
        "missing message details, got: {}",
        err
    );
    assert!(
        err.contains("hint: linear values must be consumed or returned before function exit. Try moving or dropping it."),
        "missing hint, got: {}",
        err
    );
}

#[test]
fn test_loan_conflict_display() {
    let src = "
        fn f() {
            x: i64;
            r: &mut i64;
            entry:
            x = 10;
            r = &mut x;
            x = 20;
            drop r;
            return
        }
    ";
    let (errs, _) = run(src);
    assert!(!errs.is_empty(), "expected error");
    let err = &errs[0];
    assert!(
        err.contains("[LT-LoanConflict]"),
        "missing code tag, got: {}",
        err
    );
    assert!(
        err.contains("cannot move from 'x': already borrowed by 'r'"),
        "missing message details, got: {}",
        err
    );
    assert!(
        err.contains("hint: the borrow of 'r' is active until its last use or explicit unborrow."),
        "missing hint, got: {}",
        err
    );
}
