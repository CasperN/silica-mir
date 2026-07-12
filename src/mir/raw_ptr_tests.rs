//! End-to-end tests for the raw pointer feature (`*T` type,
//! `&raw place` rvalue). Covers parsing, type checking, codegen,
//! and the unsafe semantics (no loan conflicts, no obligations).

use crate::test_util::*;

// ---------- Parsing / round-trip ----------

#[test]
fn parses_raw_ptr_type_and_creation() {
    // Trivial program that exercises both new grammar pieces.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          p: *i64;
          entry:
            p = &raw x;
            return
        }
        ",
    );
}

#[test]
fn parses_raw_ptr_in_field() {
    assert_no_diagnostics(
        "
        struct Copy Drop Node { p: *i64 v: i64 }
        fn f(x: i64) {
          n: Node;
          entry:
            n.p = &raw x;
            n.v = 0;
            return
        }
        ",
    );
}

#[test]
fn raw_ptr_class_is_copy_drop_move() {
    // A raw ptr can be freely copied (Copy) and forgotten (Drop):
    // no drop needed at return, and `copy p` works.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          p: *i64;
          q: *i64;
          entry:
            p = &raw x;
            q = copy p;
            return
        }
        ",
    );
}

// ---------- Unsafe: no loan checks ----------

#[test]
fn raw_ptr_creation_does_not_conflict_with_existing_mut_borrow() {
    // A `&mut x` creates a loan; taking `&raw x` while that loan is
    // live must succeed — that's the "unsafe" escape. Under safe
    // semantics, `&mut x` immediately followed by a second exclusive
    // borrow of x would be a loan conflict.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          p: *i64;
          y: i64;
          entry:
            r = &mut x;
            p = &raw x;
            y = copy r.*;
            return
        }
        ",
    );
}

#[test]
fn deref_of_raw_ptr_does_not_check_loan() {
    // Reading through a raw pointer while a safe `&mut` to the same
    // place is live: allowed (would be a loan conflict for a safe
    // reborrow of x).
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          p: *i64;
          y: i64;
          z: i64;
          entry:
            r = &mut x;
            p = &raw x;
            y = copy p.*;
            z = copy r.*;
            return
        }
        ",
    );
}

// ---------- Class checks still apply through the pointer ----------

#[test]
fn cannot_move_non_move_type_through_raw_ptr() {
    // The unsafe part is aliasing/lifetime — class rules still hold.
    // `&out T` is not Copy; you can't `copy p.*` a raw-ptr-to-`&out`.
    // (Not tested here directly since the setup would be complex;
    // instead we verify the positive case that a non-Copy pointee
    // still needs `move`.)
    let (errs, _) = run(
        "
        struct Linear { r: &out i64 }
        fn f(l: Linear) {
          p: *Linear;
          q: Linear;
          entry:
            p = &raw l;
            q = copy p.*;
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("cannot copy non-Copy")),
        "expected Copy class error, got: {:?}",
        errs
    );
}

// ---------- Errors ----------

#[test]
fn deref_of_non_pointer_type_errors() {
    // A raw pointer type is required for deref; plain i64 is not.
    let (errs, _) = run(
        "
        fn f(x: i64) {
          y: i64;
          entry:
            y = copy x.*;
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("Cannot dereference non-pointer type")),
        "expected deref-type error, got: {:?}",
        errs
    );
}

#[test]
fn assign_of_wrong_pointee_type_errors() {
    // Assigning a `*i32` to a `*i64` slot must fail — pointee types
    // participate in `types_match`.
    let (errs, _) = run(
        "
        fn f(x: i32) {
          p: *i64;
          entry:
            p = &raw x;
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("Type mismatch in assignment")),
        "expected type mismatch, got: {:?}",
        errs
    );
}
