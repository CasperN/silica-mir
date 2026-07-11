//! End-to-end tests for fixed-size arrays (`[T; N]` type,
//! `place[operand]` indexing, `[e0, e1, ...]` aggregate literals).
//! Covers parsing, type checking, per-slot init tracking, codegen.

use crate::test_util::*;

// ---------- Parsing / basic use ----------

#[test]
fn parses_array_type_and_lit() {
    assert_no_diagnostics(
        "
        fn f() {
          a: [i64; 3];
          entry:
            a = [1i64, 2i64, 3i64];
            return
        }
        ",
    );
}

#[test]
fn array_element_read_via_const_index() {
    assert_no_diagnostics(
        "
        fn f() {
          a: [i64; 3];
          x: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            x = copy a[1i64];
            return
        }
        ",
    );
}

#[test]
fn array_element_read_via_dynamic_index() {
    // Reading through a dynamic index requires the whole array to be
    // Init — which it is here.
    assert_no_diagnostics(
        "
        fn f(i: i64) {
          a: [i64; 3];
          x: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            x = copy a[copy i];
            return
        }
        ",
    );
}

// ---------- Per-slot init tracking ----------

#[test]
fn piecewise_init_via_out_refs_ok() {
    // Each slot gets init'd via its own &out. After the third
    // &out is fulfilled, the whole array is Init.
    assert_no_diagnostics(
        "
        extern fn set_i64(r: &out i64, v: i64);
        fn f() {
          a: [i64; 3];
          r0: &out i64;
          r1: &out i64;
          r2: &out i64;
          entry:
            r0 = &out a[0i64];
            call set_i64(move r0, 10i64);
            r1 = &out a[1i64];
            call set_i64(move r1, 20i64);
            r2 = &out a[2i64];
            call set_i64(move r2, 30i64);
            return
        }
        ",
    );
}

#[test]
fn reading_partially_init_array_errors() {
    // Only slot 0 is init; reading slot 1 must fail.
    let (errs, _) = run(
        "
        extern fn set_i64(r: &out i64, v: i64);
        fn f() {
          a: [i64; 3];
          r0: &out i64;
          x: i64;
          entry:
            r0 = &out a[0i64];
            call set_i64(move r0, 10i64);
            x = copy a[1i64];
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("used before initialization")
            || e.contains("not fully initialized")),
        "expected init-use error, got: {:?}",
        errs
    );
}

// ---------- Aggregate literals ----------

#[test]
fn array_lit_wrong_element_type_errors() {
    let (errs, _) = run(
        "
        fn f() {
          a: [i64; 2];
          entry:
            a = [1i64, 2i32];
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("has type") || e.contains("Type mismatch")),
        "expected type error, got: {:?}",
        errs
    );
}

#[test]
fn array_lit_wrong_length_errors() {
    let (errs, _) = run(
        "
        fn f() {
          a: [i64; 3];
          entry:
            a = [1i64, 2i64];
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("Type mismatch")),
        "expected type mismatch on length, got: {:?}",
        errs
    );
}

// ---------- Errors ----------

#[test]
fn index_into_non_array_errors() {
    let (errs, _) = run(
        "
        fn f(x: i64) {
          y: i64;
          entry:
            y = copy x[0i64];
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("Cannot index non-array")),
        "expected non-array error, got: {:?}",
        errs
    );
}

#[test]
fn non_int_index_errors() {
    let (errs, _) = run(
        "
        fn f() {
          a: [i64; 3];
          b: boolean;
          x: i64;
          entry:
            a = [1i64, 2i64, 3i64];
            b = true;
            x = copy a[copy b];
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("Array index must be an integer")),
        "expected index-type error, got: {:?}",
        errs
    );
}

// ---------- Array in struct field ----------

#[test]
fn array_in_struct_field_ok() {
    assert_no_diagnostics(
        "
        struct Copy Drop Buf { data: [u8; 4] }
        fn f() {
          b: Buf;
          entry:
            b.data = [65u8, 66u8, 67u8, 68u8];
            return
        }
        ",
    );
}

// ---------- Per-slot loan precision ----------

#[test]
fn loan_on_one_slot_does_not_block_another_slot() {
    // Const-index loans track per-slot: `&mut a[0]` doesn't conflict
    // with a read of `a[1]`. This is the ergonomic payoff of the
    // per-slot init tracking + is_ancestor_or_self index matching.
    assert_no_diagnostics(
        "
        fn f() {
          a: [i64; 3];
          r: &mut i64;
          x: i64;
          y: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            r = &mut a[0i64];
            x = copy a[1i64];
            y = copy *r;
            return
        }
        ",
    );
}

#[test]
fn dynamic_index_loan_conflicts_with_any_slot_access() {
    // A loan taken with a dynamic index widens to the whole array.
    // Reading any specific slot while that loan is live must conflict
    // (would be legal with a per-slot loan, but dynamic index means
    // we don't know which slot the loan covers).
    let (errs, _) = run(
        "
        fn f(i: i64) {
          a: [i64; 3];
          r: &mut i64;
          x: i64;
          y: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            r = &mut a[copy i];
            x = copy a[0i64];
            y = copy *r;
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("already borrowed")),
        "expected loan conflict, got: {:?}",
        errs
    );
}

#[test]
fn nested_array_element_read_ok() {
    // `[[T; M]; N]` — read an element of an inner array via two
    // successive index projections.
    assert_no_diagnostics(
        "
        fn f() {
          m: [[i32; 2]; 2];
          x: i32;
          entry:
            m[0i64] = [1i32, 2i32];
            m[1i64] = [3i32, 4i32];
            x = copy m[1i64][0i64];
            return
        }
        ",
    );
}
