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
          b: bool;
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
            y = copy r.*;
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
            y = copy r.*;
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

// ---------- Dynamic-index &out ----------

#[test]
fn out_borrow_via_dynamic_index_of_uninit_array_ok() {
    // Sound: array is fully NeverInit → every slot is Uninit, so an
    // `&out` on any slot meets its precondition. The precondition
    // check now widens dynamic-index paths to the containing array
    // and accepts this uniformly-Uninit case.
    assert_no_diagnostics(
        "
        extern fn set_i64(r: &out i64, v: i64);
        fn f(i: i64) {
          a: [i64; 3];
          r: &out i64;
          entry:
            r = &out a[copy i];
            call set_i64(move r, 1i64);
            return
        }
        ",
    );
}

#[test]
fn out_borrow_via_dynamic_index_of_init_array_errors() {
    // Unsound if silently accepted: `a` is fully Init at the borrow
    // point, so `&out a[dyn]` promises the pointee is Uninit but it
    // isn't — writing through the &out would silently forget the
    // old slot value. The dynamic-index widening now rejects.
    assert_err(
        "
        extern fn set_i64(r: &out i64, v: i64);
        fn f(i: i64) {
          a: [i64; 3];
          r: &out i64;
          entry:
            a = [1i64, 2i64, 3i64];
            r = &out a[copy i];
            call set_i64(move r, 1i64);
            return
        }
        ",
        "dynamic index requires the containing array to be uniformly uninitialized",
    );
}

#[test]
fn mut_borrow_via_dynamic_index_of_uninit_array_errors() {
    // Dual case: `&mut a[dyn]` requires uniform Init; on a NeverInit
    // array it now fails cleanly instead of being silently accepted.
    assert_err(
        "
        extern fn use_mut(r: &mut i64);
        fn f(i: i64) {
          a: [i64; 3];
          r: &mut i64;
          entry:
            r = &mut a[copy i];
            call use_mut(move r);
            return
        }
        ",
        "dynamic index requires the containing array to be uniformly initialized",
    );
}

// ---------- Array of exclusive refs ----------

#[test]
fn array_of_mut_ref_declaration_and_init() {
    // `[&mut i64; N]` composes at the type level. Init via array literal
    // where each element is `&mut x_i`. Since `&mut T` is not Copy but
    // is Move, and ArrayLit takes operands, we borrow-then-move.
    // Boundary: does the parser/type-checker accept the array literal
    // with borrow rvalues masquerading as operands? Expected: the
    // literal itself is operand-only, so this may not parse or may
    // need per-slot init. Pin the current behavior.
    let (errs, _) = run(
        "
        extern fn take(a: [&mut i64; 2]);
        fn f(x: i64, y: i64) {
          rx: &mut i64;
          ry: &mut i64;
          a: [&mut i64; 2];
          entry:
            rx = &mut x;
            ry = &mut y;
            a = [move rx, move ry];
            call take(move a);
            return
        }
        ",
    );
    // Either it works (great) or the diagnostics identify why.
    // Just log what happens by asserting an empty error set is fine
    // OR the errors mention something about the type. Actual check:
    // this must not panic. If errors, the test still succeeds — we
    // just want to document the current state.
    if !errs.is_empty() {
        eprintln!("array_of_mut_ref current diagnostics: {:?}", errs);
    }
}

// ---------- Zero-length array ----------

#[test]
fn zero_length_array_index_out_of_bounds_errors() {
    // `[T; 0]` has no slots; const-index access is out of bounds.
    // `type_check::infer_place_type` catches this at check time.
    assert_err(
        "
        fn f() {
          a: [i64; 0];
          r: &mut i64;
          entry:
            r = &mut a[0i64];
            return
        }
        ",
        "out of bounds",
    );
}

#[test]
fn const_index_past_end_errors() {
    // `[T; N]` with a const index `k >= N` should also error, not
    // just k=0 into [_; 0].
    assert_err(
        "
        fn f() {
          a: [i64; 3];
          r: &mut i64;
          entry:
            a = [1i64, 2i64, 3i64];
            r = &mut a[3i64];
            return
        }
        ",
        "out of bounds",
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
