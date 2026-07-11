//! LLVM lowering for fixed-size arrays: `[T; N]` type emission,
//! `Place::Index` GEP shape, `RValue::ArrayLit` aggregate init,
//! nested arrays, arrays inside struct fields.

use super::test_util::*;

// ---------- Type emission / alloca ----------

#[test]
fn array_type_lowers_to_llvm_array() {
    let ll = ll_of(
        "
        fn f() {
          a: [i64; 3];
          entry:
            a = [1i64, 2i64, 3i64];
            return
        }
        ",
    );
    assert_contains(&ll, "%local.a = alloca [3 x i64], align 8");
}

#[test]
fn byte_array_uses_element_alignment() {
    // `[u8; N]` has align 1 (element's natural alignment).
    let ll = ll_of(
        "
        fn f() {
          b: [u8; 4];
          entry:
            b = [65u8, 66u8, 67u8, 68u8];
            return
        }
        ",
    );
    assert_contains(&ll, "%local.b = alloca [4 x i8], align 1");
}

#[test]
fn nested_array_type_shape() {
    // Array of arrays: `[[i32; 2]; 3]` — outer stride is inner-size.
    let ll = ll_of(
        "
        fn f(m: [[i32; 2]; 3]) {
          entry: return
        }
        ",
    );
    // Arrays pass by value — the param takes the full LLVM array
    // type, not a pointer. The alloca preserves the nesting.
    assert_contains(&ll, "define void @f([3 x [2 x i32]] %arg.m)");
    assert_contains(&ll, "alloca [3 x [2 x i32]]");
}

// ---------- ArrayLit codegen ----------

#[test]
fn array_lit_writes_each_slot_via_gep() {
    let ll = ll_of(
        "
        fn f() {
          a: [i64; 3];
          entry:
            a = [10i64, 20i64, 30i64];
            return
        }
        ",
    );
    // One GEP + store per slot. Element-type single-index form.
    assert_contains(&ll, "getelementptr i64, ptr %local.a, i64 0");
    assert_contains(&ll, "store i64 10,");
    assert_contains(&ll, "getelementptr i64, ptr %local.a, i64 1");
    assert_contains(&ll, "store i64 20,");
    assert_contains(&ll, "getelementptr i64, ptr %local.a, i64 2");
    assert_contains(&ll, "store i64 30,");
}

#[test]
fn empty_array_lit_emits_no_stores() {
    // Zero-length arrays lay out as zero bytes but the alloca still
    // reserves space; ArrayLit is a no-op for stores.
    let ll = ll_of(
        "
        fn f() {
          a: [i64; 0];
          entry:
            a = [];
            return
        }
        ",
    );
    assert_contains(&ll, "%local.a = alloca [0 x i64], align 8");
    // No `store i64` referencing local.a should be present.
    let a_stores: Vec<&str> = ll
        .lines()
        .filter(|l| l.contains("store i64") && l.contains("%local.a"))
        .collect();
    assert!(
        a_stores.is_empty(),
        "empty array literal should emit no stores, got:\n{:?}",
        a_stores
    );
}

// ---------- Static-index read/write ----------

#[test]
fn static_index_read_uses_constant_gep_offset() {
    let ll = ll_of(
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
    // After the three init GEPs+stores, a read GEP with index 1 and
    // then a load feeding a store into x.
    assert_contains(&ll, "getelementptr i64, ptr %local.a, i64 1");
    assert_contains(&ll, "load i64, ptr");
    assert_contains(&ll, "store i64");
}

// ---------- Dynamic-index read: extension of narrower ints ----------

#[test]
fn dynamic_index_sext_from_signed_narrower() {
    // `i32` index gets `sext` to `i64` before GEP.
    let ll = ll_of(
        "
        fn f(i: i32) {
          a: [i64; 3];
          x: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            x = copy a[copy i];
            return
        }
        ",
    );
    assert_contains(&ll, "sext i32");
    assert_contains(&ll, "to i64");
}

#[test]
fn dynamic_index_zext_from_unsigned_narrower() {
    let ll = ll_of(
        "
        fn f(i: u32) {
          a: [i64; 3];
          x: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            x = copy a[copy i];
            return
        }
        ",
    );
    assert_contains(&ll, "zext i32");
    assert_contains(&ll, "to i64");
}

#[test]
fn dynamic_index_i64_needs_no_extension() {
    let ll = ll_of(
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
    // No sext/zext should be present for the i64 index; it feeds
    // the GEP directly.
    assert!(
        !ll.contains("sext") && !ll.contains("zext"),
        "i64 index should not need extension:\n{}",
        ll
    );
}

// ---------- Struct-nested array ----------

#[test]
fn array_in_struct_field_geps_through_both() {
    let ll = ll_of(
        "
        struct Copy Drop Row { data: [i64; 2] }
        fn f() {
          r: Row;
          x: i64;
          entry:
            r.data = [7i64, 42i64];
            x = copy r.data[1i64];
            return
        }
        ",
    );
    // Struct type carries the array.
    assert_contains(&ll, "%Row = type { [2 x i64] }");
    // Field GEP → array-element GEP chain.
    assert_contains(&ll, "getelementptr %Row, ptr %local.r, i32 0, i32 0");
    assert_contains(&ll, "getelementptr i64, ptr");
}

// ---------- Golden IR snapshot ----------

#[test]
fn snapshot_static_index_full_ir() {
    // Pins the full lowering — alloca, ArrayLit expansion (three
    // GEP+store pairs), then a read GEP+load into a scalar local.
    assert_ll_eq(
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
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.a = alloca [3 x i64], align 8
  %local.x = alloca i64, align 8
  br label %entry
entry:
  %t.0 = getelementptr i64, ptr %local.a, i64 0
  store i64 10, ptr %t.0
  %t.1 = getelementptr i64, ptr %local.a, i64 1
  store i64 20, ptr %t.1
  %t.2 = getelementptr i64, ptr %local.a, i64 2
  store i64 30, ptr %t.2
  %t.3 = getelementptr i64, ptr %local.a, i64 1
  %t.4 = load i64, ptr %t.3
  store i64 %t.4, ptr %local.x
  ret void
}",
    );
}

#[test]
fn snapshot_dynamic_index_full_ir() {
    // Pins the dynamic-index sext + GEP shape.
    assert_ll_eq(
        "
        fn f(i: i32) {
          a: [i64; 3];
          x: i64;
          entry:
            a = [10i64, 20i64, 30i64];
            x = copy a[copy i];
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f(i32 %arg.i) {
.init:
  %local.i = alloca i32, align 4
  store i32 %arg.i, ptr %local.i
  %local.a = alloca [3 x i64], align 8
  %local.x = alloca i64, align 8
  br label %entry
entry:
  %t.0 = getelementptr i64, ptr %local.a, i64 0
  store i64 10, ptr %t.0
  %t.1 = getelementptr i64, ptr %local.a, i64 1
  store i64 20, ptr %t.1
  %t.2 = getelementptr i64, ptr %local.a, i64 2
  store i64 30, ptr %t.2
  %t.3 = load i32, ptr %local.i
  %t.4 = sext i32 %t.3 to i64
  %t.5 = getelementptr i64, ptr %local.a, i64 %t.4
  %t.6 = load i64, ptr %t.5
  store i64 %t.6, ptr %local.x
  ret void
}",
    );
}
