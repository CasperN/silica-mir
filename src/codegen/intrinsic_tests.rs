//! Intrinsic call lowering. Verifies each intrinsic emits the expected
//! LLVM instruction sequence inline, with no `call void @$name(...)`
//! surviving to the emitted `.ll`.
//!
//! Test structure: bind an `&out` ref to a local first (`out = &out r;`),
//! then call the intrinsic with `move out`. This is Silica's standard
//! calling convention for out-params.

use super::test_util::*;

// ---------- Interception ----------

#[test]
fn intrinsic_call_produces_no_symbol_call() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_add(copy a, copy b, move out);
            return
        }
        ",
    );
    // The intrinsic symbol must not appear in codegen output; the call
    // was intercepted and lowered inline.
    assert!(
        !ll.contains("@$i64_add"),
        "intrinsic symbol leaked into IR:\n{}",
        ll
    );
    assert!(
        !ll.contains("call void @$"),
        "no `call void @$…` should be present:\n{}",
        ll
    );
}

// ---------- Integer arithmetic ----------

#[test]
fn i64_add_lowers_to_llvm_add() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_add(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= add i64");
}

#[test]
fn i64_sub_lowers_to_llvm_sub() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_sub(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= sub i64");
}

#[test]
fn i64_mul_lowers_to_llvm_mul() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_mul(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= mul i64");
}

// ---------- Comparison (result is boolean) ----------

#[test]
fn i64_lt_lowers_to_icmp_slt() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: boolean;
          out: &out boolean;
          entry:
            out = &out r;
            call $i64_lt(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= icmp slt i64");
    // Result stored as i1 through the &out boolean pointer.
    assert_contains(&ll, "store i1");
}

// ---------- Unary ----------

#[test]
fn i64_neg_lowers_to_sub_zero() {
    let ll = ll_of(
        "
        fn f(a: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_neg(copy a, move out);
            return
        }
        ",
    );
    // LLVM has no dedicated `neg` — canonical is `sub 0, x`.
    assert_contains(&ll, "= sub i64 0,");
}

// ---------- Float ----------

#[test]
fn f64_add_lowers_to_llvm_fadd() {
    let ll = ll_of(
        "
        fn f(a: f64, b: f64) {
          r: f64;
          out: &out f64;
          entry:
            out = &out r;
            call $f64_add(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fadd double");
}

#[test]
fn f64_mul_lowers_to_llvm_fmul() {
    let ll = ll_of(
        "
        fn f(a: f64, b: f64) {
          r: f64;
          out: &out f64;
          entry:
            out = &out r;
            call $f64_mul(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fmul double");
}

// ---------- Result routing ----------

#[test]
fn intrinsic_result_stored_through_out_pointer() {
    // The `move out` operand loads out's slot to get the pointee address;
    // the intrinsic result is stored through that pointer.
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_add(copy a, copy b, move out);
            return
        }
        ",
    );
    // Sequence check: the add's result feeds a `store i64 %..., ptr %...`.
    let store_line = ll
        .lines()
        .find(|l| l.contains("store i64 %"))
        .unwrap_or_else(|| panic!("no store i64 %... in IR:\n{}", ll));
    assert!(
        store_line.contains(", ptr %"),
        "expected store-through-ptr shape: {}",
        store_line
    );
}

// ---------- Golden IR: full lowering snapshots ----------
//
// The tests above pin individual instructions. These pin the *whole*
// emitted module for a small program — same idea as the `assert_elab_eq`
// snapshot tests in `lifetime/nll_tests.rs`, but at the codegen layer.
// If temp-name numbering, alloca ordering, .init block layout, or any
// other codegen shape changes unintentionally, these fail loudly.

#[test]
fn snapshot_i64_add_full_ir() {
    assert_ll_eq(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_add(copy a, copy b, move out);
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.a, i64 %arg.b) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.b = alloca i64, align 8
  store i64 %arg.b, ptr %local.b
  %local.r = alloca i64, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i64, ptr %local.a
  %t.1 = load i64, ptr %local.b
  %t.2 = add i64 %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store i64 %t.2, ptr %t.3
  ret void
}",
    );
}

#[test]
fn snapshot_i64_lt_full_ir() {
    // Comparison intrinsic: operand type is i64, result type is
    // boolean (i1). Verifies the two-type shape of the signature and
    // that the &out slot is `alloca ptr` regardless of pointee.
    assert_ll_eq(
        "
        fn f(a: i64, b: i64) {
          r: boolean;
          out: &out boolean;
          entry:
            out = &out r;
            call $i64_lt(copy a, copy b, move out);
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.a, i64 %arg.b) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.b = alloca i64, align 8
  store i64 %arg.b, ptr %local.b
  %local.r = alloca i1, align 1
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i64, ptr %local.a
  %t.1 = load i64, ptr %local.b
  %t.2 = icmp slt i64 %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store i1 %t.2, ptr %t.3
  ret void
}",
    );
}

#[test]
fn snapshot_i64_neg_full_ir() {
    // Unary intrinsic — single input + out. Verifies the LLVM `sub 0, x`
    // idiom for integer negation.
    assert_ll_eq(
        "
        fn f(a: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_neg(copy a, move out);
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f(i64 %arg.a) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.r = alloca i64, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i64, ptr %local.a
  %t.1 = sub i64 0, %t.0
  %t.2 = load ptr, ptr %local.out
  store i64 %t.1, ptr %t.2
  ret void
}",
    );
}

#[test]
fn snapshot_f64_mul_full_ir() {
    // Float intrinsic — operand and out both `double`.
    assert_ll_eq(
        "
        fn f(a: f64, b: f64) {
          r: f64;
          out: &out f64;
          entry:
            out = &out r;
            call $f64_mul(copy a, copy b, move out);
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @f(double %arg.a, double %arg.b) {
.init:
  %local.a = alloca double, align 8
  store double %arg.a, ptr %local.a
  %local.b = alloca double, align 8
  store double %arg.b, ptr %local.b
  %local.r = alloca double, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load double, ptr %local.a
  %t.1 = load double, ptr %local.b
  %t.2 = fmul double %t.0, %t.1
  %t.3 = load ptr, ptr %local.out
  store double %t.2, ptr %t.3
  ret void
}",
    );
}

#[test]
fn snapshot_composed_intrinsics_full_ir() {
    // Multiple intrinsics feeding each other, plus a call from a fn
    // returning through &out. Pins the full lowering of a realistic
    // arithmetic pipeline: `(a + b) * a` written to `*out`.
    assert_ll_eq(
        "
        fn compute(a: i64, b: i64, out: &out i64) {
          t1: i64;
          t2: i64;
          t1_out: &out i64;
          t2_out: &out i64;
          entry:
            t1_out = &out t1;
            call $i64_add(copy a, copy b, move t1_out);
            t2_out = &out t2;
            call $i64_mul(copy t1, copy a, move t2_out);
            *out = copy t2;
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()

define void @compute(i64 %arg.a, i64 %arg.b, ptr %arg.out) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.b = alloca i64, align 8
  store i64 %arg.b, ptr %local.b
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  %local.t1 = alloca i64, align 8
  %local.t2 = alloca i64, align 8
  %local.t1_out = alloca ptr, align 8
  %local.t2_out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.t1, ptr %local.t1_out
  %t.0 = load i64, ptr %local.a
  %t.1 = load i64, ptr %local.b
  %t.2 = add i64 %t.0, %t.1
  %t.3 = load ptr, ptr %local.t1_out
  store i64 %t.2, ptr %t.3
  store ptr %local.t2, ptr %local.t2_out
  %t.4 = load i64, ptr %local.t1
  %t.5 = load i64, ptr %local.a
  %t.6 = mul i64 %t.4, %t.5
  %t.7 = load ptr, ptr %local.t2_out
  store i64 %t.6, ptr %t.7
  %t.8 = load i64, ptr %local.t2
  %t.9 = load ptr, ptr %local.out
  store i64 %t.8, ptr %t.9
  ret void
}",
    );
}

// ---------- Exotic-intrinsic path (llvm_declares) ----------

#[test]
fn snapshot_i64_popcount_full_ir() {
    // Exercises the `@llvm.*`-call path: an intrinsic with a
    // `llvm_declares` entry surfaces its `declare` in the module
    // preamble AND its `call i64 @llvm.ctpop.i64(...)` inline.
    // Pins the whole shape so future changes to declare-emission
    // (e.g. ordering, dedupe, per-fn vs module-level) fail loudly.
    assert_ll_eq(
        "
        fn f(a: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_popcount(copy a, move out);
            return
        }
        ",
        "\
; Generated from Silica-MIR
declare void @abort()
declare i64 @llvm.ctpop.i64(i64)

define void @f(i64 %arg.a) {
.init:
  %local.a = alloca i64, align 8
  store i64 %arg.a, ptr %local.a
  %local.r = alloca i64, align 8
  %local.out = alloca ptr, align 8
  br label %entry
entry:
  store ptr %local.r, ptr %local.out
  %t.0 = load i64, ptr %local.a
  %t.1 = call i64 @llvm.ctpop.i64(i64 %t.0)
  %t.2 = load ptr, ptr %local.out
  store i64 %t.1, ptr %t.2
  ret void
}",
    );
}

#[test]
fn unused_intrinsic_declare_is_not_emitted() {
    // Programs that don't call popcount must not have popcount's
    // `declare` in their preamble — proves `llvm_declares_needed`
    // prunes correctly. Guards against future declare emission
    // becoming unconditional and bloating every module.
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_add(copy a, copy b, move out);
            return
        }
        ",
    );
    assert!(
        !ll.contains("@llvm.ctpop.i64"),
        "popcount's declare leaked into a program that doesn't use it:\n{}",
        ll
    );
}

// ---------- Boolean branch smoke (README punch-list "boolean flow") ----------

#[test]
fn boolean_result_of_intrinsic_used_in_branch_ok() {
    // Compute a boolean via `$i64_gt` (writes through `&out boolean`),
    // then feed to a `branch` terminator. Currently the branch does
    // no refinement on its operand (unlike switchEnum); this pins the
    // current behavior and provides an anchor for a future flow-
    // analysis change on booleans (README punch list).
    let (errs, _) = crate::test_util::run(
        "
        fn f(x: i64) {
          b: boolean;
          bo: &out boolean;
          y: i64;
          entry:
            bo = &out b;
            call $i64_gt(copy x, 0i64, move bo);
            branch(copy b) [true: t_arm, false: f_arm]
          t_arm:
            y = 1;
            goto join
          f_arm:
            y = 2;
            goto join
          join:
            return
        }
        ",
    );
    assert!(
        errs.is_empty(),
        "expected clean run for boolean-branch program, got: {:?}",
        errs
    );
}

// ---------- Missing intrinsics (documents a gap) ----------

#[test]
fn f64_lt_is_not_yet_an_intrinsic() {
    // README lists only `$f64_add` and `$f64_mul`. Any missing float
    // predicate should surface as an unknown-function error. When
    // `$f64_lt` gets added, flip this test.
    let (errs, _) = crate::test_util::run(
        "
        fn f(x: f64, y: f64) {
          b: boolean;
          out: &out boolean;
          entry:
            out = &out b;
            call $f64_lt(copy x, copy y, move out);
            return
        }
        ",
    );
    assert!(
        errs.iter().any(|e| e.contains("$f64_lt") || e.contains("Undeclared")
            || e.contains("undeclared") || e.contains("not defined")),
        "expected an unknown-function-style error mentioning $f64_lt, got: {:?}",
        errs
    );
}
