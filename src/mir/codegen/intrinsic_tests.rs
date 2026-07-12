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

// ---------- Comparison (result is bool) ----------

#[test]
fn i64_lt_lowers_to_icmp_slt() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: bool;
          out: &out bool;
          entry:
            out = &out r;
            call $i64_lt(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= icmp slt i64");
    // Result stored as i1 through the &out bool pointer.
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
    // bool (i1). Verifies the two-type shape of the signature and
    // that the &out slot is `alloca ptr` regardless of pointee.
    assert_ll_eq(
        "
        fn f(a: i64, b: i64) {
          r: bool;
          out: &out bool;
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

// ---------- Bool branch smoke (README punch-list "bool flow") ----------

#[test]
fn bool_result_of_intrinsic_used_in_branch_ok() {
    // Compute a bool via `$i64_gt` (writes through `&out bool`),
    // then feed to a `branch` terminator. Currently the branch does
    // no refinement on its operand (unlike switchEnum); this pins the
    // current behavior and provides an anchor for a future flow-
    // analysis change on bools (README punch list).
    let (errs, _) = crate::test_util::run(
        "
        fn f(x: i64) {
          b: bool;
          bo: &out bool;
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
        "expected clean run for bool-branch program, got: {:?}",
        errs
    );
}

// ---------- Float comparisons ----------

#[test]
fn f64_lt_lowers_to_ordered_fcmp() {
    // Float predicates are ordered by default (NaN inputs make the
    // comparison false). Ordered less-than lowers to `fcmp olt`.
    let ll = ll_of(
        "
        fn f(x: f64, y: f64) {
          b: bool;
          out: &out bool;
          entry:
            out = &out b;
            call $f64_lt(copy x, copy y, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "fcmp olt double");
}

// ---------- Expanded surface: per-width, bitwise, shifts, div/rem ----------

#[test]
fn i32_add_uses_i32_width() {
    let ll = ll_of(
        "
        fn f(a: i32, b: i32) {
          r: i32;
          out: &out i32;
          entry:
            out = &out r;
            call $i32_add(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= add i32");
}

#[test]
fn u8_mul_uses_i8_width() {
    // u8 and i8 share the LLVM i8 type — signedness only affects
    // ops like sdiv/udiv, not add/sub/mul.
    let ll = ll_of(
        "
        fn f(a: u8, b: u8) {
          r: u8;
          out: &out u8;
          entry:
            out = &out r;
            call $u8_mul(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= mul i8");
}

#[test]
fn i64_and_or_xor_lower_to_bitwise() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_and(copy a, copy b, move out);
            call $i64_or(copy a, copy b, move out);
            call $i64_xor(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= and i64");
    assert_contains(&ll, "= or i64");
    assert_contains(&ll, "= xor i64");
}

#[test]
fn i32_shr_uses_ashr_but_u32_shr_uses_lshr() {
    let ll = ll_of(
        "
        fn f(a: i32, b: i32, c: u32, d: u32) {
          r_signed: i32;
          out_signed: &out i32;
          r_unsigned: u32;
          out_unsigned: &out u32;
          entry:
            out_signed = &out r_signed;
            call $i32_shr(copy a, copy b, move out_signed);
            out_unsigned = &out r_unsigned;
            call $u32_shr(copy c, copy d, move out_unsigned);
            return
        }
        ",
    );
    assert_contains(&ll, "= ashr i32");
    assert_contains(&ll, "= lshr i32");
}

#[test]
fn i32_div_uses_sdiv_but_u32_div_uses_udiv() {
    let ll = ll_of(
        "
        fn f(a: i32, b: i32, c: u32, d: u32) {
          r_signed: i32;
          out_signed: &out i32;
          r_unsigned: u32;
          out_unsigned: &out u32;
          entry:
            out_signed = &out r_signed;
            call $i32_div(copy a, copy b, move out_signed);
            out_unsigned = &out r_unsigned;
            call $u32_div(copy c, copy d, move out_unsigned);
            return
        }
        ",
    );
    assert_contains(&ll, "= sdiv i32");
    assert_contains(&ll, "= udiv i32");
}

#[test]
fn i64_rem_lowers_to_srem() {
    let ll = ll_of(
        "
        fn f(a: i64, b: i64) {
          r: i64;
          out: &out i64;
          entry:
            out = &out r;
            call $i64_rem(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= srem i64");
}

// ---------- Float surface: sub, div, neg ----------

#[test]
fn f64_sub_div_neg_lower_correctly() {
    let ll = ll_of(
        "
        fn f(a: f64, b: f64) {
          r: f64;
          out: &out f64;
          entry:
            out = &out r;
            call $f64_sub(copy a, copy b, move out);
            call $f64_div(copy a, copy b, move out);
            call $f64_neg(copy a, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fsub double");
    assert_contains(&ll, "= fdiv double");
    assert_contains(&ll, "= fneg double");
}

#[test]
fn f32_arithmetic_uses_float_type() {
    let ll = ll_of(
        "
        fn f(a: f32, b: f32) {
          r: f32;
          out: &out f32;
          entry:
            out = &out r;
            call $f32_add(copy a, copy b, move out);
            call $f32_mul(copy a, copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fadd float");
    assert_contains(&ll, "= fmul float");
}

// ---------- Casts ----------

#[test]
fn i32_to_i64_lowers_to_sext() {
    let ll = ll_of(
        "
        fn f(x: i32) {
          y: i64;
          out: &out i64;
          entry:
            out = &out y;
            call $i32_to_i64(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= sext i32");
    assert_contains(&ll, " to i64");
}

#[test]
fn u32_to_u64_lowers_to_zext() {
    let ll = ll_of(
        "
        fn f(x: u32) {
          y: u64;
          out: &out u64;
          entry:
            out = &out y;
            call $u32_to_u64(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= zext i32");
    assert_contains(&ll, " to i64");
}

#[test]
fn i64_to_i32_lowers_to_trunc() {
    let ll = ll_of(
        "
        fn f(x: i64) {
          y: i32;
          out: &out i32;
          entry:
            out = &out y;
            call $i64_to_i32(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= trunc i64");
    assert_contains(&ll, " to i32");
}

#[test]
fn i64_to_f64_uses_sitofp() {
    let ll = ll_of(
        "
        fn f(x: i64) {
          y: f64;
          out: &out f64;
          entry:
            out = &out y;
            call $i64_to_f64(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= sitofp i64");
    assert_contains(&ll, " to double");
}

#[test]
fn f64_to_u32_uses_fptoui() {
    let ll = ll_of(
        "
        fn f(x: f64) {
          y: u32;
          out: &out u32;
          entry:
            out = &out y;
            call $f64_to_u32(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fptoui double");
    assert_contains(&ll, " to i32");
}

#[test]
fn f32_to_f64_uses_fpext() {
    let ll = ll_of(
        "
        fn f(x: f32) {
          y: f64;
          out: &out f64;
          entry:
            out = &out y;
            call $f32_to_f64(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= fpext float");
}

#[test]
fn bool_to_i32_uses_zext_from_i1() {
    let ll = ll_of(
        "
        fn f(b: bool) {
          y: i32;
          out: &out i32;
          entry:
            out = &out y;
            call $bool_to_i32(copy b, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "= zext i1");
    assert_contains(&ll, " to i32");
}

// ---------- LLVM-intrinsic-backed ops ----------

#[test]
fn i32_clz_calls_llvm_ctlz_with_zero_undef_false() {
    let ll = ll_of(
        "
        fn f(x: i32) {
          y: i32;
          out: &out i32;
          entry:
            out = &out y;
            call $i32_clz(copy x, move out);
            return
        }
        ",
    );
    // The declare line lists the extra i1 arg; the call passes false.
    assert_contains(&ll, "declare i32 @llvm.ctlz.i32(i32, i1)");
    assert_contains(&ll, "call i32 @llvm.ctlz.i32(i32");
    assert_contains(&ll, ", i1 false)");
}

#[test]
fn f64_sqrt_calls_llvm_sqrt() {
    let ll = ll_of(
        "
        fn f(x: f64) {
          y: f64;
          out: &out f64;
          entry:
            out = &out y;
            call $f64_sqrt(copy x, move out);
            return
        }
        ",
    );
    assert_contains(&ll, "declare double @llvm.sqrt.double(double)");
    assert_contains(&ll, "call double @llvm.sqrt.double(double");
}
