//! Multi-feature integration programs.
//!
//! These aren't unit tests for any single pass — they're realistic
//! computations written in the current MIR, combining arithmetic
//! intrinsics, control flow, structs, enums, references, and casts.
//! Each program is a small representative of a language capability
//! and doubles as a boundary test: if a combination is under-tested
//! by unit suites, breakage will show up here.

use crate::mir::test_util::*;

// ---------- Recursion via reference-passed results ----------

#[test]
fn recursive_factorial_ok() {
    // Silica has no return values — `fact` writes through an &out.
    // Recursion goes through a local &out that references the caller's
    // slot. Exercises: recursion, intrinsics (mul/sub/le), branch.
    assert_no_diagnostics(
        "
        fn fact(n: i64, out: &out i64) {
          base: bool;
          bo: &out bool;
          sub: i64;
          sub_out: &out i64;
          sub_result: i64;
          rec_out: &out i64;
          mul_out: &out i64;
          entry:
            bo = &out base;
            call $i64_le(copy n, 1i64, move bo);
            branch(copy base) [true: base_arm, false: rec_arm]
          base_arm:
            out.* = 1i64;
            return
          rec_arm:
            sub_out = &out sub;
            call $i64_sub(copy n, 1i64, move sub_out);
            rec_out = &out sub_result;
            call fact(copy sub, move rec_out);
            mul_out = &out out.*;
            call $i64_mul(copy n, copy sub_result, move mul_out);
            return
        }
        ",
    );
}

#[test]
fn iterative_fibonacci_loop_ok() {
    // Loop with two mutable state locals updated per iteration.
    // Exercises: loop CFG, bool flow through intrinsic result,
    // multi-var state, arithmetic.
    //
    // Note the two-slot pattern for each intrinsic output: `foo_tmp`
    // is the fresh slot the intrinsic writes into, then we `move` it
    // to the persistent state var. This is the standard Silica
    // discipline — `&out foo` promises to initialize an Uninit slot,
    // so an Init slot on the loop back-edge doesn't qualify. The
    // `move` at the end of the body consumes `foo_tmp`, restoring
    // its Uninit state for the next iteration's `&out foo_tmp`.
    assert_no_diagnostics(
        "
        fn fib(n: i64, out: &out i64) {
          a: i64;
          b: i64;
          i: i64;
          i_tmp: i64;
          done_tmp: bool;
          done_out: &out bool;
          next_tmp: i64;
          next_out: &out i64;
          inc_out: &out i64;
          entry:
            a = 0i64;
            b = 1i64;
            i = 0i64;
            goto head
          head:
            done_out = &out done_tmp;
            call $i64_ge(copy i, copy n, move done_out);
            branch(move done_tmp) [true: exit, false: body]
          body:
            next_out = &out next_tmp;
            call $i64_add(copy a, copy b, move next_out);
            a = copy b;
            b = move next_tmp;
            inc_out = &out i_tmp;
            call $i64_add(copy i, 1i64, move inc_out);
            i = move i_tmp;
            goto head
          exit:
            out.* = copy a;
            return
        }
        ",
    );
}

// ---------- Deep enum projection ----------

#[test]
fn enum_of_enum_switch_and_downcast_ok() {
    // Outer::A(Inner::X(payload)) — two levels of downcast. Once
    // switchEnum refines the outer, a nested switchEnum on the
    // extracted payload can refine the inner. Exercises: nested
    // enum layout, refinement across levels, per-arm variance.
    assert_no_diagnostics(
        "
        enum Copy Drop Inner { X: i64 Y: i64 }
        enum Copy Drop Outer { A: Inner B: i64 }
        fn f(o: Outer, out: &out i64) {
          inner: Inner;
          entry:
            switchEnum(o) [A: a_arm, B: b_arm]
          a_arm:
            inner = copy o as A;
            switchEnum(inner) [X: x_arm, Y: y_arm]
          x_arm:
            out.* = copy inner as X;
            return
          y_arm:
            out.* = copy inner as Y;
            return
          b_arm:
            out.* = copy o as B;
            return
        }
        ",
    );
}

// ---------- Never variant in a switchEnum ----------

#[test]
fn enum_with_never_variant_unreachable_arm_ok() {
    // `enum { A: i64, N: never }` — the `N` variant is uninhabited
    // (no `never` value can exist to wrap). variant_flow recognizes
    // this and accepts an `unreachable` terminator on the N arm.
    assert_no_diagnostics(
        "
        enum Copy Drop E { A: i64 N: never }
        fn f(e: E, out: &out i64) {
          entry:
            switchEnum(e) [A: a_arm, N: n_arm]
          a_arm:
            out.* = copy e as A;
            return
          n_arm:
            unreachable
        }
        ",
    );
}

// ---------- Array of enums, per-slot switch ----------

#[test]
fn array_of_enums_per_slot_switch_ok() {
    // Take an array `[Tag; N]` and sum contributions per slot.
    // Exercises: array indexing × enum switch × per-arm arithmetic.
    // Neg arms use a temp slot (`v0_neg`) since the negation
    // intrinsic writes via &out, and we can't &out an Init slot.
    assert_no_diagnostics(
        "
        enum Copy Drop Tag { Zero: unit Pos: i64 Neg: i64 }
        fn sum(a: [Tag; 2], out: &out i64) {
          t0: Tag;
          t1: Tag;
          v0: i64;
          v1: i64;
          v0_neg: i64;
          v1_neg: i64;
          neg_out: &out i64;
          add_out: &out i64;
          entry:
            t0 = copy a[0i64];
            t1 = copy a[1i64];
            switchEnum(t0) [Zero: z0, Pos: p0, Neg: n0]
          z0:
            v0 = 0i64;
            goto do_t1
          p0:
            v0 = copy t0 as Pos;
            goto do_t1
          n0:
            neg_out = &out v0_neg;
            call $i64_neg(copy t0 as Neg, move neg_out);
            v0 = copy v0_neg;
            drop v0_neg;
            goto do_t1
          do_t1:
            switchEnum(t1) [Zero: z1, Pos: p1, Neg: n1]
          z1:
            v1 = 0i64;
            goto combine
          p1:
            v1 = copy t1 as Pos;
            goto combine
          n1:
            neg_out = &out v1_neg;
            call $i64_neg(copy t1 as Neg, move neg_out);
            v1 = copy v1_neg;
            drop v1_neg;
            goto combine
          combine:
            add_out = &out out.*;
            call $i64_add(copy v0, copy v1, move add_out);
            return
        }
        ",
    );
}

// ---------- Cast round trips ----------

#[test]
fn i32_to_i64_and_back_ok() {
    // Widening + narrowing round trip. Values that fit in i32 survive
    // trunc(sext(x)) intact.
    assert_no_diagnostics(
        "
        fn f(x: i32, out: &out i32) {
          wide: i64;
          wide_out: &out i64;
          narrow_out: &out i32;
          entry:
            wide_out = &out wide;
            call $i32_to_i64(copy x, move wide_out);
            narrow_out = &out out.*;
            call $i64_to_i32(copy wide, move narrow_out);
            return
        }
        ",
    );
}

#[test]
fn bool_to_int_arithmetic_ok() {
    // Bool derived from a comparison, promoted to i32, and used
    // in arithmetic. This is the closest thing to `x < 0 ? 1 : 0`
    // in current Silica.
    assert_no_diagnostics(
        "
        fn f(x: i64, out: &out i32) {
          neg: bool;
          bo: &out bool;
          zext_out: &out i32;
          entry:
            bo = &out neg;
            call $i64_lt(copy x, 0i64, move bo);
            zext_out = &out out.*;
            call $bool_to_i32(copy neg, move zext_out);
            return
        }
        ",
    );
}

// ---------- Bit manipulation ----------

#[test]
fn is_power_of_two_via_bitops_ok() {
    // `x & (x - 1) == 0` — classical bit-twiddling.
    assert_no_diagnostics(
        "
        fn is_pow2(x: u64, out: &out bool) {
          minus_one: u64;
          masked: u64;
          sub_out: &out u64;
          and_out: &out u64;
          bo: &out bool;
          entry:
            sub_out = &out minus_one;
            call $u64_sub(copy x, 1u64, move sub_out);
            and_out = &out masked;
            call $u64_and(copy x, copy minus_one, move and_out);
            bo = &out out.*;
            call $u64_eq(copy masked, 0u64, move bo);
            return
        }
        ",
    );
}

#[test]
fn popcount_and_clz_compose_ok() {
    // Small program that uses both LLVM-backed intrinsics.
    assert_no_diagnostics(
        "
        fn f(x: i32, out: &out i32) {
          leading: i32;
          pop: i32;
          pop_out: &out i32;
          clz_out: &out i32;
          add_out: &out i32;
          entry:
            pop_out = &out pop;
            call $i32_popcount(copy x, move pop_out);
            clz_out = &out leading;
            call $i32_clz(copy x, move clz_out);
            add_out = &out out.*;
            call $i32_add(copy pop, copy leading, move add_out);
            return
        }
        ",
    );
}

// ---------- Function pointer indirect call ----------

#[test]
fn function_pointer_indirect_call_ok() {
    // Assign a function name to an `fn(...)` local, call through it.
    // Exercises: FnName const, fn-typed locals, Copy Drop on fn.
    assert_no_diagnostics(
        "
        fn double(x: i64, out: &out i64) {
          add_out: &out i64;
          entry:
            add_out = &out out.*;
            call $i64_add(copy x, copy x, move add_out);
            return
        }
        fn call_it(f: fn(i64, &out i64), x: i64, out: &out i64) {
          fwd_out: &out i64;
          entry:
            fwd_out = &out out.*;
            call copy f(copy x, move fwd_out);
            return
        }
        fn main(exit: &out i32) {
          r: i64;
          r_out: &out i64;
          trunc_out: &out i32;
          entry:
            r_out = &out r;
            call call_it(double, 21i64, move r_out);
            trunc_out = &out exit.*;
            call $i64_to_i32(copy r, move trunc_out);
            return
        }
        ",
    );
}

// ---------- Struct through raw pointer ----------

#[test]
fn raw_ptr_to_struct_field_access_ok() {
    // `p: *Point`. `p.*.x` — Deref of a raw pointer followed by field
    // projection. Raw pointer skips loan/init checks but the field
    // projection still needs to typecheck.
    assert_no_diagnostics(
        "
        struct Copy Drop Point { x: i64 y: i64 }
        fn f(pt: Point, out: &out i64) {
          p: *Point;
          entry:
            p = &raw pt;
            out.* = copy p.*.x;
            return
        }
        ",
    );
}

// ---------- Two-arm switchEnum with different obligations ----------

#[test]
fn switch_arm_asymmetric_ref_use_ok() {
    // r: &mut i64 param. In arm A we consume-and-restore the pointee;
    // in arm B we leave it untouched. Both paths converge to return
    // with the obligation satisfied.
    assert_no_diagnostics(
        "
        enum Copy Drop Which { A: unit B: unit }
        fn f(r: &mut i64, w: Which) {
          consumed: i64;
          entry:
            switchEnum(w) [A: a_arm, B: b_arm]
          a_arm:
            consumed = move r.*;
            r.* = 99i64;
            goto join
          b_arm:
            goto join
          join:
            return
        }
        ",
    );
}

// ---------- Struct-of-refs constructed piecewise ----------

#[test]
fn pack_two_refs_into_struct_and_pass_ok() {
    // Two &mut i64 borrowers packed into a Move struct, passed to
    // a sink. Exercises: piecewise struct init with ref fields,
    // whole-struct move consuming both loans, sink discharging them.
    assert_no_diagnostics(
        "
        struct Move Pair { a: &mut i64 b: &mut i64 }
        extern fn use_pair(p: Pair);
        fn f(x: i64, y: i64) {
          p: Pair;
          entry:
            p.a = &mut x;
            p.b = &mut y;
            call use_pair(move p);
            return
        }
        ",
    );
}

// ---------- Sum an array with a dynamic index ----------

// ---------- Downcast-target reassignment ----------

#[test]
fn downcast_target_reassignment_elaborates_to_full_construction() {
    // `o as Some = 7` used to silently overwrite the old payload.
    // Drop-elab now rewrites the whole statement to
    // `drop (o as Some); o = Option::Some(7)` so the old payload's
    // destructor eventually runs. This avoids the enum-atomicity
    // trap: a bare `drop (o as Some)` cascades o to Moved and
    // breaks the subsequent write, but pairing it with an
    // EnumConstr reconstruction restores o to Init as variant Some.
    use crate::mir::parser::Parser;
    use crate::mir::pretty_print::pretty_print;
    use crate::elaborate_and_check_mir;
    let src = "
        enum Copy Drop Option { None: unit Some: i64 }
        fn f(o: Option) {
          entry:
            switchEnum(o) [None: n, Some: s]
          s:
            o as Some = 7;
            return
          n: return
        }
    ";
    let program = Parser::new(src.to_string()).parse().unwrap();
    let mut d = crate::diagnostics::Diagnostics::default().with_source(program.source.clone());
    let (elaborated, _env) = elaborate_and_check_mir(&program, &mut d);
    assert!(d.is_clean(), "expected clean run, got {:?}", d.errors_str());
    let out = pretty_print(&elaborated);
    assert!(
        out.contains("drop o as Some;")
            && out.contains("o = Option::Some(7);"),
        "expected downcast rewrite in elaborated form:\n{}",
        out
    );
}

// ---------- Straight-line reassignment via &out ----------

#[test]
fn straight_line_reassign_via_out_ok_via_elaboration() {
    // A sequence of intrinsic calls that all write through `&out r`
    // to the SAME slot `r`. Without pre-`&out` drop elaboration this
    // would require a fresh temp per call and a `move` back into r.
    // The elaborator now inserts an implicit `drop r` before each
    // rebinding of `&out r`. Note we don't read `r` inside the same
    // call that reborrows it — the loan doesn't end until the ref
    // is consumed at the last operand.
    assert_no_diagnostics(
        "
        fn f(a: i64, b: i64, c: i64, out: &out i64) {
          r: i64;
          r_out: &out i64;
          entry:
            r_out = &out r;
            call $i64_add(copy a, copy b, move r_out);
            r_out = &out r;
            call $i64_mul(copy a, copy c, move r_out);
            out.* = copy r;
            return
        }
        ",
    );
}

#[test]
fn sum_array_via_dynamic_index_loop_ok() {
    // Classic loop over an array. Dynamic index means every access
    // widens to the whole array — since the array is fully Init at
    // the loop head, all iterations satisfy read preconditions.
    // Same tmp-slot pattern as fib for accumulator + loop counter.
    assert_no_diagnostics(
        "
        fn sum(a: [i64; 4], out: &out i64) {
          sum: i64;
          sum_tmp: i64;
          i: i64;
          i_tmp: i64;
          done_tmp: bool;
          done_out: &out bool;
          slot: i64;
          add_out: &out i64;
          inc_out: &out i64;
          entry:
            sum = 0i64;
            i = 0i64;
            goto head
          head:
            done_out = &out done_tmp;
            call $i64_ge(copy i, 4i64, move done_out);
            branch(move done_tmp) [true: exit, false: body]
          body:
            slot = copy a[copy i];
            add_out = &out sum_tmp;
            call $i64_add(copy sum, copy slot, move add_out);
            sum = move sum_tmp;
            drop slot;
            inc_out = &out i_tmp;
            call $i64_add(copy i, 1i64, move inc_out);
            i = move i_tmp;
            goto head
          exit:
            out.* = copy sum;
            return
        }
        ",
    );
}
