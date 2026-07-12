//! Enum type emission, `EnumConstr` (whole-value construction),
//! `Downcast` place projection, and `SwitchEnum` terminator lowering.

use super::test_util::*;

// ---------- Type emission ----------

#[test]
fn enum_with_unit_variants_only() {
    // All variants unit → max_payload_size = 0, overall_align = 2
    // (from i16 disc). Payload lane is i16 so LLVM infers align 2.
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%E = type { i16, [0 x i8], [0 x i16] }");
}

#[test]
fn enum_with_number_payload_pads_to_i64_alignment() {
    // i64 needs align 8 → payload_offset = 8, pad_bytes = 6.
    // Payload lane is i64 (align 8) with count ceil(8/8) = 1, so
    // LLVM infers the struct's align as 8.
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%E = type { i16, [6 x i8], [1 x i64] }");
}

#[test]
fn enum_with_bool_payload_stays_align_2() {
    // bool align 1, i16 align 2 → overall_align 2, pad_bytes 0.
    // Payload lane is i16, count = ceil(1/2) = 1 (2 bytes storage
    // for a 1-byte payload — trivial slack).
    let ll = ll_of(
        "
        enum E { A: bool B: unit }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%E = type { i16, [0 x i8], [1 x i16] }");
}

#[test]
fn enum_with_ref_payload_pads_to_pointer_alignment() {
    let ll = ll_of(
        "
        enum E { A: &mut i64 B: unit }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%E = type { i16, [6 x i8], [1 x i64] }");
}

#[test]
fn enum_infers_align_when_embedded_in_struct() {
    // Regression: with an i8 payload lane, LLVM would infer %E align = 2
    // and place `e` at offset 2 within %S, misaligning the payload. With
    // an i64 lane, LLVM infers align 8 and pads `b` correctly.
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        struct S { b: bool e: E }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%E = type { i16, [6 x i8], [1 x i64] }");
    assert_contains(&ll, "%S = type { i1, %E }");
}

// ---------- Alloca alignment ----------

#[test]
fn enum_local_alloca_uses_layout_alignment() {
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f() {
          e: E;
          entry: return
        }
        ",
    );
    assert_contains(&ll, "%local.e = alloca %E, align 8");
}

#[test]
fn enum_of_only_unit_variants_alloca_is_align_2() {
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f() {
          e: E;
          entry: return
        }
        ",
    );
    assert_contains(&ll, "%local.e = alloca %E, align 2");
}

// ---------- EnumConstr ----------

#[test]
fn enum_construction_writes_discriminant_at_field_zero() {
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f() {
          e: E;
          entry:
            e = E::A(42);
            return
        }
        ",
    );
    // Discriminant address at field 0.
    assert_contains(
        &ll,
        "getelementptr %E, ptr %local.e, i32 0, i32 0",
    );
    // A is variant 0 (declaration order).
    assert_contains(&ll, "store i16 0, ptr");
}

#[test]
fn enum_construction_second_variant_gets_index_1() {
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f() {
          e: E;
          entry:
            e = E::B(unit);
            return
        }
        ",
    );
    assert_contains(&ll, "store i16 1, ptr");
}

#[test]
fn enum_construction_writes_payload_at_field_two() {
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f() {
          e: E;
          entry:
            e = E::A(99);
            return
        }
        ",
    );
    assert_contains(
        &ll,
        "getelementptr %E, ptr %local.e, i32 0, i32 2",
    );
    // Payload store at that address.
    assert_contains(&ll, "store i64 99, ptr");
}

#[test]
fn enum_construction_with_unit_payload_skips_payload_store() {
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f() {
          e: E;
          entry:
            e = E::A(unit);
            return
        }
        ",
    );
    // Disc write only — no GEP to field 2 for this variant.
    assert_contains(&ll, "store i16 0, ptr");
    assert!(
        !ll.contains("getelementptr %E, ptr %local.e, i32 0, i32 2"),
        "expected no payload GEP for unit variant:\n{}",
        ll
    );
}

// ---------- Downcast (place projection) ----------

#[test]
fn downcast_read_geps_to_payload_field() {
    // Refined via the switchEnum arm — variant_flow requires it.
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f(e: E) {
          x: i64;
          entry:
            switchEnum(e) [A: a_arm, B: b_arm]
          a_arm:
            x = copy e as A;
            return
          b_arm: return
        }
        ",
    );
    // In a_arm: GEP to payload (field 2), then load.
    assert_contains(
        &ll,
        "getelementptr %E, ptr %local.e, i32 0, i32 2",
    );
    assert_contains(&ll, "load i64, ptr");
}

// ---------- SwitchEnum ----------

#[test]
fn switch_enum_loads_disc_and_emits_switch() {
    let ll = ll_of(
        "
        enum E { A: i64 B: unit }
        fn f(e: E) {
          entry:
            switchEnum(e) [A: a_arm, B: b_arm]
          a_arm: return
          b_arm: return
        }
        ",
    );
    assert_contains(
        &ll,
        "getelementptr %E, ptr %local.e, i32 0, i32 0",
    );
    assert_contains(&ll, "load i16, ptr");
    assert_contains(&ll, "switch i16");
    assert_contains(&ll, "i16 0, label %a_arm");
    assert_contains(&ll, "i16 1, label %b_arm");
}

#[test]
fn switch_enum_reserves_unreachable_default_block() {
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f(e: E) {
          entry:
            switchEnum(e) [A: a_arm, B: b_arm]
          a_arm: return
          b_arm: return
        }
        ",
    );
    assert_contains(&ll, "label %.switch_default.0");
    assert_contains(&ll, ".switch_default.0:");
    // The default block body is `unreachable`.
    let default_idx = ll.find(".switch_default.0:").expect("default block emitted");
    let tail = &ll[default_idx..];
    assert!(
        tail.contains("unreachable"),
        "default block should contain `unreachable`:\n{}",
        tail
    );
}

#[test]
fn multiple_switches_number_their_defaults() {
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f(e: E, e2: E) {
          entry:
            switchEnum(e) [A: a1, B: b1]
          a1:
            switchEnum(e2) [A: a2, B: b2]
          b1: return
          a2: return
          b2: return
        }
        ",
    );
    assert_contains(&ll, ".switch_default.0:");
    assert_contains(&ll, ".switch_default.1:");
}

#[test]
fn switch_default_blocks_come_after_body_blocks() {
    // Structural: default blocks are appended after all MIR blocks so
    // they don't interrupt the natural block ordering the pretty-printer
    // (and any downstream reader) expects.
    let ll = ll_of(
        "
        enum E { A: unit B: unit }
        fn f(e: E) {
          entry:
            switchEnum(e) [A: a_arm, B: b_arm]
          a_arm: return
          b_arm: return
        }
        ",
    );
    let default_pos = ll.find(".switch_default.0:").unwrap();
    let a_arm_pos = ll.find("a_arm:").unwrap();
    let b_arm_pos = ll.find("b_arm:").unwrap();
    assert!(
        default_pos > a_arm_pos && default_pos > b_arm_pos,
        "default block should come after all MIR blocks"
    );
}
