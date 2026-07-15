//! Size and alignment computation for scalars, references, function
//! types, structs, and enums.

use crate::mir::layout::{align_of, size_of};
use crate::mir::parser::Parser;
use crate::mir::type_check::Env;
use crate::mir::ast::*;

/// Parse `src` and build an `Env`. Doesn't run any check pass — the
/// tests just need type-name resolution.
fn env_of(src: &str) -> Env {
    let program = Parser::new(src.to_string()).parse().unwrap_or_else(|d| {
        panic!(
            "parse error:\n{}\n--- source ---\n{}",
            d.errors_str().join("\n"),
            src
        )
    });
    Env::build(&program).0
}

// ---------- Scalars and pointers ----------

#[test]
fn scalar_sizes() {
    let env = env_of("fn f() { entry: return }");
    assert_eq!(size_of(&Type::Int(IntTy::I64), &env), 8);
    assert_eq!(size_of(&Type::Bool, &env), 1);
    assert_eq!(size_of(&Type::Unit, &env), 0);
    assert_eq!(size_of(&Type::Never, &env), 0);
}

#[test]
fn scalar_alignments() {
    let env = env_of("fn f() { entry: return }");
    assert_eq!(align_of(&Type::Int(IntTy::I64), &env), 8);
    assert_eq!(align_of(&Type::Bool, &env), 1);
    assert_eq!(align_of(&Type::Unit, &env), 1);
    assert_eq!(align_of(&Type::Never, &env), 1);
}

#[test]
fn all_ref_kinds_and_fn_are_pointer_sized() {
    let env = env_of("fn f() { entry: return }");
    let inner = Box::new(Type::Int(IntTy::I64));
    for kind in [
        RefKind::Shared,
        RefKind::Mut,
        RefKind::Out,
        RefKind::Drop,
        RefKind::Uninit,
    ] {
        let ty = Type::Ref(kind, inner.clone());
        assert_eq!(size_of(&ty, &env), 8);
        assert_eq!(align_of(&ty, &env), 8);
    }
    let fn_ty = Type::Fn(vec![Type::Int(IntTy::I64), Type::Bool]);
    assert_eq!(size_of(&fn_ty, &env), 8);
    assert_eq!(align_of(&fn_ty, &env), 8);
}

// ---------- Structs ----------

#[test]
fn empty_struct_is_zero_sized() {
    let env = env_of("struct S { } fn f() { entry: return }");
    let ty = Type::Custom("S".to_string());
    assert_eq!(size_of(&ty, &env), 0);
    assert_eq!(align_of(&ty, &env), 1);
}

#[test]
fn homogeneous_struct_sums_field_sizes() {
    let env = env_of("struct P { x: i64 y: i64 } fn f() { entry: return }");
    let ty = Type::Custom("P".to_string());
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}

#[test]
fn struct_pads_between_smaller_then_larger_field() {
    // b:bool at offset 0 (size 1), then x:i64 aligned to 8 → offset 8;
    // total = 8 + 8 = 16, rounded to align 8.
    let env = env_of("struct P { b: bool x: i64 } fn f() { entry: return }");
    let ty = Type::Custom("P".to_string());
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}

#[test]
fn struct_rounds_up_trailing_padding_to_alignment() {
    // x:i64 at offset 0 (size 8), b:bool at offset 8 (size 1);
    // total 9, rounded to align 8 → 16.
    let env = env_of("struct P { x: i64 b: bool } fn f() { entry: return }");
    let ty = Type::Custom("P".to_string());
    assert_eq!(size_of(&ty, &env), 16);
}

#[test]
fn packed_bool_only_struct_is_tightly_packed() {
    // Three bools, all align 1: no padding.
    let env = env_of(
        "struct P { a: bool b: bool c: bool } fn f() { entry: return }",
    );
    let ty = Type::Custom("P".to_string());
    assert_eq!(size_of(&ty, &env), 3);
    assert_eq!(align_of(&ty, &env), 1);
}

#[test]
fn nested_struct_inherits_alignment() {
    let env = env_of(
        "
        struct Inner { x: i64 }
        struct Outer { i: Inner b: bool }
        fn f() { entry: return }
        ",
    );
    let ty = Type::Custom("Outer".to_string());
    // Inner is 8 bytes, align 8. Outer: Inner @ 0..8, bool @ 8; total 9
    // rounded to 8 → 16.
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}

#[test]
fn struct_with_reference_field_uses_pointer_size() {
    let env = env_of("struct S { r: &mut i64 x: bool } fn f() { entry: return }");
    let ty = Type::Custom("S".to_string());
    // r at 0..8 (align 8), b at 8; total 9 → 16.
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}

// ---------- Enums ----------

#[test]
fn enum_with_unit_only_variants_is_discriminant_only() {
    let env = env_of("enum E { A: unit B: unit } fn f() { entry: return }");
    let ty = Type::Custom("E".to_string());
    // {i16, [0 x i8]} align 2 → size 2.
    assert_eq!(size_of(&ty, &env), 2);
    assert_eq!(align_of(&ty, &env), 2);
}

#[test]
fn enum_with_number_payload_pads_disc_to_8() {
    let env = env_of("enum E { A: i64 B: unit } fn f() { entry: return }");
    let ty = Type::Custom("E".to_string());
    // disc:i16 at 0..2, padded to 8 for i64-aligned payload; payload 8;
    // total 16, align 8.
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}

#[test]
fn enum_size_is_dominated_by_largest_variant_payload() {
    let env = env_of(
        "
        struct Big { a: i64 b: i64 c: i64 }
        enum E { Small: i64 Wide: Big }
        fn f() { entry: return }
        ",
    );
    let ty = Type::Custom("E".to_string());
    // Big is 24 bytes align 8. Enum: disc padded to 8, +24 payload = 32.
    assert_eq!(size_of(&ty, &env), 32);
    assert_eq!(align_of(&ty, &env), 8);
}

#[test]
fn enum_with_only_bool_payloads_is_align_2() {
    let env = env_of("enum E { A: bool B: unit } fn f() { entry: return }");
    let ty = Type::Custom("E".to_string());
    // disc:i16 at 0..2, bool at offset 2 (align 1) size 1, total 3,
    // rounded to align 2 = 4.
    assert_eq!(size_of(&ty, &env), 4);
    assert_eq!(align_of(&ty, &env), 2);
}

#[test]
fn enum_with_ref_payload_is_pointer_aligned() {
    let env = env_of("enum E { A: &mut i64 B: unit } fn f() { entry: return }");
    let ty = Type::Custom("E".to_string());
    // disc padded to 8, +8 pointer = 16, align 8.
    assert_eq!(size_of(&ty, &env), 16);
    assert_eq!(align_of(&ty, &env), 8);
}
