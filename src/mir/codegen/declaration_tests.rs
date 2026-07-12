//! Preamble, extern function declarations, and struct type definitions.

use super::test_util::*;

#[test]
fn preamble_declares_abort() {
    let ll = ll_of("fn f() { entry: return }");
    assert_contains(&ll, "declare void @abort()");
}

#[test]
fn extern_fn_declaration() {
    let ll = ll_of("extern fn print_num(x: i64);");
    assert_contains(&ll, "declare void @print_num(i64)");
}

#[test]
fn extern_fn_with_ref_and_bool() {
    let ll = ll_of("extern fn f(a: bool, r: &mut i64);");
    assert_contains(&ll, "declare void @f(i1, ptr)");
}

#[test]
fn struct_decl_lowered_to_named_type() {
    let ll = ll_of(
        "
        struct P { x: i64 y: i64 }
        fn f() { entry: return }
        ",
    );
    assert_contains(&ll, "%P = type { i64, i64 }");
}
