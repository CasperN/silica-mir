use crate::mir::test_util::*;

#[test]
fn env_build_ok_mixed_decls() {
    assert_ok(
        "
        struct Point { x: i64 y: i64 }
        enum Option: Copy + Drop { None: unit Some: i64 }
        fn f() { entry: return }
        extern fn g();
        ",
    );
}

#[test]
fn struct_duplicate_field_name_error() {
    assert_err(
        "
        struct S {
            x: i64
            x: bool
        }
        ",
        "field 'x' is declared more than once",
    );
}

#[test]
fn enum_duplicate_variant_name_error() {
    assert_err(
        "
        enum E {
            A: unit
            A: i64
        }
        ",
        "variant 'A' is declared more than once",
    );
}

#[test]
fn env_build_duplicate_struct() {
    assert_err(
        "
        struct P { x: i64 }
        struct P { y: i64 }
        ",
        "Duplicate declaration of type 'P'",
    );
}

#[test]
fn env_build_duplicate_enum() {
    assert_err(
        "
        enum E { A: i64 }
        enum E { B: i64 }
        ",
        "Duplicate declaration of type 'E'",
    );
}

#[test]
fn env_build_struct_enum_name_clash() {
    assert_err(
        "
        struct N { x: i64 }
        enum N { A: i64 }
        ",
        "Duplicate declaration of type 'N'",
    );
}

#[test]
fn env_build_duplicate_function() {
    assert_err(
        "
        fn f() { entry: return }
        fn f() { entry: return }
        ",
        "Duplicate declaration of function 'f'",
    );
}

#[test]
fn env_build_struct_and_fn_same_name_currently_ok() {
    // Documents current behavior: struct/enum and fn share different namespaces.
    // If we ever unify, this test tightens into an assert_err.
    assert_ok(
        "
        struct N { x: i64 }
        fn N() { entry: return }
        ",
    );
}