use crate::test_util::*;


#[test]
fn duplicate_param_name_error() {
    assert_err(
        "fn f(x: i64, x: i64) { entry: return }",
        "Duplicate variable name 'x' in parameters",
    );
}

#[test]
fn local_shadows_param_error() {
    assert_err(
        "
        fn f(x: i64) {
            x: i64;
            entry:
            return
        }
        ",
        "Duplicate variable name 'x'",
    );
}

#[test]
fn duplicate_local_name_error() {
    assert_err(
        "
        fn f() {
            x: i64;
            x: i64;
            entry:
            return
        }
        ",
        "Duplicate variable name 'x'",
    );
}

#[test]
fn extern_fn_declared_and_callable_ok() {
    assert_ok(
        "
        extern fn takes_num(a: i64);
        fn f() {
            entry:
            call takes_num(1);
            return
        }
        ",
    );
}

#[test]
fn extern_fn_with_bad_param_type_error() {
    assert_err("extern fn foo(x: Nope);", "Use of undeclared type 'Nope'");
}

#[test]
fn unreachable_with_statements_ok() {
    // Intentionally allowed: an `unreachable` block can host debug/printf
    // statements for when the compiler mispredicts unreachability.
    assert_ok(
        "
        fn f() {
            x: i64;
            entry:
            x = 42;
            unreachable
        }
        ",
    );
}

#[test]
fn empty_function_body_error() {
    assert_err("fn f() { }", "Function 'f' has no entry block");
}
