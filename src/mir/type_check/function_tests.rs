use crate::mir::test_util::*;


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

#[test]
fn return_param_not_last_error() {
    assert_err(
        "fn f($return: &out i64, x: i64) { entry: return }",
        "parameter '$return' must be in the final position",
    );
}

#[test]
fn return_param_wrong_type_error() {
    assert_err(
        "fn f(x: i64, $return: i64) { entry: return }",
        "parameter '$return' must be of type '&out ReturnType'",
    );
    assert_err(
        "fn f(x: i64, $return: &mut i64) { entry: return }",
        "parameter '$return' must be of type '&out ReturnType'",
    );
}

#[test]
fn return_param_valid_ok() {
    assert_ok("fn f(x: i64, $return: &out i64) { entry: $return.* = copy x; return }");
}
