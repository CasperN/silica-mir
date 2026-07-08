use crate::test_util::*;

#[test]
fn validate_undeclared_field_type() {
    assert_err("struct S { x: Nope }", "Use of undeclared type 'Nope'");
}

#[test]
fn validate_undeclared_enum_payload_type() {
    assert_err("enum E { A: Nope }", "Use of undeclared type 'Nope'");
}

#[test]
fn validate_undeclared_param_type() {
    assert_err(
        "fn f(x: Nope) { entry: return }",
        "Use of undeclared type 'Nope'",
    );
}

#[test]
fn validate_undeclared_local_type() {
    assert_err(
        "fn f() { x: Nope; entry: return }",
        "Use of undeclared type 'Nope'",
    );
}

#[test]
fn validate_undeclared_type_inside_ref() {
    assert_err(
        "fn f(x: &mut Nope) { entry: return }",
        "Use of undeclared type 'Nope'",
    );
}

#[test]
fn validate_undeclared_type_inside_fn_type() {
    assert_err(
        "fn f(g: fn(Nope)) { entry: return }",
        "Use of undeclared type 'Nope'",
    );
}