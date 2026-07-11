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

// ---------- Never type ----------

#[test]
fn never_local_ok() {
    // Never is uninhabited — a local of type never starts NeverInit
    // and stays NeverInit (nothing can construct one). Trivially valid.
    assert_ok(
        "
        fn f() {
          x: never;
          entry:
            return
        }
        ",
    );
}

#[test]
fn never_in_all_marker_struct_ok() {
    // Never is vacuously Copy + Drop + Move, so a struct with all
    // markers may contain a never-typed field. The whole struct is
    // uninhabited but the declaration is legal.
    assert_ok(
        "
        struct Copy Drop Move Void { x: never }
        ",
    );
}

#[test]
fn never_inside_ref_ok() {
    // `&never`, `&mut never` etc. are legal reference types (also
    // uninhabited, since there's no valid place to point to).
    assert_ok(
        "
        fn f(r: &never) {
          entry:
            return
        }
        ",
    );
}