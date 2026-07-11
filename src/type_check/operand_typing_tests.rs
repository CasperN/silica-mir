use crate::test_util::*;

#[test]
fn operand_number_const_ok() {
    assert_ok(
        "
        fn f() {
            x: i64;
            entry:
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn operand_unit_const_ok() {
    assert_ok(
        "
        fn f() {
            u: unit;
            entry:
            u = unit;
            return
        }
        ",
    );
}

#[test]
fn unit_as_enum_payload_ok() {
    assert_ok(
        "
        enum Copy Drop Tag { A: unit B: i64 }
        fn f() {
            t: Tag;
            entry:
            t = Tag::A(unit);
            return
        }
        ",
    );
}

#[test]
fn unit_type_mismatch_error() {
    assert_err(
        "
        fn f() {
            n: i64;
            entry:
            n = unit;
            return
        }
        ",
        "Type mismatch in assignment",
    );
}

#[test]
fn operand_boolean_const_ok() {
    assert_ok(
        "
        fn f() {
            b: boolean;
            entry:
            b = true;
            return
        }
        ",
    );
}

#[test]
fn operand_fnname_defined_ok() {
    assert_ok(
        "
        fn callee(x: i64) { entry: return }
        fn f() {
            g: fn(i64);
            entry:
            g = callee;
            return
        }
        ",
    );
}

#[test]
fn operand_fnname_extern_ok() {
    assert_ok(
        "
        extern fn callee(x: i64);
        fn f() {
            g: fn(i64);
            entry:
            g = callee;
            return
        }
        ",
    );
}

#[test]
fn operand_fnname_undeclared_error() {
    // A bare identifier in operand position is parsed as ConstVal::FnName —
    // if it isn't a declared function, this is where the error surfaces.
    assert_err(
        "
        fn f() {
            g: fn(i64);
            entry:
            g = missing;
            return
        }
        ",
        "Undeclared function name 'missing'",
    );
}
