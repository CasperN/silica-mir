use crate::test_util::*;

#[test]
fn rvalue_ref_shared_ok() {
    assert_ok(
        "
        fn f(y: number) {
            r: &number;
            entry:
            r = &y;
            return
        }
        ",
    );
}

#[test]
fn rvalue_ref_mut_ok() {
    assert_ok(
        "
        fn f(y: number) {
            r: &mut number;
            entry:
            r = &mut y;
            return
        }
        ",
    );
}

#[test]
fn rvalue_enum_constr_ok() {
    assert_ok(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f() {
            o: Option;
            entry:
            o = Option::Some(42);
            return
        }
        ",
    );
}

#[test]
fn rvalue_enum_constr_unknown_enum_error() {
    assert_err(
        "
        fn f() {
            entry:
            return
        }
        enum Copy Drop Option { None: Option Some: number }
        struct S { x: number }
        fn g() {
            o: Option;
            entry:
            o = Nope::Some(42);
            return
        }
        ",
        "Undeclared enum 'Nope'",
    );
}

#[test]
fn rvalue_enum_constr_unknown_variant_error() {
    assert_err(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f() {
            o: Option;
            entry:
            o = Option::Wat(42);
            return
        }
        ",
        "Enum 'Option' has no variant 'Wat'",
    );
}

#[test]
fn rvalue_enum_constr_wrong_payload_type_error() {
    assert_err(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f() {
            o: Option;
            entry:
            o = Option::Some(true);
            return
        }
        ",
        "expects type",
    );
}

#[test]
fn rvalue_enum_constr_self_recursive_payload_ok() {
    // Option::None has payload type Option (matches whole enum).
    assert_ok(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f(o: Option) {
            r: Option;
            entry:
            r = Option::None(move o);
            return
        }
        ",
    );
}