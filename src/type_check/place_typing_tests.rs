use crate::test_util::*;

#[test]
fn place_unknown_var_error() {
    assert_err(
        "
        fn f() {
            entry:
            x = 42;
            return
        }
        ",
        "Use of undeclared variable 'x'",
    );
}

#[test]
fn place_struct_field_ok() {
    assert_ok(
        "
        struct Copy Drop P { x: number y: number }
        fn f(p: P) {
            a: number;
            entry:
            a = copy p.x;
            return
        }
        ",
    );
}

#[test]
fn place_unknown_field_error() {
    assert_err(
        "
        struct P { x: number }
        fn f(p: P) {
            a: number;
            entry:
            a = copy p.z;
            return
        }
        ",
        "Struct 'P' has no field 'z'",
    );
}

#[test]
fn place_field_on_non_struct_error() {
    assert_err(
        "
        fn f(n: number) {
            a: number;
            entry:
            a = copy n.x;
            return
        }
        ",
        "Cannot project field",
    );
}

#[test]
fn place_field_on_enum_error() {
    assert_err(
        "
        enum E { A: number }
        fn f(e: E) {
            a: number;
            entry:
            a = copy e.x;
            return
        }
        ",
        "Cannot project field 'x' of enum type 'E'",
    );
}

#[test]
fn place_downcast_ok() {
    // Downcast reads are only legal in a block refined by a preceding
    // switchEnum arm — enforced by `enum_variants`.
    assert_ok(
        "
        enum Copy Drop Option { None: unit Some: number }
        fn f(o: Option) {
            x: number;
            entry:
            switchEnum(o) [None: n, Some: s]
            s:
            x = copy o as Some;
            return
            n: return
        }
        ",
    );
}

#[test]
fn place_downcast_unknown_variant_error() {
    assert_err(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f(o: Option) {
            x: number;
            entry:
            x = copy o as Wat;
            return
        }
        ",
        "Enum 'Option' has no variant 'Wat'",
    );
}

#[test]
fn place_downcast_on_non_enum_type() {
    // Downcasting a non-Custom (e.g. reference) hits the dedicated
    // 'Cannot downcast non-enum type' branch.
    assert_err(
        "
        fn f(r: &number) {
            x: number;
            entry:
            x = copy r as Some;
            return
        }
        ",
        "Cannot downcast non-enum type",
    );
}

#[test]
fn place_downcast_on_struct_error() {
    assert_err(
        "
        struct S { x: number }
        fn f(s: S) {
            x: number;
            entry:
            x = copy s as Some;
            return
        }
        ",
        "Cannot downcast struct type 'S'",
    );
}

#[test]
fn place_deref_ok() {
    assert_ok(
        "
        fn f(r: &number) {
            x: number;
            entry:
            x = copy *r;
            return
        }
        ",
    );
}

#[test]
fn nested_reference_type_ok() {
    // `&mut &mut T` — parser and tc handle both the type and the double
    // deref on the read side.
    assert_ok(
        "
        fn f(r: &mut &mut number) {
            a: number;
            entry:
            a = copy **r;
            return
        }
        ",
    );
}

#[test]
fn zero_arity_fn_type_ok() {
    // `fn()` as a local type — the operand chain and Type::Fn(vec![])
    // round-trip through the checker cleanly.
    assert_ok(
        "
        fn noop() { entry: return }
        fn f() {
            g: fn();
            entry:
            g = noop;
            call copy g();
            return
        }
        ",
    );
}

#[test]
fn place_deref_of_non_ref_error() {
    assert_err(
        "
        fn f(y: number) {
            x: number;
            entry:
            x = copy *y;
            return
        }
        ",
        "Cannot dereference non-reference type",
    );
}

#[test]
fn place_deref_through_field_ok() {
    // Exercises Deref(Field(Var, "r")) — a reference held in a struct field.
    assert_ok(
        "
        struct Copy Drop Ptr { r: &number }
        fn f(p: Ptr) {
            a: number;
            entry:
            a = copy *p.r;
            return
        }
        ",
    );
}
