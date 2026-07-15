use crate::mir::test_util::*;

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
        struct P: Copy + Drop { x: i64 y: i64 }
        fn f(p: P) {
            a: i64;
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
        struct P { x: i64 }
        fn f(p: P) {
            a: i64;
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
        fn f(n: i64) {
            a: i64;
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
        enum E { A: i64 }
        fn f(e: E) {
            a: i64;
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
        enum Option: Copy + Drop { None: unit Some: i64 }
        fn f(o: Option) {
            x: i64;
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
        enum Option: Copy + Drop { None: unit Some: i64 }
        fn f(o: Option) {
            x: i64;
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
        fn f(r: &i64) {
            x: i64;
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
        struct S { x: i64 }
        fn f(s: S) {
            x: i64;
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
        fn f(r: &i64) {
            x: i64;
            entry:
            x = copy r.*;
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
        fn f(r: &mut &mut i64) {
            a: i64;
            entry:
            a = copy r.*.*;
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
        fn f(y: i64) {
            x: i64;
            entry:
            x = copy y.*;
            return
        }
        ",
        "Cannot dereference non-pointer type",
    );
}

#[test]
fn place_deref_through_field_ok() {
    // Exercises Deref(Field(Var, "r")) — dereference a reference stored in a
    // struct field. `p.r.*` parses as Deref(Field(Var(p), r)).
    assert_ok(
        "
        struct Ptr: Copy + Drop { r: &i64 }
        fn f(p: Ptr) {
            a: i64;
            entry:
            a = copy p.r.*;
            return
        }
        ",
    );
}
