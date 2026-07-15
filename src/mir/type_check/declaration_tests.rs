use crate::mir::test_util::*;

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
        struct Void: Copy + Drop + Move { x: never }
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

#[test]
fn out_never_signals_divergence_ok() {
    // `&out never` is an obligation to initialize an uninhabited
    // pointee — unsatisfiable. The only way to type-check such a
    // function is to not reach `return`. Combined with the return-
    // reachability waiver, an abort-only body is legal.
    assert_ok(
        "
        fn f(r: &out never) {
          entry:
            abort
        }
        ",
    );
}

#[test]
fn never_param_body_is_unreachable_ok() {
    // A function that takes a `never` param is uninhabitedly-callable.
    // Its body can be `unreachable`. `x` at param entry is Init (per
    // `initial_state`), but as an uninhabited value nothing observes it.
    assert_ok(
        "
        fn f(x: never) {
          entry:
            unreachable
        }
        ",
    );
}

#[test]
fn enum_of_only_never_variants_ok() {
    // All variants have `never` payloads → the enum is uninhabited
    // by value but the declaration is legal. Compositional class
    // check passes because never is vacuously Copy Drop Move.
    assert_ok(
        "
        enum Uninhabited: Copy + Drop { A: never B: never }
        ",
    );
}

#[test]
fn copy_struct_with_never_field_full_roundtrip_ok() {
    // Copy Drop Move struct containing a never field. Since the
    // struct is uninhabited by value, we can only exercise the
    // class check compositionally — copy/move via a param that
    // will never be invoked at runtime, body reaches unreachable.
    assert_ok(
        "
        struct Absurd: Copy + Drop + Move { x: i64 y: never }
        extern fn take(a: Absurd);
        fn f(a: Absurd) {
          b: Absurd;
          entry:
            b = copy a;
            unreachable
        }
        ",
    );
}

#[test]
fn local_of_all_never_enum_is_never_init_ok() {
    // Local of an all-never enum stays NeverInit — no way to construct
    // one. At return, NeverInit is not a leak.
    assert_ok(
        "
        enum Uninhabited: Copy + Drop { A: never B: never }
        fn f() {
          e: Uninhabited;
          entry:
            return
        }
        ",
    );
}