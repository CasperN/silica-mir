use crate::test_util::*;
// ---------- Statement: Assign ----------

#[test]
fn assign_type_match_ok() {
    assert_ok(
        "
        fn f() {
            x: number;
            entry:
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn assign_type_mismatch_error() {
    assert_err(
        "
        fn f() {
            x: number;
            entry:
            x = true;
            return
        }
        ",
        "Type mismatch in assignment",
    );
}

#[test]
fn assign_through_mut_ref_ok() {
    // `&mut r` starts pointee Init; writing through *r requires first
    // consuming the pointee (transitioning to Uninit). Use `drop *r`
    // to consume the pointee without needing a local receiver.
    assert_ok(
        "
        fn f(r: &mut number) {
            entry:
            drop *r;
            *r = 42;
            return
        }
        ",
    );
}

#[test]
fn assign_field_type_mismatch_error() {
    assert_err(
        "
        struct S { f: number }
        fn f(s: S) {
            entry:
            s.f = true;
            return
        }
        ",
        "Type mismatch in assignment",
    );
}

#[test]
fn assign_via_downcast_ok() {
    // Downcast writes need the same refinement as reads.
    assert_ok(
        "
        enum Copy Drop Option { None: unit Some: number }
        fn f(o: Option) {
            entry:
            switchEnum(o) [None: n, Some: s]
            s:
            o as Some = 7;
            return
            n: return
        }
        ",
    );
}

#[test]
fn assign_ref_kind_mismatch_error() {
    assert_err(
        "
        fn f(y: number) {
            r: &mut number;
            entry:
            r = &y;
            return
        }
        ",
        "Type mismatch in assignment",
    );
}

#[test]
fn assign_fn_arity_mismatch_error() {
    assert_err(
        "
        fn callee(x: number) { entry: return }
        fn f() {
            g: fn(number, number);
            entry:
            g = callee;
            return
        }
        ",
        "Type mismatch in assignment",
    );
}

// ---------- Statement: Call ----------

#[test]
fn call_direct_by_fn_name_ok() {
    assert_ok(
        "
        extern fn add(a: number, b: number);
        fn f() {
            entry:
            call add(1, 2);
            return
        }
        ",
    );
}

#[test]
fn call_through_local_ok() {
    assert_ok(
        "
        extern fn add(a: number, b: number);
        fn f() {
            g: fn(number, number);
            entry:
            g = add;
            call copy g(1, 2);
            return
        }
        ",
    );
}

#[test]
fn call_wrong_arity_error() {
    assert_err(
        "
        extern fn add(a: number, b: number);
        fn f() {
            entry:
            call add(1);
            return
        }
        ",
        "Wrong number of arguments",
    );
}

#[test]
fn call_wrong_arg_type_error() {
    assert_err(
        "
        extern fn takes_num(a: number);
        fn f() {
            entry:
            call takes_num(true);
            return
        }
        ",
        "Call argument 0 type mismatch",
    );
}

#[test]
fn call_non_function_target_error() {
    assert_err(
        "
        fn f() {
            x: number;
            entry:
            x = 42;
            call copy x();
            return
        }
        ",
        "Call target is not a function type",
    );
}

#[test]
fn call_ref_kind_mismatch_error() {
    assert_err(
        "
        extern fn takes_drop(r: &drop number);
        fn f(y: number) {
            r: &mut number;
            entry:
            r = &mut y;
            call takes_drop(move r);
            return
        }
        ",
        "Call argument 0 type mismatch",
    );
}

// ---------- Terminators ----------

#[test]
fn goto_defined_label_ok() {
    assert_ok(
        "
        fn f() {
            entry:
            goto end
            end:
            return
        }
        ",
    );
}

// ---------- drop statement ----------

#[test]
fn drop_statement_ok() {
    // Syntactically well-formed drop on a param of Drop type.
    assert_ok(
        "
        fn f(x: number) {
            entry:
            drop x;
            return
        }
        ",
    )
}
#[test]
fn double_drop_error() {
    // Syntactically well-formed drop on a param of Drop type.
    assert_err(
        "
        fn f(x: number) {
            entry:
            drop x;
            drop x;
            return
        }
        ",
        "In function 'f', block 'entry': variable 'x' is used after move",
    );
}

#[test]
fn drop_of_undeclared_var_error() {
    assert_err(
        "
        fn f() {
            entry:
            drop x;
            return
        }
        ",
        "Use of undeclared variable 'x'",
    );
}

#[test]
fn trivial_terminators_ok() {
    // return / abort / unreachable in well-formed blocks all pass.
    assert_ok(
        "
        fn a() { entry: return }
        fn b() { entry: abort }
        fn c() { entry: unreachable }
        ",
    );
}
