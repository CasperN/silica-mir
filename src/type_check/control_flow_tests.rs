use crate::test_util::*;

#[test]
fn empty_program_ok() {
    // Zero declarations — every pass should silently succeed.
    assert_no_diagnostics("");
}

#[test]
fn infinite_loop_function_ok() {
    // No return; every analysis must terminate on the CFG cycle.
    assert_no_diagnostics(
        "
        fn f() {
            entry:
            goto entry
        }
        ",
    );
}

#[test]
fn cross_function_local_names_are_independent() {
    // Two functions each define a local `x` and a block labeled `entry`.
    // Nothing should cross-pollinate — same-named things in one function
    // don't affect the other.
    assert_no_diagnostics(
        "
        fn f() {
            x: number;
            entry:
            x = 42;
            return
        }
        fn g() {
            x: number;
            entry:
            x = 7;
            return
        }
        ",
    );
}

#[test]
fn goto_label_defined_in_another_function_is_undefined() {
    // Labels are function-scoped; a label defined in one function is
    // invisible to gotos in another.
    assert_err(
        "
        fn f() {
            entry:
            goto other
        }
        fn g() {
            other:
            return
        }
        ",
        "goto targets undefined block 'other'",
    );
}

#[test]
fn goto_undefined_label_error() {
    assert_err(
        "
        fn f() {
            entry:
            goto nowhere
        }
        ",
        "goto targets undefined block 'nowhere'",
    );
}

#[test]
fn branch_ok() {
    assert_ok(
        "
        fn f(b: boolean) {
            entry:
            branch(copy b) [true: yes, false: no]
            yes:
            return
            no:
            return
        }
        ",
    );
}

#[test]
fn branch_non_boolean_error() {
    assert_err(
        "
        fn f(n: number) {
            entry:
            branch(copy n) [true: yes, false: no]
            yes:
            return
            no:
            return
        }
        ",
        "branch condition must be boolean",
    );
}

#[test]
fn branch_true_label_undefined_error() {
    assert_err(
        "
        fn f(b: boolean) {
            entry:
            branch(copy b) [true: nowhere, false: no]
            no:
            return
        }
        ",
        "branch true target undefined block 'nowhere'",
    );
}

#[test]
fn branch_false_label_undefined_error() {
    assert_err(
        "
        fn f(b: boolean) {
            entry:
            branch(copy b) [true: yes, false: nowhere]
            yes:
            return
        }
        ",
        "branch false target undefined block 'nowhere'",
    );
}

#[test]
fn switch_enum_ok() {
    assert_ok(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f(o: Option) {
            entry:
            switchEnum(o) [None: end, Some: end]
            end:
            return
        }
        ",
    );
}

#[test]
fn switch_enum_non_enum_place_error() {
    assert_err(
        "
        fn f(n: number) {
            entry:
            switchEnum(n) [A: end]
            end:
            return
        }
        ",
        "switchEnum place must be an enum type",
    );
}

#[test]
fn switch_enum_unknown_variant_error() {
    assert_err(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f(o: Option) {
            entry:
            switchEnum(o) [Wat: end]
            end:
            return
        }
        ",
        "variant 'Wat' is not part of enum 'Option'",
    );
}

#[test]
fn switch_enum_undefined_target_error() {
    assert_err(
        "
        enum Copy Drop Option { None: Option Some: number }
        fn f(o: Option) {
            entry:
            switchEnum(o) [None: nowhere]
        }
        ",
        "targets undefined block 'nowhere'",
    );
}