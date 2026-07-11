use crate::test_util::*;

#[test]
fn error_includes_line_and_col() {
    // A bad assignment on a specific line — verify the exact `at L:C:`
    // shows up (not just some span). Line 4, col 17 for `x = true`.
    let src = "fn f() {\n  x: number;\n  entry:\n                x = true;\n                return\n}";
    let errs = errors_of(src);
    assert_errors_contain(&errs, &["at 4:17:", "Type mismatch in assignment"]);
}

#[test]
fn distinct_errors_carry_distinct_spans() {
    let src = "fn f() {\n  x: number;\n  y: number;\n  entry:\n    x = true;\n    y = true;\n    return\n}";
    let errs = errors_of(src);
    assert_errors_contain(&errs, &["at 5:5:", "at 6:5:"]);
}

#[test]
fn accumulate_env_build_duplicates() {
    let errs = errors_of(
        "
        struct S { x: number }
        struct S { y: number }
        fn f() { entry: return }
        fn f() { entry: return }
        ",
    );
    assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
    assert_errors_contain(&errs, &["type 'S'", "function 'f'"]);
}

#[test]
fn accumulate_statement_errors_in_one_block() {
    let errs = errors_of(
        "
        fn f() {
            x: number;
            y: number;
            entry:
            x = true;
            y = true;
            return
        }
        ",
    );
    // Two independent bad assigns in one block should both be reported.
    assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
    assert!(errs
        .iter()
        .all(|e| e.contains("Type mismatch in assignment")));
}

#[test]
fn accumulate_across_functions() {
    let errs = errors_of(
        "
        fn f() {
            x: number;
            entry:
            x = true;
            return
        }
        fn g() {
            y: number;
            entry:
            y = true;
            return
        }
        ",
    );
    assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
    assert_errors_contain(&errs, &["'f'", "'g'"]);
}

#[test]
fn accumulate_branch_multi_error() {
    // A single `branch` terminator can produce three independent errors:
    // non-boolean cond and both labels undefined.
    let errs = errors_of(
        "
        fn f(n: number) {
            entry:
            branch(copy n) [true: nowhere1, false: nowhere2]
        }
        fn g(n: number) {
            entry:
            branch(copy n) [true: nowhere1, false: nowhere2]
            nowhere1:
            return
            nowhere2: 
            return
        }
        ",
    );
    assert_errors_contain(&errs, &["branch condition must be boolean"]);

    assert_one_error_contains_all(
        &errs,
        &["4:13", "branch true target undefined block 'nowhere1'"],
    );
    assert_one_error_contains_all(
        &errs,
        &["4:13", "branch false target undefined block 'nowhere2'"],
    );
}

#[test]
fn accumulate_switch_enum_multi_error() {
    // switchEnum with an unknown variant AND an undefined target should
    // report both, and continue past the failed variant check.
    let errs = errors_of(
        "
        enum Copy Drop Option { None: unit Some: number }
        fn f(o: Option) {
            entry:
            switchEnum(o) [Wat: nowhere, None: end]
            end:
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &[
            "variant 'Wat' is not part of enum 'Option'",
            "targets undefined block 'nowhere'",
        ],
    );
}