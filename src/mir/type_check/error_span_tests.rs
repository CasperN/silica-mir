use crate::ast::Span;
use crate::test_util::*;
use crate::type_check::TypeCheckCode;

#[test]
fn error_includes_line_and_col() {
    // A bad assignment on a specific line — verify the exact `at L:C:`
    // shows up (not just some span). Line 4, col 17 for `x = true`.
    let src = "fn f() {\n  x: i64;\n  entry:\n                x = true;\n                return\n}";
    let errs = errors_of(src);
    assert_errors_contain(&errs, &["at 4:17:", "Type mismatch in assignment"]);
}

#[test]
fn distinct_errors_carry_distinct_spans() {
    let src = "fn f() {\n  x: i64;\n  y: i64;\n  entry:\n    x = true;\n    y = true;\n    return\n}";
    let errs = errors_of(src);
    assert_errors_contain(&errs, &["at 5:5:", "at 6:5:"]);
}

#[test]
fn accumulate_env_build_duplicates() {
    let errs = errors_of(
        "
        struct S { x: i64 }
        struct S { y: i64 }
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
            x: i64;
            y: i64;
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
            x: i64;
            entry:
            x = true;
            return
        }
        fn g() {
            y: i64;
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
    // non-bool cond and both labels undefined.
    let errs = errors_of(
        "
        fn f(n: i64) {
            entry:
            branch(copy n) [true: nowhere1, false: nowhere2]
        }
        fn g(n: i64) {
            entry:
            branch(copy n) [true: nowhere1, false: nowhere2]
            nowhere1:
            return
            nowhere2: 
            return
        }
        ",
    );
    assert_errors_contain(&errs, &["branch condition must be bool"]);

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
        enum Copy Drop Option { None: unit Some: i64 }
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

// ---------- Structured (code + span) assertions ----------
//
// These verify not just the user-facing message but the machine
// -readable code + exact primary span. Ensures the code enum stays
// in sync with the actual push site and catches accidental span
// drift under refactors.

#[test]
fn structured_assignment_type_mismatch_at_stmt_span() {
    // `x = true;` on line 4, col 17.
    let src = "fn f() {\n  x: i64;\n  entry:\n                x = true;\n                return\n}";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::AssignmentTypeMismatch,
        Span { line: 4, col: 17 },
    );
}

#[test]
fn structured_duplicate_declaration_at_name_span() {
    // Two `struct S {...}` declarations. The second one's name
    // starts at line 3 col 16.
    let src = "\n        struct S { x: i64 }\n        struct S { y: i64 }\n        fn f() { entry: return }\n";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::DuplicateDeclaration,
        Span { line: 3, col: 16 },
    );
}

#[test]
fn structured_goto_undefined_target_at_terminator_span() {
    // The `goto missing_label` sits on line 4 col 17.
    let src = "\n        fn f() {
              entry:
                goto missing_label
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::TerminatorUndefinedTarget,
        Span { line: 4, col: 17 },
    );
}

#[test]
fn structured_undeclared_variable_carries_stmt_span() {
    // Inner `infer_place_type` error propagates through the statement
    // check; the span is the statement, the code is the specific
    // inner failure — not a generic wrapper.
    let src = "
            fn f() {
              x: i64;
              entry:
                x = copy missing;
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::UndeclaredVariable,
        Span { line: 5, col: 17 },
    );
}

#[test]
fn structured_deref_of_non_pointer() {
    // `*x` where `x: i64` — inner place error `DerefOfNonPointer`.
    let src = "
            fn f(x: i64) {
              y: i64;
              entry:
                y = copy *x;
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::DerefOfNonPointer,
        Span { line: 5, col: 17 },
    );
}

#[test]
fn structured_array_index_out_of_bounds() {
    // Const index past array length.
    let src = "
            fn f() {
              a: [i64; 2];
              x: i64;
              entry:
                a = [1i64, 2i64];
                x = copy a[2i64];
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        TypeCheckCode::ArrayIndexOutOfBounds,
        Span { line: 7, col: 17 },
    );
}