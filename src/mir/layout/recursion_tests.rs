//! By-value recursion detection for struct and enum types.
//!
//! Uses the full `test_util::run` pipeline so we exercise the diagnostic
//! wire-up as well as the check logic.

use crate::mir::test_util::*;

// ---------- Not recursive (should pass) ----------

#[test]
fn plain_struct_ok() {
    assert_no_diagnostics(
        "
        struct P { x: i64 y: i64 }
        fn f() { entry: return }
        ",
    );
}

#[test]
fn struct_referencing_itself_by_reference_ok() {
    // The referent is behind a pointer of bounded size — no infinite layout.
    assert_no_diagnostics(
        "
        struct Node { next: &mut Node }
        fn f() { entry: return }
        ",
    );
}

#[test]
fn enum_variant_referencing_itself_by_reference_ok() {
    assert_no_diagnostics(
        "
        enum List { Nil: unit Cons: &mut List }
        fn f() { entry: return }
        ",
    );
}

#[test]
fn mutually_referencing_via_references_ok() {
    assert_no_diagnostics(
        "
        struct A { b: &mut B }
        struct B { a: &mut A }
        fn f() { entry: return }
        ",
    );
}

// ---------- Recursive: self-loops ----------

#[test]
fn struct_containing_itself_by_value_errors() {
    assert_err(
        "
        struct S { s: S }
        fn f() { entry: return }
        ",
        "type 'S' is recursive by value",
    );
}

#[test]
fn enum_variant_carrying_itself_by_value_errors() {
    // The README's `Loop { A: unit B: Loop }` — now rejected.
    assert_err(
        "
        enum Loop { A: unit B: Loop }
        fn f() { entry: return }
        ",
        "type 'Loop' is recursive by value",
    );
}

// ---------- Recursive: mutual ----------

#[test]
fn mutually_recursive_structs_by_value_errors() {
    let (errs, _) = run(
        "
        struct A { b: B }
        struct B { a: A }
        fn f() { entry: return }
        ",
    );
    assert_errors_contain(&errs, &["is recursive by value"]);
    let cycle_report = errs.iter().find(|e| e.contains("recursive")).unwrap();
    assert!(
        cycle_report.contains("A") && cycle_report.contains("B"),
        "expected cycle to mention both A and B: {}",
        cycle_report,
    );
}

#[test]
fn mutually_recursive_struct_and_enum_errors() {
    let (errs, _) = run(
        "
        enum E { V: S }
        struct S { e: E }
        fn f() { entry: return }
        ",
    );
    assert_errors_contain(&errs, &["is recursive by value"]);
}

#[test]
fn three_way_cycle_errors_once() {
    let (errs, _) = run(
        "
        struct A { b: B }
        struct B { c: C }
        struct C { a: A }
        fn f() { entry: return }
        ",
    );
    let cycle_errs: Vec<_> = errs
        .iter()
        .filter(|e| e.contains("recursive by value"))
        .collect();
    assert_eq!(
        cycle_errs.len(),
        1,
        "expected one aggregate cycle error, got {}: {:?}",
        cycle_errs.len(),
        cycle_errs,
    );
}

// ---------- Recursive through function type: bounded, allowed ----------

#[test]
fn struct_holding_fn_of_self_is_ok() {
    // fn types lower to pointers — no infinite size, so allowed.
    assert_no_diagnostics(
        "
        struct S { f: fn(S) }
        fn f() { entry: return }
        ",
    );
}
