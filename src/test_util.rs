//! Shared test helpers for the full check pipeline. Every helper builds on
//! `run(src)`, which runs parse → type_check + all analyses
//! against a single `Diagnostics`.

use crate::parser::Parser;
use crate::run_all_passes;

/// Parse `src` and run every check. Returns `(errors, warnings)`.
pub fn run(src: &str) -> (Vec<String>, Vec<String>) {
    let program = Parser::new(src.to_string())
        .parse()
        .unwrap_or_else(|e| panic!("parse error: {}\n--- source ---\n{}", e, src));
    let d = run_all_passes(&program);
    (d.errors, d.warnings)
}

/// Convenience: just the errors from `run(src)`.
pub fn errors_of(src: &str) -> Vec<String> {
    run(src).0
}

/// Assert the pipeline produced no errors. Warnings are allowed.
#[track_caller]
pub fn assert_ok(src: &str) {
    let (errors, warnings) = run(src);
    if !errors.is_empty() {
        panic!(
            "expected success, got errors:\n  {}\nwarnings:\n  {}\n--- source ---\n{}",
            errors.join("\n  "),
            warnings.join("\n  "),
            src
        );
    }
}

/// Stricter than [`assert_ok`]: no errors AND no warnings.
#[track_caller]
pub fn assert_no_diagnostics(src: &str) {
    let (errors, warnings) = run(src);
    if !errors.is_empty() || !warnings.is_empty() {
        panic!(
            "expected clean run, got:\nerrors:\n  {}\nwarnings:\n  {}\n--- source ---\n{}",
            errors.join("\n  "),
            warnings.join("\n  "),
            src
        );
    }
}

/// Assert that the pipeline produced at least one error containing `needle`.
#[track_caller]
pub fn assert_err(src: &str, needle: &str) {
    let (errors, _) = run(src);
    if errors.is_empty() {
        panic!(
            "expected error containing {:?}, got Ok\n--- source ---\n{}",
            needle, src
        );
    }
    assert_errors_contain(&errors, &[needle]);
}

/// Assert every needle appears as a substring in at least one error.
#[track_caller]
pub fn assert_errors_contain(errs: &[String], needles: &[&str]) {
    let missing: Vec<&str> = needles
        .iter()
        .copied()
        .filter(|n| !errs.iter().any(|e| e.contains(n)))
        .collect();
    if !missing.is_empty() {
        let missing_str = missing
            .iter()
            .map(|n| format!("  {:?}", n))
            .collect::<Vec<_>>()
            .join("\n");
        let errs_str = if errs.is_empty() {
            "  (no errors)".to_string()
        } else {
            errs.iter()
                .map(|e| format!("  {}", e))
                .collect::<Vec<_>>()
                .join("\n")
        };
        panic!(
            "missing expected error substrings:\n{}\ngot {} error(s):\n{}",
            missing_str,
            errs.len(),
            errs_str
        );
    }
}

/// Assert at least one error contains ALL of the given substrings. Useful for
/// pinning "span + message" pairs to the same error line.
#[track_caller]
pub fn assert_one_error_contains_all(errs: &[String], needles: &[&str]) {
    let matched = errs.iter().any(|e| needles.iter().all(|n| e.contains(n)));
    if !matched {
        let needles_str = needles
            .iter()
            .map(|n| format!("  {:?}", n))
            .collect::<Vec<_>>()
            .join("\n");
        let errs_str = if errs.is_empty() {
            "  (no errors)".to_string()
        } else {
            errs.iter()
                .map(|e| format!("  {}", e))
                .collect::<Vec<_>>()
                .join("\n")
        };
        panic!(
            "no single error contained all substrings:\n{}\ngot {} error(s):\n{}",
            needles_str,
            errs.len(),
            errs_str
        );
    }
}

/// Assert every needle appears as a substring in at least one warning.
#[track_caller]
pub fn assert_warnings_contain(warnings: &[String], needles: &[&str]) {
    let missing: Vec<&str> = needles
        .iter()
        .copied()
        .filter(|n| !warnings.iter().any(|w| w.contains(n)))
        .collect();
    if !missing.is_empty() {
        panic!(
            "missing expected warning substrings:\n  {}\ngot {} warning(s):\n  {}",
            missing
                .iter()
                .map(|n| format!("{:?}", n))
                .collect::<Vec<_>>()
                .join("\n  "),
            warnings.len(),
            warnings.join("\n  ")
        );
    }
}
