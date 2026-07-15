//! Shared test helpers for the full check pipeline. Every helper builds on
//! `run(src)`, which runs parse → type_check + all analyses
//! against a single `Diagnostics`.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::parser::Parser;
use crate::run_all_passes;

/// Full pipeline run that yields the structured `Diagnostics` container.
/// Used by tests that need to assert on codes/spans, not just strings.
#[track_caller]
pub fn run_structured(src: &str) -> Diagnostics {
    let program = Parser::new(src.to_string()).parse().unwrap_or_else(|d| {
        panic!(
            "parse error:\n{}\n--- source ---\n{}",
            d.errors_str().join("\n"),
            src
        )
    });
    let mut d = Diagnostics::default().with_source(program.source.clone());
    run_all_passes(&program, &mut d);
    d
}

/// Assert that `d` contains at least one error with the given code whose
/// primary span *starts* at `(line, col)`. End position is ignored: tests
/// pin the point-of-error, not the extent, and widening `Span` to carry
/// end positions should not force every test to update.
#[track_caller]
pub fn assert_error_at(d: &Diagnostics, code: impl Into<DiagCode>, at: (u32, u32)) {
    let expected_code = code.into();
    let matched = d
        .errors()
        .any(|e| e.code() == expected_code && (e.span().line, e.span().col) == at);
    if !matched {
        panic!(
            "no error matched code={:?} at {}:{}\n--- got {} error(s) ---\n{}",
            expected_code,
            at.0, at.1,
            d.error_count(),
            format_diagnostics(d.errors()),
        );
    }
}

/// Warning-side counterpart of [`assert_error_at`]. Matches code and
/// span-start only (see that fn for rationale).
#[track_caller]
pub fn assert_warning_at(d: &Diagnostics, code: impl Into<DiagCode>, at: (u32, u32)) {
    let expected_code = code.into();
    let matched = d
        .warnings()
        .any(|w| w.code() == expected_code && (w.span().line, w.span().col) == at);
    if !matched {
        panic!(
            "no warning matched code={:?} at {}:{}\n--- got {} warning(s) ---\n{}",
            expected_code,
            at.0, at.1,
            d.warning_count(),
            format_diagnostics(d.warnings()),
        );
    }
}

fn format_diagnostics<'a>(diagnostics: impl Iterator<Item = &'a Diagnostic>) -> String {
    let mut lines = Vec::new();
    for diag in diagnostics {
        lines.push(format!("  [{:?}] at {}: {}", diag.code(), diag.span(), diag.message()));
    }
    if lines.is_empty() {
        "  (none)".to_string()
    } else {
        lines.join("\n")
    }
}

/// Parse `src` and run the whole pipeline (check → elaborate → validate).
/// Returns `(errors, warnings)` as preformatted strings — matches the
/// original test API shape. Structured diagnostics live on the
/// `Diagnostics` container returned by `run_all_passes` directly; use
/// that when a test needs code/span rather than substring matching.
pub fn run(src: &str) -> (Vec<String>, Vec<String>) {
    let program = Parser::new(src.to_string()).parse().unwrap_or_else(|d| {
        panic!(
            "parse error:\n{}\n--- source ---\n{}",
            d.errors_str().join("\n"),
            src
        )
    });
    let mut d = Diagnostics::default().with_source(program.source.clone());
    run_all_passes(&program, &mut d);
    (d.errors_str(), d.warnings_str())
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
