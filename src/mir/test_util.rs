//! Shared test helpers for the full check pipeline. Every helper builds on
//! `run(src)`, which runs parse → type_check + all analyses
//! against a single `Diagnostics`.
//!
//! Fixture extraction mode: setting `EXTRACT_FIXTURES=1` in the
//! environment causes every `run` / `run_structured` call to also
//! write the source string to `tests/{elab,errors}/…/<test_name>.sim`
//! as a side effect. Directory is inferred from whether the run
//! produced errors. Used to bulk-migrate the unit-test corpus into
//! the fixture runner (see `tests/fixtures.rs`).

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::parser::Parser;
use crate::elaborate_and_check_mir;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

// ============================================================
// Fixture extraction (opt-in via EXTRACT_FIXTURES=1)
// ============================================================

fn extract_mode() -> bool {
    std::env::var("EXTRACT_FIXTURES").ok().as_deref() == Some("1")
}

// Per-test call counter so multiple `run(...)` calls in one test each
// get a distinct fixture filename (`name.sim`, `name_call1.sim`, ...).
static EXTRACT_COUNTERS: OnceLock<Mutex<HashMap<String, usize>>> = OnceLock::new();

/// Write `src` to a fixture file derived from the current test's
/// module path + name. `has_errors` is used only to strip the
/// matching `_ok`/`_error` suffix from the test name.
/// No-op when EXTRACT_FIXTURES is unset.
pub(crate) fn maybe_write_fixture(src: &str, has_errors: bool) {
    maybe_write_fixture_ext(src, has_errors, "sim")
}

pub(crate) fn maybe_write_fixture_ext(src: &str, has_errors: bool, ext: &str) {
    maybe_write_fixture_impl(src, None, has_errors, ext)
}

/// Codegen extraction: writes to `tests/codegen-raw/` regardless of
/// diagnostic content, since these tests bypass the checker pipeline
/// entirely.
pub(crate) fn maybe_write_fixture_stage(src: &str, stage: &str, ext: &str) {
    maybe_write_fixture_impl(src, Some(stage), false, ext)
}

fn maybe_write_fixture_impl(src: &str, forced_subdir: Option<&str>, has_errors: bool, ext: &str) {
    if !extract_mode() {
        return;
    }
    let test_name = std::thread::current()
        .name()
        .map(|s| s.to_string())
        .unwrap_or_else(|| "unknown".to_string());

    let (dir_rel, stem) = derive_fixture_path(&test_name, forced_subdir, has_errors);

    let counters = EXTRACT_COUNTERS.get_or_init(|| Mutex::new(HashMap::new()));
    let call_index = {
        let mut lock = counters.lock().unwrap();
        let count = lock.entry(test_name.clone()).or_insert(0);
        let idx = *count;
        *count += 1;
        idx
    };
    let stem_with_suffix = if call_index == 0 {
        stem
    } else {
        format!("{}_call{}", stem, call_index)
    };

    let mut base = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    if let Some(sub) = forced_subdir {
        base = base.join(sub);
    }
    base = base.join(&dir_rel);
    if let Err(e) = std::fs::create_dir_all(&base) {
        eprintln!("EXTRACT: create_dir_all({}) failed: {}", base.display(), e);
        return;
    }
    let dest = base.join(format!("{}.{}", stem_with_suffix, ext));
    if let Err(e) = std::fs::write(&dest, src) {
        eprintln!("EXTRACT: write({}) failed: {}", dest.display(), e);
    }
}

/// Derive `(dir_rel, stem)` from a fully-qualified test path such as
/// `silica_mir::mir::init_state::foo_tests::bar_ok`. Rules:
/// * Drop crate prefix (`silica_mir`).
/// * Drop leading `mir::` — fixtures live directly under `tests/`.
/// * When `forced_subdir` is `"codegen-raw"`, also drop leading
///   `codegen::` (the subdir already carries that context).
/// * Strip `_tests` suffix from module names; drop bare `tests` (inline
///   `mod tests` blocks).
/// * Strip trailing `_ok` (clean) or `_error` (has errors) from the
///   test fn.
fn derive_fixture_path(test_name: &str, forced_subdir: Option<&str>, has_errors: bool) -> (String, String) {
    let mut parts: Vec<&str> = test_name.split("::").collect();
    if parts.first() == Some(&"silica_mir") {
        parts.remove(0);
    }
    if parts.first() == Some(&"mir") {
        parts.remove(0);
    }
    if forced_subdir == Some("codegen-raw") && parts.first() == Some(&"codegen") {
        parts.remove(0);
    }
    let last = parts.pop().unwrap_or("unknown").to_string();
    let suffix = if has_errors { "_error" } else { "_ok" };
    let stem = last.strip_suffix(suffix).unwrap_or(&last).to_string();

    let dir_parts: Vec<String> = parts
        .into_iter()
        .filter(|p| *p != "tests")
        .map(|p| p.strip_suffix("_tests").unwrap_or(p).to_string())
        .collect();
    (dir_parts.join("/"), stem)
}

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
    elaborate_and_check_mir(program, &mut d);
    maybe_write_fixture(src, d.has_errors());
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
/// `Diagnostics` container populated by `elaborate_and_check_mir` directly;
/// use that when a test needs code/span rather than substring matching.
pub fn run(src: &str) -> (Vec<String>, Vec<String>) {
    let program = Parser::new(src.to_string()).parse().unwrap_or_else(|d| {
        panic!(
            "parse error:\n{}\n--- source ---\n{}",
            d.errors_str().join("\n"),
            src
        )
    });
    let mut d = Diagnostics::default().with_source(program.source.clone());
    elaborate_and_check_mir(program, &mut d);
    maybe_write_fixture(src, d.has_errors());
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
