//! Shared helpers for the codegen test suite. Codegen tests bypass the
//! checker pipeline — they parse a hand-crafted MIR source and run
//! `lower_mir_to_llvm` directly — so the crate-level `test_util` (which
//! runs `run_all_passes`) isn't applicable here.

use crate::mir::codegen::lower_mir_to_llvm;
use crate::mir::parser::Parser;
use crate::mir::type_check::Env;

/// Parse `src` (assumed well-typed) and return the emitted LLVM IR.
/// Env build errors are discarded — test sources don't have duplicate
/// declarations.
pub fn ll_of(src: &str) -> String {
    let program = Parser::new(src.to_string()).parse().unwrap_or_else(|d| {
        panic!(
            "parse error:\n{}\n--- source ---\n{}",
            d.errors_str().join("\n"),
            src
        )
    });
    let (env, _) = Env::build(&program);
    lower_mir_to_llvm(&program, &env)
}

#[track_caller]
pub fn assert_contains(haystack: &str, needle: &str) {
    assert!(
        haystack.contains(needle),
        "expected {:?} in output:\n{}",
        needle,
        haystack
    );
}

/// Assert that emitting `input` produces the exact LLVM IR `expected`
/// (leading/trailing whitespace on each side trimmed; no tolerance
/// for internal differences). Mirrors the "golden output" pattern
/// used by `assert_elab_eq` in `lifetime/nll_tests.rs`.
#[track_caller]
pub fn assert_ll_eq(input: &str, expected: &str) {
    let got = ll_of(input);
    let a = got.trim();
    let b = expected.trim();
    if a != b {
        panic!("LLVM IR differs\n{}", format_line_diff(b, a));
    }
}

/// Format a line-by-line diff of two strings. Only lines that differ
/// are shown, each labeled with its line number and both sides.
/// Length mismatches are surfaced explicitly.
pub fn format_line_diff(expected: &str, got: &str) -> String {
    let expected_lines: Vec<&str> = expected.lines().collect();
    let got_lines: Vec<&str> = got.lines().collect();
    let mut out = String::new();
    let max_len = expected_lines.len().max(got_lines.len());
    let mut diff_count = 0;
    for i in 0..max_len {
        let e = expected_lines.get(i).copied();
        let g = got_lines.get(i).copied();
        if e == g {
            continue;
        }
        diff_count += 1;
        out.push_str(&format!(
            "  line {}:\n    expected: {}\n    got:      {}\n",
            i + 1,
            e.map(|s| format!("{:?}", s)).unwrap_or_else(|| "<missing>".to_string()),
            g.map(|s| format!("{:?}", s)).unwrap_or_else(|| "<missing>".to_string()),
        ));
    }
    if diff_count == 0 {
        // Should not happen when called from a real diff site.
        return "(no line differences — trailing whitespace or non-line-based difference)\n".to_string();
    }
    format!(
        "{} of {} line(s) differ (expected {}, got {}):\n\n{}",
        diff_count,
        max_len,
        expected_lines.len(),
        got_lines.len(),
        out,
    )
}

#[cfg(test)]
mod diff_tests {
    use super::format_line_diff;

    #[test]
    fn format_line_diff_shows_per_line_pairs() {
        let expected = "one\ntwo\nthree";
        let got = "one\nTWO\nthree";
        let diff = format_line_diff(expected, got);
        assert!(
            diff.contains("1 of 3 line(s) differ (expected 3, got 3):"),
            "missing header, got:\n{}",
            diff
        );
        assert!(
            diff.contains("  line 2:\n    expected: \"two\"\n    got:      \"TWO\"\n"),
            "missing line 2 pair, got:\n{}",
            diff
        );
    }

    #[test]
    fn format_line_diff_handles_length_mismatch() {
        let expected = "one\ntwo";
        let got = "one\ntwo\nthree";
        let diff = format_line_diff(expected, got);
        assert!(
            diff.contains("1 of 3 line(s) differ (expected 2, got 3):"),
            "missing header, got:\n{}",
            diff
        );
        assert!(
            diff.contains("  line 3:\n    expected: <missing>\n    got:      \"three\"\n"),
            "missing line 3 pair, got:\n{}",
            diff
        );
    }
}
