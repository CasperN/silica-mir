//! Shared helpers for the codegen test suite. Codegen tests bypass the
//! checker pipeline — they parse a hand-crafted MIR source and run
//! `generate_llvm` directly — so the crate-level `test_util` (which
//! runs `run_all_passes`) isn't applicable here.

use crate::codegen::generate_llvm;
use crate::parser::Parser;
use crate::type_check::Env;

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
    generate_llvm(&program, &env)
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
        panic!(
            "LLVM IR differs\n--- expected ---\n{}\n--- got ---\n{}",
            b, a
        );
    }
}
