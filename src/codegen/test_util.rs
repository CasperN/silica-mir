//! Shared helpers for the codegen test suite. Codegen tests bypass the
//! checker pipeline — they parse a hand-crafted MIR source and run
//! `generate_llvm` directly — so the crate-level `test_util` (which
//! runs `run_all_passes`) isn't applicable here.

use crate::codegen::generate_llvm;
use crate::parser::Parser;

/// Parse `src` (assumed well-typed) and return the emitted LLVM IR.
pub fn ll_of(src: &str) -> String {
    let program = Parser::new(src.to_string())
        .parse()
        .unwrap_or_else(|e| panic!("parse error: {}\n--- source ---\n{}", e, src));
    generate_llvm(&program)
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
