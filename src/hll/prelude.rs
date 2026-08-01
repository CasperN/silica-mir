//! HLL surface prelude — extern signatures for the compiler-provided
//! wrappers (`size_of<T>`, `ptr_offset<T>`) that expose `$`-prefixed
//! intrinsics under names user code can spell. The wrappers' *bodies*
//! live in the MIR pipeline (see `mir::intrinsics::prelude_decls`).
//! At the HLL layer we only need surface signatures; type-check and
//! lowering both call `prelude_fn_decls()` to register them in their
//! respective envs without adding the signatures to the user program's
//! declaration list (which would produce duplicates at MIR level once
//! the bodies land).

use crate::diagnostics::Diagnostics;
use crate::hll::ast::*;
use crate::hll::parser::Parser;

const PRELUDE_HLL: &str = r#"
extern fn<T> size_of() -> u64;
extern fn<T> ptr_offset(p: *T, i: u64) -> *T;
"#;

/// Return the HLL `FnDecl`s for every compiler-provided prelude
/// wrapper. Called by HLL type-check and lowering to preload their
/// envs — the decls are NOT injected into the user program's
/// declaration list; the MIR side owns the wrapper bodies separately.
/// Panics on parse failure — the constant is compiler-authored, so
/// any failure is an internal bug.
pub fn prelude_fn_decls() -> Vec<FnDecl> {
    let mut d = Diagnostics::default();
    let program = Parser::new(PRELUDE_HLL).parse(&mut d).unwrap_or_else(|| {
        panic!(
            "internal error: compiler-provided PRELUDE_HLL failed to parse: {:?}",
            d.errors().collect::<Vec<_>>()
        )
    });
    program
        .declarations
        .into_iter()
        .filter_map(|d| match d {
            Declaration::Fn(f) => Some(f),
            _ => None,
        })
        .collect()
}
