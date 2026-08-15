//! HLL surface declarations for compiler-provided functions and traits.
//! Their MIR definitions live in `mir::intrinsics::prelude_decls`; these
//! declarations are visible during HLL checking but are not lowered into the
//! user program, avoiding duplicates when the MIR prelude is injected.

use crate::diagnostics::Diagnostics;
use crate::hll::ast::*;
use crate::hll::parser::Parser;

const PRELUDE_HLL: &str = r#"
trait AutoClone {
  fn clone(recv: & Self) -> Self;
}

trait AutoDestroy {
  fn destroy(recv: &drop Self);
}

extern fn<T> size_of() -> u64;
extern fn<T> ptr_offset(p: *T, i: u64) -> *T;
"#;

fn prelude_decls() -> Vec<Declaration> {
    let mut d = Diagnostics::default();
    Parser::new(PRELUDE_HLL)
        .parse(&mut d)
        .unwrap_or_else(|| {
            panic!(
                "internal error: compiler-provided PRELUDE_HLL failed to parse: {:?}",
                d.errors().collect::<Vec<_>>()
            )
        })
        .declarations
}

/// Return the HLL `FnDecl`s for every compiler-provided prelude
/// wrapper. Called by HLL type-check and lowering to preload their
/// envs — the decls are NOT injected into the user program's
/// declaration list; the MIR side owns the wrapper bodies separately.
/// Panics on parse failure — the constant is compiler-authored, so
/// any failure is an internal bug.
pub fn prelude_fn_decls() -> Vec<FnDecl> {
    prelude_decls()
        .into_iter()
        .filter_map(|d| match d {
            Declaration::Fn(f) => Some(f),
            _ => None,
        })
        .collect()
}

/// Return the HLL trait declarations whose compiler-provided methods may be
/// named in surface bounds or selected by HLL type checking.
pub fn prelude_trait_decls() -> Vec<TraitDecl> {
    prelude_decls()
        .into_iter()
        .filter_map(|declaration| match declaration {
            Declaration::Trait(trait_decl) => Some(trait_decl),
            _ => None,
        })
        .collect()
}
