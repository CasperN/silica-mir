//! Lifetime (loan) tracking for MIR references.
//!
//! Loans are the "who borrows what" side of the borrow story; owning them
//! independently of init-state lets each subsystem focus on its own
//! invariant. `loans` holds the dataflow machinery, `check` runs it and
//! emits diagnostics, `nll` elaborates `unborrow` insertions before the
//! check runs.
//!
//! `init_state` handles the post-consumption obligation check (that the
//! pointee reached the ref kind's `ends_init`); this module only tracks
//! the loan itself.
//!
//! From this module's view the four exclusive reference kinds (`&mut`,
//! `&out`, `&drop`, `&uninit`) are indistinguishable — they're all
//! "exclusive borrow of p". The kind is retained solely to shape the
//! diagnostic ("borrow as &out", etc.) and to enable shared/shared
//! compatibility.

use crate::diagnostics::DiagCode;

pub mod check;
pub mod constraints;
pub mod desugaring;
pub mod loans;
pub mod nll;
pub mod region;

#[cfg(test)]
mod nll_tests;

pub use region::Region;

/// Machine-readable codes emitted by the lifetime / loan-conflict pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifetimeCode {
    /// A place is accessed while an outstanding exclusive loan (or
    /// otherwise incompatible loan) covers it. Includes reads,
    /// writes, moves, drops, and new borrows.
    LoanConflict,
    /// An outlives constraint between two distinct named lifetimes
    /// is required but cannot be proven. E.g. `dst: &'a T = src: &'b T`
    /// with no `where 'b: 'a` bound in scope.
    LifetimeMismatch,
    /// A borrow rooted in a body-local (no signature-visible name for
    /// its region) is stored into a signature-visible slot whose
    /// region is a named lifetime. The loan would outlive the
    /// storage that backs it — an escape.
    LifetimeEscape,
}

impl From<LifetimeCode> for DiagCode {
    fn from(code: LifetimeCode) -> DiagCode {
        DiagCode::Lifetime(code)
    }
}
