//! Initialization-state dataflow for local variables.
//!
//! Detects: use of uninitialized locals, use of moved-out locals, use where
//! the init state is inconsistent across control-flow paths, and use of a
//! partially-initialized struct. Also tracks reference (cur, post)
//! obligations and their transitions through `*r` operations and eager
//! borrow-creation moves.
//!
//! The state has two slots (`PointState`):
//! - `locals`: per root Var, a small lattice
//!   `NeverInit | Moved | Init | Partial(map) | Diverged`. `Partial(map)`
//!   records per-field state for struct-typed places; nested Partials are
//!   permitted so `p.q.r = ...` refines the state of `p.q.r` specifically.
//!   Canonicalization collapses a Partial whose fields are all in the
//!   same simple state.
//! - `refs`: per ref-typed owned path, the (is_init, ends_init) obligation
//!   for the pointee. Any owned path (Var, struct field, enum-variant
//!   downcast) can hold a reference; the map is keyed by `Place`.
//!
//! Freeze/thaw is not modeled here — the lifetime pass owns loan tracking
//! and blocks access to any borrowed place independently. This pass
//! eagerly applies the borrow's post-transition on the loaned place at
//! creation (e.g. `y = &out x` marks `x` `Init` immediately), which is
//! safe because lifetime prevents direct access until the loan ends.
//!
//! Paths through `Deref` are not walked in the `locals` tree — we never
//! project into a reference's pointee — but `refs` supplies the pointee
//! init state for `*r` operations via `apply_deref_op`. Downcast-in-move
//! sets the whole enum to `Moved` (enum atomicity, per README); downcast-
//! in-write does not change enum state.

pub mod analysis;
pub mod check;
pub mod drop_elaboration;

#[cfg(test)]
mod analysis_tests;
#[cfg(test)]
mod check_tests;
#[cfg(test)]
mod drop_elaboration_tests;

