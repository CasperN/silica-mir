//! Surface → canonical MIR rewrites that run before type checking.
//!
//! Each submodule owns one desugaring:
//!
//! - [`lifetime`] fills in every `None` lifetime slot in decl-position
//!   references and records the elision-derived outlives axioms.
//! - [`self_alias`] replaces `Self` in impl-method signatures and
//!   locals with the impl's target type.
//!
//! Passes are independent and idempotent. Call order is fixed by
//! [`crate::lib`]'s `prepare_mir_for_elaboration`.

pub mod lifetime;
pub mod self_alias;
