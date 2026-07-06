//! Substructural (Copy / Drop / linear / affine) type-system passes.
//!
//! - `composition` — verifies that a struct/enum's declared markers are
//!   compositionally consistent with its field/variant types.
//! - `check` — verifies statements respect substructural preconditions
//!   (`copy p` requires Copy; `drop p` requires Drop) and, post-
//!   elaboration, verifies no value is leaked at `return`.
//! - `elaboration` — inserts explicit `drop` statements so the elaborated
//!   MIR satisfies the leak check.

pub mod check;
pub mod composition;
pub mod elaboration;
