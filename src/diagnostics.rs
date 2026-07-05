//! Shared diagnostic container for analysis passes. Every pass takes a
//! `&mut Diagnostics` and pushes into `errors` / `warnings` directly.

#[derive(Debug, Default)]
pub struct Diagnostics {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}
