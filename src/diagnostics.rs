//! Shared diagnostic container for analysis passes.

#[derive(Debug, Default)]
pub struct Diagnostics {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl Diagnostics {
    pub fn extend(&mut self, other: Diagnostics) {
        self.errors.extend(other.errors);
        self.warnings.extend(other.warnings);
    }
}
