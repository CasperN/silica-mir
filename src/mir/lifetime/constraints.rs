//! Region outlives constraints. Emitted during the loan-check walk;
//! solved and enforced in later phases.
//!
//! A constraint `(a, b)` means "region `a` outlives region `b`",
//! i.e. every point where a value of region `b` is live, region
//! `a`'s referent is also live. `Static` outlives every region;
//! reflexivity (`x outlives x`) is trivial.
//!
//! Constraints emit at two points:
//! 1. Assignment `dst = src` where both are refs: the source's
//!    region must outlive the destination's region.
//! 2. Call sites: caller's arg regions unify with (instantiated)
//!    callee param regions; the returned ref's region matches the
//!    instantiated callee return region.

use crate::mir::lifetime::region::Region;
use crate::mir::ast::Span;

/// One outlives relation: `outlives` outlives `sub` (i.e. `outlives`
/// is at least as long-lived as `sub`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub outlives: Region,
    pub sub: Region,
    /// Span at which the constraint was emitted, for diagnostics.
    pub origin: Span,
}

impl Constraint {
    pub fn new(outlives: Region, sub: Region, origin: Span) -> Self {
        Self { outlives, sub, origin }
    }
}

/// Accumulated outlives constraints for one function. Grows during
/// the check walk; consumed by phase 4's solver.
#[derive(Debug, Clone, Default)]
pub struct ConstraintSet {
    pub constraints: Vec<Constraint>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn emit(&mut self, outlives: Region, sub: Region, origin: Span) {
        // Trivial cases pruned to keep the set focused.
        if outlives == sub {
            return;
        }
        if matches!(outlives, Region::Static) {
            return;
        }
        self.constraints.push(Constraint::new(outlives, sub, origin));
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.constraints.iter()
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Lifetime;

    #[test]
    fn emit_stores_constraint() {
        let mut cs = ConstraintSet::new();
        cs.emit(
            Region::Named(Lifetime("a".into())),
            Region::Named(Lifetime("b".into())),
            Span::default(),
        );
        assert_eq!(cs.len(), 1);
    }

    #[test]
    fn reflexive_constraint_is_pruned() {
        let mut cs = ConstraintSet::new();
        let a = Region::Named(Lifetime("a".into()));
        cs.emit(a.clone(), a, Span::default());
        assert!(cs.is_empty());
    }

    #[test]
    fn static_outliving_anything_is_pruned() {
        let mut cs = ConstraintSet::new();
        cs.emit(Region::Static, Region::Free(0), Span::default());
        assert!(cs.is_empty());
    }

    #[test]
    fn ref_to_ref_assignment_emits_outlives() {
        use crate::mir::parser::Parser;
        use crate::mir::type_check::Env;
        use crate::mir::elision;
        // `r = copy x` where both are `&i64`: source region must
        // outlive destination region. After elision x's region is
        // 's0 (from signature). r is a body-local, so its region is
        // Free.
        let src = "
            fn f(x: &i64) {
              r: &i64;
              entry:
                r = copy x;
                return
            }
        ";
        let mut program = Parser::new(src.to_string()).parse().expect("parse");
        elision::elide_program(&mut program);
        let (env, _errs) = Env::build(&program);
        let cs = crate::mir::lifetime::constraints_for(&env, &env.functions["f"]);
        assert_eq!(cs.len(), 1, "expected one outlives constraint");
        let c = &cs.constraints[0];
        assert_eq!(c.outlives, Region::Named(Lifetime("s0".into())));
        assert!(matches!(c.sub, Region::Free(_)));
    }
}
