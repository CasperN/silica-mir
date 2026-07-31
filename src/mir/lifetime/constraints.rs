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

#[cfg(test)]
use crate::common::GeneratedKind;
use crate::mir::ast::SourceInfo;
#[cfg(test)]
use crate::mir::ast::Span;
use crate::mir::lifetime::region::Region;
use std::collections::BTreeSet;

/// Why an outlives relation is required. Retained through solving so a
/// diagnostic can explain the source-language operation that introduced the
/// missing bound rather than only printing the two regions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintCause {
    Assignment,
    Call { callee: String },
    TypeRequirement { type_name: String },
}

impl ConstraintCause {
    pub fn description(&self) -> String {
        match self {
            Self::Assignment => "this assignment".to_string(),
            Self::Call { callee } => format!("the call to '{}'", callee),
            Self::TypeRequirement { type_name } => format!("type '{}'", type_name),
        }
    }
}

/// One outlives relation: `outlives` outlives `sub` (i.e. `outlives`
/// is at least as long-lived as `sub`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    pub outlives: Region,
    pub sub: Region,
    pub cause: ConstraintCause,
    /// Source attribution at which the constraint was emitted, for diagnostics.
    pub origin: SourceInfo,
}

impl Constraint {
    pub fn new(outlives: Region, sub: Region, cause: ConstraintCause, origin: SourceInfo) -> Self {
        Self {
            outlives,
            sub,
            cause,
            origin,
        }
    }
}

/// Accumulated outlives constraints for one function. Deduped by
/// `(outlives, sub)` — a repeat of the same pair keeps the earliest cause and
/// source attribution for diagnostics. Consumed by the constraint solver.
#[derive(Debug, Clone, Default)]
pub struct ConstraintSet {
    pub constraints: Vec<Constraint>,
    seen: std::collections::BTreeSet<(Region, Region)>,
}

impl ConstraintSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn emit(
        &mut self,
        outlives: Region,
        sub: Region,
        cause: ConstraintCause,
        origin: SourceInfo,
    ) {
        if outlives == sub || matches!(outlives, Region::Static) {
            return;
        }
        if self.seen.insert((outlives.clone(), sub.clone())) {
            self.constraints
                .push(Constraint::new(outlives, sub, cause, origin));
        }
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

    /// Eliminate existential call-instantiation regions from the constraint
    /// graph, retaining only requirements between regions meaningful in the
    /// caller body.
    ///
    /// A path such as `'q -> ?callee_b -> ?callee_a -> 'p` becomes the caller
    /// requirement `'q -> 'p`. A mutual invariant path `'p -> ?callee_a -> 'p`
    /// becomes reflexive and is pruned by `emit`. Paths beginning at an
    /// `Inference` region have no caller-side lower bound and impose no
    /// requirement: the existential can be chosen to satisfy them.
    ///
    /// Traversal stops on the first non-`Inference` region. In particular, it
    /// never invents transitive requirements through body-local `Free` regions
    /// or source-visible `Named` regions; those have their own semantics in the
    /// failure classifier.
    pub fn project_inference(&self) -> ConstraintSet {
        let mut outgoing: std::collections::BTreeMap<Region, Vec<&Constraint>> =
            std::collections::BTreeMap::new();
        for constraint in &self.constraints {
            outgoing
                .entry(constraint.outlives.clone())
                .or_default()
                .push(constraint);
        }

        let mut projected = ConstraintSet::new();
        for root in &self.constraints {
            if matches!(root.outlives, Region::Inference(_)) {
                continue;
            }
            project_from(
                &root.outlives,
                root,
                &outgoing,
                &mut BTreeSet::new(),
                &mut projected,
            );
        }
        projected
    }
}

fn project_from(
    root: &Region,
    edge: &Constraint,
    outgoing: &std::collections::BTreeMap<Region, Vec<&Constraint>>,
    visiting: &mut BTreeSet<Region>,
    projected: &mut ConstraintSet,
) {
    let Region::Inference(_) = &edge.sub else {
        projected.emit(
            root.clone(),
            edge.sub.clone(),
            edge.cause.clone(),
            edge.origin,
        );
        return;
    };

    if !visiting.insert(edge.sub.clone()) {
        return;
    }
    if let Some(next_edges) = outgoing.get(&edge.sub) {
        for next in next_edges {
            project_from(root, next, outgoing, visiting, projected);
        }
    }
    visiting.remove(&edge.sub);
}

/// Compute the transitive closure of a set of outlives axioms. Given
/// axioms `[(a, b), (b, c)]`, the closure contains `(a, b)`, `(b, c)`,
/// and `(a, c)`. Also adds reflexive pairs `(r, r)` for every region
/// mentioned, and `(Static, r)` for every non-Static region.
pub fn transitive_closure(axioms: &[(Region, Region)]) -> BTreeSet<(Region, Region)> {
    let mut closure: BTreeSet<(Region, Region)> = axioms.iter().cloned().collect();
    let mut regions: BTreeSet<Region> = BTreeSet::new();
    for (a, b) in axioms {
        regions.insert(a.clone());
        regions.insert(b.clone());
    }
    for r in &regions {
        closure.insert((r.clone(), r.clone()));
        if !matches!(r, Region::Static) {
            closure.insert((Region::Static, r.clone()));
        }
    }
    // Naive transitive closure — sufficient for the small constraint
    // sets we see in practice. Iterate until no new pairs added.
    loop {
        let mut added = false;
        let snapshot: Vec<_> = closure.iter().cloned().collect();
        for (a, b) in &snapshot {
            for (b2, c) in &snapshot {
                if b == b2 && closure.insert((a.clone(), c.clone())) {
                    added = true;
                }
            }
        }
        if !added {
            break;
        }
    }
    closure
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Lifetime;

    fn source() -> SourceInfo {
        SourceInfo::generated(GeneratedKind::TestHelper, Span::default())
    }

    #[test]
    fn emit_stores_constraint() {
        let mut cs = ConstraintSet::new();
        cs.emit(
            Region::Named(Lifetime("a".into())),
            Region::Named(Lifetime("b".into())),
            ConstraintCause::Assignment,
            source(),
        );
        assert_eq!(cs.len(), 1);
    }

    #[test]
    fn reflexive_constraint_is_pruned() {
        let mut cs = ConstraintSet::new();
        let a = Region::Named(Lifetime("a".into()));
        cs.emit(a.clone(), a, ConstraintCause::Assignment, source());
        assert!(cs.is_empty());
    }

    #[test]
    fn static_outliving_anything_is_pruned() {
        let mut cs = ConstraintSet::new();
        cs.emit(
            Region::Static,
            Region::Free(0),
            ConstraintCause::Assignment,
            source(),
        );
        assert!(cs.is_empty());
    }

    #[test]
    fn transitive_closure_chains() {
        let a = Region::Named(Lifetime("a".into()));
        let b = Region::Named(Lifetime("b".into()));
        let c = Region::Named(Lifetime("c".into()));
        let axioms = vec![(a.clone(), b.clone()), (b.clone(), c.clone())];
        let closure = transitive_closure(&axioms);
        assert!(closure.contains(&(a.clone(), c.clone())));
        assert!(closure.contains(&(a.clone(), a.clone())));
        assert!(closure.contains(&(Region::Static, a)));
    }

    #[test]
    fn inference_projection_derives_caller_requirement() {
        let p = Region::Named(Lifetime("p".into()));
        let q = Region::Named(Lifetime("q".into()));
        let callee_a = Region::Inference(0);
        let callee_b = Region::Inference(1);
        let mut cs = ConstraintSet::new();
        cs.emit(
            q.clone(),
            callee_b.clone(),
            ConstraintCause::Call {
                callee: "needs_bound".into(),
            },
            source(),
        );
        cs.emit(
            callee_b,
            callee_a.clone(),
            ConstraintCause::Call {
                callee: "needs_bound".into(),
            },
            source(),
        );
        cs.emit(
            p.clone(),
            callee_a.clone(),
            ConstraintCause::Call {
                callee: "needs_bound".into(),
            },
            source(),
        );
        cs.emit(
            callee_a,
            p.clone(),
            ConstraintCause::Call {
                callee: "needs_bound".into(),
            },
            source(),
        );

        let projected = cs.project_inference();
        assert_eq!(projected.len(), 1);
        assert_eq!(projected.constraints[0].outlives, q);
        assert_eq!(projected.constraints[0].sub, p);
    }

    #[test]
    fn inference_projection_preserves_body_local_escape() {
        let local = Region::Free(0);
        let caller = Region::Named(Lifetime("p".into()));
        let inst = Region::Inference(1);
        let mut cs = ConstraintSet::new();
        cs.emit(
            local.clone(),
            inst.clone(),
            ConstraintCause::Call {
                callee: "returns_ref".into(),
            },
            source(),
        );
        cs.emit(
            inst,
            caller.clone(),
            ConstraintCause::Call {
                callee: "returns_ref".into(),
            },
            source(),
        );

        let projected = cs.project_inference();
        assert_eq!(projected.len(), 1);
        assert_eq!(projected.constraints[0].outlives, local);
        assert_eq!(projected.constraints[0].sub, caller);
    }

    #[test]
    fn unconstrained_inference_imposes_no_caller_requirement() {
        let inst = Region::Inference(0);
        let caller = Region::Named(Lifetime("p".into()));
        let mut cs = ConstraintSet::new();
        cs.emit(
            inst,
            caller,
            ConstraintCause::Call {
                callee: "output_only".into(),
            },
            source(),
        );

        assert!(cs.project_inference().is_empty());
    }

    #[test]
    fn ref_to_ref_assignment_emits_outlives() {
        use crate::mir::desugar::lifetime as desugaring;
        use crate::mir::env::IndexedProgram;
        use crate::mir::parser::Parser;
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
        let mut program = Parser::parse_or_panic(src);
        desugaring::desugar_program(&mut program);
        let (env, _errs) = IndexedProgram::build(&program);
        let func = program.find_fn("f").expect("fn f");
        let cs = crate::mir::lifetime::check::constraints_for(&env, func);
        assert_eq!(cs.len(), 1, "expected one outlives constraint");
        let c = &cs.constraints[0];
        assert_eq!(c.outlives, Region::Named(Lifetime("s0".into())));
        assert!(matches!(c.sub, Region::Free(_)));
    }
}
