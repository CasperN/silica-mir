//! Lifetime (loan) tracking for MIR references.
//!
//! Owns the "who borrows what" side of the borrow story: an active
//! borrow of a place `p` by a borrower variable `r` registers a `Loan`.
//! While the loan is live, direct access to `p` (or a prefix/extension
//! sharing storage with `p`) is blocked unless it is compatible with
//! the loan's kind (only shared/shared is compatible).
//!
//! Loans expire when the borrower is consumed — moved to a callee,
//! dropped, or explicitly `unborrow`ed. `init_state` handles the
//! post-consumption obligation check (that the pointee reached the
//! ref kind's `ends_init`); this module only tracks the loan itself.
//!
//! `Loan` participates in a set-valued lattice: joining two branches
//! that both bind the same borrower variable to different loaned places
//! (a *branch-of-borrows*) unions their `loaned` sets so any of them
//! may be the actual pointee. `check_loan_conflict` then reports a
//! conflict on any place that appears in *any* live loan's loaned set.
//!
//! The four exclusive reference kinds (`&mut`, `&out`, `&drop`,
//! `&uninit`) differ only in their pointee init obligations, not in
//! their exclusivity: from the lifetime module's view they are all
//! "exclusive borrow of p". The kind is retained solely to shape the
//! diagnostic ("borrow as &out", etc.) and to enable shared/shared
//! compatibility.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction, Results};
use crate::mir::helpers::*;
use crate::mir::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::BTreeSet;

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

pub mod constraints;
mod nll;
pub mod region;

pub use region::Region;

/// Elaborate non-lexical lifetimes by inserting explicit `unborrow`
/// statements at borrower last-use points.
pub fn elaborate(program: &mut Program, env: &Env) {
    nll::elaborate(program, env);
}

/// A record of a borrow that's currently in force. `loaned` is a set to
/// support multi-loan: when a branch-of-borrows produces different loaned
/// places on each side, the join unions them so all possible pointees
/// stay tracked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loan {
    pub kind: RefKind,
    /// The region this loan lives in. Set when the loan is registered
    /// (at `x = &p`) from the borrower's region assignment. Body-local
    /// borrowers get `Region::Free`; signature borrowers get
    /// `Region::Named`.
    pub region: Region,
    pub loaned: BTreeSet<Place>,
    pub create_span: Span,
}

impl Loan {
    pub fn single(kind: RefKind, region: Region, loaned: Place, create_span: Span) -> Self {
        let mut set = BTreeSet::new();
        set.insert(loaned);
        Loan {
            kind,
            region,
            loaned: set,
            create_span,
        }
    }
}

/// Map from borrower *place* to its active loan. The key is an owned
/// path in the local frame — a `Place` with no `Deref` steps — since
/// a ref only rests in a place we can name (`x`, `b.p`, `e as V`).
/// Values in ref-typed struct fields are first-class borrowers so
/// `b.p = &mut x` produces an entry keyed on `b.p`, not `b`.
pub type LoanMap = IndexMap<Place, Loan>;

/// How a place is being accessed. Used to classify conflicts against
/// active loans.
#[derive(Debug, Clone)]
pub enum AccessKind {
    /// Read (copy, or discriminant read in switchEnum).
    Read,
    /// Write to the place (RHS of assign target).
    Write,
    /// Move / consumption (destructive read).
    Move,
    /// A new borrow of this kind is being created here.
    Borrow(RefKind),
}

impl std::fmt::Display for AccessKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccessKind::Read => write!(f, "read"),
            AccessKind::Write => write!(f, "write to"),
            AccessKind::Move => write!(f, "move from"),
            AccessKind::Borrow(k) => write!(f, "borrow as {}", k),
        }
    }
}

/// True if the two paths share a prefix — i.e. one is a prefix of the
/// other, meaning they refer to overlapping storage. `Deref` steps compare
/// like any other: two `Deref` steps at the same position match, so a loan
/// on `*r` (path=[Deref]) prefix-matches `*r`, `(*r).f`, etc., and the
/// empty path (raw `r`) is a prefix of `[Deref]` too.
fn paths_conflict(a: &[PathStep], b: &[PathStep]) -> bool {
    let n = a.len().min(b.len());
    for i in 0..n {
        let same = match (&a[i], &b[i]) {
            (PathStep::Field(x), PathStep::Field(y)) => x == y,
            (PathStep::Downcast(x), PathStep::Downcast(y)) => x == y,
            (PathStep::Deref, PathStep::Deref) => true,
            // Index steps: two const indices conflict iff equal;
            // any dynamic index widens to "conflicts with any slot."
            (PathStep::Index(x), PathStep::Index(y)) => match (x, y) {
                (Some(k1), Some(k2)) => k1 == k2,
                _ => true,
            },
            _ => false,
        };
        if !same {
            return false;
        }
    }
    true
}

/// Compatible = both shared read/borrow. Anything else against a live
/// loan is a conflict.
fn is_compatible(loan_kind: &RefKind, access: &AccessKind) -> bool {
    matches!(loan_kind, RefKind::Shared)
        && matches!(
            access,
            AccessKind::Read | AccessKind::Borrow(RefKind::Shared)
        )
}

/// True if `stmt` is a `drop <place>` that drop-elaboration inserted
/// immediately before an assign to the same owned path. Drop-elab
/// preserves the assign's span on the inserted drop, so both share
/// `drop_span`; the checker uses this to suppress a duplicate
/// LoanConflict — the assign carries the authoritative diagnostic.
fn is_elab_inserted_drop(place: &Place, drop_span: Span, next: Option<&Statement>) -> bool {
    let Some(next_stmt) = next else {
        return false;
    };
    if next_stmt.span != drop_span {
        return false;
    }
    let StatementKind::Assign(target, _) = &next_stmt.kind else {
        return false;
    };
    as_owned_path(target).as_ref() == Some(place)
}

/// Join two `LoanMap`s. Same-borrower entries merge by unioning their
/// loaned sets (branch-of-borrows produces a multi-loan). Different
/// kinds at the same borrower name can't happen — type_check enforces
/// uniform ref types — so we drop as a conservative fallback if it
/// somehow occurs.
pub fn join_loans(a: &LoanMap, b: &LoanMap) -> LoanMap {
    let mut out = LoanMap::new();
    for (place, la) in a {
        if let Some(lb) = b.get(place) {
            if la.kind == lb.kind {
                let mut merged = la.clone();
                merged.loaned.extend(lb.loaned.iter().cloned());
                out.insert(place.clone(), merged);
            }
        }
    }
    out
}

// ---------- Dataflow ----------

/// If `op` is a `move` of an owned path, remove any loan whose borrower
/// place *is* that path or lies underneath it. An ancestor move
/// (`move b`) cascades to close every ref-typed field's loan
/// (`b.p`, `b.q`, ...).
pub fn consume_operand(loans: &mut LoanMap, op: &Operand) {
    if let Operand::Move(place) = op {
        if let Some(consumed) = as_owned_path(place) {
            close_loans_under(loans, &consumed);
        }
    }
}

fn close_loans_under(loans: &mut LoanMap, consumed: &Place) {
    let victims: Vec<Place> = loans
        .keys()
        .filter(|k| is_ancestor_or_self(consumed, k))
        .cloned()
        .collect();
    for v in victims {
        loans.shift_remove(&v);
    }
}

fn consume_rvalue(loans: &mut LoanMap, rv: &RValue) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
            consume_operand(loans, op)
        }
        RValue::Ref(_, _) | RValue::RawRef(_) => {}
        RValue::ArrayLit(ops) => {
            for op in ops {
                consume_operand(loans, op);
            }
        }
    }
}

/// For an assign `target = <rvalue>` where the rvalue transfers a
/// borrower via move, gather every loan whose borrower is rooted at
/// the moved source path (src itself or any owned-path descendant) and
/// re-key each under `target`. Mirrors `init_state::capture_carried_refs`.
///
/// - `Use(Move(src))` → re-key under `target` directly.
/// - `EnumConstr(_, V, Move(src))` → re-key under `target as V`.
///
/// Returns `Vec<(new_key, loan)>` to be re-inserted after the source's
/// loans are removed by `consume_rvalue`.
fn capture_carried_loans(target: &Place, rvalue: &RValue, loans: &LoanMap) -> Vec<(Place, Loan)> {
    let Some(dst) = as_owned_path(target) else {
        return Vec::new();
    };
    let (src, dst_effective) = match rvalue {
        RValue::Use(Operand::Move(src_place)) => {
            let Some(src) = as_owned_path(src_place) else {
                return Vec::new();
            };
            (src, dst)
        }
        RValue::EnumConstr(_, _, variant, Operand::Move(src_place)) => {
            let Some(src) = as_owned_path(src_place) else {
                return Vec::new();
            };
            (src, downcast_place(dst, variant.clone()))
        }
        RValue::PtrCast(Operand::Move(src_place), _) => {
            let Some(src) = as_owned_path(src_place) else {
                return Vec::new();
            };
            (src, dst)
        }
        _ => return Vec::new(),
    };
    loans
        .iter()
        .filter_map(|(k, loan)| {
            let new_key = rekey_owned_path(&src, &dst_effective, k)?;
            Some((new_key, loan.clone()))
        })
        .collect()
}

/// Forward dataflow analysis over `LoanMap`. Runs independently of the
/// init-state analysis — the two share nothing beyond the statement they
/// both observe.
struct LoanAnalysis<'a> {
    region_ctx: &'a region::RegionCtx,
}

impl<'a> Analysis for LoanAnalysis<'a> {
    type State = LoanMap;
    fn direction(&self) -> Direction {
        Direction::Forward
    }
    fn initial_state(&self) -> Self::State {
        LoanMap::new()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join_loans(a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, span: Span) {
        transfer_stmt(state, stmt, span, self.region_ctx);
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        if let TerminatorKind::Branch { cond, .. } = &term.kind {
            consume_operand(state, cond);
        }
    }
}

/// Apply the whole-statement loan transition. Silent (no diagnostics);
/// the diagnostic walk in `init_state` uses the smaller `consume_operand`
/// helper alongside inline inserts/removes.
fn transfer_stmt(
    loans: &mut LoanMap,
    stmt: &Statement,
    span: Span,
    region_ctx: &region::RegionCtx,
) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // Capture BEFORE consume: the loans rooted at the moved
            // source (whole-var or struct-descendant) will be removed
            // by consume_rvalue, so grab them first for re-key.
            let carried = capture_carried_loans(target, rvalue, loans);

            consume_rvalue(loans, rvalue);
            if let Some(t) = as_owned_path(target) {
                // Overwriting the target closes its previous loan.
                loans.shift_remove(&t);
            }
            if let (Some(t), RValue::Ref(kind, place)) = (as_owned_path(target), rvalue) {
                let region = region_ctx.get(&t).cloned().unwrap_or(Region::Static);
                loans.insert(t, Loan::single(kind.clone(), region, place.clone(), span));
            }
            for (new_key, loan) in carried {
                loans.insert(new_key, loan);
            }
        }
        StatementKind::Call(target, args) => {
            consume_operand(loans, target);
            for a in args {
                consume_operand(loans, a);
            }
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            // Consume of a borrower place ends its loan (and any
            // ref-field loans it holds). `drop *r` consumes the pointee,
            // not the borrower; the borrower path passes through Deref
            // and won't match as_owned_path.
            if let Some(consumed) = as_owned_path(place) {
                close_loans_under(loans, &consumed);
            }
        }
        StatementKind::RequireUninit(_) => {
            // Ghost assertion; it has no loan-state effect.
        }
    }
}

/// Run the LoanAnalysis fixpoint over `body` using the per-fn region
/// context.
pub fn run(body: &FunctionBody, region_ctx: &region::RegionCtx) -> Results<LoanMap> {
    dataflow::run(&LoanAnalysis { region_ctx }, body)
}

// ---------- Check pass ----------

/// Verify per-statement access against the active loan set. Emits
/// "already borrowed by" diagnostics on conflicts. Runs the LoanAnalysis
/// fixpoint, then walks each block re-applying the transfer in lockstep
/// with per-access checks.
///
/// Independent of `init_state`: this pass sees a program purely as
/// borrows and accesses, without regard to the ref kind's init obligation.
pub fn check_program(program: &Program, env: &Env, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }
    let region_ctx = region::build_region_ctx(func, env);
    let entry_states = run(body, &region_ctx);
    let mut constraints = constraints::ConstraintSet::new();
    let locals = func.locals_map();
    let mut checker = Checker {
        env,
        func,
        locals,
        region_ctx: &region_ctx,
        constraints: &mut constraints,
        d,
    };
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut loans = entry.clone();
        for (i, stmt) in block.statements.iter().enumerate() {
            let next = block.statements.get(i + 1);
            checker.check_and_transfer_stmt(block, stmt, next, &mut loans);
            checker.emit_stmt_constraints(stmt);
        }
        checker.check_and_transfer_terminator(block, &mut loans);
    }
    let escape_visible = signature_visible_regions(func, env);
    checker.check_constraints(&escape_visible);
}

/// Return the set of Named regions that are reachable from a
/// caller-visible slot: through `$return`, or through any
/// caller-provided `&mut` / `&out` parameter (i.e. any pointer the
/// callee can write into, whose target the caller reads back).
///
/// A Named region that only appears in body-local types (e.g. a
/// struct field of a locally-owned struct decl instantiated at
/// use-site with no lifetime args) is NOT escape-visible.
fn signature_visible_regions(func: &Function, env: &Env) -> BTreeSet<Lifetime> {
    let mut out = BTreeSet::new();
    for p in &func.params {
        // $return is the sret slot; any &out or &mut is caller-provided
        // storage the callee writes into.
        let visible = p.name == "$return"
            || matches!(
                &p.ty.kind,
                TypeKind::Ref(RefKind::Out, _, _) | TypeKind::Ref(RefKind::Mut, _, _)
            );
        if !visible {
            continue;
        }
        // Peel off the outer ref (that ref's own lifetime is the
        // caller's storage lifetime; irrelevant to escape) and collect
        // named regions in the pointee.
        let pointee = match &p.ty.kind {
            TypeKind::Ref(_, _, inner) => inner.as_ref().clone(),
            _ => p.ty.clone(),
        };
        let mut visited = BTreeSet::new();
        collect_named_regions(&pointee, env, &mut visited, &mut out);
    }
    out
}

fn collect_named_regions(
    ty: &Type,
    env: &Env,
    visited: &mut BTreeSet<String>,
    out: &mut BTreeSet<Lifetime>,
) {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), inner) => {
            out.insert(lt.clone());
            collect_named_regions(inner, env, visited, out);
        }
        TypeKind::Ref(_, None, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            collect_named_regions(inner, env, visited, out);
        }
        TypeKind::Custom(name, lifetime_args, type_args) => {
            for lt in lifetime_args {
                out.insert(lt.clone());
            }
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    for f in &s.fields {
                        let sub = s.meta.substitute(&f.ty, lifetime_args, type_args);
                        collect_named_regions(&sub, env, visited, out);
                    }
                }
                Some(TypeDecl::Enum(e)) => {
                    for v in &e.variants {
                        let sub = e.meta.substitute(&v.ty, lifetime_args, type_args);
                        collect_named_regions(&sub, env, visited, out);
                    }
                }
                _ => {}
            }
            visited.remove(name);
        }
        TypeKind::Fn(args) => {
            for a in args {
                collect_named_regions(a, env, visited, out);
            }
        }
        _ => {}
    }
}

/// Test-only: compute the outlives constraints emitted for `func`
/// without running any check. Exercises the accumulation path.
#[cfg(test)]
pub fn constraints_for(env: &Env, func: &Function) -> constraints::ConstraintSet {
    let mut cs = constraints::ConstraintSet::new();
    let Some(body) = &func.body else { return cs };
    if body.blocks.is_empty() {
        return cs;
    }
    let region_ctx = region::build_region_ctx(func, env);
    let locals = func.locals_map();
    let mut dummy_d = Diagnostics::default();
    let mut checker = Checker {
        env,
        func,
        locals,
        region_ctx: &region_ctx,
        constraints: &mut cs,
        d: &mut dummy_d,
    };
    for block in &body.blocks {
        for stmt in &block.statements {
            checker.emit_stmt_constraints(stmt);
        }
    }
    cs
}

/// Variance of a position, used to determine which direction an
/// outlives constraint is emitted at a lifetime slot.
#[derive(Copy, Clone, PartialEq)]
enum Variance {
    /// Arg position: `caller_region outlives inst_region`.
    Contravariant,
    /// Return position: `inst_region outlives caller_region`. Reached
    /// only by walking through a contravariant position — currently
    /// only fn-pointer arg positions produce that flip, and `Type::Fn`
    /// isn't walked yet (see the "Call-site handling ignores fn
    /// pointers" punchlist item). `combine`'s `(Contra, Co) →
    /// Invariant` rule and `emit_variance`'s `Covariant` branch are
    /// pre-wired for that walk.
    #[allow(dead_code)]
    Covariant,
    /// Descended through an exclusive kind: emit both directions.
    Invariant,
}

impl Variance {
    fn combine(self, other: Variance) -> Variance {
        match (self, other) {
            (Variance::Invariant, _) | (_, Variance::Invariant) => Variance::Invariant,
            (Variance::Contravariant, Variance::Covariant)
            | (Variance::Covariant, Variance::Contravariant) => Variance::Invariant,
            (a, _) => a,
        }
    }
}

fn emit_variance(
    caller: &Region,
    inst: &Region,
    v: Variance,
    constraints: &mut constraints::ConstraintSet,
    span: Span,
) {
    match v {
        Variance::Contravariant => {
            constraints.emit(caller.clone(), inst.clone(), span);
        }
        Variance::Covariant => {
            constraints.emit(inst.clone(), caller.clone(), span);
        }
        Variance::Invariant => {
            constraints.emit(caller.clone(), inst.clone(), span);
            constraints.emit(inst.clone(), caller.clone(), span);
        }
    }
}

/// Return the first named-region-like lifetime found in `ty`,
/// substituted through `inst`. Used to identify the "returned ref's
/// region" for synthetic loan placement.
fn first_named_region(ty: &Type, inst: &IndexMap<Lifetime, Region>) -> Option<Region> {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), _) => {
            Some(inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone())))
        }
        TypeKind::Custom(_, lts, _) => {
            let lt = lts.first()?;
            Some(inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone())))
        }
        TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => first_named_region(elem, inst),
        _ => None,
    }
}

/// Get the outer ref-kind of `place` when its type is `TypeKind::Ref`.
fn ref_kind_of_place(place: &Place, locals: &IndexMap<String, Type>, env: &Env) -> Option<RefKind> {
    match crate::mir::type_util::place_type(locals, env, place)?.kind {
        TypeKind::Ref(kind, _, _) => Some(kind),
        _ => None,
    }
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Const(_) => None,
    }
}

struct Checker<'a> {
    env: &'a Env,
    func: &'a Function,
    locals: IndexMap<String, Type>,
    region_ctx: &'a region::RegionCtx,
    constraints: &'a mut constraints::ConstraintSet,
    d: &'a mut Diagnostics,
}

impl<'a> Checker<'a> {
    fn error(&self, code: LifetimeCode, span: Span, msg: String) -> Diagnostic {
        Diagnostic::new(code, span, msg).in_function(&self.func.meta.name)
    }

    /// Enforce accumulated outlives constraints. Without `where`-clause
    /// bounds in scope, the only satisfiable inter-named-region relation
    /// is equality (or `Static outlives anything`, already pruned at
    /// emit). Any constraint pairing two distinct Named regions fires
    /// `LT-LifetimeMismatch`. Free ↔ Named or Free ↔ Free are treated as
    /// unifiable at this phase (escape checking handles the interesting
    /// Free ↔ signature-visible case in phase 5).
    fn check_constraints(&mut self, escape_visible: &BTreeSet<Lifetime>) {
        let axioms: Vec<(Region, Region)> = self
            .func
            .meta
            .outlives
            .iter()
            .map(|(a, b)| (Region::Named(a.clone()), Region::Named(b.clone())))
            .collect();
        let closure = constraints::transitive_closure(&axioms);
        for c in self.constraints.iter() {
            match (&c.outlives, &c.sub) {
                (Region::Named(_), Region::Named(_)) if c.outlives != c.sub => {
                    if closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                        continue;
                    }
                    let msg = format!(
                        "lifetime mismatch: expected value with region {}, found value with region {}",
                        c.sub, c.outlives,
                    );
                    self.d
                        .push_error(self.error(LifetimeCode::LifetimeMismatch, c.origin, msg));
                }
                // Escape: a Free-region loan (body-local storage) flowing
                // into a Named region that's actually reachable through a
                // caller-visible output ($return or &out/&mut param).
                (Region::Free(_), Region::Named(dst)) if escape_visible.contains(dst) => {
                    let msg = format!(
                        "borrow escapes function: value with local (unnamed) region cannot be stored into region {}",
                        dst,
                    );
                    self.d
                        .push_error(self.error(LifetimeCode::LifetimeEscape, c.origin, msg));
                }
                // Named outlives Free: source is a real (signature)
                // region, dst is a body-local. Always satisfiable — a
                // named region outlives any local temp.
                (Region::Named(_), Region::Free(_)) => {}
                _ => {}
            }
        }
    }

    /// Emit outlives constraints for one statement. Currently covers
    /// assignment `dst = src` where both sides are ref-typed: the
    /// source's region must outlive the destination's.
    fn emit_stmt_constraints(&mut self, stmt: &Statement) {
        let StatementKind::Assign(target, rvalue) = &stmt.kind else {
            return;
        };
        let (src_region, target_place) = match rvalue {
            RValue::Use(op) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, target.clone())
            }
            RValue::Ref(_, place) => {
                let r = if let Some(owned) = as_owned_path(place) {
                    self.region_ctx
                        .get(&owned)
                        .cloned()
                        .unwrap_or(Region::Free(u32::MAX))
                } else {
                    let mut cur = place;
                    while let Place::Field(inner, _)
                    | Place::Downcast(inner, _)
                    | Place::Index(inner, _) = cur
                    {
                        cur = inner;
                    }
                    if let Place::Deref(inner) = cur {
                        self.region_ctx
                            .region_of_place(inner, &self.locals, self.env)
                            .unwrap_or(Region::Free(u32::MAX))
                    } else {
                        Region::Free(u32::MAX)
                    }
                };
                (r, target.clone())
            }
            RValue::EnumConstr(_, _, variant, op) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, downcast_place(target.clone(), variant.clone()))
            }
            RValue::PtrCast(op, _) => {
                let Some(src) = operand_place(op) else { return };
                let Some(r) = self.region_ctx.region_of_place(src, &self.locals, self.env) else {
                    return;
                };
                (r, target.clone())
            }
            _ => return,
        };
        let Some(t_r) = self
            .region_ctx
            .region_of_place(&target_place, &self.locals, self.env)
        else {
            return;
        };
        // Emit variance-aware constraint. Shared refs are covariant
        // (source outlives dst is enough). Exclusive-write kinds are
        // invariant (source outlives dst AND dst outlives source).
        let target_kind = ref_kind_of_place(&target_place, &self.locals, self.env);
        self.constraints
            .emit(src_region.clone(), t_r.clone(), stmt.span);
        if !matches!(target_kind, Some(RefKind::Shared)) {
            self.constraints.emit(t_r, src_region, stmt.span);
        }
    }

    /// Check whether accessing `place` in the given way conflicts with any
    /// active loan. Uses `extract_path_with_deref` so accesses through `*r`
    /// or ancestors of `*r` (like `r` itself) can conflict with a reborrow
    /// loan on `Deref(Var(r))`.
    ///
    /// A conflict is reported when: the access root matches a loan's root
    /// (i.e. touches the same base variable) AND the access path shares a
    /// prefix with the loaned path AND the loan kind is not compatible with
    /// the access kind.
    fn check_loan_conflict(
        &mut self,
        block: &BasicBlock,
        place: &Place,
        access: AccessKind,
        span: Span,
        loans: &LoanMap,
    ) {
        let (access_root, access_path) = extract_path_with_deref(place);

        for (borrower_place, loan) in loans {
            // Ignore the borrower itself. Consumption of the borrower's own
            // storage (`move r`, `move b.p`) doesn't conflict with the loan
            // it holds — that's handled by close_ref_if_present. But an
            // *ancestor* consumption (`move b` when `b.p` holds a loan)
            // still needs to fire on `b.p`'s loan, so this skip only fires
            // when the access is exactly the borrower place.
            let (borrower_root, borrower_path) = extract_path_with_deref(borrower_place);
            if borrower_root == access_root && borrower_path == access_path {
                continue;
            }
            if is_compatible(&loan.kind, &access) {
                continue;
            }
            // Multi-loan: any place in the set may be the actual pointee.
            // Report at most one error per loan (first matching place).
            for loaned in &loan.loaned {
                let (loan_root, loan_path) = extract_path_with_deref(loaned);
                if loan_root != access_root {
                    continue;
                }
                if !paths_conflict(&access_path, &loan_path) {
                    continue;
                }
                let borrower_name = format_place(borrower_place);
                let hint = format!(
                    "the borrow of '{}' is active until its last use or explicit unborrow.",
                    borrower_name,
                );
                let msg = format!(
                    "cannot {} '{}': already borrowed by '{}'",
                    access,
                    format_place(place),
                    borrower_name,
                );
                let mut diag = self
                    .error(LifetimeCode::LoanConflict, span, msg)
                    .in_block(&block.label)
                    .with_hint(hint);
                // Attach the borrow's origin as a secondary span if we
                // captured one (within-block loans have real spans;
                // cross-block dataflow-propagated loans have Span::default,
                // which renders as no snippet).
                if loan.create_span.line != 0 || loan.create_span.col != 0 {
                    diag = diag.with_secondary(
                        loan.create_span,
                        format!("borrow of '{}' occurs here", format_place(place)),
                    );
                }
                self.d.push_error(diag);
                break;
            }
        }
    }

    fn check_operand_access(
        &mut self,
        block: &BasicBlock,
        op: &Operand,
        span: Span,
        loans: &LoanMap,
    ) {
        let (place, access) = match op {
            Operand::Copy(p) => (p, AccessKind::Read),
            Operand::Move(p) => (p, AccessKind::Move),
            Operand::Const(_) => return,
        };
        self.check_loan_conflict(block, place, access, span, loans);
    }

    /// Emit outlives constraints for a `call callee(args)` statement,
    /// and register synthetic loans on caller-side output slots so the
    /// loan tracker can detect aliasing of caller-side inputs through
    /// callee-returned refs.
    ///
    /// From the lifetime pass's view, all four exclusive-borrow kinds
    /// (`&mut`, `&out`, `&drop`, `&uninit`) behave the same: they're
    /// exclusive borrows whose pointee lifetimes are invariant. Init-
    /// state discipline distinguishes them; lifetime doesn't.
    ///
    /// Algorithm:
    /// 1. Look up callee's Function in env. Bail on fn-pointer /
    ///    non-fn-name callees.
    /// 2. Allocate fresh Free regions from `region_ctx.fresh()` for
    ///    each callee lifetime param.
    /// 3. Walk each (caller arg, callee param) in parallel. At each
    ///    lifetime slot emit constraints:
    ///    - Argument-position (contravariant): `caller outlives inst`.
    ///    - Return-position (covariant, i.e. inside an exclusive
    ///      pointee): `inst outlives caller`.
    ///    - Exclusive descent: emit BOTH directions (invariance).
    ///    Snapshot input arg loans by instantiated region for step 5.
    /// 4. Instantiate the callee's signature_outlives axioms.
    /// 5. Register synthetic loans on caller-side output slots: for
    ///    each arg that's `&mut T`/`&out T`/... containing an inner
    ///    ref of instantiated region R, look at the arg's own loan's
    ///    loaned places (caller-side backing storage) and place a
    ///    synthetic loan there whose `loaned` = union of input loans
    ///    sharing region R.
    fn check_call_regions(
        &mut self,
        target: &Operand,
        args: &[Operand],
        span: Span,
        loans: &mut LoanMap,
    ) {
        let Operand::Const(ConstVal::FnName(callee_name, _)) = target else {
            return;
        };
        let Some(callee) = self.env.functions.get(callee_name) else {
            return;
        };
        if callee.params.len() != args.len() {
            return;
        }

        // Fresh instantiation region per callee lifetime param.
        let inst: IndexMap<Lifetime, Region> = callee
            .meta
            .lifetime_params
            .iter()
            .map(|lt| (lt.clone(), self.region_ctx.fresh()))
            .collect();

        let mut per_output_inputs: IndexMap<Region, BTreeSet<Place>> = IndexMap::new();

        for (arg, param) in args.iter().zip(callee.params.iter()) {
            let Some(arg_place) = operand_place(arg) else {
                continue;
            };
            self.walk_call_regions(
                &param.ty,
                arg_place,
                &inst,
                Variance::Contravariant,
                loans,
                &mut per_output_inputs,
                span,
            );
        }

        for (a, b) in &callee.meta.outlives {
            let a_r = inst.get(a).cloned().unwrap_or(Region::Named(a.clone()));
            let b_r = inst.get(b).cloned().unwrap_or(Region::Named(b.clone()));
            self.constraints.emit(a_r, b_r, span);
        }

        for (arg, param) in args.iter().zip(callee.params.iter()) {
            let Some(arg_place) = operand_place(arg) else {
                continue;
            };
            let Some(arg_owned) = as_owned_path(arg_place) else {
                continue;
            };
            let TypeKind::Ref(kind, _, inner_ty) = &param.ty.kind else {
                continue;
            };
            if matches!(kind, RefKind::Shared) {
                continue;
            }
            // The value the callee writes has a region: the outermost
            // named region in the inner type.
            let Some(out_region) = first_named_region(inner_ty, &inst) else {
                continue;
            };
            let Some(input_places) = per_output_inputs.get(&out_region) else {
                continue;
            };
            if input_places.is_empty() {
                continue;
            }

            let mut merged: BTreeSet<Place> = BTreeSet::new();
            for src in input_places {
                if let Some(loan) = loans.get(src) {
                    merged.extend(loan.loaned.iter().cloned());
                }
            }
            if merged.is_empty() {
                continue;
            }

            // Synthetic loan's kind mirrors the callee's returned ref.
            let synth_kind = match &inner_ty.kind {
                TypeKind::Ref(k, _, _) => k.clone(),
                _ => kind.clone(),
            };
            let arg_loan = loans.get(&arg_owned).cloned();
            if let Some(arg_loan) = arg_loan {
                for slot in arg_loan.loaned {
                    loans.insert(
                        slot,
                        Loan {
                            kind: synth_kind.clone(),
                            region: out_region.clone(),
                            loaned: merged.clone(),
                            create_span: span,
                        },
                    );
                }
            }
        }
    }

    /// Walk callee param type and caller arg place in parallel, emitting
    /// outlives constraints at each lifetime slot and recording input-
    /// side loans for synthetic-loan registration on outputs.
    fn walk_call_regions(
        &mut self,
        callee_ty: &Type,
        caller_place: &Place,
        inst: &IndexMap<Lifetime, Region>,
        variance: Variance,
        loans: &LoanMap,
        per_output_inputs: &mut IndexMap<Region, BTreeSet<Place>>,
        span: Span,
    ) {
        match &callee_ty.kind {
            TypeKind::Ref(kind, Some(lt), inner) => {
                let inst_region = inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone()));
                if let Some(caller_r) =
                    self.region_ctx
                        .region_of_place(caller_place, &self.locals, self.env)
                {
                    emit_variance(&caller_r, &inst_region, variance, self.constraints, span);
                    if matches!(variance, Variance::Contravariant | Variance::Invariant) {
                        if let Some(owned) = as_owned_path(caller_place) {
                            if loans.contains_key(&owned) {
                                per_output_inputs
                                    .entry(inst_region.clone())
                                    .or_default()
                                    .insert(owned);
                            }
                        }
                    }
                }
                // Exclusive kinds make the pointee's lifetimes invariant.
                // Shared preserves the current variance.
                let inner_variance = match kind {
                    RefKind::Shared => variance,
                    _ => Variance::Invariant,
                };
                let inner_caller = crate::mir::helpers::deref_place(caller_place.clone());
                self.walk_call_regions(
                    inner,
                    &inner_caller,
                    inst,
                    inner_variance,
                    loans,
                    per_output_inputs,
                    span,
                );
            }
            TypeKind::Custom(_, lts, args) => {
                // A generic type's lifetime args behave like a container
                // reference: default to invariance (conservative, safe).
                for lt in lts {
                    let inst_region = inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone()));
                    let caller_ty =
                        crate::mir::type_util::place_type(&self.locals, self.env, caller_place);
                    if let Some(caller_ty) = caller_ty {
                        if let TypeKind::Custom(_, caller_lts, _) = &caller_ty.kind {
                            if let Some(caller_lt) = caller_lts.first() {
                                let caller_r = Region::Named(caller_lt.clone());
                                emit_variance(
                                    &caller_r,
                                    &inst_region,
                                    variance.combine(Variance::Invariant),
                                    self.constraints,
                                    span,
                                );
                            }
                        }
                    }
                }
                // Recurse into type args (invariant for now).
                for a in args {
                    self.walk_call_regions(
                        a,
                        caller_place,
                        inst,
                        variance.combine(Variance::Invariant),
                        loans,
                        per_output_inputs,
                        span,
                    );
                }
            }
            TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => {
                self.walk_call_regions(
                    elem,
                    caller_place,
                    inst,
                    variance,
                    loans,
                    per_output_inputs,
                    span,
                );
            }
            _ => {}
        }
    }

    /// Check accesses in `stmt` against `loans`, then advance `loans` via
    /// `transfer_stmt`. `Call` is handled inline (not via `transfer_stmt`)
    /// so operand-by-operand consumption sees prior operands' releases —
    /// e.g. `call f(move r, copy y)` where `y` is loaned by `r` must pass.
    ///
    /// `next` is the immediately-following statement in the block, used
    /// to skip loan-conflict emission on drop-elab-inserted drops (see
    /// the Drop arm).
    fn check_and_transfer_stmt(
        &mut self,
        block: &BasicBlock,
        stmt: &Statement,
        next: Option<&Statement>,
        loans: &mut LoanMap,
    ) {
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                match rvalue {
                    RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                        self.check_operand_access(block, op, stmt.span, loans);
                    }
                    RValue::Ref(kind, place) => {
                        self.check_loan_conflict(
                            block,
                            place,
                            AccessKind::Borrow(kind.clone()),
                            stmt.span,
                            loans,
                        );
                    }
                    RValue::RawRef(_) => {
                        // Raw pointer creation is the "unsafe" escape hatch
                        // — no loan-conflict check. Aliasing with live
                        // borrows is the programmer's responsibility.
                    }
                    RValue::ArrayLit(ops) => {
                        for op in ops {
                            self.check_operand_access(block, op, stmt.span, loans);
                        }
                    }
                }
                self.check_loan_conflict(block, target, AccessKind::Write, stmt.span, loans);
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::Call(target, args) => {
                self.check_operand_access(block, target, stmt.span, loans);
                self.check_call_regions(target, args, stmt.span, loans);
                consume_operand(loans, target);
                for a in args {
                    self.check_operand_access(block, a, stmt.span, loans);
                    consume_operand(loans, a);
                }
            }
            StatementKind::Drop(place) => {
                // Skip the loan-conflict emission on drop-elab-inserted
                // drops. Drop-elab rewrites `x = <rvalue>` (Init x, Drop
                // type) into `drop x; x = <rvalue>` with the inserted
                // drop carrying the *assign's* span. Both statements
                // would fire against the same borrower at the same span,
                // reporting a single user event twice. The assign
                // carries the authoritative diagnostic; the auto-drop is
                // silent but still advances the loan map.
                if !is_elab_inserted_drop(place, stmt.span, next) {
                    self.check_loan_conflict(block, place, AccessKind::Move, stmt.span, loans);
                }
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::Unborrow(place) => {
                // Consumes the borrower Var. Its own loan is skipped in
                // check_loan_conflict (the "borrower == access_root with
                // empty path" case), but a *reborrow* of this borrower —
                // loan borrowed by s on `*r` — still needs to block `unborrow r`.
                self.check_loan_conflict(block, place, AccessKind::Move, stmt.span, loans);
                transfer_stmt(loans, stmt, stmt.span, self.region_ctx);
            }
            StatementKind::RequireUninit(_) => {
                // Place-state validates the assertion. It is not a runtime
                // access and therefore does not participate in loan checks.
            }
        }
    }

    fn check_and_transfer_terminator(&mut self, block: &BasicBlock, loans: &mut LoanMap) {
        let terminator_span = block.terminator.span;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                self.check_operand_access(block, cond, terminator_span, loans);
                consume_operand(loans, cond);
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                // Discriminant read.
                self.check_loan_conflict(block, place, AccessKind::Read, terminator_span, loans);
            }
            _ => {}
        }
    }
}

// nll_tests covers pass-specific snapshot behavior (assert_elab_eq)
// that the fixture runner can't observe. Most of its round-trip tests
// duplicate fixtures; keeping the file whole is simpler than stripping.
#[cfg(test)]
mod nll_tests;
