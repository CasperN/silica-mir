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

use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::dataflow::{self, Analysis, Direction, Results};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
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
pub mod nll;
pub mod region;

pub use region::Region;

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

impl AccessKind {
    fn describe(&self) -> &'static str {
        match self {
            AccessKind::Read => "read",
            AccessKind::Write => "write to",
            AccessKind::Move => "move from",
            AccessKind::Borrow(k) => match k {
                RefKind::Shared => "borrow as &",
                RefKind::Mut => "borrow as &mut",
                RefKind::Out => "borrow as &out",
                RefKind::Drop => "borrow as &drop",
                RefKind::Uninit => "borrow as &uninit",
            },
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

/// Check whether accessing `place` in the given way conflicts with any
/// active loan. Uses `extract_path_with_deref` so accesses through `*r`
/// or ancestors of `*r` (like `r` itself) can conflict with a reborrow
/// loan on `Deref(Var(r))`.
///
/// A conflict is reported when: the access root matches a loan's root
/// (i.e. touches the same base variable) AND the access path shares a
/// prefix with the loaned path AND the loan kind is not compatible with
/// the access kind.
pub fn check_loan_conflict(
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    access: AccessKind,
    span: Span,
    loans: &LoanMap,
    d: &mut Diagnostics,
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
            // Dedup: drop-elaboration expands `target = <rvalue>` into
            // `drop target; target = <rvalue>` when target's type is
            // Drop. Both statements then produce a LoanConflict against
            // the same borrower at the same span (Move + Write access).
            // Keep the *later* emission — for a drop-elab-expanded
            // assign that's the Write, which matches what the user
            // actually wrote. Remove any prior LoanConflict matching
            // this (span, borrower) before pushing the new one.
            let borrower_msg = format!("already borrowed by '{}'", borrower_name);
            d.retain_errors(|e| {
                !(e.code() == DiagCode::Lifetime(LifetimeCode::LoanConflict)
                    && e.span() == span
                    && e.message().contains(&borrower_msg))
            });
            let hint = format!(
                "the borrow of '{}' is active until its last use or explicit unborrow.",
                borrower_name,
            );
            let mut diag = Diagnostic::new(
                LifetimeCode::LoanConflict,
                span,
                format!(
                    "cannot {} '{}': already borrowed by '{}'",
                    access.describe(),
                    format_place(place),
                    borrower_name,
                ),
            )
            .in_function(&func.name)
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
            d.push_error(diag);
            break;
        }
    }
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
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) => consume_operand(loans, op),
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
fn capture_carried_loans(
    target: &Place,
    rvalue: &RValue,
    loans: &LoanMap,
) -> Vec<(Place, Loan)> {
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
        if let Terminator::Branch { cond, .. } = term {
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
    match stmt {
        Statement::Assign(target, rvalue) => {
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
                loans.insert(
                    t,
                    Loan::single(kind.clone(), region, place.clone(), span),
                );
            }
            for (new_key, loan) in carried {
                loans.insert(new_key, loan);
            }
        }
        Statement::Call(target, args) => {
            consume_operand(loans, target);
            for a in args {
                consume_operand(loans, a);
            }
        }
        Statement::Drop(place) | Statement::Unborrow(place) => {
            // Consume of a borrower place ends its loan (and any
            // ref-field loans it holds). `drop *r` consumes the pointee,
            // not the borrower; the borrower path passes through Deref
            // and won't match as_owned_path.
            if let Some(consumed) = as_owned_path(place) {
                close_loans_under(loans, &consumed);
            }
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
pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
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
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut loans = entry.clone();
        for (stmt, span) in &block.statements {
            check_and_transfer_stmt(env, func, block, stmt, *span, &mut loans, &region_ctx, &mut constraints, d);
            emit_stmt_constraints(env, func, stmt, *span, &region_ctx, &mut constraints);
        }
        check_and_transfer_terminator(func, block, &mut loans, d);
    }
    let escape_visible = signature_visible_regions(func, env);
    check_constraints(&constraints, func, &escape_visible, d);
}

/// Return the set of Named regions that are reachable from a
/// caller-visible slot: through `$return`, or through any
/// caller-provided `&mut` / `&out` parameter (i.e. any pointer the
/// callee can write into, whose target the caller reads back).
///
/// A Named region that only appears in body-local types (e.g. a
/// struct field of a locally-owned struct decl instantiated at
/// use-site with no lifetime args) is NOT escape-visible.
fn signature_visible_regions(
    func: &Function,
    env: &Env,
) -> BTreeSet<Lifetime> {
    let mut out = BTreeSet::new();
    for p in &func.params {
        // $return is the sret slot; any &out or &mut is caller-provided
        // storage the callee writes into.
        let visible = p.name == "$return"
            || matches!(&p.ty, Type::Ref(RefKind::Out, _, _) | Type::Ref(RefKind::Mut, _, _));
        if !visible {
            continue;
        }
        // Peel off the outer ref (that ref's own lifetime is the
        // caller's storage lifetime; irrelevant to escape) and collect
        // named regions in the pointee.
        let pointee = match &p.ty {
            Type::Ref(_, _, inner) => inner.as_ref().clone(),
            other => other.clone(),
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
    use crate::mir::type_util::substitute_all;
    match ty {
        Type::Ref(_, Some(lt), inner) => {
            out.insert(lt.clone());
            collect_named_regions(inner, env, visited, out);
        }
        Type::Ref(_, None, inner) | Type::RawPtr(inner) | Type::Array(inner, _) => {
            collect_named_regions(inner, env, visited, out);
        }
        Type::Custom(name, lifetime_args, type_args) => {
            for lt in lifetime_args {
                out.insert(lt.clone());
            }
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    for f in &s.fields {
                        let sub = substitute_all(&f.ty, &s.lifetime_params, lifetime_args, &s.type_params, type_args);
                        collect_named_regions(&sub, env, visited, out);
                    }
                }
                Some(TypeDecl::Enum(e)) => {
                    for v in &e.variants {
                        let sub = substitute_all(&v.ty, &e.lifetime_params, lifetime_args, &e.type_params, type_args);
                        collect_named_regions(&sub, env, visited, out);
                    }
                }
                _ => {}
            }
            visited.remove(name);
        }
        Type::Fn(args) => {
            for a in args {
                collect_named_regions(a, env, visited, out);
            }
        }
        _ => {}
    }
}

/// Enforce accumulated outlives constraints. Without `where`-clause
/// bounds in scope, the only satisfiable inter-named-region relation
/// is equality (or `Static outlives anything`, already pruned at
/// emit). Any constraint pairing two distinct Named regions fires
/// `LT-LifetimeMismatch`. Free ↔ Named or Free ↔ Free are treated as
/// unifiable at this phase (escape checking handles the interesting
/// Free ↔ signature-visible case in phase 5).
fn check_constraints(
    cs: &constraints::ConstraintSet,
    func: &Function,
    escape_visible: &BTreeSet<Lifetime>,
    d: &mut Diagnostics,
) {
    let axioms: Vec<(Region, Region)> = func
        .signature_outlives
        .iter()
        .map(|(a, b)| (Region::Named(a.clone()), Region::Named(b.clone())))
        .collect();
    let closure = constraints::transitive_closure(&axioms);
    for c in cs.iter() {
        match (&c.outlives, &c.sub) {
            (Region::Named(_), Region::Named(_)) if c.outlives != c.sub => {
                if closure.contains(&(c.outlives.clone(), c.sub.clone())) {
                    continue;
                }
                d.push_error(
                    Diagnostic::new(
                        LifetimeCode::LifetimeMismatch,
                        c.origin,
                        format!(
                            "lifetime mismatch: expected value with region {}, found value with region {}",
                            c.sub, c.outlives,
                        ),
                    )
                    .in_function(&func.name),
                );
            }
            // Escape: a Free-region loan (body-local storage) flowing
            // into a Named region that's actually reachable through a
            // caller-visible output ($return or &out/&mut param).
            (Region::Free(_), Region::Named(dst)) if escape_visible.contains(dst) => {
                d.push_error(
                    Diagnostic::new(
                        LifetimeCode::LifetimeEscape,
                        c.origin,
                        format!(
                            "borrow escapes function: value with local (unnamed) region cannot be stored into region {}",
                            dst,
                        ),
                    )
                    .in_function(&func.name),
                );
            }
            // Named outlives Free: source is a real (signature)
            // region, dst is a body-local. Always satisfiable — a
            // named region outlives any local temp.
            (Region::Named(_), Region::Free(_)) => {}
            _ => {}
        }
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
    for block in &body.blocks {
        for (stmt, span) in &block.statements {
            emit_stmt_constraints(env, func, stmt, *span, &region_ctx, &mut cs);
        }
    }
    cs
}

/// Emit outlives constraints for one statement. Currently covers
/// assignment `dst = src` where both sides are ref-typed: the
/// source's region must outlive the destination's.
fn emit_stmt_constraints(
    env: &Env,
    func: &Function,
    stmt: &Statement,
    span: Span,
    region_ctx: &region::RegionCtx,
    constraints: &mut constraints::ConstraintSet,
) {
    let locals = func.locals_map();
    let Statement::Assign(target, rvalue) = stmt else { return };
    let (src_region, target_place) = match rvalue {
        RValue::Use(op) => {
            let Some(src) = operand_place(op) else { return };
            let Some(r) = region_of_ref_place(src, &locals, env, region_ctx) else { return };
            (r, target.clone())
        }
        RValue::Ref(_, place) => {
            let r = if let Some(owned) = as_owned_path(place) {
                region_ctx.get(&owned).cloned().unwrap_or(Region::Free(u32::MAX))
            } else {
                Region::Free(u32::MAX)
            };
            (r, target.clone())
        }
        RValue::EnumConstr(_, _, variant, op) => {
            let Some(src) = operand_place(op) else { return };
            let Some(r) = region_of_ref_place(src, &locals, env, region_ctx) else { return };
            (r, downcast_place(target.clone(), variant.clone()))
        }
        _ => return,
    };
    let Some(t_r) = region_of_ref_place(&target_place, &locals, env, region_ctx) else {
        return;
    };
    // Emit variance-aware constraint. Shared refs are covariant
    // (source outlives dst is enough). Exclusive-write kinds are
    // invariant (source outlives dst AND dst outlives source).
    let target_kind = ref_kind_of_place(&target_place, &locals, env);
    constraints.emit(src_region.clone(), t_r.clone(), span);
    if !matches!(target_kind, Some(RefKind::Shared)) {
        constraints.emit(t_r, src_region, span);
    }
}

/// Emit outlives constraints for a `call callee(args)` statement,
/// and register synthetic loans on caller-side output slots so the
/// loan tracker can detect aliasing of caller-side inputs through
/// callee-returned refs.
///
/// Algorithm:
/// 1. Look up callee's Function in env. If callee isn't a static
///    fn name (call-through-fn-pointer, intrinsic without a Function
///    entry, ...), skip — call-site propagation is fn-name-only.
/// 2. Allocate fresh Free regions for each callee lifetime param.
/// 3. For each caller arg matched with callee param position:
///    walk both types in parallel; at each lifetime slot emit an
///    outlives constraint between caller region and instantiated
///    callee region. Direction depends on the surrounding ref kind:
///    input (regular ref pointee) → `caller outlives inst`;
///    output (`&mut`/`&out` pointee) → `inst outlives caller`.
/// 4. Snapshot each caller arg's loans keyed by the callee region
///    that same arg position maps to.
/// 5. After callee's signature_outlives axioms are instantiated
///    and emitted, register synthetic loans on caller output
///    positions: each output slot with callee region 'out gets a
///    loan whose `loaned` set is the union of the snapshotted
///    input loans that shared 'out.
fn check_call_regions(
    env: &Env,
    func: &Function,
    target: &Operand,
    args: &[Operand],
    span: Span,
    loans: &mut LoanMap,
    region_ctx: &region::RegionCtx,
    constraints: &mut constraints::ConstraintSet,
    _d: &mut Diagnostics,
) {
    let Operand::Const(ConstVal::FnName(callee_name, _)) = target else { return };
    let Some(callee) = env.functions.get(callee_name) else { return };
    if callee.params.len() != args.len() {
        return;
    }

    // Fresh instantiation region per callee lifetime param.
    let inst: IndexMap<Lifetime, Region> = callee
        .lifetime_params
        .iter()
        .enumerate()
        .map(|(i, lt)| (lt.clone(), Region::Free(u32::MAX - 1 - i as u32)))
        .collect();

    let locals = func.locals_map();

    // Walk each (caller arg, callee param) in parallel, emitting
    // constraints and collecting output-position information for
    // synthetic loan registration.
    let mut per_output_inputs: IndexMap<Region, BTreeSet<Place>> = IndexMap::new();

    for (arg, param) in args.iter().zip(callee.params.iter()) {
        let Some(arg_place) = operand_place(arg) else { continue };
        walk_call_regions(
            &param.ty,
            arg_place,
            &inst,
            &locals,
            env,
            region_ctx,
            CallPos::Input,
            loans,
            &mut per_output_inputs,
            constraints,
            span,
        );
    }

    // Instantiate callee's signature outlives axioms.
    for (a, b) in &callee.signature_outlives {
        let a_r = inst.get(a).cloned().unwrap_or(Region::Named(a.clone()));
        let b_r = inst.get(b).cloned().unwrap_or(Region::Named(b.clone()));
        constraints.emit(a_r, b_r, span);
    }

    // Register synthetic loans on caller-side output slots. For each
    // caller arg that is `&out T` where T contains a ref, look up
    // the arg's own loan to find the caller-side backing storage,
    // and place a synthetic loan there whose `loaned` = union of
    // input loans sharing that output's callee region.
    for (arg, param) in args.iter().zip(callee.params.iter()) {
        let Some(arg_place) = operand_place(arg) else { continue };
        let Some(arg_owned) = as_owned_path(arg_place) else { continue };
        // Only outer &out/&mut positions can be write-outputs.
        let Type::Ref(kind, _, inner_ty) = &param.ty else { continue };
        if !matches!(kind, RefKind::Out | RefKind::Mut) { continue }
        let Some(inner_lt) = extract_outer_lifetime(inner_ty) else { continue };
        let out_region = inst.get(&inner_lt).cloned().unwrap_or(Region::Named(inner_lt));
        let Some(input_places) = per_output_inputs.get(&out_region) else { continue };
        if input_places.is_empty() { continue }

        // Merge loaned places from inputs sharing this region.
        let mut merged: BTreeSet<Place> = BTreeSet::new();
        for src in input_places {
            if let Some(loan) = loans.get(src) {
                merged.extend(loan.loaned.iter().cloned());
            }
        }
        if merged.is_empty() { continue }

        // The caller's backing storage for this output slot: the
        // places pointed at by the arg's own loan.
        let arg_loan = loans.get(&arg_owned).cloned();
        if let Some(arg_loan) = arg_loan {
            for slot in arg_loan.loaned {
                loans.insert(
                    slot,
                    Loan {
                        kind: RefKind::Mut,
                        region: out_region.clone(),
                        loaned: merged.clone(),
                        create_span: span,
                    },
                );
            }
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
enum CallPos {
    Input,
    Output,
}

/// Walk callee param type and caller arg place in parallel, at each
/// ref boundary emit the appropriate outlives constraint and record
/// output-position info for synthetic loans.
fn walk_call_regions(
    callee_ty: &Type,
    caller_place: &Place,
    inst: &IndexMap<Lifetime, Region>,
    locals: &IndexMap<String, Type>,
    env: &Env,
    region_ctx: &region::RegionCtx,
    pos: CallPos,
    loans: &LoanMap,
    per_output_inputs: &mut IndexMap<Region, BTreeSet<Place>>,
    constraints: &mut constraints::ConstraintSet,
    span: Span,
) {
    match callee_ty {
        Type::Ref(kind, Some(lt), inner) => {
            let inst_region = inst.get(lt).cloned().unwrap_or(Region::Named(lt.clone()));
            if let Some(caller_r) = region_of_ref_place(caller_place, locals, env, region_ctx) {
                match pos {
                    CallPos::Input => {
                        constraints.emit(caller_r, inst_region.clone(), span);
                        if let Some(owned) = as_owned_path(caller_place) {
                            if loans.contains_key(&owned) {
                                per_output_inputs
                                    .entry(inst_region.clone())
                                    .or_default()
                                    .insert(owned);
                            }
                        }
                    }
                    CallPos::Output => {
                        constraints.emit(inst_region.clone(), caller_r, span);
                    }
                }
            }
            // Recurse into inner. Exclusive-write kinds flip position.
            let inner_pos = match kind {
                RefKind::Mut | RefKind::Out => CallPos::Output,
                _ => pos,
            };
            let inner_caller = crate::mir::helpers::deref_place(caller_place.clone());
            walk_call_regions(
                inner,
                &inner_caller,
                inst,
                locals,
                env,
                region_ctx,
                inner_pos,
                loans,
                per_output_inputs,
                constraints,
                span,
            );
        }
        _ => {}
    }
}

fn extract_outer_lifetime(ty: &Type) -> Option<Lifetime> {
    match ty {
        Type::Ref(_, lt, _) => lt.clone(),
        _ => None,
    }
}

/// Get the outer ref-kind of `place` when its type is `Type::Ref`.
fn ref_kind_of_place(
    place: &Place,
    locals: &IndexMap<String, Type>,
    env: &Env,
) -> Option<RefKind> {
    match crate::mir::type_util::place_type(locals, env, place)? {
        Type::Ref(kind, _, _) => Some(kind),
        _ => None,
    }
}

/// Region of `place` when it's ref-typed. Falls back to reading the
/// lifetime slot from `place`'s computed type for non-owned paths
/// (e.g. `$return.*` — a Deref that isn't in the region map).
fn region_of_ref_place(
    place: &Place,
    locals: &IndexMap<String, Type>,
    env: &Env,
    region_ctx: &region::RegionCtx,
) -> Option<Region> {
    if let Some(owned) = as_owned_path(place) {
        if let Some(r) = region_ctx.get(&owned) {
            return Some(r.clone());
        }
    }
    let ty = crate::mir::type_util::place_type(locals, env, place)?;
    if let Type::Ref(_, Some(lt), _) = ty {
        Some(Region::Named(lt))
    } else {
        None
    }
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Const(_) => None,
    }
}


/// Check accesses in `stmt` against `loans`, then advance `loans` via
/// `transfer_stmt`. `Call` is handled inline (not via `transfer_stmt`)
/// so operand-by-operand consumption sees prior operands' releases —
/// e.g. `call f(move r, copy y)` where `y` is loaned by `r` must pass.
fn check_and_transfer_stmt(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    loans: &mut LoanMap,
    region_ctx: &region::RegionCtx,
    constraints: &mut constraints::ConstraintSet,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            match rvalue {
                RValue::Use(op) | RValue::EnumConstr(_, _, _, op) => {
                    check_operand_access(func, block, op, span, loans, d);
                }
                RValue::Ref(kind, place) => {
                    check_loan_conflict(
                        func,
                        block,
                        place,
                        AccessKind::Borrow(kind.clone()),
                        span,
                        loans,
                        d,
                    );
                }
                RValue::RawRef(_) => {
                    // Raw pointer creation is the "unsafe" escape hatch
                    // — no loan-conflict check. Aliasing with live
                    // borrows is the programmer's responsibility.
                }
                RValue::ArrayLit(ops) => {
                    for op in ops {
                        check_operand_access(func, block, op, span, loans, d);
                    }
                }
            }
            check_loan_conflict(func, block, target, AccessKind::Write, span, loans, d);
            transfer_stmt(loans, stmt, span, region_ctx);
        }
        Statement::Call(target, args) => {
            check_operand_access(func, block, target, span, loans, d);
            check_call_regions(env, func, target, args, span, loans, region_ctx, constraints, d);
            consume_operand(loans, target);
            for a in args {
                check_operand_access(func, block, a, span, loans, d);
                consume_operand(loans, a);
            }
        }
        Statement::Drop(place) => {
            check_loan_conflict(func, block, place, AccessKind::Move, span, loans, d);
            transfer_stmt(loans, stmt, span, region_ctx);
        }
        Statement::Unborrow(place) => {
            // Consumes the borrower Var. Its own loan is skipped in
            // check_loan_conflict (the "borrower == access_root with
            // empty path" case), but a *reborrow* of this borrower —
            // loan borrowed by s on `*r` — still needs to block `unborrow r`.
            check_loan_conflict(func, block, place, AccessKind::Move, span, loans, d);
            transfer_stmt(loans, stmt, span, region_ctx);
        }
    }
}

fn check_and_transfer_terminator(
    func: &Function,
    block: &BasicBlock,
    loans: &mut LoanMap,
    d: &mut Diagnostics,
) {
    let ts = block.terminator_span;
    match &block.terminator {
        Terminator::Branch { cond, .. } => {
            check_operand_access(func, block, cond, ts, loans, d);
            consume_operand(loans, cond);
        }
        Terminator::SwitchEnum { place, .. } => {
            // Discriminant read.
            check_loan_conflict(func, block, place, AccessKind::Read, ts, loans, d);
        }
        _ => {}
    }
}

fn check_operand_access(
    func: &Function,
    block: &BasicBlock,
    op: &Operand,
    span: Span,
    loans: &LoanMap,
    d: &mut Diagnostics,
) {
    let (place, access) = match op {
        Operand::Copy(p) => (p, AccessKind::Read),
        Operand::Move(p) => (p, AccessKind::Move),
        Operand::Const(_) => return,
    };
    check_loan_conflict(func, block, place, access, span, loans, d);
}


// nll_tests covers pass-specific snapshot behavior (assert_elab_eq)
// that the fixture runner can't observe. Most of its round-trip tests
// duplicate fixtures; keeping the file whole is simpler than stripping.
#[cfg(test)]
mod nll_tests;
