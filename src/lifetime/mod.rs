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

use crate::ast::*;
use crate::dataflow::{self, Analysis, Direction, Results};
use crate::diagnostics::Diagnostics;
use crate::push_error;
use crate::type_check::Env;
use indexmap::IndexMap;
use std::collections::BTreeSet;

pub mod nll;

/// A record of a borrow that's currently in force. `loaned` is a set to
/// support multi-loan: when a branch-of-borrows produces different loaned
/// places on each side, the join unions them so all possible pointees
/// stay tracked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loan {
    pub kind: RefKind,
    pub loaned: BTreeSet<Place>,
    pub create_span: Span,
}

impl Loan {
    pub fn single(kind: RefKind, loaned: Place, create_span: Span) -> Self {
        let mut set = BTreeSet::new();
        set.insert(loaned);
        Loan {
            kind,
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
            push_error!(
                d,
                span,
                func,
                block,
                "cannot {} '{}': already borrowed by '{}'",
                access.describe(),
                format_place(place),
                format_place(borrower_place),
            );
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
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => consume_operand(loans, op),
        RValue::Ref(_, _) => {}
    }
}

/// If the assign is `dst_place = move src_place` and both sides are
/// owned paths, returns `src_place`. This is the pattern where a
/// reference's ref-state and loan should transfer from src to dst
/// instead of being lost. Handles `x = move y`, `b.p = move t`,
/// `t = move b.p`, etc.
fn ref_move_source(target: &Place, rvalue: &RValue) -> Option<Place> {
    if !is_owned_path(target) {
        return None;
    }
    let RValue::Use(Operand::Move(src)) = rvalue else {
        return None;
    };
    as_owned_path(src)
}

/// Forward dataflow analysis over `LoanMap`. Runs independently of the
/// init-state analysis — the two share nothing beyond the statement they
/// both observe.
struct LoanAnalysis;

impl Analysis for LoanAnalysis {
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
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement) {
        transfer_stmt(state, stmt);
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
fn transfer_stmt(loans: &mut LoanMap, stmt: &Statement) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            let carried = ref_move_source(target, rvalue).and_then(|src| loans.get(&src).cloned());

            consume_rvalue(loans, rvalue);
            if let Some(t) = as_owned_path(target) {
                // Overwriting the target closes its previous loan.
                loans.shift_remove(&t);
            }
            if let (Some(t), RValue::Ref(kind, place)) = (as_owned_path(target), rvalue) {
                loans.insert(
                    t,
                    Loan::single(kind.clone(), place.clone(), Span { line: 0, col: 0 }),
                );
            }
            if let (Some(dst), Some(loan)) = (as_owned_path(target), carried) {
                loans.insert(dst, loan);
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

/// Run the LoanAnalysis fixpoint over `body`. Returns per-block entry
/// `LoanMap`.
pub fn run(body: &FunctionBody) -> Results<LoanMap> {
    dataflow::run(&LoanAnalysis, body)
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
        check_function(f, d);
    }
}

fn check_function(func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }
    let entry_states = run(body);
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut loans = entry.clone();
        for (stmt, span) in &block.statements {
            check_and_transfer_stmt(func, block, stmt, *span, &mut loans, d);
        }
        check_and_transfer_terminator(func, block, &mut loans, d);
    }
}

/// Check accesses in `stmt` against `loans`, then advance `loans` via
/// `transfer_stmt`. `Call` is handled inline (not via `transfer_stmt`)
/// so operand-by-operand consumption sees prior operands' releases —
/// e.g. `call f(move r, copy y)` where `y` is loaned by `r` must pass.
fn check_and_transfer_stmt(
    func: &Function,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    loans: &mut LoanMap,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            match rvalue {
                RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
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
            }
            check_loan_conflict(func, block, target, AccessKind::Write, span, loans, d);
            transfer_stmt(loans, stmt);
        }
        Statement::Call(target, args) => {
            check_operand_access(func, block, target, span, loans, d);
            consume_operand(loans, target);
            for a in args {
                check_operand_access(func, block, a, span, loans, d);
                consume_operand(loans, a);
            }
        }
        Statement::Drop(place) => {
            check_loan_conflict(func, block, place, AccessKind::Move, span, loans, d);
            transfer_stmt(loans, stmt);
        }
        Statement::Unborrow(place) => {
            // Consumes the borrower Var. Its own loan is skipped in
            // check_loan_conflict (the "borrower == access_root with
            // empty path" case), but a *reborrow* of this borrower —
            // loan borrowed by s on `*r` — still needs to block `unborrow r`.
            check_loan_conflict(func, block, place, AccessKind::Move, span, loans, d);
            transfer_stmt(loans, stmt);
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

#[cfg(test)]
mod loan_tests;
#[cfg(test)]
mod nll_tests;
#[cfg(test)]
mod path_borrower_tests;
#[cfg(test)]
mod reborrow_tests;
#[cfg(test)]
mod unborrow_tests;
