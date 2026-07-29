//! Loan dataflow — the "who borrows what" side of the borrow story.
//!
//! An active borrow of a place `p` by a borrower variable `r` registers a
//! `Loan`. While the loan is live, direct access to `p` (or a prefix/extension
//! sharing storage with `p`) is blocked unless it is compatible with the
//! loan's kind (only shared/shared is compatible). Loans expire when the
//! borrower is consumed — moved to a callee, dropped, or explicitly
//! `unborrow`ed.
//!
//! `Loan` participates in a set-valued lattice: joining two branches that
//! both bind the same borrower variable to different loaned places (a
//! *branch-of-borrows*) unions their `loaned` sets so any of them may be
//! the actual pointee.
//!
//! The four exclusive reference kinds (`&mut`, `&out`, `&drop`, `&uninit`)
//! differ only in their pointee init obligations, not in their exclusivity:
//! from the loan tracker's view they are all "exclusive borrow of p". The
//! kind is retained solely to shape the diagnostic ("borrow as &out", etc.)
//! and to enable shared/shared compatibility.

use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction, Results};
use crate::mir::helpers::*;
use indexmap::IndexMap;
use std::collections::BTreeSet;


/// A record of a borrow that's currently in force. `loaned` is a set to
/// support multi-loan: when a branch-of-borrows produces different loaned
/// places on each side, the join unions them so all possible pointees
/// stay tracked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loan {
    pub kind: RefKind,
    pub loaned: BTreeSet<Place>,
    pub create_source: SourceInfo,
}

impl Loan {
    pub fn single(kind: RefKind, loaned: Place, create_source: SourceInfo) -> Self {
        let mut set = BTreeSet::new();
        set.insert(loaned);
        Loan {
            kind,
            loaned: set,
            create_source,
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
pub(super) fn paths_conflict(a: &[PathStep], b: &[PathStep]) -> bool {
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
pub(super) fn is_compatible(loan_kind: &RefKind, access: &AccessKind) -> bool {
    matches!(loan_kind, RefKind::Shared)
        && matches!(
            access,
            AccessKind::Read | AccessKind::Borrow(RefKind::Shared)
        )
}

/// True if `stmt` is a `drop <place>` that drop-elaboration inserted
/// immediately before an assign to the same owned path. Drop-elab
/// preserves the assign's span on the inserted drop, so both share
/// `drop_source`; the checker uses this to suppress a duplicate
/// LoanConflict — the assign carries the authoritative diagnostic.
pub(super) fn is_elab_inserted_drop(
    place: &Place,
    drop_source: SourceInfo,
    next: Option<&Statement>,
) -> bool {
    if drop_source.generated_kind() != Some(GeneratedKind::DropElaboration) {
        return false;
    }
    let Some(next_stmt) = next else {
        return false;
    };
    if next_stmt.span() != drop_source.span() {
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
struct LoanAnalysis;

impl Analysis for LoanAnalysis {
    type State = LoanMap;
    fn direction(&self) -> Direction {
        Direction::Forward
    }
    fn boundary_state(&self) -> Self::State {
        LoanMap::new()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join_loans(a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, source: SourceInfo) {
        transfer_stmt(state, stmt, source);
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        if let TerminatorKind::Branch { cond, .. } = &term.kind {
            consume_operand(state, cond);
        }
    }
}

/// Apply the whole-statement loan transition. Silent (no diagnostics);
/// the diagnostic walk in `check` uses the smaller `consume_operand`
/// helper alongside inline inserts/removes.
pub(super) fn transfer_stmt(loans: &mut LoanMap, stmt: &Statement, source: SourceInfo) {
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
                loans.insert(t, Loan::single(kind.clone(), place.clone(), source));
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

/// Run the LoanAnalysis fixpoint over `body`.
pub fn run(body: &FunctionBody) -> Results<LoanMap> {
    dataflow::run(&LoanAnalysis, body)
}
