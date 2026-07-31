//! Copy relaxation: specialize `take` operands to `move` or `copy`.
//!
//! HLL lowers ordinary value reads as `Operand::Take`. This pass rewrites
//! each `take place` to either `move place` (last-use consumption) or
//! `copy place` (a later reachable use / ref post-Init obligation demands
//! the value, or the path structurally forbids consumption). Explicit
//! `move` and `copy` in the input are authoritative and never rewritten,
//! so hand-written `.sim` fixtures can pin exact operand kinds.
//!
//! It deliberately runs before NLL elaboration. Specializing `take` to
//! `move` versus `copy` changes whether the read closes a borrower loan,
//! so NLL must compute liveness from the resolved program.
//!
//! The analysis is backward, with separate may-demand sets for values and
//! the owned bases needed to access them. At a CFG join the sets union:
//! an operand must be preserved if either successor can still use it.
//!
//! Path classification (all `Field` / `Downcast` / const-`Index` steps
//! are transparent):
//! - **Mandatory-copy** — the path crosses a shared reference (`&T`) or
//!   contains a dynamic index. Moving through `&T` is illegal; a dynamic
//!   index has no stable identity, so consuming it would silently lose
//!   the storage. `take` on such a path is always specialized to `copy`;
//!   a non-Copy type here is `RELAX-MandatoryCopyNonCopy`.
//! - **Stable candidates** — owned paths, chains of exclusive-ref
//!   dereferences, and paths crossing raw pointers. Raw pointers already
//!   sit inside `unsafe`, so the pass demand-relaxes them like ordinary
//!   candidates rather than mandating copy. Resolution: `copy` when
//!   demand is live and the type is Copy, otherwise `move` (falling back
//!   to `copy` for Copy-only types).
//! - **`Index` operand position** — a non-consuming read. `take` there
//!   is forced to `copy`; `move` is `RELAX-IndexOperandNotReading`. This
//!   keeps downstream analyses (place-state, NLL, lifetime) from having
//!   to recurse into `Index` projections.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction};
use crate::mir::helpers::*;
use crate::mir::place_state::analysis::RefState;
use crate::mir::type_check::Env;
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// User-facing errors emitted by the `take` resolver. Distinct from
/// the pre-elaboration substructural check (which flags places whose
/// type supports neither `Copy` nor `Move`): these fire when the
/// resolution decision itself has no valid target — for example, a
/// `take` on a Move-only value through a shared-reference boundary,
/// where the boundary demands `copy` but the type isn't `Copy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyRelaxationCode {
    /// The path crosses a shared reference or dynamic-index projection
    /// (both mandate a `copy` resolution), but the place's type isn't
    /// `Copy`. Only `move` would be type-valid, but `move` is
    /// semantically illegal on this path.
    MandatoryCopyNonCopy,
    /// A `move` or `take` appears inside an `Index` projection. Array
    /// indexing reads its operand non-consumingly; place-state, NLL,
    /// and lifetime analyses only walk the outer operand, so a
    /// consuming index would silently escape ownership tracking.
    /// Index operands must be `copy` or a constant.
    IndexOperandNotReading,
}

impl From<CopyRelaxationCode> for DiagCode {
    fn from(code: CopyRelaxationCode) -> DiagCode {
        DiagCode::CopyRelaxation(code)
    }
}

/// Specialize each `take` operand into `move` or `copy` based on
/// backward may-demand and static path shape. Explicit `move`/`copy` are
/// authoritative and never rewritten. Idempotent: after resolution no
/// `take` remains, so a second run is a no-op.
///
/// Diagnostics are user-facing errors emitted when a `take` cannot be
/// resolved to any valid operand (e.g. a non-Copy pointee through a
/// shared-reference or dynamic-index boundary, where `copy` would be
/// required but the type isn't `Copy`).
pub fn elaborate(program: &mut Program, env: &Env, d: &mut Diagnostics) {
    for func in program.functions_mut() {
        elaborate_function(func, env, d);
    }
}

/// Post-elaboration invariant: no `Take` operand survives. If any do,
/// push a single internal-error diagnostic naming the first offender
/// (with a count so a broken pass doesn't spam per-operand). Downstream
/// passes assume this invariant and `unreachable!` on `Take`, so callers
/// must skip elaboration/checking when this returns anything.
pub fn verify_no_take(program: &Program, d: &mut crate::diagnostics::Diagnostics) {
    let mut first: Option<SourceInfo> = None;
    let mut count = 0usize;
    for func in program.functions() {
        let Some(body) = &func.body else { continue };
        for block in &body.blocks {
            for stmt in &block.statements {
                scan_statement_for_take(stmt, &mut first, &mut count);
            }
            scan_terminator_for_take(&block.terminator, &mut first, &mut count);
        }
    }
    if count == 0 {
        return;
    }
    let source = first
        .unwrap_or_else(|| SourceInfo::generated(GeneratedKind::CopyRelaxation, Span::default()));
    d.push_internal_error(crate::diagnostics::Diagnostic::new(
        crate::diagnostics::DiagCode::Parser(crate::mir::parser::ParserCode::MalformedCst),
        source,
        format!(
            "copy relaxation left {count} unresolved `take` operand(s); every `take` must be specialized to `move` or `copy` before downstream passes run"
        ),
    ));
}

fn scan_statement_for_take(stmt: &Statement, first: &mut Option<SourceInfo>, count: &mut usize) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            scan_place_for_take(target, stmt.source, first, count);
            scan_rvalue_for_take(rvalue, stmt.source, first, count);
        }
        StatementKind::Call(target, args) => {
            scan_operand_for_take(target, stmt.source, first, count);
            for op in args {
                scan_operand_for_take(op, stmt.source, first, count);
            }
        }
        StatementKind::Drop(place)
        | StatementKind::Unborrow(place)
        | StatementKind::RequireUninit(place) => {
            scan_place_for_take(place, stmt.source, first, count);
        }
    }
}

fn scan_terminator_for_take(term: &Terminator, first: &mut Option<SourceInfo>, count: &mut usize) {
    match &term.kind {
        TerminatorKind::Branch { cond, .. } => {
            scan_operand_for_take(cond, term.source, first, count)
        }
        TerminatorKind::SwitchEnum { place, .. } => {
            scan_place_for_take(place, term.source, first, count)
        }
        TerminatorKind::Goto(_)
        | TerminatorKind::Return
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

fn scan_rvalue_for_take(
    rv: &RValue,
    source: SourceInfo,
    first: &mut Option<SourceInfo>,
    count: &mut usize,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
            scan_operand_for_take(op, source, first, count);
        }
        RValue::Ref(_, place) | RValue::RawRef(place) => {
            scan_place_for_take(place, source, first, count);
        }
        RValue::ArrayLit(ops) => {
            for op in ops {
                scan_operand_for_take(op, source, first, count);
            }
        }
    }
}

fn scan_operand_for_take(
    op: &Operand,
    source: SourceInfo,
    first: &mut Option<SourceInfo>,
    count: &mut usize,
) {
    match op {
        Operand::Take(place) => {
            *count += 1;
            if first.is_none() {
                *first = Some(source);
            }
            scan_place_for_take(place, source, first, count);
        }
        Operand::Copy(place) | Operand::Move(place) => {
            scan_place_for_take(place, source, first, count);
        }
        Operand::Const(_) => {}
    }
}

/// Recurse into a place, visiting any operand that appears inside an
/// `Index` projection. Without this, a `Take` nested inside a dynamic
/// index would slip past both `verify_no_take` and the resolver.
fn scan_place_for_take(
    place: &Place,
    source: SourceInfo,
    first: &mut Option<SourceInfo>,
    count: &mut usize,
) {
    match place {
        Place::Var(_) => {}
        Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => {
            scan_place_for_take(inner, source, first, count);
        }
        Place::Index(inner, op) => {
            scan_place_for_take(inner, source, first, count);
            scan_operand_for_take(op, source, first, count);
        }
    }
}

fn elaborate_function(func: &mut Function, env: &Env, d: &mut Diagnostics) {
    let locals = func.locals_map();
    let scope = func.meta.param_scope();
    let return_obligations = collect_return_obligations(func);
    let func_name = func.meta.name.clone();
    let Some(body) = &mut func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let analysis = MovePathDemand {
        return_obligations: &return_obligations,
    };
    let exits = dataflow::run(&analysis, body);
    for block in &mut body.blocks {
        let Some(exit_demand) = exits.get(&block.label) else {
            continue;
        };
        let mut demand = exit_demand.clone();
        analysis.transfer_terminator(&mut demand, &block.terminator);
        let mut ctx = RelaxCtx {
            env,
            locals: &locals,
            scope: &scope,
            d,
            func_name: &func_name,
            block_label: &block.label,
        };
        relax_terminator(&mut block.terminator, &mut demand, &mut ctx);
        for stmt in block.statements.iter_mut().rev() {
            relax_statement(stmt, &mut demand, &mut ctx);
        }
    }
}

/// Per-block relaxation context. Bundles the env/locals/scope needed for
/// type queries with the diagnostics sink and the function/block context
/// used when emitting a user-facing error (e.g. `take` of a place that
/// resolves to neither `move` nor `copy`).
struct RelaxCtx<'a> {
    env: &'a Env,
    locals: &'a IndexMap<String, Type>,
    scope: &'a IndexMap<String, Markers>,
    d: &'a mut Diagnostics,
    func_name: &'a str,
    block_label: &'a str,
}

/// Ref-typed places whose obligation requires an Init pointee at expiry.
/// Injected as backward demand at `Return`: keeping the pointee Init through
/// the tail of the function is what those references contracted for, so any
/// `move place.*` reaching `Return` unmodified must relax to `copy` when the
/// pointee type permits.
///
/// Local refs may not actually live to `Return` — a move to a callee ends
/// them earlier — but the write that transfers the ref also kills demand on
/// its pointee, so the injection is safe over-approximation.
fn collect_return_obligations(func: &Function) -> BTreeSet<Place> {
    let mut out = BTreeSet::new();
    for param in &func.params {
        collect_post_init_pointees(&var_place(param.name.clone()), &param.ty, &mut out);
    }
    if let Some(body) = &func.body {
        for local in &body.locals {
            collect_post_init_pointees(&var_place(local.name.clone()), &local.ty, &mut out);
        }
    }
    out
}

fn collect_post_init_pointees(place: &Place, ty: &Type, out: &mut BTreeSet<Place>) {
    if let TypeKind::Ref(kind, _, inner) = &ty.kind {
        if RefState::from_kind(kind).is_some_and(|state| state.ends_init) {
            let pointee = deref_place(place.clone());
            out.insert(pointee.clone());
            collect_post_init_pointees(&pointee, inner, out);
        }
    }
}

/// Backward may-demand. `values` names storage whose current value is needed
/// by a successor. `accesses` names owned reference/index bases that must stay
/// available merely to reach some projected place. Keeping these separate is
/// what prevents a later use of borrower `r` from preserving pointee `r.*`.
#[derive(Clone, Default, PartialEq, Eq)]
struct Demand {
    values: BTreeSet<Place>,
    accesses: BTreeSet<Place>,
}

/// Backward may-demand for move paths.
struct MovePathDemand<'a> {
    return_obligations: &'a BTreeSet<Place>,
}

impl<'a> Analysis for MovePathDemand<'a> {
    type State = Demand;

    fn direction(&self) -> Direction {
        Direction::Backward
    }

    fn initial_state(&self) -> Self::State {
        Demand::default()
    }

    fn boundary_state(&self) -> Self::State {
        Demand::default()
    }

    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        Demand {
            values: a.values.union(&b.values).cloned().collect(),
            accesses: a.accesses.union(&b.accesses).cloned().collect(),
        }
    }

    fn transfer_stmt(&self, demand: &mut Self::State, stmt: &Statement, _source: SourceInfo) {
        transfer_statement_demand(stmt, demand);
    }

    fn transfer_terminator(&self, demand: &mut Self::State, term: &Terminator) {
        if matches!(term.kind, TerminatorKind::Return) {
            for place in self.return_obligations {
                demand.values.insert(place.clone());
            }
        }
        transfer_terminator_demand(term, demand);
    }
}

fn transfer_statement_demand(stmt: &Statement, demand: &mut Demand) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            transfer_place_index_operands(target, demand);
            kill_future_demand(demand, target);
            transfer_rvalue_demand(rvalue, demand);
            if as_owned_path(target).is_none() {
                add_access_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
            transfer_operand_demand(target, demand);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            transfer_place_index_operands(place, demand);
            add_value_demand(demand, place);
        }
        // This is a postcondition, not a value use. A preceding move should
        // remain a move when this is the only later statement mentioning it.
        StatementKind::RequireUninit(place) => {
            transfer_place_index_operands(place, demand);
        }
    }
}

fn transfer_terminator_demand(term: &Terminator, demand: &mut Demand) {
    match &term.kind {
        TerminatorKind::Branch { cond, .. } => transfer_operand_demand(cond, demand),
        TerminatorKind::SwitchEnum { place, .. } => {
            transfer_place_index_operands(place, demand);
            add_value_demand(demand, place);
        }
        TerminatorKind::Goto(_)
        | TerminatorKind::Return
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

fn transfer_rvalue_demand(rvalue: &RValue, demand: &mut Demand) {
    match rvalue {
        RValue::Use(operand)
        | RValue::EnumConstr(_, _, _, operand)
        | RValue::PtrCast(operand, _) => transfer_operand_demand(operand, demand),
        RValue::Ref(kind, place) => {
            transfer_place_index_operands(place, demand);
            transfer_ref_demand(kind, place, demand);
        }
        RValue::RawRef(place) => {
            transfer_place_index_operands(place, demand);
        }
        RValue::ArrayLit(operands) => {
            for operand in operands.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
        }
    }
}

fn transfer_operand_demand(operand: &Operand, demand: &mut Demand) {
    match operand {
        Operand::Copy(place) => {
            transfer_place_index_operands(place, demand);
            add_value_demand(demand, place);
        }
        Operand::Move(place) => {
            transfer_place_index_operands(place, demand);
            // Move consumes `place`'s subtree — downstream demand for its
            // descendants is void after the move, so drop it as we cross
            // this operand backward. The read itself is still a demand for
            // `place` pre-move.
            kill_future_demand(demand, place);
            add_value_demand(demand, place);
        }
        // Take is unresolved: over-approximate as a non-consuming read so
        // the fixpoint carries the largest safe demand set. The mutation
        // walk performs the actual resolution and applies the correct
        // move/copy transfer semantics.
        Operand::Take(place) => {
            transfer_place_index_operands(place, demand);
            add_value_demand(demand, place);
        }
        Operand::Const(_) => {}
    }
}

/// Contribute demand from any operand nested inside an `Index` projection.
/// The outer place demands the index value at the same point it demands
/// its own value.
fn transfer_place_index_operands(place: &Place, demand: &mut Demand) {
    match place {
        Place::Var(_) => {}
        Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => {
            transfer_place_index_operands(inner, demand);
        }
        Place::Index(inner, op) => {
            transfer_place_index_operands(inner, demand);
            transfer_operand_demand(op, demand);
        }
    }
}

/// An operation that establishes a new state for `place` makes any future
/// demand for that old state irrelevant on its input side.
fn kill_future_demand(demand: &mut Demand, target: &Place) {
    let Some(target_depth) = static_deref_depth(target) else {
        return;
    };

    // A write establishes a new value for the target. Any overlapping future
    // value at the same dereference depth (or deeper) is therefore not the old
    // value. Killing ancestors too is deliberately conservative: representing
    // "the old aggregate except this newly-written field" would require a
    // complement path set.
    demand
        .values
        .retain(|needed| !write_invalidates_demand(target, target_depth, needed));
    demand
        .accesses
        .retain(|needed| !write_invalidates_demand(target, target_depth, needed));
}

fn write_invalidates_demand(target: &Place, target_depth: usize, needed: &Place) -> bool {
    static_deref_depth(needed).is_some_and(|needed_depth| {
        needed_depth >= target_depth
            && (is_ancestor_or_self(target, needed) || is_ancestor_or_self(needed, target))
    })
}

fn paths_overlap(a: &Place, b: &Place) -> bool {
    is_ancestor_or_self(a, b) || is_ancestor_or_self(b, a)
}

fn demand_preserves(candidate: &Place, needed: &Place) -> bool {
    let Some(candidate_depth) = static_deref_depth(candidate) else {
        return false;
    };
    static_deref_depth(needed).is_some_and(|needed_depth| {
        needed_depth >= candidate_depth && paths_overlap(candidate, needed)
    })
}

fn is_static_access_path(place: &Place) -> bool {
    static_deref_depth(place).is_some()
}

/// Count dereference boundaries in a statically comparable place. Dynamic
/// indices return `None`: equality of `a[i]` at two program points is not
/// enough to prove that `i` still denotes the same slot.
fn static_deref_depth(place: &Place) -> Option<usize> {
    match place {
        Place::Var(_) => Some(0),
        Place::Field(inner, _) | Place::Downcast(inner, _) => static_deref_depth(inner),
        Place::Index(inner, operand) if const_int_operand(operand).is_some() => {
            static_deref_depth(inner)
        }
        Place::Index(_, _) => None,
        Place::Deref(inner) => static_deref_depth(inner).map(|depth| depth + 1),
    }
}

/// Backward transfer for a borrow's pointee transition. This mirrors
/// init-state's eager loan transitions, restricted to statically-owned
/// paths: `&out` establishes Init, `&drop` establishes Uninit, and
/// `&uninit` requires/retains Uninit. Only ordinary and mutable borrows
/// merely read an existing value.
fn transfer_ref_demand(kind: &RefKind, place: &Place, demand: &mut Demand) {
    match kind {
        RefKind::Shared | RefKind::Mut => add_value_demand(demand, place),
        RefKind::Drop => {
            kill_ref_transition_demand(demand, place);
            add_value_demand(demand, place);
        }
        RefKind::Out | RefKind::Uninit => {
            kill_ref_transition_demand(demand, place);
            if as_owned_path(place).is_none() {
                add_access_demand(demand, place);
            }
        }
    }
}

/// A reference state transition on a subplace also invalidates demand for a
/// containing aggregate. For example, after `&out p.field`, a future read of
/// `p` cannot justify preserving an earlier `move p`: the borrow itself
/// requires `p.field` to have been uninitialized. Ordinary assignment differs
/// here — overwriting a field of an already-preserved Copy aggregate is fine.
fn kill_ref_transition_demand(demand: &mut Demand, place: &Place) {
    let Some(depth) = static_deref_depth(place) else {
        return;
    };
    demand.values.retain(|needed| {
        !static_deref_depth(needed)
            .is_some_and(|needed_depth| needed_depth >= depth && paths_overlap(place, needed))
    });
    demand.accesses.retain(|needed| {
        !static_deref_depth(needed)
            .is_some_and(|needed_depth| needed_depth >= depth && paths_overlap(place, needed))
    });
}

/// Record that the current value of `place` is needed. Full logical places
/// are retained only when they are statically comparable.
fn add_value_demand(demand: &mut Demand, place: &Place) {
    if is_static_access_path(place) {
        demand.values.insert(place.clone());
    }
    add_access_demand(demand, place);
}

/// Record every reference value needed to evaluate or write `place`, without
/// claiming that the final pointee value is needed. For `r.*.next.*`, both
/// `r` and `r.*.next` are access carriers.
fn add_access_demand(demand: &mut Demand, place: &Place) {
    let mut cur = place;
    loop {
        match cur {
            Place::Var(_) => break,
            Place::Deref(inner) => {
                if is_static_access_path(inner) {
                    demand.accesses.insert((**inner).clone());
                }
                cur = inner;
            }
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
                cur = inner
            }
        }
    }
    if let Some(owned) = nearest_owned_path(place) {
        demand.accesses.insert(owned);
    }
}

fn nearest_owned_path(place: &Place) -> Option<Place> {
    if let Some(owned) = as_owned_path(place) {
        return Some(owned);
    }
    match place {
        Place::Var(_) => None,
        Place::Field(inner, _)
        | Place::Downcast(inner, _)
        | Place::Deref(inner)
        | Place::Index(inner, _) => nearest_owned_path(inner),
    }
}

fn relax_statement(stmt: &mut Statement, demand: &mut Demand, ctx: &mut RelaxCtx) {
    let source = stmt.source;
    match &mut stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // Nested index operands inside the target place are reads
            // evaluated to project into the target; visit them so any
            // `take` inside gets resolved even if the target itself is
            // just an assignment sink.
            relax_place_index_operands(target, demand, ctx, source);
            kill_future_demand(demand, target);
            relax_rvalue(rvalue, demand, ctx, source);
            if as_owned_path(target).is_none() {
                add_access_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter_mut().rev() {
                relax_operand(operand, demand, ctx, source);
            }
            relax_operand(target, demand, ctx, source);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            relax_place_index_operands(place, demand, ctx, source);
            add_value_demand(demand, place);
        }
        StatementKind::RequireUninit(place) => {
            relax_place_index_operands(place, demand, ctx, source);
        }
    }
}

fn relax_terminator(term: &mut Terminator, demand: &mut Demand, ctx: &mut RelaxCtx) {
    let source = term.source;
    match &mut term.kind {
        TerminatorKind::Branch { cond, .. } => relax_operand(cond, demand, ctx, source),
        TerminatorKind::SwitchEnum { place, .. } => {
            relax_place_index_operands(place, demand, ctx, source);
            add_value_demand(demand, place);
        }
        TerminatorKind::Goto(_)
        | TerminatorKind::Return
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

fn relax_rvalue(rvalue: &mut RValue, demand: &mut Demand, ctx: &mut RelaxCtx, source: SourceInfo) {
    match rvalue {
        RValue::Use(operand)
        | RValue::EnumConstr(_, _, _, operand)
        | RValue::PtrCast(operand, _) => relax_operand(operand, demand, ctx, source),
        RValue::Ref(kind, place) => {
            relax_place_index_operands(place, demand, ctx, source);
            transfer_ref_demand(kind, place, demand);
        }
        RValue::RawRef(place) => {
            relax_place_index_operands(place, demand, ctx, source);
        }
        RValue::ArrayLit(operands) => {
            for operand in operands.iter_mut().rev() {
                relax_operand(operand, demand, ctx, source);
            }
        }
    }
}

/// Recurse into a place, resolving any `take` operand that appears
/// inside an `Index` projection. Called before every place-level use so
/// nested `take`s don't slip past resolution.
///
/// Index operands must be **non-consuming reads**: place-state, NLL,
/// and lifetime analyses only walk the outer operand, so a `move` or
/// `take → move` inside `Index` would silently escape ownership
/// tracking. A `take` inside `Index` is forced to `Copy`; a `Move` is
/// a hand-written invariant violation and gets a user diagnostic.
fn relax_place_index_operands(
    place: &mut Place,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    source: SourceInfo,
) {
    match place {
        Place::Var(_) => {}
        Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => {
            relax_place_index_operands(inner, demand, ctx, source);
        }
        Place::Index(inner, op) => {
            relax_place_index_operands(inner, demand, ctx, source);
            resolve_index_operand(op, demand, ctx, source);
        }
    }
}

fn resolve_index_operand(
    operand: &mut Operand,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    source: SourceInfo,
) {
    match operand {
        Operand::Const(_) => {}
        Operand::Copy(p) => {
            relax_place_index_operands(p, demand, ctx, source);
            add_value_demand(demand, p);
        }
        Operand::Move(p) => {
            relax_place_index_operands(p, demand, ctx, source);
            ctx.d.push_error(
                Diagnostic::new(
                    CopyRelaxationCode::IndexOperandNotReading,
                    source,
                    format!(
                        "`move` of '{}' inside `Index` projection: array indexing is a \
                         non-consuming read, so its operand must be `copy` or a constant",
                        format_place(p)
                    ),
                )
                .in_function(ctx.func_name)
                .in_block(ctx.block_label),
            );
        }
        Operand::Take(p) => {
            relax_place_index_operands(p, demand, ctx, source);
            let place = p.clone();
            let ty = ctx.env.type_of_place(&place, ctx.locals).ok();
            let is_copy = ty
                .as_ref()
                .map(|t| ctx.env.class_of(t, ctx.scope).implies(Marker::Copy))
                .unwrap_or(false);
            if !is_copy {
                ctx.d.push_error(
                    Diagnostic::new(
                        CopyRelaxationCode::IndexOperandNotReading,
                        source,
                        format!(
                            "`take` of non-Copy place '{}' inside `Index` projection: \
                             array indexing must resolve to a non-consuming read",
                            format_place(&place)
                        ),
                    )
                    .in_function(ctx.func_name)
                    .in_block(ctx.block_label),
                );
            }
            *operand = Operand::Copy(place.clone());
            add_value_demand(demand, &place);
        }
    }
}

fn relax_operand(
    operand: &mut Operand,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    source: SourceInfo,
) {
    // First, recurse into any `take` nested inside the operand's own
    // place (dynamic-index case: `move a[take i]`).
    match operand {
        Operand::Copy(p) | Operand::Move(p) | Operand::Take(p) => {
            relax_place_index_operands(p, demand, ctx, source);
        }
        Operand::Const(_) => {}
    }

    // Explicit `move` / `copy` are authoritative — never rewritten.
    if !matches!(operand, Operand::Take(_)) {
        match operand {
            Operand::Copy(p) => add_value_demand(demand, p),
            Operand::Move(p) => {
                kill_future_demand(demand, p);
                add_value_demand(demand, p);
            }
            Operand::Take(_) | Operand::Const(_) => {}
        }
        return;
    }

    // Now resolve `Take`. Extract place, classify, decide.
    let place = match operand {
        Operand::Take(p) => p.clone(),
        _ => unreachable!(),
    };

    let mandatory_copy = requires_copy_semantics(&place, ctx.env, ctx.locals);
    let ty = ctx.env.type_of_place(&place, ctx.locals).ok();
    let class = ty
        .as_ref()
        .map(|t| ctx.env.class_of(t, ctx.scope))
        .unwrap_or_default();
    let is_copy = class.implies(Marker::Copy);
    let is_move = class.implies(Marker::Move);

    let resolved = if mandatory_copy {
        // Move is semantically invalid here (shared-ref crossing or
        // dynamic index). Copy is the only legal resolution — emit a
        // user error if the type isn't Copy.
        if !is_copy {
            push_relax_error(
                ctx,
                source,
                CopyRelaxationCode::MandatoryCopyNonCopy,
                format!(
                    "cannot resolve `take` of '{}' to `copy`: path crosses a shared \
                     reference or dynamic-index projection and the type is not Copy",
                    format_place(&place)
                ),
            );
        }
        Operand::Copy(place.clone())
    } else {
        // Stable owned or all-exclusive-deref path. Prefer `copy` when a
        // later use demands the value and the type supports it; otherwise
        // fall through to `move` (or `copy` when only Copy is available).
        let has_demand = demand
            .values
            .iter()
            .any(|needed| demand_preserves(&place, needed))
            || demand
                .accesses
                .iter()
                .any(|needed| demand_preserves(&place, needed));
        if has_demand && is_copy {
            Operand::Copy(place.clone())
        } else if is_move {
            Operand::Move(place.clone())
        } else if is_copy {
            Operand::Copy(place.clone())
        } else {
            // Silent recovery. The pre-elaboration substructural check
            // owns the "neither Copy nor Move" diagnostic (its
            // `ClassMarker::CopyOrMove` case fires on the same
            // condition), so emitting again here would just duplicate.
            // Type-query failures also land here and are already
            // reported by earlier passes.
            Operand::Copy(place.clone())
        }
    };

    let is_now_move = matches!(resolved, Operand::Move(_));
    *operand = resolved;
    if is_now_move {
        kill_future_demand(demand, &place);
    }
    add_value_demand(demand, &place);
}

/// True when the path can only be read (not consumed) at this point:
/// - crosses a shared reference (`&T`) anywhere, or
/// - contains a dynamic index (identity not stable across program
///   points, so a `move` here would silently lose track of which slot
///   was consumed).
///
/// In either case `move` is either semantically illegal (shared-ref)
/// or would silently lose track of the storage (dynamic index).
/// Resolution must emit `copy`.
///
/// Raw-pointer dereferences are deliberately NOT mandatory-copy: they
/// carry no ownership tracking and the author is already in `unsafe`
/// territory, so `take *p` resolves via the ordinary flexible rule
/// (prefer `move` when the type supports it).
fn requires_copy_semantics(place: &Place, env: &Env, locals: &IndexMap<String, Type>) -> bool {
    match place {
        Place::Var(_) => false,
        Place::Field(inner, _) | Place::Downcast(inner, _) => {
            requires_copy_semantics(inner, env, locals)
        }
        Place::Index(inner, op) => {
            if !matches!(op.as_ref(), Operand::Const(ConstVal::Int { .. })) {
                return true;
            }
            requires_copy_semantics(inner, env, locals)
        }
        Place::Deref(inner) => {
            let boundary_requires_copy = env
                .type_of_place(inner, locals)
                .is_ok_and(|ty| matches!(&ty.kind, TypeKind::Ref(RefKind::Shared, _, _)));
            boundary_requires_copy || requires_copy_semantics(inner, env, locals)
        }
    }
}

fn push_relax_error(ctx: &mut RelaxCtx, source: SourceInfo, code: CopyRelaxationCode, msg: String) {
    ctx.d.push_error(
        Diagnostic::new(code, source, msg)
            .in_function(ctx.func_name)
            .in_block(ctx.block_label),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::parser::Parser;

    fn elaborate_source(source: &str) -> Program {
        let mut program = Parser::parse_or_panic(source);
        let (env, errors) = Env::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");
        let mut d = Diagnostics::default();
        elaborate(&mut program, &env, &mut d);
        assert!(
            !d.has_errors(),
            "unexpected relaxation diagnostics: {:?}",
            d.errors_str(),
        );
        program
    }

    fn call_arg<'a>(program: &'a Program, function: &str, statement: usize) -> &'a Operand {
        let func = program
            .functions()
            .find(|func| func.meta.name == function)
            .unwrap();
        let body = func.body.as_ref().unwrap();
        let StatementKind::Call(_, args) = &body.blocks[0].statements[statement].kind else {
            panic!("expected call statement");
        };
        &args[0]
    }

    fn call_arg_in_block<'a>(
        program: &'a Program,
        function: &str,
        block_label: &str,
        statement: usize,
    ) -> &'a Operand {
        let func = program
            .functions()
            .find(|func| func.meta.name == function)
            .unwrap();
        let block = func
            .body
            .as_ref()
            .unwrap()
            .blocks
            .iter()
            .find(|block| block.label == block_label)
            .unwrap();
        let StatementKind::Call(_, args) = &block.statements[statement].kind else {
            panic!("expected call statement");
        };
        &args[0]
    }

    #[test]
    fn relaxes_an_earlier_copyable_move_but_keeps_the_last_move() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(x: i64) {
              entry:
                call consume(take x);
                call consume(take x);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
        assert!(matches!(call_arg(&program, "f", 1), Operand::Move(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn relaxes_an_earlier_move_through_an_exclusive_reference() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut i64) {
              entry:
                call consume(take r.*);
                call consume(take r.*);
                r.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 1), Operand::Move(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn resolves_take_through_a_shared_reference_to_copy() {
        // Shared-reference crossings are mandatory-copy: `move r.*`
        // through `&T` is illegal, so a `take` on that path must
        // specialize to `copy`. For a Copy pointee this succeeds
        // silently; a non-Copy pointee would produce a user error.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &i64) {
              entry:
                call consume(take r.*);
                call consume(copy r.*);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn relaxes_through_arbitrarily_nested_exclusive_references() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut &mut i64) {
              entry:
                call consume(take r.*.*.*);
                call consume(take r.*.*.*);
                r.*.*.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*.*.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 1), Operand::Move(place) if format_place(place) == "r.*.*.*")
        );
    }

    #[test]
    fn shared_reference_anywhere_in_a_nested_path_forces_copy() {
        // Any shared-reference crossing in the deref chain makes the
        // whole path mandatory-copy: `move` through it would be
        // illegal regardless of which end the `&T` sits on.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn shared_inner(r: &mut &i64) {
              entry:
                call consume(take r.*.*);
                call consume(copy r.*.*);
                return
            }
            fn shared_outer(r: &&mut i64) {
              entry:
                call consume(take r.*.*);
                call consume(copy r.*.*);
                return
            }
            ",
        );
        assert!(matches!(
            call_arg(&program, "shared_inner", 0),
            Operand::Copy(_)
        ));
        assert!(matches!(
            call_arg(&program, "shared_outer", 0),
            Operand::Copy(_)
        ));
    }

    #[test]
    fn replacing_an_intermediate_reference_kills_nested_demand() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64, replacement: &mut i64) {
              entry:
                call consume(take r.*.*);
                r.* = take replacement;
                call consume(take r.*.*);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn relaxes_nested_paths_with_projections_between_dereferences() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            struct Link: Move { next: &mut Pair }
            enum Choice: Move { A: &mut i64 B: unit }
            extern fn consume(x: i64);
            fn field(r: &mut Link) {
              entry:
                call consume(take r.*.next.*.left);
                call consume(take r.*.next.*.left);
                r.*.next.*.left = 0;
                return
            }
            fn index(r: &mut [&mut i64; 2]) {
              entry:
                call consume(take r.*[0].*);
                call consume(take r.*[0].*);
                r.*[0].* = 0;
                return
            }
            fn downcast(r: &mut Choice) {
              entry:
                call consume(take r.* as A.*);
                call consume(take r.* as A.*);
                r.* as A.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "field", 0), Operand::Copy(place) if format_place(place) == "r.*.next.*.left")
        );
        assert!(
            matches!(call_arg(&program, "index", 0), Operand::Copy(place) if format_place(place) == "r.*[0].*")
        );
        assert!(
            matches!(call_arg(&program, "downcast", 0), Operand::Copy(place) if format_place(place) == "r.* as A.*")
        );
    }

    #[test]
    fn shallower_borrower_use_does_not_preserve_a_deeper_pointee() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            extern fn consume_ref(r: &mut i64);
            fn f(r: &mut &mut i64) {
              entry:
                call consume(take r.*.*);
                call consume_ref(take r.*);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn raw_pointer_dereferences_resolve_to_move_or_copy_by_type() {
        // Raw pointers are unsafe and carry no ownership tracking. The
        // pass does not treat a raw-pointer boundary as mandatory-copy
        // (unlike shared references and dynamic indices) — the author
        // is already inside `unsafe`. `take` on such a path resolves via
        // the ordinary flexible rule: `move` when the type supports it,
        // downgraded to `copy` if a later use demands the value.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(p: **i64) {
              entry:
                call consume(take p.*.*);
                call consume(copy p.*.*);
                return
            }
            ",
        );
        // Later `copy p.*.*` demands the pointee, so the earlier `take`
        // downgrades to `copy` to preserve it.
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(_)));
    }

    #[test]
    fn borrower_use_alone_does_not_preserve_its_pointee() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &drop i64) {
              s: &drop i64;
              entry:
                call consume(take r.*);
                s = take r;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Move(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn dereference_write_kills_old_pointee_demand() {
        // The write at index 1 kills demand for `r.*` backward from the
        // second call and from `r`'s post-Init obligation at Return, so
        // the earlier `take r.*` at index 0 sees no demand and stays as
        // move. The final `take r.*` at index 2 still relaxes to `copy`
        // — otherwise `r.*` would be Uninit at Return, violating the
        // &mut obligation.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut i64) {
              entry:
                call consume(take r.*);
                r.* = 1;
                call consume(take r.*);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Move(place) if format_place(place) == "r.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 2), Operand::Copy(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn relaxes_the_same_projected_pointee_but_not_a_sibling() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn same(r: &mut Pair) {
              entry:
                call consume(take r.*.left);
                call consume(take r.*.left);
                r.*.left = 0;
                return
            }
            fn sibling(r: &mut Pair) {
              entry:
                call consume(take r.*.left);
                call consume(take r.*.right);
                r.*.left = 0;
                r.*.right = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "same", 0), Operand::Copy(place) if format_place(place) == "r.*.left")
        );
        assert!(
            matches!(call_arg(&program, "sibling", 0), Operand::Move(place) if format_place(place) == "r.*.left")
        );
    }

    #[test]
    fn relaxes_a_constant_pointee_index_and_forces_copy_on_dynamic_index() {
        // Constant-index paths participate in the ordinary relaxation
        // decision — the demand from the second use downgrades the first
        // to `copy`. Dynamic-index paths lack stable identity across
        // program points, so they're mandatory-copy: resolving to `move`
        // would let repeated `move a[i]` slip through as if operating on
        // distinct slots.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn constant(r: &mut [i64; 2]) {
              entry:
                call consume(take r.*[0]);
                call consume(take r.*[0]);
                r.*[0] = 0;
                return
            }
            fn dynamic(r: &mut [i64; 2], i: i64) {
              entry:
                call consume(take r.*[copy i]);
                call consume(take r.*[copy i]);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "constant", 0), Operand::Copy(place) if format_place(place) == "r.*[0]")
        );
        assert!(matches!(call_arg(&program, "dynamic", 0), Operand::Copy(_)));
    }

    #[test]
    fn relaxes_a_downcast_pointee_projection() {
        let program = elaborate_source(
            "
            enum Choice: Copy + Drop { A: i64 B: i64 }
            extern fn consume(x: i64);
            fn f(r: &mut Choice) {
              entry:
                call consume(take r.* as A);
                call consume(take r.* as A);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.* as A")
        );
    }

    #[test]
    fn relaxes_a_projected_pointee_on_a_successor_path() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn f(r: &mut Pair, b: bool) {
              entry:
                call consume(take r.*.left);
                branch(copy b) [true: use_left, false: done]
              use_left:
                call consume(take r.*.left);
                r.*.left = 0;
                goto done
              done:
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*.left")
        );
    }

    #[test]
    fn preserves_a_move_when_only_a_sibling_field_is_later_used() {
        let program = elaborate_source(
            "
            struct Pair: Move { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn f(p: Pair) {
              entry:
                call consume(take p.left);
                call consume(take p.right);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn relaxes_a_move_needed_on_a_successor_path() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(b: bool, x: i64) {
              entry:
                call consume(take x);
                branch(copy b) [true: use_x, false: done]
              use_x:
                call consume(take x);
                goto done
              done:
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn relaxes_a_move_needed_on_a_loop_back_edge() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(b: bool, x: i64) {
              entry:
                goto loop
              loop:
                call consume(take x);
                branch(copy b) [true: loop, false: done]
              done:
                return
            }
            ",
        );
        assert!(matches!(
            call_arg_in_block(&program, "f", "loop", 0),
            Operand::Copy(Place::Var(x)) if x == "x"
        ));
    }

    #[test]
    fn resolves_take_inside_a_non_exiting_loop() {
        // Backward dataflow must process every block, not just those
        // reachable from an exit terminator. `entry` here loops forever;
        // under a naive seed-terminals-only worklist it never gets
        // processed and the `take x` stays unresolved. With every block
        // seeded at bottom, the fixpoint reaches `entry` and — because
        // the back-edge itself demands `x` on the next iteration — the
        // read resolves to `copy`.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(x: i64) {
              entry:
                call consume(take x);
                goto entry
            }
            ",
        );
        assert!(matches!(
            call_arg_in_block(&program, "f", "entry", 0),
            Operand::Copy(Place::Var(x)) if x == "x"
        ));
    }

    #[test]
    fn uses_declared_copy_class_for_custom_types() {
        let program = elaborate_source(
            "
            struct Token: Copy + Drop { value: i64 }
            extern fn consume(x: Token);
            fn f(x: Token) {
              entry:
                call consume(take x);
                call consume(take x);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn does_not_copy_an_exclusive_reference() {
        let program = elaborate_source(
            "
            extern fn consume(r: &mut i64);
            fn f(r: &mut i64) {
              entry:
                call consume(take r);
                call consume(take r);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(r)) if r == "r"));
    }

    #[test]
    fn does_not_preserve_a_value_for_an_out_borrow() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            extern fn finish(r: &out i64);
            fn f(x: i64) {
              r: &out i64;
              entry:
                call consume(take x);
                r = &out x;
                r.* = 1;
                call finish(take r);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn out_borrow_reinitialization_kills_loop_carried_demand() {
        let program = elaborate_source(
            "
            extern fn fill(r: &out i64);
            extern fn consume(x: i64);
            fn f(again: bool, x: i64) {
              r: &out i64;
              entry:
                goto loop
              loop:
                r = &out x;
                call fill(take r);
                call consume(take x);
                branch(copy again) [true: loop, false: done]
              done:
                return
            }
            ",
        );
        assert!(matches!(
            call_arg_in_block(&program, "f", "loop", 2),
            Operand::Move(Place::Var(x)) if x == "x"
        ));
    }

    #[test]
    fn out_borrow_of_a_field_blocks_aggregate_preservation() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn take_pair(p: Pair);
            fn f(p: Pair) {
              r: &out i64;
              entry:
                call take_pair(take p);
                r = &out p.left;
                r.* = 1;
                call take_pair(take p);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(p)) if p == "p"));
    }

    #[test]
    fn elaboration_is_idempotent() {
        let mut program = Parser::parse_or_panic(
            "
            extern fn consume(x: i64);
            fn f(x: i64) {
              entry:
                call consume(take x);
                call consume(take x);
                return
            }
            ",
        );
        let (env, errors) = Env::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");

        let mut d = Diagnostics::default();
        elaborate(&mut program, &env, &mut d);
        let once = program.clone();
        elaborate(&mut program, &env, &mut d);
        assert_eq!(program, once);
    }
}
