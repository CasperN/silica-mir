//! Copy relaxation: resolve each `take` operand to `move`, `copy`, an
//! `AutoClone::clone` call, or a bounded reborrow.
//!
//! HLL lowers ordinary value reads as `Operand::Take`. This pass picks a
//! concrete resolution per operand from the four modes:
//! - `move place` — last-use consumption.
//! - `copy place` — trivial preservation for `Copy` types.
//! - `AutoClone` — call `AutoClone::clone(&place)` into a fresh local for
//!   types that opt into non-trivial preservation.
//! - Reborrow — mint `$tmp = &kind place.*` and pass `move $tmp`, so an
//!   exclusive reference (`&mut`, `&out`, `&drop`, `&uninit`) can be
//!   preserved without a trivial copy.
//!
//! Explicit `move` and `copy` in the input are authoritative and never
//! rewritten, so hand-written `.sim` fixtures can pin exact operand kinds.
//!
//! The pass runs before NLL elaboration. Specializing `take` changes whether
//! the read closes a borrower loan, so NLL must compute liveness from the
//! resolved program.
//!
//! The analysis is backward, with separate may-demand sets for values and
//! the owned bases needed to access them. At a CFG join the sets union: an
//! operand must be preserved if either successor can still use it.
//!
//! Preservation is required whenever the place is inside a borrow (any ref
//! kind) or a dynamic index — borrowed storage can't have holes, and a
//! dynamic index has no stable identity to track partial consumption against.
//! When preservation is required and every non-`move` resolution fails,
//! resolution falls through to `move` UNLESS the path crosses a shared
//! reference or dynamic index (`crosses_shared_boundary`), where `move` is
//! semantically illegal and relaxation instead emits
//! `RELAX-MandatoryPreservationUnavailable`.
//!
//! Raw-pointer dereferences are deliberately not preservation-triggering:
//! they carry no ownership tracking and the author is already in `unsafe`
//! territory, so `take *p` resolves via the ordinary flexible rule.
//!
//! `Index` operand position is a non-consuming read: `take` there is forced
//! to `copy` and `move` is `RELAX-IndexOperandNotReading`. This keeps
//! downstream analyses from having to recurse into `Index` projections.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction};
use crate::mir::env::{IndexedProgram, LocalEnv};
use crate::mir::helpers::*;
use crate::mir::place_state::analysis::RefState;
use indexmap::IndexMap;
use std::collections::BTreeSet;
use std::ops::ControlFlow;

/// User-facing errors emitted by the `take` resolver. Distinct from
/// the pre-elaboration substructural check (which flags places whose
/// type supports neither `Copy` nor `Move`): these fire when the
/// resolution decision itself has no valid target — for example, a
/// `take` on a Move-only value through a shared-reference boundary,
/// where the boundary demands preservation but neither `Copy` nor an
/// applicable `AutoClone` implementation is available.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyRelaxationCode {
    /// The path crosses a shared reference or dynamic-index projection, so
    /// moving is illegal, but neither `Copy` nor `AutoClone` can preserve it.
    MandatoryPreservationUnavailable,
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
pub fn elaborate(program: &mut IndexedProgram, d: &mut Diagnostics) {
    program.visit_function_bodies_mut(|env, function, body| {
        elaborate_function(function, body, env, d)
    });
}

/// Post-elaboration invariant: no `Take` operand survives. If any do,
/// push a single internal-error diagnostic naming the first offender
/// (with a count so a broken pass doesn't spam per-operand). Downstream
/// passes assume this invariant and `unreachable!` on `Take`, so callers
/// must skip elaboration/checking when this returns anything.
pub fn verify_no_take(program: &IndexedProgram, d: &mut crate::diagnostics::Diagnostics) {
    let mut first: Option<SourceInfo> = None;
    let mut count = 0usize;
    program.function_bodies(|_env, _func, body| {
        for block in &body.blocks {
            for stmt in &block.statements {
                scan_statement_for_take(stmt, &mut first, &mut count);
            }
            scan_terminator_for_take(&block.terminator, &mut first, &mut count);
        }
    });
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

/// Recurse into a place, visiting any operand nested inside an `Index` projection.
fn walk_place_index_operands(place: &Place, visit: &mut dyn FnMut(&Operand)) {
    match place {
        Place::Var(_) => {}
        Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => {
            walk_place_index_operands(inner, visit);
        }
        Place::Index(inner, op) => {
            walk_place_index_operands(inner, visit);
            visit(op);
        }
    }
}

/// Recurse into a place, visiting and potentially mutating any operand nested inside an `Index` projection.
fn walk_place_index_operands_mut(place: &mut Place, visit: &mut dyn FnMut(&mut Operand)) {
    match place {
        Place::Var(_) => {}
        Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => {
            walk_place_index_operands_mut(inner, visit);
        }
        Place::Index(inner, op) => {
            walk_place_index_operands_mut(inner, visit);
            visit(op);
        }
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
    walk_place_index_operands(place, &mut |op| scan_operand_for_take(op, source, first, count));
}

fn elaborate_function(
    func: &Function,
    body: &mut FunctionBody,
    env: LocalEnv<'_>,
    d: &mut Diagnostics,
) {
    let mut locals = body.locals_map(&func.params);
    let return_obligations = collect_return_obligations(func, body);
    let func_name = env.fully_qualified_fn_name(&func.meta.name);
    if body.blocks.is_empty() {
        return;
    }

    let analysis = MovePathDemand {
        return_obligations: &return_obligations,
    };
    let exits = dataflow::run(&analysis, body);
    let mut blocks = std::mem::take(&mut body.blocks);
    {
        let mut local_allocator = body.local_allocator(&func.params, "$clone_");
        for block in &mut blocks {
            let Some(exit_demand) = exits.get(&block.label) else {
                continue;
            };
            let mut demand = exit_demand.clone();
            analysis.transfer_terminator(&mut demand, &block.terminator);
            let block_label = block.label.clone();
            let mut ctx = RelaxCtx {
                env,
                locals: &mut locals,
                body,
                local_allocator: &mut local_allocator,
                d,
                func_name: &func_name,
                block_label: &block_label,
            };
            let mut terminator_prefix = Vec::new();
            relax_terminator(
                &mut block.terminator,
                &mut demand,
                &mut ctx,
                &mut terminator_prefix,
            );

            let mut rewritten = Vec::new();
            for mut stmt in std::mem::take(&mut block.statements).into_iter().rev() {
                let mut prefix = Vec::new();
                relax_statement(&mut stmt, &mut demand, &mut ctx, &mut prefix);
                rewritten.push((prefix, stmt));
            }
            for (prefix, stmt) in rewritten.into_iter().rev() {
                block.statements.extend(prefix);
                block.statements.push(stmt);
            }
            block.statements.append(&mut terminator_prefix);
        }
    }
    body.blocks = blocks;
}

/// Per-block relaxation context. Bundles the env/locals/scope needed for
/// type queries with the diagnostics sink and the function/block context
/// used when emitting a user-facing error (e.g. `take` of a place that
/// cannot be legally consumed or preserved).
struct RelaxCtx<'env, 'ctx> {
    env: LocalEnv<'env>,
    locals: &'ctx mut IndexMap<String, Type>,
    body: &'ctx mut FunctionBody,
    local_allocator: &'ctx mut LocalAllocator,
    d: &'ctx mut Diagnostics,
    func_name: &'ctx str,
    block_label: &'ctx str,
}

impl RelaxCtx<'_, '_> {
    fn add_local(&mut self, ty: Type, source: SourceInfo) -> Place {
        let place = self
            .local_allocator
            .add_local(self.body, ty.clone(), source);
        let Place::Var(name) = &place else {
            unreachable!("local allocator always returns a variable place");
        };
        self.locals.insert(name.clone(), ty);
        place
    }

    fn auto_clone(&mut self, place: &Place, ty: &Type, source: SourceInfo) -> CloneExpansion {
        let generated_source = SourceInfo::generated(GeneratedKind::CopyRelaxation, source.span());
        let value = self.add_local(ty.clone(), generated_source);
        let recv = self.add_local(shared_ref_ty(ty.clone()), generated_source);
        let out = self.add_local(out_ref_ty(ty.clone()), generated_source);
        let callee = trait_fn_op(
            Instance::bare("AutoClone"),
            ty.clone(),
            Instance::bare("clone"),
        );
        CloneExpansion {
            operand: move_op(value.clone()),
            statements: vec![
                assign_stmt(
                    recv.clone(),
                    ref_rv(RefKind::Shared, place.clone()),
                    generated_source,
                ),
                assign_stmt(out.clone(), ref_rv(RefKind::Out, value), generated_source),
                call_stmt(callee, vec![move_op(recv), move_op(out)], generated_source),
            ],
        }
    }
}

struct CloneExpansion {
    operand: Operand,
    statements: Vec<Statement>,
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
fn collect_return_obligations(func: &Function, body: &FunctionBody) -> BTreeSet<Place> {
    let mut out = BTreeSet::new();
    for param in &func.params {
        collect_post_init_pointees(&var_place(param.name.clone()), &param.ty, &mut out);
    }
    for local in &body.locals {
        collect_post_init_pointees(&var_place(local.name.clone()), &local.ty, &mut out);
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
    walk_place_index_operands(place, &mut |op| transfer_operand_demand(op, demand));
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

fn relax_statement(
    stmt: &mut Statement,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    prefix: &mut Vec<Statement>,
) {
    let source = stmt.source;
    match &mut stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // Nested index operands inside the target place are reads
            // evaluated to project into the target; visit them so any
            // `take` inside gets resolved even if the target itself is
            // just an assignment sink.
            relax_place_index_operands(target, demand, ctx, source);
            kill_future_demand(demand, target);
            relax_rvalue(rvalue, demand, ctx, source, prefix);
            if as_owned_path(target).is_none() {
                add_access_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter_mut().rev() {
                relax_operand(operand, demand, ctx, source, prefix);
            }
            relax_operand(target, demand, ctx, source, prefix);
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

fn relax_terminator(
    term: &mut Terminator,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    prefix: &mut Vec<Statement>,
) {
    let source = term.source;
    match &mut term.kind {
        TerminatorKind::Branch { cond, .. } => relax_operand(cond, demand, ctx, source, prefix),
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

fn relax_rvalue(
    rvalue: &mut RValue,
    demand: &mut Demand,
    ctx: &mut RelaxCtx,
    source: SourceInfo,
    prefix: &mut Vec<Statement>,
) {
    match rvalue {
        RValue::Use(operand)
        | RValue::EnumConstr(_, _, _, operand)
        | RValue::PtrCast(operand, _) => relax_operand(operand, demand, ctx, source, prefix),
        RValue::Ref(kind, place) => {
            relax_place_index_operands(place, demand, ctx, source);
            transfer_ref_demand(kind, place, demand);
        }
        RValue::RawRef(place) => {
            relax_place_index_operands(place, demand, ctx, source);
        }
        RValue::ArrayLit(operands) => {
            for operand in operands.iter_mut().rev() {
                relax_operand(operand, demand, ctx, source, prefix);
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
    walk_place_index_operands_mut(place, &mut |op| resolve_index_operand(op, demand, ctx, source));
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
                .map(|t| ctx.env.class_of(t).implies(Marker::Copy))
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
    prefix: &mut Vec<Statement>,
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

    // Now resolve `Take`. Extract place, decide, apply.
    let place = match operand {
        Operand::Take(p) => p.clone(),
        _ => unreachable!(),
    };

    match analyze_take(&place, demand, ctx.env, ctx.locals) {
        Ok(TakeResolution::Move) => {
            *operand = move_op(place.clone());
            kill_future_demand(demand, &place);
        }
        Ok(TakeResolution::Copy) => {
            *operand = copy_op(place.clone());
        }
        Ok(TakeResolution::AutoClone) => {
            let ty = ctx
                .env
                .type_of_place(&place, ctx.locals)
                .expect("AutoClone resolution implies a known type");
            let expansion = ctx.auto_clone(&place, &ty, source);
            prefix.splice(0..0, expansion.statements);
            *operand = expansion.operand;
        }
        Ok(TakeResolution::Reborrow) => {
            let ty = ctx
                .env
                .type_of_place(&place, ctx.locals)
                .expect("Reborrow resolution implies a known reference type");
            let TypeKind::Ref(kind, _, _) = ty.kind else {
                unreachable!("Reborrow resolution implies a reference type at `place`");
            };
            let generated =
                SourceInfo::generated(GeneratedKind::CopyRelaxation, source.span());
            let temp = ctx.add_local(ty.clone(), generated);
            prefix.push(assign_stmt(
                temp.clone(),
                ref_rv(kind, deref_place(place.clone())),
                generated,
            ));
            *operand = move_op(temp);
        }
        Err(NoPreservationPath) => {
            push_relax_error(
                ctx,
                source,
                CopyRelaxationCode::MandatoryPreservationUnavailable,
                format!(
                    "cannot preserve `take` of '{}': path crosses a shared reference \
                     or dynamic-index projection, and no valid Copy or AutoClone resolution is available",
                    format_place(&place)
                ),
            );
            *operand = copy_op(place.clone());
        }
    }
    add_value_demand(demand, &place);
}

/// A concrete resolution of a `take` operand. Every variant is a valid
/// consumption strategy: transfer it (`Move`), duplicate it trivially
/// (`Copy`), call an `AutoClone` implementation, or mint a bounded
/// reborrow. The consumer builds the reborrow's kind from the place's
/// type — the analyzer doesn't carry it.
enum TakeResolution {
    Move,
    Copy,
    AutoClone,
    Reborrow,
}

/// `analyze_take` failure. Fires when the place must survive the take,
/// no preservation-compatible resolution is available (not `Copy`, not an
/// exclusive reference, no `AutoClone`), and the path crosses a boundary
/// that also forbids `move` (shared reference or dynamic index). The
/// consumer emits the `MandatoryPreservationUnavailable` diagnostic and
/// falls back to `copy` for recovery.
struct NoPreservationPath;

/// Decide how a `take place` should be elaborated. Pure over its inputs.
///
/// Preservation is required when the place is inside a borrow whose
/// pointee-Init obligation demands the aggregate stay whole
/// ([`requires_preservation`]) or when a later program point still reads
/// it. Both triggers funnel to the same resolution table because the
/// choice depends on the type at hand, not on why preservation was
/// required.
fn analyze_take(
    place: &Place,
    demand: &Demand,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> Result<TakeResolution, NoPreservationPath> {
    let ty = env.type_of_place(place, locals).ok();
    let class = ty.as_ref().map(|t| env.class_of(t)).unwrap_or_default();
    let is_copy = class.implies(Marker::Copy);
    let is_move = class.implies(Marker::Move);
    let future_demand = demand
        .values
        .iter()
        .any(|needed| demand_preserves(place, needed))
        || demand
            .accesses
            .iter()
            .any(|needed| demand_preserves(place, needed));
    let must_preserve = requires_preservation(place, env, locals) || future_demand;

    if must_preserve {
        if is_copy {
            return Ok(TakeResolution::Copy);
        }
        if ty.as_ref().is_some_and(is_exclusive_ref) {
            return Ok(TakeResolution::Reborrow);
        }
        if let Some(ty) = &ty {
            if env.has_applicable_trait_impl(&Instance::bare("AutoClone"), ty) {
                return Ok(TakeResolution::AutoClone);
            }
        }
        if crosses_shared_boundary(place, env, locals) {
            return Err(NoPreservationPath);
        }
        // Preservation demanded but nothing above worked; the path allows
        // move, so fall through and let the later leak/obligation check
        // surface any real hole.
    }

    if is_move {
        Ok(TakeResolution::Move)
    } else if is_copy {
        Ok(TakeResolution::Copy)
    } else {
        // Silent recovery. The pre-elaboration substructural check owns the
        // "neither Copy nor Move" diagnostic; emitting again here would just
        // duplicate. Type-query failures land here and were already reported
        // by earlier passes.
        Ok(TakeResolution::Copy)
    }
}

/// True when `ty` is an exclusive reference (`&mut`, `&out`, `&drop`,
/// `&uninit`). Shared references are already `Copy` and don't need
/// reborrow elaboration.
fn is_exclusive_ref(ty: &Type) -> bool {
    matches!(
        &ty.kind,
        TypeKind::Ref(RefKind::Mut | RefKind::Out | RefKind::Drop | RefKind::Uninit, _, _),
    )
}


/// True when the enclosing storage of `place` obligates its contents to
/// remain intact across the `take`. Preservation is governed by the
/// innermost enclosing reference — the first `Deref` encountered walking
/// from the leaf outward — because that reference's contract is the
/// nearest one a leaf move can violate. If that reference is `&T` or
/// `&mut T`, its pointee must stay `Init` at expiry, so consuming a
/// field creates a hole the obligation check would reject. `&out`,
/// `&drop`, and `&uninit` are excluded: their obligations are satisfied
/// by the pointee ending `Uninit` (or by moving out to enable that), so
/// `take` there must stay flexible enough to resolve to `move`.
///
/// Outer references above the innermost `Deref` don't add a constraint
/// on the leaf: they govern their own immediate pointee (a reference
/// value at that layer), whose Init-ness isn't affected by moves at a
/// deeper layer.
///
/// A dynamic index anywhere between the leaf and the innermost `Deref`
/// (or, for an owned path, anywhere in the path) also triggers
/// preservation — the index has no stable identity to track partial
/// consumption against.
///
/// Raw-pointer dereferences are deliberately not preservation-triggering:
/// they carry no ownership tracking and the author is already in `unsafe`
/// territory, so `take *p` resolves via the ordinary flexible rule.
fn requires_preservation(
    place: &Place,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> bool {
    walk_projection(place, &|receiver| {
        ControlFlow::Break(env.type_of_place(receiver, locals).is_ok_and(|ty| {
            matches!(
                &ty.kind,
                TypeKind::Ref(RefKind::Shared | RefKind::Mut, _, _)
            )
        }))
    })
}

/// True when the path crosses a boundary where `move` is not a legal
/// operation — a shared reference (`&T`) or a dynamic index.
fn crosses_shared_boundary(
    place: &Place,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> bool {
    walk_projection(place, &|receiver| {
        let is_shared = env
            .type_of_place(receiver, locals)
            .is_ok_and(|ty| matches!(&ty.kind, TypeKind::Ref(RefKind::Shared, _, _)));
        if is_shared {
            ControlFlow::Break(true)
        } else {
            ControlFlow::Continue(())
        }
    })
}

/// Walk a place bottom-up (leaf to root), returning `true` when the
/// path crosses a boundary of interest. Var reaches root with no hit;
/// Field/Downcast recurse; a dynamic Index short-circuits to true and a
/// constant Index recurses. At each `Deref`, `at_deref(receiver)` decides:
/// `Break(v)` stops with that verdict, `Continue(())` recurses past.
fn walk_projection<F>(place: &Place, at_deref: &F) -> bool
where
    F: Fn(&Place) -> ControlFlow<bool>,
{
    match place {
        Place::Var(_) => false,
        Place::Field(inner, _) | Place::Downcast(inner, _) => walk_projection(inner, at_deref),
        Place::Index(inner, op) => {
            !matches!(op.as_ref(), Operand::Const(ConstVal::Int { .. }))
                || walk_projection(inner, at_deref)
        }
        Place::Deref(inner) => match at_deref(inner) {
            ControlFlow::Break(v) => v,
            ControlFlow::Continue(()) => walk_projection(inner, at_deref),
        },
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
    use crate::mir::pretty_print::pretty_print;

    fn elaborate_source(source: &str) -> IndexedProgram {
        let parsed = Parser::parse_or_panic(source);
        let (mut program, errors) = IndexedProgram::build(&parsed);
        assert!(errors.is_empty(), "environment errors: {errors:?}");
        let mut d = Diagnostics::default();
        elaborate(&mut program, &mut d);
        assert!(
            !d.has_errors(),
            "unexpected relaxation diagnostics: {:?}",
            d.errors_str(),
        );
        program
    }

    fn call_arg<'a>(program: &'a IndexedProgram, function: &str, statement: usize) -> &'a Operand {
        let func = program.functions.get(function).unwrap();
        let body = func.body.as_ref().unwrap();
        let StatementKind::Call(_, args) = &body.blocks[0].statements[statement].kind else {
            panic!("expected call statement");
        };
        &args[0]
    }

    fn call_arg_in_block<'a>(
        program: &'a IndexedProgram,
        function: &str,
        block_label: &str,
        statement: usize,
    ) -> &'a Operand {
        let func = program.functions.get(function).unwrap();
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
    fn preserves_every_take_through_an_exclusive_reference() {
        // `r.*` under a `&mut` deref forces preservation on every take,
        // even the last one before an in-place write. Drop-elab handles
        // the subsequent `r.* = 0` by inserting a drop.
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
            matches!(call_arg(&program, "f", 1), Operand::Copy(place) if format_place(place) == "r.*")
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
    fn preserves_takes_through_arbitrarily_nested_exclusive_references() {
        // The innermost `&mut` deref (closest to the leaf) governs
        // preservation. Every `take r.*.*.*` resolves to `copy` because
        // the deepest boundary is a `&mut` and the leaf type is `Copy`.
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
            matches!(call_arg(&program, "f", 1), Operand::Copy(place) if format_place(place) == "r.*.*.*")
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
    fn preservation_holds_across_reference_replacement() {
        // Even though the intermediate `r.* = take replacement` kills
        // future demand on the old pointee, `r.*.*` sits under a `&mut`
        // deref boundary and the leaf is `Copy`, so both reads resolve
        // to `copy`.
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
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(_)));
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
    fn deeper_pointee_preserved_via_innermost_boundary() {
        // `r.*.*` sits under the innermost `&mut` deref, so preservation
        // applies to it independently of any shallower use of `r.*`.
        // The consume of `r.*` at statement 1 does not remove the
        // preservation demand on `r.*.*` — that demand comes from the
        // boundary, not from a future read.
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
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(_)));
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
    fn deref_of_mut_ref_pointee_preserves_across_calls() {
        // `r.*` is inside a `&mut` deref, so preservation is required
        // for both reads. The pointee is `Copy`, so both `take r.*`
        // resolve to `copy`. Drop-elab inserts a `drop r.*` before the
        // intermediate `r.* = 1` to satisfy the write precondition.
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
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 2), Operand::Copy(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn preserves_projected_pointee_fields_uniformly() {
        // Both `r.*.left` and `r.*.right` sit under the `&mut Pair`
        // boundary and are `Copy`, so every take resolves to `copy`
        // whether the field pattern repeats or diverges.
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
            matches!(call_arg(&program, "sibling", 0), Operand::Copy(place) if format_place(place) == "r.*.left")
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
    fn reborrows_an_exclusive_reference_with_future_demand() {
        // `&mut i64` is not `Copy`, so preserving `r` across two calls
        // resolves via reborrow: each call gets a fresh bounded borrow
        // sourced from `*r`, and `r` itself remains bound between them.
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
        // The reborrow prefix pushes the first call to statement index 1.
        assert!(matches!(
            call_arg(&program, "f", 1),
            Operand::Move(Place::Var(name)) if name.starts_with('$')
        ));
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
        // The reborrow prefix for `take r` inserts an Assign at
        // statement 1, pushing the `call consume(take x)` from index 2
        // to index 3. `x` has demand carried through the loop back-edge
        // but the `&out x` reinitialization on each iteration kills it,
        // so the take resolves to `move` on the copy-only `i64` path.
        assert!(matches!(
            call_arg_in_block(&program, "f", "loop", 3),
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
        let parsed = Parser::parse_or_panic(
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
        let (mut program, errors) = IndexedProgram::build(&parsed);
        assert!(errors.is_empty(), "environment errors: {errors:?}");

        let mut d = Diagnostics::default();
        elaborate(&mut program, &mut d);
        let once = pretty_print(&program);
        elaborate(&mut program, &mut d);
        assert_eq!(pretty_print(&program), once);
    }

    #[test]
    fn autoclone_elaboration_is_idempotent() {
        let mut program = elaborate_source(
            "
            struct Value: Move { field: i64 }
            impl AutoClone for Value {
              fn clone(recv: &Value, out: &out Value) {
                entry:
                  out.*.field = copy recv.*.field;
                  return
              }
            }
            extern fn consume(x: Value);
            fn f(x: Value) {
              entry:
                call consume(take x);
                call consume(take x);
                return
            }
            ",
        );
        let once = pretty_print(&program);
        let mut d = Diagnostics::default();
        elaborate(&mut program, &mut d);
        assert!(
            !d.has_errors(),
            "unexpected diagnostics: {:?}",
            d.errors_str()
        );
        assert_eq!(pretty_print(&program), once);
    }
}
