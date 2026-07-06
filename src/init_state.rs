//! Initialization-state dataflow for local variables.
//!
//! Detects: use of uninitialized locals, use of moved-out locals, use where
//! the init state is inconsistent across control-flow paths, and use of a
//! partially-initialized struct.
//!
//! State per root Var is a small lattice: `NeverInit | Moved | Init |
//! Partial(map) | Diverged`. `Partial(map)` records per-field state for
//! struct-typed places; nested Partials are permitted so `p.q.r = ...`
//! refines the state of `p.q.r` specifically. Canonicalization collapses a
//! Partial whose fields are all in the same simple state.
//!
//! Deferred to follow-ups:
//!   * substructural-class-driven weakening at joins and leak check at
//!     `return`,
//!   * borrow init preconditions (`&out` requires uninit, etc.) and
//!     freeze/thaw state.
//!
//! Paths through `Deref` are not tracked (we don't follow references here).
//! Downcast-in-move sets the whole enum to `Moved` (enum atomicity, per
//! README). Downcast-in-write does not change enum state.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::push_error;
use crate::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::{BTreeMap, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InitState {
    NeverInit,
    Moved,
    Init,
    /// Per-field state for a struct. Field list is complete when this
    /// variant is constructed. Nested Partials permitted for struct fields.
    Partial(BTreeMap<String, InitState>),
    /// Predecessors disagreed on the state at some CFG join.
    Diverged,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RefCur { Init, Uninit }

/// Per-reference-variable state: the current and (post-expiry) required
/// state of the pointee. Only tracked for exclusive reference kinds (`&mut`,
/// `&out`, `&drop`, `&uninit`). Shared references (`&T`) don't carry an
/// obligation — they're `Copy Drop`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RefState {
    pub cur: RefCur,
    pub post: RefCur,
}

impl RefState {
    /// The (cur, post) at borrow creation for a given ref kind. Returns
    /// `None` for shared borrows (which don't carry an obligation).
    pub fn from_kind(kind: &RefKind) -> Option<Self> {
        match kind {
            RefKind::Shared => None,
            RefKind::Mut    => Some(RefState { cur: RefCur::Init,   post: RefCur::Init }),
            RefKind::Out    => Some(RefState { cur: RefCur::Uninit, post: RefCur::Init }),
            RefKind::Drop   => Some(RefState { cur: RefCur::Init,   post: RefCur::Uninit }),
            RefKind::Uninit => Some(RefState { cur: RefCur::Uninit, post: RefCur::Uninit }),
        }
    }

    pub fn obligation_fulfilled(&self) -> bool {
        self.cur == self.post
    }
}

/// State at a single program point.
///
/// - `locals`: init state per root Var, potentially projecting through
///   struct fields and enum downcasts.
/// - `refs`: the (cur, post) obligation for each ref-typed Var that is
///   currently `Init`. Absent when the ref var is not Init, is shared,
///   or has been consumed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PointState {
    pub locals: IndexMap<String, InitState>,
    pub refs: IndexMap<String, RefState>,
}

struct Ctx<'a> {
    env: &'a Env,
    locals: &'a IndexMap<String, Type>,
}

// ---------- Type lookups ----------

fn struct_fields_of<'a>(ty: &Type, env: &'a Env) -> Option<&'a [StructField]> {
    let Type::Custom(name) = ty else { return None; };
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => Some(&s.fields),
        _ => None,
    }
}

fn enum_variant_payload_ty(ty: &Type, variant: &str, env: &Env) -> Option<Type> {
    let Type::Custom(name) = ty else { return None; };
    match env.types.get(name) {
        Some(TypeDecl::Enum(e)) => e.variants.iter()
            .find(|v| v.name == variant)
            .map(|v| v.ty.clone()),
        _ => None,
    }
}

// ---------- Canonicalization ----------

/// If a `Partial` has all fields at the same simple (non-Partial) state,
/// collapse to that state. Applied recursively to nested Partials.
fn canonicalize(state: InitState) -> InitState {
    if let InitState::Partial(mut m) = state {
        for v in m.values_mut() {
            let taken = std::mem::replace(v, InitState::NeverInit);
            *v = canonicalize(taken);
        }
        if m.is_empty() {
            return InitState::Init;
        }
        let first = m.values().next().unwrap().clone();
        let uniform = m.values().all(|v| *v == first);
        if uniform && !matches!(first, InitState::Partial(_)) {
            return first;
        }
        InitState::Partial(m)
    } else {
        state
    }
}

// ---------- Expansion ----------

/// Convert a uniform state to a Partial map with each of `fields` set to a
/// clone of the original state. Used when a field-refining transition needs
/// to see per-field granularity.
fn expand_uniform(state: &InitState, fields: &[StructField]) -> BTreeMap<String, InitState> {
    fields
        .iter()
        .map(|f| (f.name.clone(), state.clone()))
        .collect()
}

// ---------- Joins ----------

fn join_state(a: &InitState, b: &InitState) -> InitState {
    if a == b {
        return a.clone();
    }
    // Try to join field-wise when at least one side is Partial.
    match (a, b) {
        (InitState::Partial(ma), InitState::Partial(mb)) => {
            join_partials(ma, mb)
        }
        (InitState::Partial(ma), other) => {
            let mb = expand_from_partial_keys(other, ma);
            join_partials(ma, &mb)
        }
        (other, InitState::Partial(mb)) => {
            let ma = expand_from_partial_keys(other, mb);
            join_partials(&ma, mb)
        }
        _ => InitState::Diverged,
    }
}

fn expand_from_partial_keys(
    state: &InitState,
    template: &BTreeMap<String, InitState>,
) -> BTreeMap<String, InitState> {
    template
        .keys()
        .map(|k| (k.clone(), state.clone()))
        .collect()
}

fn join_partials(
    ma: &BTreeMap<String, InitState>,
    mb: &BTreeMap<String, InitState>,
) -> InitState {
    let mut out = BTreeMap::new();
    for (k, va) in ma {
        let vb = mb.get(k).cloned().unwrap_or(InitState::NeverInit);
        out.insert(k.clone(), join_state(va, &vb));
    }
    for (k, vb) in mb {
        if !ma.contains_key(k) {
            out.insert(k.clone(), vb.clone());
        }
    }
    canonicalize(InitState::Partial(out))
}

fn join_point(a: &PointState, b: &PointState) -> PointState {
    let locals: IndexMap<String, InitState> = a.locals.iter()
        .map(|(name, sa)| {
            let sb = b.locals.get(name).cloned().unwrap_or(InitState::NeverInit);
            (name.clone(), join_state(sa, &sb))
        })
        .collect();
    // Refs: keep only entries that agree exactly on both sides. Disagreement
    // is treated as "not currently bound" for the joined point — subsequent
    // uses will see no ref state and behave conservatively.
    let mut refs: IndexMap<String, RefState> = IndexMap::new();
    for (name, ra) in &a.refs {
        if let Some(rb) = b.refs.get(name) {
            if ra == rb {
                refs.insert(name.clone(), *ra);
            }
        }
    }
    PointState { locals, refs }
}

// ---------- Path walks ----------

/// Apply a write of `leaf_state` at the given path from `state` (which is
/// the current state of the root Var). Promotes intermediate states to
/// Partial as needed. Downcast steps in a write path do not update state.
fn write_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env, leaf_state: InitState) {
    if path.is_empty() {
        *state = leaf_state;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = struct_fields_of(ty, env) else { return; };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields.iter().find(|fd| fd.name == *f).map(|fd| fd.ty.clone());
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    write_at(field_state, &field_ty, &path[1..], env, leaf_state);
                }
            }
        }
        PathStep::Downcast(_) => {
            // Direct write into a variant payload does not initialize the
            // enum in our model (enum construction goes via `Name::V(...)`).
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Apply a move at the given path. Downcast steps set the whole enum to
/// `Moved` (enum atomicity).
fn move_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env) {
    if path.is_empty() {
        *state = InitState::Moved;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = struct_fields_of(ty, env) else { return; };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields.iter().find(|fd| fd.name == *f).map(|fd| fd.ty.clone());
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    move_at(field_state, &field_ty, &path[1..], env);
                }
            }
        }
        PathStep::Downcast(_) => {
            *state = InitState::Moved;
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Return the effective state at the given path (for a read check).
fn read_at(state: &InitState, ty: &Type, path: &[PathStep], env: &Env) -> InitState {
    if path.is_empty() {
        return state.clone();
    }
    match &path[0] {
        PathStep::Field(f) => match state {
            InitState::Init
            | InitState::NeverInit
            | InitState::Moved
            | InitState::Diverged => state.clone(),
            InitState::Partial(map) => {
                let field_ty = struct_fields_of(ty, env)
                    .and_then(|fs| fs.iter().find(|fd| fd.name == *f))
                    .map(|fd| fd.ty.clone());
                let field_state = map.get(f).cloned().unwrap_or(InitState::NeverInit);
                match field_ty {
                    Some(ft) => read_at(&field_state, &ft, &path[1..], env),
                    None => field_state,
                }
            }
        },
        PathStep::Downcast(v) => match state {
            InitState::NeverInit | InitState::Moved | InitState::Diverged => state.clone(),
            InitState::Init | InitState::Partial(_) => {
                // Enum atomicity: if the enum is Init, the payload is Init.
                // (Partial on an enum is not expected but we treat it like Init.)
                let payload_ty = enum_variant_payload_ty(ty, v, env);
                match payload_ty {
                    Some(pt) => read_at(&InitState::Init, &pt, &path[1..], env),
                    None => InitState::Init,
                }
            }
        },
    }
}

// ---------- Top-level pipeline ----------

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
}

/// For each `Return`-terminated block in `func`, compute the init state at
/// the point just before the terminator (all statements applied). Used by
/// other passes (e.g. substructural leak-at-return checks) that need to see
/// what a function actually leaves initialized when it returns.
pub fn states_before_returns<'a>(
    env: &Env,
    func: &'a Function,
) -> Vec<(&'a BasicBlock, PointState)> {
    let mut out = Vec::new();
    let Some(body) = &func.body else { return out; };
    if body.blocks.is_empty() { return out; }

    let locals = func.locals_map();
    let ctx = Ctx { env, locals: &locals };
    let entry_states = compute_entry_states(&ctx, func, body);

    for block in &body.blocks {
        if !matches!(block.terminator, Terminator::Return) { continue; }
        let Some(entry) = entry_states.get(&block.label) else { continue; };
        let mut state = entry.clone();
        for (stmt, _) in &block.statements {
            transfer_stmt(&ctx, stmt, &mut state);
        }
        // Return terminator has no state effect.
        out.push((block, state));
    }
    out
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    if body.blocks.is_empty() { return; }

    let locals = func.locals_map();
    let ctx = Ctx { env, locals: &locals };
    let entry_states = compute_entry_states(&ctx, func, body);

    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else { continue; };
        let mut state = entry.clone();
        check_block(&ctx, func, block, &mut state, d);
    }
}

fn initial_state(func: &Function, body: &FunctionBody, env: &Env) -> PointState {
    let mut s = PointState::default();
    for p in &func.params {
        s.locals.insert(p.name.clone(), InitState::Init);
        // Reference parameters carry the loan for the whole body, so at
        // entry we know their pointee is in the kind's creation-cur.
        if let Type::Ref(kind, _) = &p.ty {
            if let Some(rs) = RefState::from_kind(kind) {
                s.refs.insert(p.name.clone(), rs);
            }
        }
    }
    for l in &body.locals {
        // A struct with zero declared fields is trivially initialized —
        // there's nothing to write. Same for any type reducing to one.
        let init = if is_trivially_init(&l.ty, env) {
            InitState::Init
        } else {
            InitState::NeverInit
        };
        s.locals.insert(l.name.clone(), init);
    }
    s
}

fn is_trivially_init(ty: &Type, env: &Env) -> bool {
    match ty {
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => s.fields.is_empty(),
            _ => false,
        },
        _ => false,
    }
}

fn compute_entry_states(
    ctx: &Ctx,
    func: &Function,
    body: &FunctionBody,
) -> IndexMap<String, PointState> {
    let mut states: IndexMap<String, PointState> = IndexMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), initial_state(func, body, ctx.env));
    worklist.push_back(entry_label);

    let blocks_by_label = body.blocks_by_label();

    while let Some(label) = worklist.pop_front() {
        let block = blocks_by_label[label.as_str()];
        let mut state = states[&label].clone();
        for (stmt, _) in &block.statements {
            transfer_stmt(ctx, stmt, &mut state);
        }
        transfer_terminator(ctx, &block.terminator, &mut state);

        for succ in terminator_successors(&block.terminator) {
            if !blocks_by_label.contains_key(succ) { continue; }
            let new_state = match states.get(succ) {
                None => state.clone(),
                Some(existing) => join_point(existing, &state),
            };
            if states.get(succ).map_or(true, |e| e != &new_state) {
                states.insert(succ.to_string(), new_state);
                worklist.push_back(succ.to_string());
            }
        }
    }

    states
}

// ---------- Transfer (state updates) ----------

fn transfer_stmt(ctx: &Ctx, stmt: &Statement, state: &mut PointState) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            apply_rvalue_moves(ctx, rvalue, state);
            // Silent mirror of check_and_transfer_stmt's assign-side effects
            // for the fixpoint. Errors are emitted only by the diagnostic
            // pass; here we just propagate state.
            if let Place::Var(name) = target {
                state.refs.shift_remove(name);
            }
            if matches!(target, Place::Deref(_)) {
                apply_deref_op(ctx, target, DerefOp::Write, state, None);
            } else {
                apply_write(ctx, target, state, InitState::Init);
                if let (Place::Var(name), RValue::Ref(kind, _)) = (target, rvalue) {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(name.clone(), rs);
                    }
                }
            }
        }
        Statement::Call(target, args) => {
            apply_operand_move(ctx, target, state);
            for a in args {
                apply_operand_move(ctx, a, state);
            }
        }
        Statement::Drop(place) => {
            if let Place::Var(name) = place {
                state.refs.shift_remove(name);
            }
            apply_move(ctx, place, state);
        }
    }
}

fn transfer_terminator(ctx: &Ctx, term: &Terminator, state: &mut PointState) {
    if let Terminator::Branch { cond, .. } = term {
        apply_operand_move(ctx, cond, state);
    }
}

fn apply_rvalue_moves(ctx: &Ctx, rv: &RValue, state: &mut PointState) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => apply_operand_move(ctx, op, state),
        RValue::Ref(_, _) => {}
    }
}

fn apply_operand_move(ctx: &Ctx, op: &Operand, state: &mut PointState) {
    // Deref through *r transitions the ref's pointee state; do it before
    // the whole-var move that follows for consistency.
    match op {
        Operand::Copy(place) => apply_deref_op(ctx, place, DerefOp::Read, state, None),
        Operand::Move(place) => {
            apply_deref_op(ctx, place, DerefOp::Move, state, None);
            apply_move(ctx, place, state);
        }
        Operand::Const(_) => {}
    }
}

fn apply_write(ctx: &Ctx, place: &Place, state: &mut PointState, leaf: InitState) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let root_state = state.locals.entry(root).or_insert(InitState::NeverInit);
    write_at(root_state, &root_ty, &path, ctx.env, leaf);
}

fn apply_move(ctx: &Ctx, place: &Place, state: &mut PointState) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let root_state = state.locals.entry(root.clone()).or_insert(InitState::NeverInit);
    move_at(root_state, &root_ty, &path, ctx.env);
    // Whole-var move of an exclusive reference: the loan is transferred
    // to whoever receives the move. From the caller's perspective, the
    // ref entry is gone; no obligation check here (that'd double-count
    // if the callee's signature enforces its own).
    if path.is_empty() {
        state.refs.shift_remove(&root);
    }
}

/// Which kind of dereference operation is being performed. Distinguishes
/// state precondition (init vs uninit) and post-condition transition.
#[derive(Debug, Clone, Copy)]
enum DerefOp {
    /// `copy *r` / discriminant read of *r — requires pointee Init, no
    /// transition.
    Read,
    /// `move *r` — requires pointee Init, transitions to Uninit.
    Move,
    /// `*r = v` — requires pointee Uninit, transitions to Init.
    Write,
}

/// Apply the state effect of an operation through `*r`. If `place` isn't
/// a shallow deref of a Var, returns without effect.
///
/// When `report` is `Some`, precondition failures emit errors; when `None`
/// the check is silent (used from the fixpoint transfer).
///
/// Nested paths like `(*r).field` aren't handled here — pinned as a
/// deferred limitation. Only the shape `*r` where `r: exclusive-ref` is
/// tracked; shared refs generate a diagnostic on write/move but not read.
fn apply_deref_op(
    ctx: &Ctx,
    place: &Place,
    op: DerefOp,
    state: &mut PointState,
    report: Option<(&Function, &BasicBlock, Span, &mut Diagnostics)>,
) {
    let Place::Deref(inner) = place else { return; };
    let Place::Var(name) = &**inner else { return; };
    let Some(root_ty) = ctx.locals.get(name) else { return; };
    let Type::Ref(kind, _) = root_ty else { return; };

    if matches!(kind, RefKind::Shared) {
        if !matches!(op, DerefOp::Read) {
            if let Some((func, block, span, d)) = report {
                push_error!(
                    d, span, func, block,
                    "cannot mutate through shared reference '{}'", name
                );
            }
        }
        return;
    }

    let Some(rs) = state.refs.get(name).copied() else {
        if let Some((func, block, span, d)) = report {
            push_error!(
                d, span, func, block,
                "cannot dereference '{}': reference state is unknown here", name
            );
        }
        return;
    };

    let required = match op {
        DerefOp::Read | DerefOp::Move => RefCur::Init,
        DerefOp::Write => RefCur::Uninit,
    };
    if rs.cur != required {
        if let Some((func, block, span, d)) = report {
            let action = match op {
                DerefOp::Read => "read from",
                DerefOp::Move => "move out of",
                DerefOp::Write => "write into",
            };
            let expected = match required {
                RefCur::Init => "initialized",
                RefCur::Uninit => "uninitialized",
            };
            let actual = match rs.cur {
                RefCur::Init => "initialized",
                RefCur::Uninit => "uninitialized",
            };
            push_error!(
                d, span, func, block,
                "cannot {} pointee of '{}': pointee must be {} here, but is {}",
                action, name, expected, actual
            );
        }
    }

    // Apply the transition. Do this even on precondition failure so
    // downstream analysis sees consistent state.
    let new_cur = match op {
        DerefOp::Read => rs.cur,
        DerefOp::Move => RefCur::Uninit,
        DerefOp::Write => RefCur::Init,
    };
    state.refs.insert(name.clone(), RefState { cur: new_cur, post: rs.post });
}

/// If `place` is a whole-var ref binding with an outstanding obligation
/// (`refs[name]` exists), verify its obligation is fulfilled and remove
/// the entry. Called at any point where the reference value is being
/// silently forgotten: `drop r`, or overwrite of `r`.
fn close_ref_if_present(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    let _ = ctx;
    let Place::Var(name) = place else { return; };
    let Some(rs) = state.refs.get(name).copied() else { return; };
    if !rs.obligation_fulfilled() {
        push_error!(
            d, span, func, block,
            "cannot forget reference '{}': obligation not fulfilled (cur={:?}, post={:?})",
            name, rs.cur, rs.post
        );
    }
    state.refs.shift_remove(name);
}

// ---------- Diagnostic pass ----------

fn check_block(ctx: &Ctx, func: &Function, block: &BasicBlock, state: &mut PointState, d: &mut Diagnostics) {
    for (stmt, span) in &block.statements {
        check_and_transfer_stmt(ctx, func, block, stmt, *span, state, d);
    }
    check_and_transfer_terminator(ctx, func, block, state, d);
}

/// Combined check + transfer. Operands are consumed left-to-right so that a
/// later operand in the same statement sees the state after prior moves —
/// this is what makes `call f(move x, copy x)` correctly error on the second
/// operand.
fn check_and_transfer_stmt(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            eval_rvalue(ctx, func, block, rvalue, span, state, d);
            check_lhs_downcast(ctx, func, block, target, span, state, d);

            // Overwriting a bound ref var is a silent-forget of the
            // pointee obligation; error unless already fulfilled.
            close_ref_if_present(ctx, func, block, target, span, state, d);

            // Deref-write: transition the ref's pointee state through *r.
            if matches!(target, Place::Deref(_)) {
                apply_deref_op(ctx, target, DerefOp::Write, state,
                    Some((func, block, span, d)));
            } else {
                apply_write(ctx, target, state, InitState::Init);
                // Borrow creation: attach the initial ref state to the
                // target var (skipped for shared refs — no obligation).
                if let (Place::Var(name), RValue::Ref(kind, _)) = (target, rvalue) {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(name.clone(), rs);
                    }
                }
            }
        }
        Statement::Call(target, args) => {
            eval_operand(ctx, func, block, target, span, state, d);
            for a in args {
                eval_operand(ctx, func, block, a, span, state, d);
            }
        }
        Statement::Drop(place) => {
            // Read the place, then consume it. Same effect on state as
            // `move`. The substructural checker (separate pass) is the
            // one that will require the type to be Drop. For a ref-typed
            // Var, also verify the pointee obligation before forgetting.
            check_place_read(ctx, func, block, place, span, state, d);
            close_ref_if_present(ctx, func, block, place, span, state, d);
            apply_move(ctx, place, state);
        }
    }
}

fn check_and_transfer_terminator(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    let ts = block.terminator_span;
    match &block.terminator {
        Terminator::Branch { cond, .. } => eval_operand(ctx, func, block, cond, ts, state, d),
        Terminator::SwitchEnum { place, .. } => {
            // Discriminant read: no move, no consumption.
            check_place_read(ctx, func, block, place, ts, state, d);
        }
        _ => {}
    }
}

fn eval_rvalue(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    rv: &RValue,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
            eval_operand(ctx, func, block, op, span, state, d);
        }
        RValue::Ref(kind, place) => {
            check_borrow_precondition(ctx, func, block, kind, place, span, state, d);
        }
    }
}

/// Verify that the state of the borrowed place matches the reference kind's
/// creation-cur:
///   * `&`, `&mut`, `&drop` require the pointee to be Init.
///   * `&out`, `&uninit` require the pointee to be uninitialized
///     (NeverInit or Moved).
///
/// The check inspects the leaf state via [`read_at`]; partial and diverged
/// states at the leaf never match either precondition, so they're rejected
/// with a clear "not fully X" message.
fn check_borrow_precondition(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    kind: &RefKind,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let Some(root_state) = state.locals.get(&root) else { return; };
    let leaf = read_at(root_state, &root_ty, &path, ctx.env);

    let (requires_init, kind_str) = match kind {
        RefKind::Shared => (true,  "&"),
        RefKind::Mut    => (true,  "&mut"),
        RefKind::Drop   => (true,  "&drop"),
        RefKind::Out    => (false, "&out"),
        RefKind::Uninit => (false, "&uninit"),
    };

    let ok = if requires_init {
        matches!(leaf, InitState::Init)
    } else {
        matches!(leaf, InitState::NeverInit | InitState::Moved)
    };
    if ok { return; }

    let path_str = format_path(&root, &path);
    let expected = if requires_init { "initialized" } else { "uninitialized" };
    let actual = describe_state(&leaf);
    push_error!(
        d, span, func, block,
        "cannot create {} of '{}': place must be {} at borrow, but is {}",
        kind_str, path_str, expected, actual
    );
}

fn format_path(root: &str, path: &[PathStep]) -> String {
    let mut s = String::from(root);
    for step in path {
        match step {
            PathStep::Field(f) => { s.push('.'); s.push_str(f); }
            PathStep::Downcast(v) => { s.push_str(" as "); s.push_str(v); }
        }
    }
    s
}

fn describe_state(s: &InitState) -> &'static str {
    match s {
        InitState::NeverInit => "not yet initialized",
        InitState::Moved => "moved-from",
        InitState::Init => "initialized",
        InitState::Partial(_) => "partially initialized",
        InitState::Diverged => "of inconsistent state across paths",
    }
}

fn eval_operand(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    op: &Operand,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    check_operand_read(ctx, func, block, op, span, state, d);
    // Deref-op transitions for *r in operand position.
    match op {
        Operand::Copy(place) => {
            apply_deref_op(ctx, place, DerefOp::Read, state,
                Some((func, block, span, d)));
        }
        Operand::Move(place) => {
            apply_deref_op(ctx, place, DerefOp::Move, state,
                Some((func, block, span, d)));
        }
        Operand::Const(_) => {}
    }
    apply_operand_move(ctx, op, state);
}

fn check_operand_read(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    op: &Operand,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Const(_) => return,
    };
    check_place_read(ctx, func, block, place, span, state, d);
}

/// If the LHS path contains a `Downcast`, the enum being downcast must be
/// `Init` at that point — you can't refine an uninitialized enum by writing
/// through a variant projection. Enum construction goes via `Name::V(...)`.
fn check_lhs_downcast(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(idx) = path.iter().position(|s| matches!(s, PathStep::Downcast(_))) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let Some(root_state) = state.locals.get(&root) else { return; };
    let prefix_state = read_at(root_state, &root_ty, &path[..idx], ctx.env);
    if !matches!(prefix_state, InitState::Init) {
        push_error!(
            d, span, func, block,
            "cannot write through variant projection: '{}' is not initialized here", root
        );
    }
}

fn check_place_read(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let Some(root_state) = state.locals.get(&root) else { return; };
    let leaf = read_at(root_state, &root_ty, &path, ctx.env);
    match leaf {
        InitState::Init => {}
        InitState::NeverInit => push_error!(
            d, span, func, block,
            "variable '{}' is used before initialization", root
        ),
        InitState::Moved => push_error!(
            d, span, func, block,
            "variable '{}' is used after move", root
        ),
        InitState::Diverged => push_error!(
            d, span, func, block,
            "variable '{}' may be used before initialization or after move (state inconsistent across paths)", root
        ),
        InitState::Partial(_) => push_error!(
            d, span, func, block,
            "variable '{}' is not fully initialized here", root
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Baseline (unchanged from phase 1) ----------

    #[test]
    fn param_starts_init_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              y: number;
              entry:
                y = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn write_then_read_ok() {
        assert_no_diagnostics(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                x = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn read_of_uninit_local_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              y: number;
              entry:
                y = copy x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
    }

    #[test]
    fn read_after_move_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                z = copy x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    #[test]
    fn join_disagreement_produces_diverged_error() {
        let (errs, _) = run(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                goto merge
              merge:
                y = copy x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
    }

    // ---------- Partial init ----------

    #[test]
    fn field_writes_complete_init_ok() {
        // Writing every declared field of a struct-typed local promotes it
        // to fully Init.
        assert_no_diagnostics(
            "
            struct Copy Drop P { x: number y: number }
            fn f() {
              p: P;
              a: number;
              entry:
                p.x = 1;
                p.y = 2;
                a = copy p.x;
                return
            }
            ",
        );
    }

    #[test]
    fn partial_field_write_leaves_root_partial_error() {
        // Only one field written; the whole struct is not fully init and
        // reading it errors.
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              q: P;
              entry:
                p.x = 1;
                q = copy p;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is not fully initialized here"]);
    }

    #[test]
    fn read_uninit_field_of_partial_struct_error() {
        // Field-granular: writing p.x doesn't init p.y — reading p.y errors.
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              a: number;
              entry:
                p.x = 1;
                a = copy p.y;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is used before initialization"]);
    }

    #[test]
    fn move_of_field_leaves_other_fields_init_ok() {
        // Struct comes in fully-init from a param; moving one field must
        // leave the other still readable. Elaboration inserts the drop
        // for the remaining p.y automatically.
        assert_no_diagnostics(
            "
            struct Copy Drop P { x: number y: number }
            fn f(p: P) {
              a: number;
              b: number;
              entry:
                a = move p.x;
                b = copy p.y;
                return
            }
            ",
        );
    }

    #[test]
    fn move_of_field_then_read_that_field_error() {
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f(p: P) {
              a: number;
              b: number;
              entry:
                a = move p.x;
                b = copy p.x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is used after move"]);
    }

    #[test]
    fn nested_field_writes_complete_init_ok() {
        // Inner struct fields inited via nested paths; the whole outer
        // struct collapses to Init once every leaf is written.
        assert_no_diagnostics(
            "
            struct Copy Drop Inner { a: number b: number }
            struct Copy Drop Outer { i: Inner c: number }
            fn f() {
              o: Outer;
              n: number;
              entry:
                o.i.a = 1;
                o.i.b = 2;
                o.c = 3;
                n = copy o.i.a;
                return
            }
            ",
        );
    }

    #[test]
    fn nested_partial_read_of_uninit_inner_field_error() {
        let (errs, _) = run(
            "
            struct Inner { a: number b: number }
            struct Outer { i: Inner c: number }
            fn f() {
              o: Outer;
              n: number;
              entry:
                o.i.a = 1;
                o.c = 3;
                n = copy o.i.b;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    #[test]
    fn whole_struct_assign_after_partial_ok() {
        // Even if we partially init, a whole-struct assign resets to Init.
        assert_no_diagnostics(
            "
            struct Copy Drop P { x: number y: number }
            fn f(src: P) {
              p: P;
              a: number;
              entry:
                p.x = 1;
                p = move src;
                a = copy p.y;
                return
            }
            ",
        );
    }

    // ---------- Joins ----------

    #[test]
    fn join_agree_init_ok() {
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                x = 2;
                goto merge
              merge:
                y = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn aborting_predecessor_doesnt_pollute_join() {
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                abort
              merge:
                y = copy x;
                return
            }
            ",
        );
    }

    // ---------- Terminator reads ----------

    #[test]
    fn branch_reads_cond() {
        let (errs, _) = run(
            "
            fn f() {
              b: boolean;
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'b' is used before initialization"]);
    }

    #[test]
    fn switch_enum_reads_place() {
        let (errs, _) = run(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                switchEnum(o) [None: end, Some: end]
              end:
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    // ---------- Projections ----------

    #[test]
    fn downcast_read_checks_root_var() {
        let (errs, _) = run(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              a: number;
              entry:
                a = copy o as Some;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    #[test]
    fn deref_read_is_not_checked() {
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              a: number;
              entry:
                a = copy *r;
                return
            }
            ",
        );
    }

    // ---------- Downcast writes ----------

    #[test]
    fn downcast_write_on_init_enum_ok() {
        // Writing through a variant projection is fine when the enum is
        // Init AND refined to the correct variant.
        assert_no_diagnostics(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: s]
              s:
                o as Some = 7;
                return
              n: return
            }
            ",
        );
    }

    #[test]
    fn downcast_write_on_uninit_enum_error() {
        // Enum construction goes via `Name::V(...)`; refining an uninit
        // enum by writing a variant payload is not allowed.
        let (errs, _) = run(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o as Some = 7;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot write through variant projection: 'o' is not initialized here"],
        );
    }

    #[test]
    fn downcast_write_on_moved_enum_error() {
        let (errs, _) = run(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              sink: Option;
              entry:
                sink = move o;
                o as Some = 7;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot write through variant projection: 'o' is not initialized here"],
        );
    }

    // ---------- Empty struct ----------

    #[test]
    fn empty_struct_local_starts_init() {
        // A struct with zero fields has no components to write, so a
        // declared local of that type is trivially usable. Marked
        // `Copy Drop` so the substructural checker permits the copy.
        assert_no_diagnostics(
            "
            struct Copy Drop Unit0 { }
            fn f() {
              u: Unit0;
              v: Unit0;
              entry:
                v = copy u;
                return
            }
            ",
        );
    }

    // ---------- Calls ----------

    #[test]
    fn call_target_of_uninit_error() {
        let (errs, _) = run(
            "
            fn f() {
              g: fn(number);
              entry:
                call copy g(1);
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'g' is used before initialization"],
        );
    }

    #[test]
    fn call_arg_read_of_uninit_error() {
        let (errs, _) = run(
            "
            extern fn takes_num(a: number);
            fn f() {
              x: number;
              entry:
                call takes_num(copy x);
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
    }

    // ---------- Loops ----------

    #[test]
    fn loop_backedge_agrees_ok() {
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              entry:
                x = 0;
                goto head
              head:
                branch(copy b) [true: body, false: done]
              body:
                x = 1;
                goto head
              done:
                return
            }
            ",
        );
    }

    // ---------- Borrow init preconditions ----------
    //
    // Each ref kind requires the borrowed place be in a specific init
    // state at the point of borrow. Tests are organized by ref kind, then
    // by the state combinations that are/aren't legal.

    // === Scenario: `&q` (shared) — requires Init ===

    #[test]
    fn shared_borrow_of_init_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              r: &number;
              entry:
                r = &x;
                return
            }
            ",
        );
    }

    #[test]
    fn shared_borrow_of_never_init_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              r: &number;
              entry:
                r = &x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create & of 'x': place must be initialized at borrow, but is not yet initialized"],
        );
    }

    #[test]
    fn shared_borrow_of_moved_error() {
        let (errs, _) = run(
            "
            extern fn sink(x: number);
            fn f(x: number) {
              r: &number;
              entry:
                call sink(move x);
                r = &x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create & of 'x': place must be initialized at borrow, but is moved-from"],
        );
    }

    // === Scenario: `&mut q` — requires Init ===

    #[test]
    fn mut_borrow_of_init_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              r: &mut number;
              entry:
                r = &mut x;
                return
            }
            ",
        );
    }

    #[test]
    fn mut_borrow_of_never_init_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              r: &mut number;
              entry:
                r = &mut x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &mut of 'x': place must be initialized at borrow, but is not yet initialized"],
        );
    }

    // === Scenario: `&drop q` — requires Init ===

    #[test]
    fn drop_borrow_of_init_ok() {
        assert_no_diagnostics(
            "
            extern fn take_drop(r: &drop number);
            fn f(x: number) {
              r: &drop number;
              entry:
                r = &drop x;
                call take_drop(move r);
                return
            }
            ",
        );
    }

    #[test]
    fn drop_borrow_of_never_init_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              r: &drop number;
              entry:
                r = &drop x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &drop of 'x': place must be initialized at borrow, but is not yet initialized"],
        );
    }

    // === Scenario: `&out q` — requires Uninit ===

    #[test]
    fn out_borrow_of_never_init_ok() {
        // A declared but never-written local is the classic &out target.
        // Slice 0a doesn't yet track that `init_number` initializes x via
        // the &out — so x stays NeverInit locally, which is fine at return.
        assert_no_diagnostics(
            "
            extern fn init_number(out: &out number);
            fn f() {
              x: number;
              r: &out number;
              entry:
                r = &out x;
                call init_number(move r);
                return
            }
            ",
        );
    }

    #[test]
    fn out_borrow_of_moved_ok() {
        // After moving out, the place is uninitialized again — legal
        // target for &out. (Slice 0a doesn't track init through the &out
        // — x stays Moved locally, which is fine at return.)
        assert_no_diagnostics(
            "
            extern fn take(y: number);
            extern fn init(out: &out number);
            fn f(x: number) {
              r: &out number;
              entry:
                call take(move x);
                r = &out x;
                call init(move r);
                return
            }
            ",
        );
    }

    #[test]
    fn out_borrow_of_init_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              entry:
                x = 1;
                return
            }
            fn g(x: number) {
              r: &out number;
              entry:
                r = &out x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &out of 'x': place must be uninitialized at borrow, but is initialized"],
        );
    }

    // === Scenario: `&uninit q` — requires Uninit ===

    #[test]
    fn uninit_borrow_of_never_init_ok() {
        assert_no_diagnostics(
            "
            extern fn discard(r: &uninit number);
            fn f() {
              x: number;
              r: &uninit number;
              entry:
                r = &uninit x;
                call discard(move r);
                return
            }
            ",
        );
    }

    #[test]
    fn uninit_borrow_of_init_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              r: &uninit number;
              entry:
                r = &uninit x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &uninit of 'x': place must be uninitialized at borrow, but is initialized"],
        );
    }

    // === Scenario: fields (Partial states) ===

    #[test]
    fn mut_borrow_of_init_field_ok() {
        // Field-granular tracking: p.x is Init (from `p.x = 1`), so
        // `&mut p.x` succeeds even though p is Partial as a whole.
        assert_no_diagnostics(
            "
            struct Copy Drop P { x: number y: number }
            extern fn use_mut(r: &mut number);
            fn f() {
              p: P;
              r: &mut number;
              entry:
                p.x = 1;
                r = &mut p.x;
                call use_mut(move r);
                drop p.x;
                return
            }
            ",
        );
    }

    #[test]
    fn mut_borrow_of_never_init_field_error() {
        let (errs, _) = run(
            "
            struct Copy Drop P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                p.y = copy p.x;
                p.y = 2;
                return
            }
            fn g() {
              p: P;
              r: &mut number;
              entry:
                p.x = 1;
                r = &mut p.y;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &mut of 'p.y': place must be initialized at borrow, but is not yet initialized"],
        );
    }

    #[test]
    fn out_borrow_of_partial_error() {
        // Borrowing the whole `p` when only `p.x` was written: the leaf
        // read on `p` is Partial, not one of the accepted states.
        let (errs, _) = run(
            "
            struct Copy Drop P { x: number y: number }
            fn f() {
              p: P;
              r: &out P;
              entry:
                p.x = 1;
                r = &out p;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot create &out of 'p': place must be uninitialized at borrow, but is partially initialized"],
        );
    }

    // === Scenario: borrow through deref is not tracked (documents gap) ===

    #[test]
    fn borrow_through_deref_not_checked() {
        // `*r` isn't a followed path in slice 0a. Any borrow whose base
        // path contains a Deref is silently skipped. This documents the
        // gap; a later slice will handle reference-through-reference.
        assert_no_diagnostics(
            "
            fn f(r: &mut number) {
              s: &number;
              entry:
                s = &*r;
                return
            }
            ",
        );
    }

    // ---------- Reference (cur, post) state tracking ----------
    //
    // Slice 0b: transitions on `*r` operations, close-check on ref-var
    // consumption, leak check at return for unfulfilled ref obligations.
    //
    // Tests organized by ref kind, then by the interesting sequences.

    // === &mut: pointee starts Init, must stay Init at expiry ===

    #[test]
    fn mut_ref_read_then_return_ok() {
        // Read through &mut leaves cur=Init; obligation trivially met.
        assert_no_diagnostics(
            "
            fn f(r: &mut number) {
              x: number;
              entry:
                x = copy *r;
                return
            }
            ",
        );
    }

    #[test]
    fn mut_ref_move_then_write_ok() {
        // Move-out drops cur to Uninit; write puts it back to Init;
        // obligation met at return.
        assert_no_diagnostics(
            "
            fn f(r: &mut number) {
              x: number;
              entry:
                x = move *r;
                *r = 42;
                return
            }
            ",
        );
    }

    #[test]
    fn mut_ref_write_without_move_error() {
        // `*r = v` on an Init pointee would silently forget the old
        // value — rejected as pre-overwrite of the pointee.
        let (errs, _) = run(
            "
            fn f(r: &mut number) {
              entry:
                *r = 42;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot write into pointee of 'r': pointee must be uninitialized here, but is initialized"],
        );
    }

    #[test]
    fn mut_ref_moved_out_return_leaks() {
        // Move-out leaves cur=Uninit; not refilled → obligation unmet.
        let (errs, _) = run(
            "
            fn f(r: &mut number) {
              x: number;
              entry:
                x = move *r;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["reference 'r' of type Ref(Mut, Number) has unfulfilled obligation at return"],
        );
    }

    // === &out: pointee starts Uninit, must reach Init at expiry ===

    #[test]
    fn out_ref_write_then_return_ok() {
        assert_no_diagnostics(
            "
            fn f(r: &out number) {
              entry:
                *r = 42;
                return
            }
            ",
        );
    }

    #[test]
    fn out_ref_unwritten_leaks() {
        let (errs, _) = run(
            "
            fn f(r: &out number) {
              entry:
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["reference 'r' of type Ref(Out, Number) has unfulfilled obligation at return"],
        );
    }

    #[test]
    fn out_ref_read_before_write_error() {
        // Can't read through &out — pointee is Uninit at creation.
        let (errs, _) = run(
            "
            fn f(r: &out number) {
              x: number;
              entry:
                x = copy *r;
                *r = 42;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot read from pointee of 'r': pointee must be initialized here, but is uninitialized"],
        );
    }

    // === &drop: pointee starts Init, must reach Uninit at expiry ===

    #[test]
    fn drop_ref_move_out_then_return_ok() {
        assert_no_diagnostics(
            "
            fn f(r: &drop number) {
              x: number;
              entry:
                x = move *r;
                return
            }
            ",
        );
    }

    #[test]
    fn drop_ref_unmoved_leaks() {
        let (errs, _) = run(
            "
            fn f(r: &drop number) {
              entry:
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["reference 'r' of type Ref(Drop, Number) has unfulfilled obligation at return"],
        );
    }

    // === &uninit: pointee starts Uninit, must stay Uninit at expiry ===

    #[test]
    fn uninit_ref_untouched_return_ok() {
        assert_no_diagnostics(
            "
            fn f(r: &uninit number) {
              entry:
                return
            }
            ",
        );
    }

    #[test]
    fn uninit_ref_write_makes_it_drop_state() {
        // After `*r = v`, r is in `&drop` state (post=Uninit, cur=Init).
        // Must move-out again to satisfy post.
        assert_no_diagnostics(
            "
            fn f(r: &uninit number) {
              x: number;
              entry:
                *r = 42;
                x = move *r;
                return
            }
            ",
        );
    }

    #[test]
    fn uninit_ref_write_without_moveback_leaks() {
        let (errs, _) = run(
            "
            fn f(r: &uninit number) {
              entry:
                *r = 42;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["reference 'r' of type Ref(Uninit, Number) has unfulfilled obligation at return"],
        );
    }

    // === Local ref: create → use → move-to-call ===

    #[test]
    fn local_mut_ref_moved_to_call_ok() {
        assert_no_diagnostics(
            "
            extern fn use_mut(r: &mut number);
            fn f(x: number) {
              r: &mut number;
              entry:
                r = &mut x;
                call use_mut(move r);
                return
            }
            ",
        );
    }

    #[test]
    fn local_drop_ref_moved_to_call_ok() {
        // Create &drop, transfer via call. Loan obligation delegated to
        // the callee.
        assert_no_diagnostics(
            "
            extern fn consume(r: &drop number);
            fn f(x: number) {
              r: &drop number;
              entry:
                r = &drop x;
                call consume(move r);
                return
            }
            ",
        );
    }

    // === Shared refs: no obligation, no state tracking ===

    #[test]
    fn shared_ref_read_ok() {
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              x: number;
              entry:
                x = copy *r;
                return
            }
            ",
        );
    }

    #[test]
    fn shared_ref_write_error() {
        let (errs, _) = run(
            "
            fn f(r: &number) {
              entry:
                *r = 1;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["cannot mutate through shared reference 'r'"]);
    }

    #[test]
    fn shared_ref_left_bound_at_return_ok() {
        // `&T` is Copy Drop; no obligation on return.
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              entry:
                return
            }
            ",
        );
    }

    // === Drop statement on refs (bitwise forget must satisfy post) ===

    #[test]
    fn drop_of_mut_ref_ok() {
        // &mut is (Init, Init) at every point; drop is trivially legal.
        assert_no_diagnostics(
            "
            fn f(r: &mut number) {
              entry:
                drop r;
                return
            }
            ",
        );
    }

    #[test]
    fn drop_of_ref_with_unfulfilled_obligation_error() {
        // Move out through &mut leaves cur=Uninit; drop-forget then
        // errors because obligation not fulfilled.
        let (errs, _) = run(
            "
            fn f(r: &mut number) {
              x: number;
              entry:
                x = move *r;
                drop r;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot forget reference 'r': obligation not fulfilled"],
        );
    }

    // ---------- Drop statement ----------

    #[test]
    fn drop_consumes_like_move() {
        // `drop x` behaves like a move for init tracking: subsequent read errors.
        let (errs, _) = run(
            "
            fn f(x: number) {
              y: number;
              entry:
                drop x;
                y = copy x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    #[test]
    fn drop_of_uninit_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              entry:
                drop x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
    }

    // ---------- Reassignment / move ordering ----------

    #[test]
    fn reassign_after_move_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                x = 42;
                z = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn move_then_move_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                z = move x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    #[test]
    fn call_args_copy_then_move_ok() {
        // Copy first, then move — the copy sees Init, the move consumes.
        assert_no_diagnostics(
            "
            extern fn take_two(a: number, b: number);
            fn f(x: number) {
              entry:
                call take_two(copy x, move x);
                return
            }
            ",
        );
    }

    #[test]
    fn call_args_move_then_copy_error() {
        // Left-to-right operand evaluation: the second `copy` sees the
        // already-moved state and errors.
        let (errs, _) = run(
            "
            extern fn take_two(a: number, b: number);
            fn f(x: number) {
              entry:
                call take_two(move x, copy x);
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    // ---------- Loops ----------

    #[test]
    fn loop_may_reach_uninit_error() {
        let (errs, _) = run(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: body, false: done]
              body:
                y = copy x;
                x = 1;
                branch(copy b) [true: body, false: done]
              done:
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
    }
}
