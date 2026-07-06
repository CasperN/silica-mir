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
use std::collections::{BTreeMap, BTreeSet, VecDeque};

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

/// A record of a borrow that's currently in force. `loaned` is a set to
/// support multi-loan: when a branch-of-borrows produces different loaned
/// places on each side, the join unions them so all possible pointees stay
/// tracked.
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
        Loan { kind, loaned: set, create_span }
    }
}

/// State at a single program point.
///
/// - `locals`: init state per root Var, potentially projecting through
///   struct fields and enum downcasts.
/// - `refs`: the (cur, post) obligation for each ref-typed Var that is
///   currently `Init`. Absent when the ref var is not Init, is shared,
///   or has been consumed.
/// - `loans`: per-borrower record of what's borrowed (kind + loaned
///   place). Keyed by borrower Var name. Populated on borrow creation;
///   removed when the borrower is consumed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PointState {
    pub locals: IndexMap<String, InitState>,
    pub refs: IndexMap<String, RefState>,
    pub loans: IndexMap<String, Loan>,
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
    // Loans: same-kind entries merge by unioning their loaned sets
    // (branch-of-borrows produces a multi-loan). Different kinds at the
    // same borrower name can't happen — type_check enforces uniform ref
    // types — so we drop as a conservative fallback if it somehow occurs.
    let mut loans: IndexMap<String, Loan> = IndexMap::new();
    for (name, la) in &a.loans {
        if let Some(lb) = b.loans.get(name) {
            if la.kind == lb.kind {
                let mut merged = la.clone();
                merged.loaned.extend(lb.loaned.iter().cloned());
                // Span: prefer earlier (either side; a's is deterministic).
                loans.insert(name.clone(), merged);
            }
        }
    }
    PointState { locals, refs, loans }
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
            // Capture ref/loan entries to transfer via `move src` BEFORE
            // apply_rvalue_moves removes them.
            let move_source = ref_move_source(target, rvalue);
            let carried = move_source.as_ref().and_then(|src| {
                Some((state.refs.get(src).copied(), state.loans.get(src).cloned()))
            });

            apply_rvalue_moves(ctx, rvalue, state);
            // Silent mirror of check_and_transfer_stmt's assign-side effects
            // for the fixpoint. Errors are emitted only by the diagnostic
            // pass; here we just propagate state.
            if let Place::Var(name) = target {
                state.refs.shift_remove(name);
                state.loans.shift_remove(name);
            }
            if matches!(target, Place::Deref(_)) {
                apply_deref_op(ctx, target, DerefOp::Write, state, None);
            } else {
                apply_write(ctx, target, state, InitState::Init);
                if let (Place::Var(name), RValue::Ref(kind, place)) = (target, rvalue) {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(name.clone(), rs);
                    }
                    // Track the loan for all kinds (including shared)
                    // for later conflict detection. Synthetic span here
                    // — the diagnostic pass supplies the real one.
                    state.loans.insert(
                        name.clone(),
                        Loan::single(kind.clone(), place.clone(), Span { line: 0, col: 0 }),
                    );
                    apply_eager_borrow_transition(ctx, kind, place, state);
                }
                // Ref/loan transfer via `dst = move src`.
                if let (Place::Var(dst), Some((refs, loan))) = (target, carried) {
                    if let Some(rs) = refs { state.refs.insert(dst.clone(), rs); }
                    if let Some(l) = loan { state.loans.insert(dst.clone(), l); }
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
                state.loans.shift_remove(name);
            }
            // `drop *r` — consume the pointee, transition r's cur.
            apply_deref_op(ctx, place, DerefOp::Move, state, None);
            apply_move(ctx, place, state);
        }
        Statement::Unborrow(place) => {
            // Silent side of `unborrow r`: consume the borrower and its
            // ref/loan entries. Obligation checks happen in the
            // diagnostic pass.
            if let Place::Var(name) = place {
                state.refs.shift_remove(name);
                state.loans.shift_remove(name);
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
        state.loans.shift_remove(&root);
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
    state.loans.shift_remove(name);
}

// ---------- Loan conflict check ----------

/// How a place is being accessed. Used to classify conflicts against
/// active loans.
#[derive(Debug, Clone)]
enum AccessKind {
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
/// other, meaning they refer to overlapping storage.
fn paths_conflict(a: &[PathStep], b: &[PathStep]) -> bool {
    let n = a.len().min(b.len());
    for i in 0..n {
        let same = match (&a[i], &b[i]) {
            (PathStep::Field(x), PathStep::Field(y)) => x == y,
            (PathStep::Downcast(x), PathStep::Downcast(y)) => x == y,
            _ => false,
        };
        if !same { return false; }
    }
    true
}

/// Compatible = both shared read/borrow. Anything else against a live
/// loan is a conflict.
fn is_compatible(loan_kind: &RefKind, access: &AccessKind) -> bool {
    matches!(loan_kind, RefKind::Shared)
        && matches!(access, AccessKind::Read | AccessKind::Borrow(RefKind::Shared))
}

/// The pointee's init state after the loan expires (post). Returned as an
/// `InitState` so the eager-transition helper can apply it directly.
fn loan_post_leaf(kind: &RefKind) -> Option<InitState> {
    match kind {
        // No transition: pointee already at post.
        RefKind::Shared | RefKind::Mut | RefKind::Uninit => None,
        // Uninit → Init: eagerly mark the loaned place initialized. The
        // loan tracker blocks direct access until the loan expires, so
        // this is sound.
        RefKind::Out => Some(InitState::Init),
        // Init → Uninit: eagerly consume.
        RefKind::Drop => Some(InitState::Moved),
    }
}

/// Apply the eager init transition on the loaned place. Called at borrow
/// creation.
fn apply_eager_borrow_transition(
    ctx: &Ctx,
    kind: &RefKind,
    place: &Place,
    state: &mut PointState,
) {
    let Some(leaf) = loan_post_leaf(kind) else { return; };
    apply_write(ctx, place, state, leaf);
}

/// If the assign is `dst_var = move src_var`, returns `src_var`. This is
/// the pattern where a reference's ref-state and loan should transfer
/// from src to dst instead of being lost.
fn ref_move_source(target: &Place, rvalue: &RValue) -> Option<String> {
    let Place::Var(_) = target else { return None; };
    let RValue::Use(Operand::Move(Place::Var(src))) = rvalue else { return None; };
    Some(src.clone())
}

/// Check whether accessing `place` in the given way conflicts with any
/// active loan. Skips accesses through `Deref` (those go via the
/// borrower and are always permitted).
fn check_loan_conflict(
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    access: AccessKind,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((access_root, access_path)) = extract_path(place) else { return; };

    for (borrower, loan) in &state.loans {
        // Ignore the borrower itself — its ref state is a separate slot.
        if *borrower == access_root {
            // e.g. `move r` where r is a borrower: consuming the ref,
            // not accessing the loaned place. Not a conflict here (the
            // consumption is handled by close_ref_if_present).
            continue;
        }
        if is_compatible(&loan.kind, &access) { continue; }
        // Multi-loan: any place in the set may be the actual pointee.
        // Report at most one error per loan (first matching place).
        for loaned in &loan.loaned {
            let Some((loan_root, loan_path)) = extract_path(loaned) else { continue; };
            if loan_root != access_root { continue; }
            if !paths_conflict(&access_path, &loan_path) { continue; }
            push_error!(
                d, span, func, block,
                "cannot {} '{}': already borrowed by '{}'",
                access.describe(), format_path(&access_root, &access_path), borrower
            );
            break;
        }
    }
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
            // Capture ref/loan state to transfer via `move src` BEFORE
            // eval_rvalue runs (which clears the source entry).
            let carried = ref_move_source(target, rvalue).map(|src| {
                (state.refs.get(&src).copied(), state.loans.get(&src).cloned())
            });

            eval_rvalue(ctx, func, block, rvalue, span, state, d);
            check_lhs_downcast(ctx, func, block, target, span, state, d);

            // Writing to a place while it's borrowed conflicts with
            // the outstanding loan.
            check_loan_conflict(func, block, target, AccessKind::Write, span, state, d);

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
                if let (Place::Var(name), RValue::Ref(kind, place)) = (target, rvalue) {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(name.clone(), rs);
                    }
                    state.loans.insert(
                        name.clone(),
                        Loan::single(kind.clone(), place.clone(), span),
                    );
                    apply_eager_borrow_transition(ctx, kind, place, state);
                }
                // Ref/loan transfer via `dst = move src`.
                if let (Place::Var(dst), Some((refs, loan))) = (target, carried) {
                    if let Some(rs) = refs { state.refs.insert(dst.clone(), rs); }
                    if let Some(l) = loan { state.loans.insert(dst.clone(), l); }
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
            check_loan_conflict(func, block, place, AccessKind::Move, span, state, d);
            close_ref_if_present(ctx, func, block, place, span, state, d);
            // `drop *r` — consume the pointee, transition r's cur.
            apply_deref_op(ctx, place, DerefOp::Move, state,
                Some((func, block, span, d)));
            apply_move(ctx, place, state);
        }
        Statement::Unborrow(place) => {
            // Explicit end-of-loan. Requires the borrower to be Init
            // and its (cur, post) obligation fulfilled — both checked
            // by close_ref_if_present. Then consume the borrower.
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
            check_loan_conflict(func, block, place, AccessKind::Read, ts, state, d);
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
            check_loan_conflict(func, block, place, AccessKind::Borrow(kind.clone()), span, state, d);
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
    let (place, access) = match op {
        Operand::Copy(p) => (p, AccessKind::Read),
        Operand::Move(p) => (p, AccessKind::Move),
        Operand::Const(_) => return,
    };
    check_place_read(ctx, func, block, place, span, state, d);
    check_loan_conflict(func, block, place, access, span, state, d);
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

#[cfg(test)] mod tests_lifecycle;
#[cfg(test)] mod tests_borrows;
#[cfg(test)] mod tests_loans;
#[cfg(test)] mod tests_unborrow;
#[cfg(test)] mod tests_cfg_shapes;
