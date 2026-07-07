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
use crate::dataflow;
use crate::diagnostics::Diagnostics;
use crate::push_error;
use crate::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::BTreeMap;

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

/// Per-reference-variable state: the current and (post-expiry) required
/// state of the pointee. Only tracked for exclusive reference kinds (`&mut`,
/// `&out`, `&drop`, `&uninit`). Shared references (`&T`) don't carry an
/// obligation — they're `Copy Drop`.
///
/// `is_init` is the pointee's current initialization state at this
/// program point; `ends_init` is what the (cur, post) rule requires by
/// the time the loan expires.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RefState {
    pub is_init: bool,
    pub ends_init: bool,
}

impl RefState {
    /// The (is_init, ends_init) at borrow creation for a given ref kind.
    /// Returns `None` for shared borrows (no obligation).
    pub fn from_kind(kind: &RefKind) -> Option<Self> {
        match kind {
            RefKind::Shared => None,
            RefKind::Mut => Some(RefState {
                is_init: true,
                ends_init: true,
            }),
            RefKind::Out => Some(RefState {
                is_init: false,
                ends_init: true,
            }),
            RefKind::Drop => Some(RefState {
                is_init: true,
                ends_init: false,
            }),
            RefKind::Uninit => Some(RefState {
                is_init: false,
                ends_init: false,
            }),
        }
    }

    pub fn obligation_fulfilled(&self) -> bool {
        self.is_init == self.ends_init
    }
}

/// Init-side state at a single program point.
///
/// - `locals`: init state per root Var, potentially projecting through
///   struct fields and enum downcasts.
/// - `refs`: the (is_init, ends_init) obligation for each ref-typed
///   *owned path* that is currently `Init`. A place can be a Var
///   (`r`), a struct field (`b.p`), or a downcast (`e as V`) — anything
///   we can name in the local frame. Absent when the ref place is not
///   Init, is shared, or has been consumed.
///
/// Loans are tracked entirely by `lifetime::check_program`, an
/// independent pass. This pass never looks at the loan set — it trusts
/// that lifetime blocks direct access to any place while borrowed, and
/// eagerly applies the borrow's post-transition on the loaned place at
/// creation (e.g. `y = &out x` marks `x` `Init` immediately).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PointState {
    pub locals: IndexMap<String, InitState>,
    pub refs: IndexMap<Place, RefState>,
}

struct Ctx<'a> {
    env: &'a Env,
    locals: &'a IndexMap<String, Type>,
}

// ---------- Type lookups ----------

fn struct_fields_of<'a>(ty: &Type, env: &'a Env) -> Option<&'a [StructField]> {
    let Type::Custom(name) = ty else {
        return None;
    };
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => Some(&s.fields),
        _ => None,
    }
}

fn enum_variant_payload_ty(ty: &Type, variant: &str, env: &Env) -> Option<Type> {
    let Type::Custom(name) = ty else {
        return None;
    };
    match env.types.get(name) {
        Some(TypeDecl::Enum(e)) => e
            .variants
            .iter()
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
        (InitState::Partial(ma), InitState::Partial(mb)) => join_partials(ma, mb),
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

fn join_partials(ma: &BTreeMap<String, InitState>, mb: &BTreeMap<String, InitState>) -> InitState {
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
    let locals: IndexMap<String, InitState> = a
        .locals
        .iter()
        .map(|(name, sa)| {
            let sb = b.locals.get(name).cloned().unwrap_or(InitState::NeverInit);
            (name.clone(), join_state(sa, &sb))
        })
        .collect();
    // Refs: keep only entries that agree exactly on both sides. Disagreement
    // is treated as "not currently bound" for the joined point — subsequent
    // uses will see no ref state and behave conservatively.
    let mut refs: IndexMap<Place, RefState> = IndexMap::new();
    for (place, ra) in &a.refs {
        if let Some(rb) = b.refs.get(place) {
            if ra == rb {
                refs.insert(place.clone(), *ra);
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
            let Some(fields) = struct_fields_of(ty, env) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields
                .iter()
                .find(|fd| fd.name == *f)
                .map(|fd| fd.ty.clone());
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
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
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
            let Some(fields) = struct_fields_of(ty, env) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields
                .iter()
                .find(|fd| fd.name == *f)
                .map(|fd| fd.ty.clone());
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    move_at(field_state, &field_ty, &path[1..], env);
                }
            }
        }
        PathStep::Downcast(_) => {
            *state = InitState::Moved;
        }
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
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
            InitState::Init | InitState::NeverInit | InitState::Moved | InitState::Diverged => {
                state.clone()
            }
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
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
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
    let Some(body) = &func.body else {
        return out;
    };
    if body.blocks.is_empty() {
        return out;
    }

    let locals = func.locals_map();
    let ctx = Ctx {
        env,
        locals: &locals,
    };
    let entry_states = run_fixpoint(&ctx, func, body);

    for block in &body.blocks {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut state = entry.clone();
        for (stmt, _) in &block.statements {
            ctx.transfer_stmt(stmt, &mut state);
        }
        // Return terminator has no state effect.
        out.push((block, state));
    }
    out
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let locals = func.locals_map();
    let ctx = Ctx {
        env,
        locals: &locals,
    };
    let init_entry_states = run_fixpoint(&ctx, func, body);

    for block in &body.blocks {
        let Some(init_entry) = init_entry_states.get(&block.label) else {
            continue;
        };
        let mut state = init_entry.clone();
        ctx.check_block(func, block, &mut state, d);
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
                s.refs.insert(Place::Var(p.name.clone()), rs);
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

/// Bridge between init_state's per-function context and the generic
/// dataflow framework. Instantiated per-function.
struct InitAnalysis<'a> {
    ctx: &'a Ctx<'a>,
    initial: PointState,
}

impl<'a> dataflow::Analysis for InitAnalysis<'a> {
    type State = PointState;
    fn direction(&self) -> dataflow::Direction {
        dataflow::Direction::Forward
    }
    fn initial_state(&self) -> Self::State {
        self.initial.clone()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join_point(a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement) {
        self.ctx.transfer_stmt(stmt, state)
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        self.ctx.transfer_terminator(term, state)
    }
}

fn run_fixpoint(ctx: &Ctx, func: &Function, body: &FunctionBody) -> IndexMap<String, PointState> {
    let analysis = InitAnalysis {
        ctx,
        initial: initial_state(func, body, ctx.env),
    };
    dataflow::run(&analysis, body)
}

// ---------- Transfer (state updates) ----------

impl<'a> Ctx<'a> {
    fn transfer_stmt(&self, stmt: &Statement, state: &mut PointState) {
        match stmt {
            Statement::Assign(target, rvalue) => {
                // Capture ref-state entries to transfer via `move src`
                // BEFORE apply_rvalue_moves removes them. If src has
                // ref-typed descendants (e.g. moving a whole struct),
                // each descendant's RefState transfers to the parallel
                // path under dst.
                let carried_refs = capture_carried_refs(target, rvalue, state);

                self.apply_rvalue_moves(rvalue, state);
                if let Some(t) = as_owned_path(target) {
                    close_refs_under(state, &t);
                }
                if matches!(target, Place::Deref(_)) {
                    self.apply_deref_op(target, DerefOp::Write, state, None);
                } else {
                    self.apply_write(target, state, InitState::Init);
                    if let (Some(t), RValue::Ref(kind, place)) = (as_owned_path(target), rvalue) {
                        if let Some(rs) = RefState::from_kind(kind) {
                            state.refs.insert(t, rs);
                        }
                        self.apply_eager_borrow_transition(kind, place, state);
                    }
                    for (dst_place, rs) in carried_refs {
                        state.refs.insert(dst_place, rs);
                    }
                }
            }
            Statement::Call(target, args) => {
                self.apply_operand_move(target, state);
                for a in args {
                    self.apply_operand_move(a, state);
                }
            }
            Statement::Drop(place) => {
                if let Some(consumed) = as_owned_path(place) {
                    close_refs_under(state, &consumed);
                }
                // `drop *r` — consume the pointee, transition r's is_init.
                self.apply_deref_op(place, DerefOp::Move, state, None);
                self.apply_move(place, state);
            }
            Statement::Unborrow(place) => {
                // Silent side of `unborrow r`: consume the borrower's ref
                // entry. Obligation checks happen in the diagnostic pass;
                // loan removal is handled by lifetime.
                if let Some(consumed) = as_owned_path(place) {
                    close_refs_under(state, &consumed);
                }
                self.apply_move(place, state);
            }
        }
    }

    fn transfer_terminator(&self, term: &Terminator, state: &mut PointState) {
        if let Terminator::Branch { cond, .. } = term {
            self.apply_operand_move(cond, state);
        }
    }

    fn apply_rvalue_moves(&self, rv: &RValue, state: &mut PointState) {
        match rv {
            RValue::Use(op) | RValue::EnumConstr(_, _, op) => self.apply_operand_move(op, state),
            RValue::Ref(_, _) => {}
        }
    }

    fn apply_operand_move(&self, op: &Operand, state: &mut PointState) {
        // Deref through *r transitions the ref's pointee state; do it before
        // the whole-var move that follows for consistency.
        match op {
            Operand::Copy(place) => self.apply_deref_op(place, DerefOp::Read, state, None),
            Operand::Move(place) => {
                self.apply_deref_op(place, DerefOp::Move, state, None);
                self.apply_move(place, state);
            }
            Operand::Const(_) => {}
        }
    }

    fn apply_write(&self, place: &Place, state: &mut PointState, leaf: InitState) {
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let root_state = state.locals.entry(root).or_insert(InitState::NeverInit);
        write_at(root_state, &root_ty, &path, self.env, leaf);
    }

    fn apply_move(&self, place: &Place, state: &mut PointState) {
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let root_state = state
            .locals
            .entry(root.clone())
            .or_insert(InitState::NeverInit);
        move_at(root_state, &root_ty, &path, self.env);
        // Move of a borrower place: drop its ref entry, and cascade
        // through any ref-typed descendants (an ancestor move like
        // `move b` closes all `b.p`, `b.q`, ...). Loans are handled by
        // lifetime; no obligation check here — that'd double-count if
        // the callee's signature enforces its own.
        if let Some(consumed) = as_owned_path(place) {
            close_refs_under(state, &consumed);
        }
    }
}

/// Remove all ref-state entries at `consumed` or any owned descendant.
/// Called at every consumption/overwrite site so an ancestor consume
/// cascades to all ref-typed fields it holds.
fn close_refs_under(state: &mut PointState, consumed: &Place) {
    let victims: Vec<Place> = state
        .refs
        .keys()
        .filter(|k| is_owned_ancestor_or_self(consumed, k))
        .cloned()
        .collect();
    for v in victims {
        state.refs.shift_remove(&v);
    }
}

/// True if `ancestor` is `descendant` or an owned-path prefix of it.
/// Both are assumed to be owned paths (no Deref).
fn is_owned_ancestor_or_self(ancestor: &Place, descendant: &Place) -> bool {
    let (ar, ap) = extract_path_owned(ancestor);
    let (dr, dp) = extract_path_owned(descendant);
    if ar != dr {
        return false;
    }
    if ap.len() > dp.len() {
        return false;
    }
    ap.iter()
        .zip(dp.iter())
        .all(|(a, b)| owned_step_eq(a, b))
}

fn owned_step_eq(a: &PathStep, b: &PathStep) -> bool {
    match (a, b) {
        (PathStep::Field(x), PathStep::Field(y)) => x == y,
        (PathStep::Downcast(x), PathStep::Downcast(y)) => x == y,
        _ => false,
    }
}

/// Like `extract_path`, but assumes the place is owned (no Deref) and
/// unwraps directly. Panics on Deref — call only on owned paths.
fn extract_path_owned(place: &Place) -> (String, Vec<PathStep>) {
    extract_path(place).expect("owned-path invariant violated")
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

impl<'a> Ctx<'a> {
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
        &self,
        place: &Place,
        op: DerefOp,
        state: &mut PointState,
        report: Option<(&Function, &BasicBlock, Span, &mut Diagnostics)>,
    ) {
        let Place::Deref(inner) = place else {
            return;
        };
        // The reference lives at `*inner`. We look up its RefState by
        // `inner` treated as an owned path.
        let Some(inner_place) = as_owned_path(inner) else {
            return;
        };
        let Some(inner_ty) = self.infer_ref_place_type(&inner_place) else {
            return;
        };
        let Type::Ref(kind, _) = inner_ty else {
            return;
        };

        let name_str = format_owned(&inner_place);

        if matches!(kind, RefKind::Shared) {
            if !matches!(op, DerefOp::Read) {
                if let Some((func, block, span, d)) = report {
                    push_error!(
                        d,
                        span,
                        func,
                        block,
                        "cannot mutate through shared reference '{}'",
                        name_str
                    );
                }
            }
            return;
        }

        let Some(rs) = state.refs.get(&inner_place).copied() else {
            if let Some((func, block, span, d)) = report {
                push_error!(
                    d,
                    span,
                    func,
                    block,
                    "cannot dereference '{}': reference state is unknown here",
                    name_str
                );
            }
            return;
        };

        let required_init = match op {
            DerefOp::Read | DerefOp::Move => true,
            DerefOp::Write => false,
        };
        if rs.is_init != required_init {
            if let Some((func, block, span, d)) = report {
                let action = match op {
                    DerefOp::Read => "read from",
                    DerefOp::Move => "move out of",
                    DerefOp::Write => "write into",
                };
                let expected = if required_init {
                    "initialized"
                } else {
                    "uninitialized"
                };
                let actual = if rs.is_init {
                    "initialized"
                } else {
                    "uninitialized"
                };
                push_error!(
                    d,
                    span,
                    func,
                    block,
                    "cannot {} pointee of '{}': pointee must be {} here, but is {}",
                    action,
                    name_str,
                    expected,
                    actual
                );
            }
        }

        // Apply the transition. Do this even on precondition failure so
        // downstream analysis sees consistent state.
        let new_is_init = match op {
            DerefOp::Read => rs.is_init,
            DerefOp::Move => false,
            DerefOp::Write => true,
        };
        state.refs.insert(
            inner_place,
            RefState {
                is_init: new_is_init,
                ends_init: rs.ends_init,
            },
        );
    }

    /// Infer the type of an owned-path place by walking the ctx's
    /// locals map for the root and projecting through fields/downcasts.
    /// Returns `None` if the place isn't a valid owned path or the
    /// projection doesn't resolve.
    fn infer_ref_place_type(&self, place: &Place) -> Option<Type> {
        let (root, path) = extract_path(place)?;
        let mut ty = self.locals.get(&root)?.clone();
        for step in &path {
            match step {
                PathStep::Field(f) => {
                    let fields = struct_fields_of(&ty, self.env)?;
                    ty = fields.iter().find(|fd| fd.name == *f)?.ty.clone();
                }
                PathStep::Downcast(v) => {
                    ty = enum_variant_payload_ty(&ty, v, self.env)?;
                }
                PathStep::Deref => return None,
            }
        }
        Some(ty)
    }
}

/// Format an owned path for diagnostics: `x`, `b.p`, `e as V`.
fn format_owned(place: &Place) -> String {
    let (root, path) = extract_path(place).expect("owned-path invariant");
    let mut s = root;
    for step in &path {
        match step {
            PathStep::Field(f) => {
                s.push('.');
                s.push_str(f);
            }
            PathStep::Downcast(v) => {
                s.push_str(" as ");
                s.push_str(v);
            }
            PathStep::Deref => unreachable!("owned-path invariant"),
        }
    }
    s
}

impl<'a> Ctx<'a> {

    /// If `place` is a whole-var ref binding with an outstanding obligation
    /// (`refs[name]` exists), verify its obligation is fulfilled and remove
    /// the entry. Called at any point where the reference value is being
    /// silently forgotten: `drop r`, or overwrite of `r`.
    fn close_ref_if_present(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let Some(owned) = as_owned_path(place) else {
            return;
        };
        // Cascade: closing/overwriting an ancestor implicitly forgets
        // every descendant ref. Each victim's obligation is checked.
        let victims: Vec<Place> = state
            .refs
            .keys()
            .filter(|k| is_owned_ancestor_or_self(&owned, k))
            .cloned()
            .collect();
        for v in victims {
            let rs = state.refs[&v];
            if !rs.obligation_fulfilled() {
                push_error!(
                    d,
                    span,
                    func,
                    block,
                    "reference '{}' has unfulfilled obligation here (is_init={}, ends_init={})",
                    format_owned(&v),
                    rs.is_init,
                    rs.ends_init
                );
            }
            state.refs.shift_remove(&v);
        }
    }
}

// ---------- Loan conflict check ----------

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

impl<'a> Ctx<'a> {
    /// Apply the eager init transition on the loaned place. Called at
    /// borrow creation.
    ///
    /// - Direct borrow of a local (`&kind x`, `&kind p.a`, ...): update
    ///   the locals init tree at that path via `apply_write`.
    /// - Reborrow through a reference (`&kind *r`): the loaned "place"
    ///   is the pointee of `r`, which locals-tracking can't reach.
    ///   Instead update `r`'s `RefState.is_init` to reflect the kind's
    ///   post, so when `s` expires `r` naturally resumes at the right
    ///   pointee-init state.
    fn apply_eager_borrow_transition(&self, kind: &RefKind, place: &Place, state: &mut PointState) {
        let Some(leaf) = loan_post_leaf(kind) else {
            return;
        };
        if let Some(parent) = deref_target(place) {
            if let Some(rs) = state.refs.get_mut(&parent) {
                rs.is_init = matches!(leaf, InitState::Init);
            }
            return;
        }
        self.apply_write(place, state, leaf);
    }
}

/// If `place` is `Deref(inner)` where `inner` is an owned path,
/// return that inner path. This is where the borrowed reference
/// lives (e.g. `*r` → `r`; `*b.p` → `b.p`).
fn deref_target(place: &Place) -> Option<Place> {
    let Place::Deref(inner) = place else {
        return None;
    };
    as_owned_path(inner)
}

/// If the assign is `dst_var = move src_var`, returns `src_var`. This is
/// the pattern where a reference's ref-state and loan should transfer
/// from src to dst instead of being lost.
fn ref_move_source(target: &Place, rvalue: &RValue) -> Option<Place> {
    if !is_owned_path(target) {
        return None;
    }
    let RValue::Use(Operand::Move(src)) = rvalue else {
        return None;
    };
    as_owned_path(src)
}

/// For an assign `target = move src` where both are owned paths, gather
/// every ref-state entry rooted at src (src itself, or any descendant
/// like src.p) and re-key it under target, replacing the src prefix
/// with target. E.g. moving `x` to `y` moves `x.r` → `y.r`.
///
/// Returns an empty vec for non-move rvalues or non-owned-path targets.
fn capture_carried_refs(
    target: &Place,
    rvalue: &RValue,
    state: &PointState,
) -> Vec<(Place, RefState)> {
    let Some(src) = ref_move_source(target, rvalue) else {
        return Vec::new();
    };
    let Some(dst) = as_owned_path(target) else {
        return Vec::new();
    };
    state
        .refs
        .iter()
        .filter_map(|(k, rs)| {
            let new_key = rekey(&src, &dst, k)?;
            Some((new_key, *rs))
        })
        .collect()
}

/// If `key` is `src` or a descendant of it, return the parallel path
/// under `dst`. `rekey(b, y, b.p)` → `y.p`. Returns None otherwise.
fn rekey(src: &Place, dst: &Place, key: &Place) -> Option<Place> {
    if !is_owned_ancestor_or_self(src, key) {
        return None;
    }
    // Extract the trailing suffix from `key` beyond `src`'s path length.
    let (_, src_path) = extract_path_owned(src);
    let (_, key_path) = extract_path_owned(key);
    let suffix = &key_path[src_path.len()..];
    let mut out = dst.clone();
    for step in suffix {
        out = match step {
            PathStep::Field(f) => Place::Field(Box::new(out), f.clone()),
            PathStep::Downcast(v) => Place::Downcast(Box::new(out), v.clone()),
            PathStep::Deref => unreachable!("owned-path invariant"),
        };
    }
    Some(out)
}

// ---------- Diagnostic pass ----------

impl<'a> Ctx<'a> {
    fn check_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        for (stmt, span) in &block.statements {
            self.check_and_transfer_stmt(func, block, stmt, *span, state, d);
        }
        self.check_and_transfer_terminator(func, block, state, d);
    }

    /// Combined check + transfer. Operands are consumed left-to-right so that a
    /// later operand in the same statement sees the state after prior moves —
    /// this is what makes `call f(move x, copy x)` correctly error on the second
    /// operand.
    fn check_and_transfer_stmt(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        match stmt {
            Statement::Assign(target, rvalue) => {
                // Capture ref-state entries to transfer via `move src`
                // BEFORE eval_rvalue runs. Cascade re-keys src.f → dst.f.
                let carried_refs = capture_carried_refs(target, rvalue, state);

                self.eval_rvalue(func, block, rvalue, span, state, d);
                self.check_lhs_downcast(func, block, target, span, state, d);

                // Overwriting a bound ref var is a silent-forget of the
                // pointee obligation; error unless already fulfilled.
                self.close_ref_if_present(func, block, target, span, state, d);

                // Deref-write: transition the ref's pointee state through *r.
                if matches!(target, Place::Deref(_)) {
                    self.apply_deref_op(
                        target,
                        DerefOp::Write,
                        state,
                        Some((func, block, span, d)),
                    );
                } else {
                    self.apply_write(target, state, InitState::Init);
                    if let (Some(t), RValue::Ref(kind, place)) = (as_owned_path(target), rvalue) {
                        if let Some(rs) = RefState::from_kind(kind) {
                            state.refs.insert(t, rs);
                        }
                        self.apply_eager_borrow_transition(kind, place, state);
                    }
                    for (dst_place, rs) in carried_refs {
                        state.refs.insert(dst_place, rs);
                    }
                }
            }
            Statement::Call(target, args) => {
                self.eval_operand(func, block, target, span, state, d);
                for a in args {
                    self.eval_operand(func, block, a, span, state, d);
                }
            }
            Statement::Drop(place) => {
                // Read the place, then consume it. Same effect on state as
                // `move`. The substructural checker (separate pass) is the
                // one that will require the type to be Drop. For a ref-typed
                // Var, also verify the pointee obligation before forgetting.
                self.check_place_read(func, block, place, span, state, d);
                self.close_ref_if_present(func, block, place, span, state, d);
                // `drop *r` — consume the pointee, transition r's is_init.
                self.apply_deref_op(place, DerefOp::Move, state, Some((func, block, span, d)));
                self.apply_move(place, state);
            }
            Statement::Unborrow(place) => {
                // Explicit end-of-loan. Requires the borrower to be Init
                // and its (is_init, ends_init) obligation fulfilled — both
                // checked by close_ref_if_present. Then consume the borrower.
                self.check_place_read(func, block, place, span, state, d);
                self.close_ref_if_present(func, block, place, span, state, d);
                self.apply_move(place, state);
            }
        }
    }

    fn check_and_transfer_terminator(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let ts = block.terminator_span;
        match &block.terminator {
            Terminator::Branch { cond, .. } => {
                self.eval_operand(func, block, cond, ts, state, d)
            }
            Terminator::SwitchEnum { place, .. } => {
                // Discriminant read: no move, no consumption.
                self.check_place_read(func, block, place, ts, state, d);
            }
            _ => {}
        }
    }

    fn eval_rvalue(
        &self,
        func: &Function,
        block: &BasicBlock,
        rv: &RValue,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        match rv {
            RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
                self.eval_operand(func, block, op, span, state, d);
            }
            RValue::Ref(kind, place) => {
                self.check_borrow_precondition(func, block, kind, place, span, state, d);
            }
        }
    }

    /// Verify that the state of the borrowed place matches the reference
    /// kind's creation-is_init:
    ///   * `&`, `&mut`, `&drop` require the pointee to be Init.
    ///   * `&out`, `&uninit` require the pointee to be uninitialized
    ///     (NeverInit or Moved).
    ///
    /// The check inspects the leaf state via [`read_at`]; partial and
    /// diverged states at the leaf never match either precondition, so
    /// they're rejected with a clear "not fully X" message.
    fn check_borrow_precondition(
        &self,
        func: &Function,
        block: &BasicBlock,
        kind: &RefKind,
        place: &Place,
        span: Span,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let (requires_init, kind_str) = match kind {
            RefKind::Shared => (true, "&"),
            RefKind::Mut => (true, "&mut"),
            RefKind::Drop => (true, "&drop"),
            RefKind::Out => (false, "&out"),
            RefKind::Uninit => (false, "&uninit"),
        };

        // Reborrow `&kind *inner`: the pointee's init state lives in
        // inner's RefState, not the locals tree. Any owned path can be
        // reborrowed through — bare `r`, `b.p`, `e as V`, etc.
        if let Some(parent) = deref_target(place) {
            let parent_str = format_owned(&parent);
            let Some(parent_rs) = state.refs.get(&parent) else {
                push_error!(
                    d, span, func, block,
                    "cannot create {} of '*{}': parent reference '{}' is not bound here",
                    kind_str, parent_str, parent_str
                );
                return;
            };
            if parent_rs.is_init != requires_init {
                let expected = if requires_init { "initialized" } else { "uninitialized" };
                let actual = if parent_rs.is_init { "initialized" } else { "uninitialized" };
                push_error!(
                    d, span, func, block,
                    "cannot create {} of '*{}': pointee must be {} at borrow, but is {}",
                    kind_str, parent_str, expected, actual
                );
            }
            return;
        }

        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let leaf = read_at(root_state, &root_ty, &path, self.env);

        let ok = if requires_init {
            matches!(leaf, InitState::Init)
        } else {
            matches!(leaf, InitState::NeverInit | InitState::Moved)
        };
        if ok {
            return;
        }

        let path_str = format_path(&root, &path);
        let expected = if requires_init {
            "initialized"
        } else {
            "uninitialized"
        };
        let actual = describe_state(&leaf);
        push_error!(
            d,
            span,
            func,
            block,
            "cannot create {} of '{}': place must be {} at borrow, but is {}",
            kind_str,
            path_str,
            expected,
            actual
        );
    }
}

fn format_path(root: &str, path: &[PathStep]) -> String {
    let mut s = String::from(root);
    for step in path {
        match step {
            PathStep::Field(f) => {
                s.push('.');
                s.push_str(f);
            }
            PathStep::Downcast(v) => {
                s.push_str(" as ");
                s.push_str(v);
            }
            PathStep::Deref => {
                unreachable!("init_state uses extract_path which never yields Deref")
            }
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

impl<'a> Ctx<'a> {
    fn eval_operand(
        &self,
        func: &Function,
        block: &BasicBlock,
        op: &Operand,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        self.check_operand_read(func, block, op, span, state, d);
        // Deref-op transitions for *r in operand position.
        match op {
            Operand::Copy(place) => {
                self.apply_deref_op(place, DerefOp::Read, state, Some((func, block, span, d)));
            }
            Operand::Move(place) => {
                self.apply_deref_op(place, DerefOp::Move, state, Some((func, block, span, d)));
            }
            Operand::Const(_) => {}
        }
        self.apply_operand_move(op, state);
    }

    fn check_operand_read(
        &self,
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
        self.check_place_read(func, block, place, span, state, d);
    }

    /// If the LHS path contains a `Downcast`, the enum being downcast must be
    /// `Init` at that point — you can't refine an uninitialized enum by writing
    /// through a variant projection. Enum construction goes via `Name::V(...)`.
    fn check_lhs_downcast(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        span: Span,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(idx) = path.iter().position(|s| matches!(s, PathStep::Downcast(_))) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let prefix_state = read_at(root_state, &root_ty, &path[..idx], self.env);
        if !matches!(prefix_state, InitState::Init) {
            push_error!(
                d,
                span,
                func,
                block,
                "cannot write through variant projection: '{}' is not initialized here",
                root
            );
        }
    }

    fn check_place_read(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        span: Span,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let leaf = read_at(root_state, &root_ty, &path, self.env);
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
}

#[cfg(test)]
mod tests_borrows;
#[cfg(test)]
mod tests_cfg_shapes;
#[cfg(test)]
mod tests_lifecycle;
