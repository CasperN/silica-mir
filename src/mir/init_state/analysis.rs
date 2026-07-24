use crate::diagnostics::{DiagCode, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow;
use crate::mir::helpers::*;
use crate::mir::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::{BTreeMap, BTreeSet};

/// Machine-readable error codes emitted by the initialization-state
/// pass. One variant per user-observable failure kind; message text
/// carries the specifics (place name, kinds, etc).
///
/// Push sites that surface the same conceptual failure share a code
/// even when the surface path differs (e.g. wrong pointee state at a
/// reborrow vs. wrong place state at a direct borrow both fold into
/// `BorrowStateMismatch`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InitStateCode {
    // ---- Reads (place-use checks) ----
    /// Read of a local (or projection thereof) whose root is `NeverInit`.
    UseBeforeInit,
    /// Read of a local (or projection thereof) whose root is `Moved`.
    UseAfterMove,
    /// Read of a place whose init state differs across predecessors
    /// (`Diverged`).
    UseInconsistent,
    /// Read of a place whose state is `Partial(...)` — some fields
    /// initialized, others not.
    UsePartiallyInit,

    // ---- Consumption / drop obligations ----
    /// Assignment target still holds an `Init` value whose type isn't
    /// `Drop`. The caller must consume it (e.g. `drop target;`) before
    /// the overwrite.
    OverwriteWithoutDrop,
    /// A ref-typed place is being silently forgotten (overwrite, drop,
    /// unborrow) while its (is_init, ends_init) obligation is
    /// unfulfilled.
    RefObligationUnfulfilled,
    /// At `return`, some non-ref path is still `Init` (or `Diverged`)
    /// — the value would leak. After elaboration, this means
    /// drop-elab couldn't insert enough drops.
    ReturnValueLeak,
    /// A `require_uninit place` assertion reached the final checker while
    /// `place` still held a value, was only partially consumed, differed
    /// across control-flow paths, or was not a statically-owned place.
    RequireUninitNotSatisfied,
    /// A `move` operand crossing a call boundary carries a ref-typed
    /// place (or a container of one) whose current pointee state
    /// doesn't match the declared kind's entry state. The callee's
    /// signature promises to receive a reference in its kind's
    /// creation-state (`&mut` → Init pointee, `&out` → Uninit,
    /// `&drop` → Init, `&uninit` → Uninit); a caller that has drifted
    /// from that state can't hand it off without lying to the callee.
    RefCallEntryMismatch,
    // ---- Through-reference operations (`*r`) ----
    /// Attempted write or move through a shared reference (`&T`).
    /// Shared refs only permit reads.
    WriteThroughSharedRef,
    /// `*r` or `&kind *r` where no `RefState` is tracked for the
    /// parent reference — its pointee state is unknown at this point.
    ReferenceStateUnknown,
    /// `*r` (read/write/move) where the pointee's is_init doesn't
    /// match the operation's required precondition.
    DerefPointeeStateMismatch,

    // ---- Borrow creation preconditions ----
    /// `&kind place` where the pointee/place is in the wrong init
    /// state for the borrow kind (e.g. `&mut` of an uninitialized
    /// place, `&out` of an initialized non-Drop place).
    BorrowStateMismatch,
    /// `&kind a[i]` with a non-constant index, but the containing
    /// array isn't in a uniform state — some slots satisfy the
    /// precondition and some don't, so no single-slot borrow is safe.
    BorrowDynamicIndexNonUniform,

    // ---- LHS projections ----
    /// Assignment through a downcast (`x as V . …`) where the enum
    /// being downcast isn't `Init` at that point. Enum construction
    /// must go via `Name::V(...)`.
    WriteThroughUninitEnumProjection,
}

impl From<InitStateCode> for DiagCode {
    fn from(code: InitStateCode) -> DiagCode {
        DiagCode::InitState(code)
    }
}
use InitStateCode::*;

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

/// Per-reference-variable state: the current pointee state and the
/// (post-expiry) required state. Only tracked for exclusive reference
/// kinds (`&mut`, `&out`, `&drop`, `&uninit`). Shared references (`&T`)
/// don't carry an obligation — they're `Copy Drop`.
///
/// `pointee` tracks the pointee's initialization at this program point
/// with full `InitState` granularity, so per-field writes via
/// `r.*.field = ...` on a struct pointee accumulate into a `Partial`
/// state that folds back to `Init` when every field lands (via
/// `canonicalize`). `ends_init` is what the (cur, post) rule requires
/// by the time the loan expires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefState {
    pub pointee: InitState,
    pub ends_init: bool,
}

impl RefState {
    /// The (pointee, ends_init) at borrow creation for a given ref kind.
    /// Returns `None` for shared borrows (no obligation).
    pub fn from_kind(kind: &RefKind) -> Option<Self> {
        match kind {
            RefKind::Shared => None,
            RefKind::Mut => Some(RefState {
                pointee: InitState::Init,
                ends_init: true,
            }),
            RefKind::Out => Some(RefState {
                pointee: InitState::NeverInit,
                ends_init: true,
            }),
            RefKind::Drop => Some(RefState {
                pointee: InitState::Init,
                ends_init: false,
            }),
            RefKind::Uninit => Some(RefState {
                pointee: InitState::NeverInit,
                ends_init: false,
            }),
        }
    }

    /// Convenience: is the pointee fully initialized right now?
    pub fn is_init(&self) -> bool {
        matches!(self.pointee, InitState::Init)
    }

    /// Convenience: has the pointee been fully consumed (or never init)?
    pub fn is_uninit(&self) -> bool {
        matches!(self.pointee, InitState::NeverInit | InitState::Moved)
    }

    /// Does the current pointee state satisfy the exit requirement?
    /// `ends_init = true` demands a fully-Init pointee at expiry;
    /// `ends_init = false` demands the pointee has been consumed. Any
    /// intermediate state (Partial, Diverged) fails either obligation.
    pub fn obligation_fulfilled(&self) -> bool {
        if self.ends_init {
            self.is_init()
        } else {
            self.is_uninit()
        }
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

pub(super) struct InitStateContext<'a> {
    pub(super) env: &'a Env,
    pub(super) locals: &'a IndexMap<String, Type>,
}

// ---------- Type lookups ----------

/// Fields of a struct type with type-parameter substitution applied.
/// `Box<i64>` → `[{inner: i64}]`, not `[{inner: T}]` — otherwise deep
/// nested projections (`p.f.g` on `Outer<Inner<i64>>`) lose the type
/// after the first step and downstream lookups fail.
pub(super) fn struct_fields_of(ty: &Type, env: &Env) -> Option<Vec<StructField>> {
    let TypeKind::Custom(name, _, args) = &ty.kind else {
        return None;
    };
    let TypeDecl::Struct(s) = env.types.get(name)? else {
        return None;
    };
    Some(
        s.fields
            .iter()
            .map(|f| StructField {
                name: f.name.clone(),
                ty: s.meta.substitute_types(&f.ty, args),
                span: f.span,
            })
            .collect(),
    )
}

pub(super) fn enum_variant_payload_ty(ty: &Type, variant: &str, env: &Env) -> Option<Type> {
    let TypeKind::Custom(name, _, args) = &ty.kind else {
        return None;
    };
    let TypeDecl::Enum(e) = env.types.get(name)? else {
        return None;
    };
    let payload = e.variants.iter().find(|v| v.name == variant)?;
    Some(e.meta.substitute_types(&payload.ty, args))
}

// ---------- Canonicalization ----------

/// If a `Partial` has all fields at the same simple (non-Partial) state,
/// collapse to that state. Applied recursively to nested Partials.
pub(super) fn canonicalize(state: InitState) -> InitState {
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
pub(super) fn expand_uniform(state: &InitState, fields: &[StructField]) -> BTreeMap<String, InitState> {
    fields
        .iter()
        .map(|f| (f.name.clone(), state.clone()))
        .collect()
}

// ---------- Joins ----------

pub(super) fn join_state(a: &InitState, b: &InitState) -> InitState {
    if a == b {
        return a.clone();
    }
    // `NeverInit` and `Moved` both mean "no value present at this path".
    // They differ historically (never written vs. written and moved out)
    // but both are consumed for leak/drop purposes, so their join is one
    // of them rather than `Diverged`.
    if is_empty(a) && is_empty(b) {
        return InitState::NeverInit;
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

pub(super) fn is_empty(s: &InitState) -> bool {
    matches!(s, InitState::NeverInit | InitState::Moved)
}

pub(super) fn expand_from_partial_keys(
    state: &InitState,
    template: &BTreeMap<String, InitState>,
) -> BTreeMap<String, InitState> {
    template
        .keys()
        .map(|k| (k.clone(), state.clone()))
        .collect()
}

pub(super) fn join_partials(ma: &BTreeMap<String, InitState>, mb: &BTreeMap<String, InitState>) -> InitState {
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

pub(super) fn join_point(a: &PointState, b: &PointState) -> PointState {
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
                refs.insert(place.clone(), ra.clone());
            }
        }
    }
    PointState { locals, refs }
}

// ---------- Path walks ----------

/// Apply a write of `leaf_state` at the given path from `state` (which is
/// the current state of the root Var). Promotes intermediate states to
/// Partial as needed. Downcast steps in a write path do not update state.
pub(super) fn write_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env, leaf_state: InitState) {
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
                *state = InitState::Partial(expand_uniform(state, &fields));
            }
            let field_ty = fields.into_iter().find(|fd| fd.name == *f).map(|fd| fd.ty);
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    write_at(field_state, &field_ty, &path[1..], env, leaf_state);
                }
            }
        }
        PathStep::Index(Some(k)) => {
            let Some((elem_ty, n)) = array_info(ty) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform_array(state, n));
            }
            if let InitState::Partial(map) = &mut *state {
                let key = k.to_string();
                if let Some(slot_state) = map.get_mut(&key) {
                    write_at(slot_state, &elem_ty, &path[1..], env, leaf_state);
                }
            }
        }
        PathStep::Downcast(_) => {
            // Direct write into a variant payload does not initialize the
            // enum in our model (enum construction goes via `Name::V(...)`).
        }
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
        PathStep::Index(None) => {
            unreachable!("init_state uses extract_path which rejects dynamic indices")
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Array info helpers for init tracking. `TypeKind::Array(elem, n)` →
/// `(elem, n)`; otherwise `None`.
pub(super) fn array_info(ty: &Type) -> Option<(Type, u64)> {
    if let TypeKind::Array(elem, n) = &ty.kind {
        Some(((**elem).clone(), *n))
    } else {
        None
    }
}

/// Expand a uniform state into an array `Partial` with N slots keyed
/// by `"0"`, `"1"`, ..., `"N-1"`.
pub(super) fn expand_uniform_array(state: &InitState, n: u64) -> BTreeMap<String, InitState> {
    (0..n).map(|i| (i.to_string(), state.clone())).collect()
}

/// Apply a move at the given path. Downcast steps set the whole enum to
/// `Moved` (enum atomicity).
pub(super) fn move_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env) {
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
                *state = InitState::Partial(expand_uniform(state, &fields));
            }
            let field_ty = fields.into_iter().find(|fd| fd.name == *f).map(|fd| fd.ty);
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    move_at(field_state, &field_ty, &path[1..], env);
                }
            }
        }
        PathStep::Index(Some(k)) => {
            let Some((elem_ty, n)) = array_info(ty) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform_array(state, n));
            }
            if let InitState::Partial(map) = &mut *state {
                let key = k.to_string();
                if let Some(slot_state) = map.get_mut(&key) {
                    move_at(slot_state, &elem_ty, &path[1..], env);
                }
            }
        }
        PathStep::Downcast(_) => {
            *state = InitState::Moved;
        }
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
        PathStep::Index(None) => {
            unreachable!("init_state uses extract_path which rejects dynamic indices")
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Return the effective state at the given path (for a read check).
pub(super) fn read_at(state: &InitState, ty: &Type, path: &[PathStep], env: &Env) -> InitState {
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
                    .and_then(|fs| fs.into_iter().find(|fd| fd.name == *f))
                    .map(|fd| fd.ty);
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
        PathStep::Index(Some(k)) => match state {
            InitState::Init | InitState::NeverInit | InitState::Moved | InitState::Diverged => {
                state.clone()
            }
            InitState::Partial(map) => {
                let elem_ty = array_info(ty).map(|(e, _)| e);
                let slot_state = map
                    .get(&k.to_string())
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                match elem_ty {
                    Some(et) => read_at(&slot_state, &et, &path[1..], env),
                    None => slot_state,
                }
            }
        },
        PathStep::Deref => unreachable!("init_state uses extract_path which never yields Deref"),
        PathStep::Index(None) => {
            unreachable!("init_state uses extract_path which rejects dynamic indices")
        }
    }
}

// ---------- Top-level public analysis API ----------

/// Compute per-block entry `PointState` for `func`. Same fixpoint as
/// `states_before_returns` uses internally, exposed so callers (drop
/// elaboration) can then walk any block from its entry to compute
/// arbitrary intermediate states (e.g. a predecessor's exit).
///
/// Also returns a closure that advances a state through a single
/// statement (silent — no diagnostics), so callers can walk a block
/// forward from its entry state to compute intermediate points.
pub fn block_entry_states(env: &Env, func: &Function) -> IndexMap<String, PointState> {
    let Some(body) = &func.body else {
        return IndexMap::new();
    };
    if body.blocks.is_empty() {
        return IndexMap::new();
    }
    let locals = func.locals_map();
    let ctx = InitStateContext {
        env,
        locals: &locals,
    };
    run_fixpoint(&ctx, func, body)
}

/// Advance `state` silently through `stmt` (no diagnostics). Uses the
/// same transfer as the fixpoint. For callers that hold a per-block
/// entry state and want to reconstruct the state at any point inside
/// the block.
pub fn transfer_stmt_silent(env: &Env, func: &Function, stmt: &Statement, state: &mut PointState) {
    let locals = func.locals_map();
    let ctx = InitStateContext {
        env,
        locals: &locals,
    };
    ctx.transfer_stmt(stmt, state);
}

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
    let ctx = InitStateContext {
        env,
        locals: &locals,
    };
    let entry_states = run_fixpoint(&ctx, func, body);

    for block in &body.blocks {
        if !matches!(block.terminator.kind, TerminatorKind::Return) {
            continue;
        }
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut state = entry.clone();
        for stmt in &block.statements {
            ctx.transfer_stmt(stmt, &mut state);
        }
        // Return terminator has no state effect.
        out.push((block, state));
    }
    out
}

pub(super) fn initial_state(func: &Function, body: &FunctionBody, env: &Env) -> PointState {
    let mut s = PointState::default();
    for p in &func.params {
        s.locals.insert(p.name.clone(), InitState::Init);
        // Parameters are fully initialized at entry, including every
        // reference-typed field of a by-value struct parameter. Enum
        // payloads deliberately stop the walk: only one variant exists at
        // runtime, so seeding every variant would invent obligations for
        // inactive storage until we have discriminant-sensitive entry facts.
        let mut visited = BTreeSet::new();
        seed_parameter_ref_states(
            var_place(p.name.clone()),
            &p.ty,
            env,
            &mut visited,
            &mut s.refs,
        );
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

pub(super) fn seed_parameter_ref_states(
    place: Place,
    ty: &Type,
    env: &Env,
    visited: &mut BTreeSet<String>,
    refs: &mut IndexMap<Place, RefState>,
) {
    if let TypeKind::Ref(kind, _, _) = &ty.kind {
        if let Some(state) = RefState::from_kind(kind) {
            refs.insert(place, state);
        }
        return;
    }

    let TypeKind::Custom(name, _, args) = &ty.kind else {
        return;
    };
    if !visited.insert(name.clone()) {
        return;
    }
    if let Some(TypeDecl::Struct(def)) = env.types.get(name) {
        let fields: Vec<_> = def
            .fields
            .iter()
            .map(|field| {
                (
                    field.name.clone(),
                    def.meta.substitute_types(&field.ty, args),
                )
            })
            .collect();
        for (field_name, field_ty) in fields {
            seed_parameter_ref_states(
                field_place(place.clone(), field_name),
                &field_ty,
                env,
                visited,
                refs,
            );
        }
    }
    visited.remove(name);
}

pub(super) fn is_trivially_init(ty: &Type, env: &Env) -> bool {
    match &ty.kind {
        TypeKind::Custom(name, _, _) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => s.fields.is_empty(),
            _ => false,
        },
        _ => false,
    }
}

/// Bridge between init_state's per-function context and the generic
/// dataflow framework. Instantiated per-function.
struct InitAnalysis<'a> {
    ctx: &'a InitStateContext<'a>,
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
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, _span: Span) {
        self.ctx.transfer_stmt(stmt, state)
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        self.ctx.transfer_terminator(term, state)
    }
}

pub(super) fn run_fixpoint(
    ctx: &InitStateContext,
    func: &Function,
    body: &FunctionBody,
) -> IndexMap<String, PointState> {
    let analysis = InitAnalysis {
        ctx,
        initial: initial_state(func, body, ctx.env),
    };
    dataflow::run(&analysis, body)
}

// ---------- Transfer (state updates) ----------

impl<'a> InitStateContext<'a> {
    pub(super) fn transfer_stmt(&self, stmt: &Statement, state: &mut PointState) {
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
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
                self.apply_target_write_state(target, rvalue, carried_refs, state, None);
            }
            StatementKind::Call(target, args) => {
                self.apply_operand_move(target, state);
                for a in args {
                    self.apply_operand_move(a, state);
                }
            }
            StatementKind::Drop(place) => {
                if let Some(consumed) = as_owned_path(place) {
                    close_refs_under(state, &consumed);
                }
                self.apply_consume_state(place, state, None);
            }
            StatementKind::Unborrow(place) => {
                // Silent side of `unborrow r`: consume the borrower's ref
                // entry. Obligation checks happen in the diagnostic pass;
                // loan removal is handled by lifetime.
                if let Some(consumed) = as_owned_path(place) {
                    close_refs_under(state, &consumed);
                }
                self.apply_move(place, state);
            }
            StatementKind::RequireUninit(place) => {
                // A requirement is a checked postcondition for dataflow,
                // including drop-elaboration planning: later program points
                // may assume the owned place is gone.
                self.apply_require_uninit_postcondition(place, state);
            }
        }
    }

    pub(super) fn transfer_terminator(&self, term: &Terminator, state: &mut PointState) {
        if let TerminatorKind::Branch { cond, .. } = &term.kind {
            self.apply_operand_move(cond, state);
        }
    }

    /// Write phase of an assignment. Shared between the silent
    /// (`transfer_stmt`) and diagnostic (`check_and_transfer_stmt`)
    /// walkers — the only per-path knob is `report`, which controls
    /// whether deref-write errors are emitted or swallowed.
    ///
    /// Preconditions: `apply_rvalue_moves` (or `eval_rvalue`) has
    /// already applied source reads; the target's ref-if-any has
    /// been closed by the caller.
    pub(super) fn apply_target_write_state(
        &self,
        target: &Place,
        rvalue: &RValue,
        carried_refs: Vec<(Place, RefState)>,
        state: &mut PointState,
        report: Option<(&Function, &BasicBlock, Span, &mut Diagnostics)>,
    ) {
        if matches!(target, Place::Deref(_)) {
            self.apply_deref_op(target, DerefOp::Write, state, report);
        } else {
            self.apply_write(target, state, InitState::Init);
            if let Some(t) = as_owned_path(target) {
                if let RValue::Ref(kind, place) = rvalue {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(t.clone(), rs);
                    }
                    self.apply_eager_borrow_transition(kind, place, state);
                } else if let RValue::PtrCast(_, to_ty) = rvalue {
                    if let TypeKind::Ref(kind, _, _) = &to_ty.kind {
                        if let Some(rs) = RefState::from_kind(kind) {
                            state.refs.insert(t.clone(), rs);
                        }
                    }
                }
            }
            for (dst_place, rs) in carried_refs {
                state.refs.insert(dst_place, rs);
            }
        }
    }

    /// Consumption tail shared by `drop place`: deref-through if
    /// `place` is `*r` (moves the pointee), then whole-place move.
    /// `report` is passed through to `apply_deref_op` so diagnostic
    /// callers surface pointee-state errors at the drop site.
    pub(super) fn apply_consume_state(
        &self,
        place: &Place,
        state: &mut PointState,
        report: Option<(&Function, &BasicBlock, Span, &mut Diagnostics)>,
    ) {
        self.apply_deref_op(place, DerefOp::Move, state, report);
        self.apply_move(place, state);
    }

    pub(super) fn apply_rvalue_moves(&self, rv: &RValue, state: &mut PointState) {
        match rv {
            RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                self.apply_operand_move(op, state)
            }
            RValue::Ref(_, _) | RValue::RawRef(_) => {}
            RValue::ArrayLit(ops) => {
                for op in ops {
                    self.apply_operand_move(op, state);
                }
            }
        }
    }

    pub(super) fn apply_operand_move(&self, op: &Operand, state: &mut PointState) {
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

    pub(super) fn apply_write(&self, place: &Place, state: &mut PointState, leaf: InitState) {
        let Some((root, path)) = extract_path(place) else {
            // Path passes through a Deref (e.g. `r.*.field = ...`).
            // Route the write into the ref's pointee state so per-field
            // writes accumulate; `canonicalize` folds `Partial{all-Init}`
            // back to `Init` once every field lands.
            self.apply_pointee_write(place, leaf, state);
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let root_state = state.locals.entry(root).or_insert(InitState::NeverInit);
        write_at(root_state, &root_ty, &path, self.env, leaf);
    }

    pub(super) fn apply_move(&self, place: &Place, state: &mut PointState) {
        let Some((root, path)) = extract_path(place) else {
            // Move out through a Deref (e.g. `move r.*.field`). Route
            // into the ref's pointee so partial consumption of a struct
            // pointee accumulates as `Partial{...}` and the exit
            // obligation check catches "not fully (de)initialized"
            // states instead of silently accepting.
            self.apply_pointee_move(place, state);
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
        // lifetime. Obligation checks belong at the operation that
        // *observes* the transfer: `close_ref_if_present` runs at
        // drop / unborrow / assign-target overwrite for the expiry
        // side, and `check_call_transfer` runs at call-boundary moves
        // for the entry side.
        if let Some(consumed) = as_owned_path(place) {
            close_refs_under(state, &consumed);
        }
    }

    /// A valid `require_uninit` establishes an analysis postcondition even
    /// when the preceding check reported that it was not satisfied. This is
    /// error recovery: later scope exits must not repeat the same leak.
    ///
    /// Invalid assertion targets establish no postcondition. In particular, a
    /// dereference would otherwise mutate its pointee state despite being
    /// outside the assertion's statically-owned-place contract.
    pub(super) fn apply_require_uninit_postcondition(&self, place: &Place, state: &mut PointState) {
        if as_owned_path(place).is_some() {
            self.apply_move(place, state);
        }
    }

    /// Route a write into the pointee of a ref. `place` must have a
    /// `Deref` node in its projection chain; the projections above the
    /// outermost Deref address the pointee, the Place below the Deref
    /// locates the ref.
    pub(super) fn apply_pointee_write(&self, place: &Place, leaf: InitState, state: &mut PointState) {
        let Some((ref_place, sub_path, pointee_ty)) = self.resolve_pointee_target(place, state)
        else {
            return;
        };
        let Some(rs) = state.refs.get_mut(&ref_place) else {
            return;
        };
        write_at(&mut rs.pointee, &pointee_ty, &sub_path, self.env, leaf);
        rs.pointee = canonicalize(std::mem::replace(&mut rs.pointee, InitState::NeverInit));
    }

    /// Route a move out of the pointee of a ref. See
    /// [`apply_pointee_write`] for the split model.
    pub(super) fn apply_pointee_move(&self, place: &Place, state: &mut PointState) {
        let Some((ref_place, sub_path, pointee_ty)) = self.resolve_pointee_target(place, state)
        else {
            return;
        };
        let Some(rs) = state.refs.get_mut(&ref_place) else {
            return;
        };
        move_at(&mut rs.pointee, &pointee_ty, &sub_path, self.env);
        rs.pointee = canonicalize(std::mem::replace(&mut rs.pointee, InitState::NeverInit));
    }

    /// Split `place` at its outermost `Deref` into (ref location,
    /// projections into the pointee, pointee type). Returns `None` if
    /// no `Deref` is present or if the ref's type / state can't be
    /// resolved.
    pub(super) fn resolve_pointee_target(
        &self,
        place: &Place,
        state: &PointState,
    ) -> Option<(Place, Vec<PathStep>, Type)> {
        let (ref_place, sub_path) = split_at_outermost_deref(place)?;
        // The ref must be bound at this point; otherwise there is no
        // pointee state to update. Silent no-op mirrors the extract_path
        // early-return elsewhere.
        state.refs.get(&ref_place)?;
        let ref_ty = self.infer_ref_place_type(&ref_place)?;
        let TypeKind::Ref(_, _, pointee_ty) = ref_ty.kind else {
            return None;
        };
        Some((ref_place, sub_path, *pointee_ty))
    }
}

/// Walk `place` outer-in, collecting projection steps until an
/// outermost `Deref` is hit. Returns (deref inner, projections above
/// the deref, in path order) or `None` if there is no `Deref`.
pub(super) fn split_at_outermost_deref(place: &Place) -> Option<(Place, Vec<PathStep>)> {
    let mut steps: Vec<PathStep> = Vec::new();
    let mut cur = place;
    loop {
        match cur {
            Place::Deref(inner) => {
                steps.reverse();
                return Some(((**inner).clone(), steps));
            }
            Place::Field(inner, f) => {
                steps.push(PathStep::Field(f.clone()));
                cur = inner;
            }
            Place::Downcast(inner, v) => {
                steps.push(PathStep::Downcast(v.clone()));
                cur = inner;
            }
            Place::Index(inner, op) => {
                steps.push(PathStep::Index(const_int_operand(op)));
                cur = inner;
            }
            Place::Var(_) => return None,
        }
    }
}

/// Remove all ref-state entries at `consumed` or any owned descendant.
/// Called at every consumption/overwrite site so an ancestor consume
/// cascades to all ref-typed fields it holds.
pub(super) fn close_refs_under(state: &mut PointState, consumed: &Place) {
    let victims: Vec<Place> = state
        .refs
        .keys()
        .filter(|k| is_ancestor_or_self(consumed, k))
        .cloned()
        .collect();
    for v in victims {
        state.refs.shift_remove(&v);
    }
}

/// Which kind of dereference operation is being performed. Distinguishes
/// state precondition (init vs uninit) and post-condition transition.
#[derive(Debug, Clone, Copy)]
pub(super) enum DerefOp {
    /// `copy *r` / discriminant read of *r — requires pointee Init, no
    /// transition.
    Read,
    /// `move *r` — requires pointee Init, transitions to Uninit.
    Move,
    /// `*r = v` — requires pointee Uninit, transitions to Init.
    Write,
}

impl<'a> InitStateContext<'a> {
    /// Apply the state effect of an operation through `*r`. If `place` isn't
    /// a shallow deref of a Var, returns without effect.
    ///
    /// When `report` is `Some`, precondition failures emit errors; when `None`
    /// the check is silent (used from the fixpoint transfer).
    ///
    /// Nested paths like `(*r).field` aren't handled here — pinned as a
    /// deferred limitation. Only the shape `*r` where `r: exclusive-ref` is
    /// tracked; shared refs generate a diagnostic on write/move but not read.
    pub(super) fn apply_deref_op(
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
        let TypeKind::Ref(kind, _, _) = inner_ty.kind else {
            return;
        };

        let name_str = format_place(&inner_place);

        if matches!(kind, RefKind::Shared) {
            if !matches!(op, DerefOp::Read) {
                if let Some((func, block, span, d)) = report {
                    let action = match op {
                        DerefOp::Move => "move out through",
                        DerefOp::Write => "write through",
                        DerefOp::Read => unreachable!(),
                    };
                    d.push_error(diag(
                        WriteThroughSharedRef,
                        span,
                        func,
                        block,
                        format!("cannot {} shared reference '{}'", action, name_str),
                    ));
                }
            }
            return;
        }

        let Some(rs) = state.refs.get(&inner_place).cloned() else {
            if let Some((func, block, span, d)) = report {
                d.push_error(diag(
                    ReferenceStateUnknown,
                    span,
                    func,
                    block,
                    format!(
                        "cannot dereference '{}': reference state is unknown here",
                        name_str
                    ),
                ));
            }
            return;
        };

        let required_init = match op {
            DerefOp::Read | DerefOp::Move => true,
            DerefOp::Write => false,
        };
        let currently_init = rs.is_init();
        if currently_init != required_init {
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
                let actual = describe_pointee_state(&rs.pointee);
                d.push_error(diag(
                    DerefPointeeStateMismatch,
                    span,
                    func,
                    block,
                    format!(
                        "cannot {} pointee of '{}': pointee must be {} here, but is {}",
                        action, name_str, expected, actual
                    ),
                ));
            }
        }

        // Apply the transition. Do this even on precondition failure so
        // downstream analysis sees consistent state.
        let new_pointee = match op {
            DerefOp::Read => rs.pointee,
            DerefOp::Move => InitState::Moved,
            DerefOp::Write => InitState::Init,
        };
        state.refs.insert(
            inner_place,
            RefState {
                pointee: new_pointee,
                ends_init: rs.ends_init,
            },
        );
    }

    /// Infer the type of an owned-path place by walking the ctx's
    /// locals map for the root and projecting through fields/downcasts.
    /// Returns `None` if the place isn't a valid owned path or the
    /// projection doesn't resolve.
    pub(super) fn infer_ref_place_type(&self, place: &Place) -> Option<Type> {
        let (root, path) = extract_path_with_deref(place);
        let mut ty = self.locals.get(&root)?.clone();
        for step in &path {
            match step {
                PathStep::Field(f) => {
                    let fields = struct_fields_of(&ty, self.env)?;
                    ty = fields.into_iter().find(|fd| fd.name == *f)?.ty;
                }
                PathStep::Downcast(v) => {
                    ty = enum_variant_payload_ty(&ty, v, self.env)?;
                }
                PathStep::Index(_) => {
                    // Any index step (const or dyn) yields the element type.
                    let (elem, _) = array_info(&ty)?;
                    ty = elem;
                }
                PathStep::Deref => return None,
            }
        }
        Some(ty)
    }

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
    pub(super) fn apply_eager_borrow_transition(&self, kind: &RefKind, place: &Place, state: &mut PointState) {
        let Some(leaf) = loan_post_leaf(kind) else {
            return;
        };
        if let Some(parent) = deref_inner(place) {
            if let Some(rs) = state.refs.get_mut(&parent) {
                rs.pointee = if matches!(leaf, InitState::Init) {
                    InitState::Init
                } else {
                    InitState::NeverInit
                };
            }
            return;
        }
        self.apply_write(place, state, leaf);
    }
}

// ---------- Loan conflict check ----------

/// The pointee's init state after the loan expires (post). Returned as an
/// `InitState` so the eager-transition helper can apply it directly.
pub(super) fn loan_post_leaf(kind: &RefKind) -> Option<InitState> {
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

/// For an assign `target = <rvalue>` where the rvalue transfers a
/// borrower via move, gather every ref-state entry rooted at the moved
/// source path (src itself, or any owned-path descendant like src.p)
/// and re-key it under `target`.
///
/// - `Use(Move(src))`  → re-key under `target` directly (moving `x` to
///   `y` moves `x.r` → `y.r`).
/// - `EnumConstr(_, V, Move(src))` → re-key under `target as V` (wrapping
///   `x` into `Wrap::V(...)` moves `x.r` → `(target as V).r`).
///
/// Returns an empty vec for rvalues that don't transfer a borrower, or
/// for non-owned-path targets.
pub(super) fn capture_carried_refs(
    target: &Place,
    rvalue: &RValue,
    state: &PointState,
) -> Vec<(Place, RefState)> {
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
    state
        .refs
        .iter()
        .filter_map(|(k, rs)| {
            let new_key = rekey_owned_path(&src, &dst_effective, k)?;
            Some((new_key, rs.clone()))
        })
        .collect()
}

/// Human-readable rendering of a `(cur, post)` obligation mismatch.
/// Returns (current pointee state, exit requirement) as short phrases
/// that read naturally in the diagnostic message.
pub(super) fn describe_obligation_mismatch(rs: &RefState) -> (&'static str, &'static str) {
    let cur = describe_pointee_state(&rs.pointee);
    let expected = if rs.ends_init {
        "initialized before the reference expires"
    } else {
        "consumed before the reference expires"
    };
    (cur, expected)
}

/// Same as [`describe_obligation_mismatch`], but exposed to other
/// passes (e.g. `substructural::check`) that raise the same diagnostic
/// with a slightly different template.
pub fn describe_obligation_mismatch_labels(rs: &RefState) -> (&'static str, &'static str) {
    describe_obligation_mismatch(rs)
}

/// Short label for a pointee's `InitState` used in diagnostics.
pub(super) fn describe_pointee_state(state: &InitState) -> &'static str {
    match state {
        InitState::Init => "initialized",
        InitState::NeverInit | InitState::Moved => "uninitialized",
        InitState::Partial(_) => "partially initialized",
        InitState::Diverged => "in an inconsistent state across control-flow paths",
    }
}

pub(super) fn describe_state(s: &InitState) -> &'static str {
    match s {
        InitState::NeverInit => "not yet initialized",
        InitState::Moved => "moved-from",
        InitState::Init => "initialized",
        InitState::Partial(_) => "partially initialized",
        InitState::Diverged => "of inconsistent state across paths",
    }
}

pub(super) fn format_path(root: &str, path: &[PathStep]) -> String {
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
            PathStep::Index(Some(k)) => {
                s.push('[');
                s.push_str(&k.to_string());
                s.push(']');
            }
            PathStep::Deref | PathStep::Index(None) => {
                unreachable!("init_state uses extract_path which rejects these")
            }
        }
    }
    s
}

/// Whether a `Partial` init-state tree contains no initialized leaf.
///
/// `Partial` preserves projection history, so a fully cleaned aggregate can
/// legitimately be represented as `{ left: Moved, right: NeverInit }` rather
/// than collapsing to a single simple state. `require_uninit` is concerned
/// with ownership, not that history: it succeeds exactly when every tracked
/// descendant is already absent.
pub(super) fn partial_is_uninit(fields: &BTreeMap<String, InitState>) -> bool {
    fields.values().all(|state| match state {
        InitState::NeverInit | InitState::Moved => true,
        InitState::Partial(fields) => partial_is_uninit(fields),
        InitState::Init | InitState::Diverged => false,
    })
}

/// Extract the owned path for initialization tracking up to the first dynamic index.
/// Returns `None` if the path contains a `Deref` prior to any dynamic index.
pub(super) fn extract_init_path(place: &Place) -> Option<(String, Vec<PathStep>)> {
    let (root_widen, path_widen) = extract_path_with_deref(place);
    if let Some(dyn_pos) = path_widen
        .iter()
        .position(|s| matches!(s, PathStep::Index(None)))
    {
        if path_widen[..dyn_pos]
            .iter()
            .any(|s| matches!(s, PathStep::Deref))
        {
            return None;
        }
        Some((root_widen, path_widen[..dyn_pos].to_vec()))
    } else {
        extract_path(place)
    }
}
