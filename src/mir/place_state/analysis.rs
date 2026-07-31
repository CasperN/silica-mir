use crate::diagnostics::{DiagCode, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow;
use crate::mir::env::IndexedProgram;
use crate::mir::helpers::*;
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
pub enum PlaceStateCode {
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
    /// State-changing borrow (`&out`, `&drop`) on a dynamic-index
    /// place. The borrow would move exactly one unidentified slot
    /// into a different init state than the rest, and no widening can
    /// recover which slot changed — so per-slot tracking would be
    /// lost. `&mut` and `&uninit` remain permitted on dynamic indices
    /// under uniform pre-state because they preserve it.
    BorrowDynamicIndexStateChanging,
    /// `move a[i]` or `drop a[i]` on a dynamic-index place. Same
    /// untrackability as `BorrowDynamicIndexStateChanging` on the
    /// consuming side: exactly one slot would become `Moved` while
    /// the rest stay `Init`, but we can't name it. `copy a[i]` and
    /// shared reads remain permitted under the uniform-Init
    /// precondition.
    DynamicIndexConsumption,

    // ---- LHS projections ----
    /// Assignment through a downcast (`x as V . …`) where the enum
    /// being downcast isn't `Init` at that point. Enum construction
    /// must go via `Name::V(...)`.
    WriteThroughUninitEnumProjection,

    // ---- Downcast refinement ----
    /// `place as V` where the tracked state doesn't prove the enclosing
    /// enum is currently variant `V`. Usually needs a preceding
    /// `switchEnum` arm (or an enum construction) to narrow the state.
    DowncastVariantNotRefined,
}

impl From<PlaceStateCode> for DiagCode {
    fn from(code: PlaceStateCode) -> DiagCode {
        DiagCode::PlaceState(code)
    }
}
use PlaceStateCode::*;

/// Sub-slot of an `InitState::Partial` state. Struct fields carry a name, array slots
/// carry the constant index; the enum keeps the two shapes distinct in the
/// data model and pushes rendering (`.foo`, `[0]`) to the diagnostic
/// boundary via [`std::fmt::Display`] instead of stringifying indices at
/// the map-key layer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum InitSlot {
    Field(String),
    Index(u64),
    /// Downcast to a named enum variant. When a `Partial` is keyed by
    /// `Variant`, the map describes an enum's per-variant payload state:
    /// each present key is a variant the enum might currently hold, and
    /// its value is the payload's state under that variant. No producer
    /// emits `Variant` keys yet — the type is in place ahead of the
    /// variant-flow unification.
    Variant(String),
}

impl std::fmt::Display for InitSlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InitSlot::Field(name) => write!(f, ".{}", name),
            InitSlot::Index(i) => write!(f, "[{}]", i),
            InitSlot::Variant(name) => write!(f, " as {}", name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InitState {
    NeverInit,
    Moved,
    Init,
    /// Per-slot state for a struct or array. Every slot the container defines
    /// has an entry when this variant is constructed. Nested Partials are
    /// permitted for struct fields and array elements.
    Partial(BTreeMap<InitSlot, InitState>),
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
/// - `refs`: the (is_init, ends_init) obligation for each statically
///   addressable ref-typed path that is currently `Init`. Besides owned
///   paths (`r`, `b.p`), keys may pass through references (`r.*.next`).
///   Nested entries are materialized lazily when first accessed and move
///   with the reference value. Absent when the ref place is not Init, is
///   shared, or has been consumed.
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

/// Whether a place has a stable syntactic identity for init/ref-state
/// tracking. Dynamic indices may select different slots at different program
/// points and therefore cannot be map keys for this purpose.
pub(super) fn is_static_place(place: &Place) -> bool {
    extract_path_with_deref(place)
        .1
        .iter()
        .all(|step| !matches!(step, PathStep::Index(None)))
}

pub(super) struct PlaceStateContext<'a> {
    pub(super) env: &'a IndexedProgram,
    pub(super) locals: &'a IndexMap<String, Type>,
}

// ---------- Type lookups ----------

// ---------- Canonicalization ----------

/// If a `Partial` has all fields at the same simple (non-Partial) state,
/// collapse to that state. Applied recursively to nested Partials.
///
/// Enum-typed Partials — those keyed by `InitSlot::Variant` — are never
/// collapsed to a simple leaf: their key set carries variant-refinement
/// information (which variants the enum might currently hold) that must
/// survive canonicalization. Downstream readers use `is_state_fully_init`
/// to recognize a fully-initialized Partial without discarding the
/// refinement.
pub(super) fn canonicalize(state: InitState) -> InitState {
    if let InitState::Partial(mut m) = state {
        for v in m.values_mut() {
            let taken = std::mem::replace(v, InitState::NeverInit);
            *v = canonicalize(taken);
        }
        if m.is_empty() {
            return InitState::Init;
        }
        let has_variant_key = m.keys().any(|k| matches!(k, InitSlot::Variant(_)));
        if has_variant_key {
            return InitState::Partial(m);
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

/// True when the state represents a fully-initialized value: `Init`, or a
/// `Partial` whose leaves are all `Init` (all fields written, or an enum
/// refined to one or more variants each with a fully-initialized payload).
/// Diverged, NeverInit, and Moved never qualify. Used at read sites that
/// gate on "the value is safe to consume" without caring about
/// variant-refinement bookkeeping.
pub(super) fn is_state_fully_init(state: &InitState) -> bool {
    match state {
        InitState::Init => true,
        InitState::Partial(m) => m.values().all(is_state_fully_init),
        InitState::NeverInit | InitState::Moved | InitState::Diverged => false,
    }
}

// ---------- Expansion ----------

/// Convert a uniform state to a Partial map with each of `fields` set to a
/// clone of the original state. Used when a field-refining transition needs
/// to see per-field granularity.
pub(super) fn expand_uniform(
    state: &InitState,
    fields: &[StructField],
) -> BTreeMap<InitSlot, InitState> {
    fields
        .iter()
        .map(|f| (InitSlot::Field(f.name.clone()), state.clone()))
        .collect()
}

/// The initialization state produced at the assignment target for an
/// rvalue. An enum construction refines the target to the specific
/// variant it constructs; all other rvalues yield an opaque `Init` leaf.
pub(super) fn rvalue_leaf_state(rvalue: &RValue) -> InitState {
    match rvalue {
        RValue::EnumConstr(_, _, variant, _) => {
            let mut m = BTreeMap::new();
            m.insert(InitSlot::Variant(variant.clone()), InitState::Init);
            InitState::Partial(m)
        }
        _ => InitState::Init,
    }
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
    template: &BTreeMap<InitSlot, InitState>,
) -> BTreeMap<InitSlot, InitState> {
    template
        .keys()
        .map(|k| (k.clone(), state.clone()))
        .collect()
}

pub(super) fn join_partials(
    ma: &BTreeMap<InitSlot, InitState>,
    mb: &BTreeMap<InitSlot, InitState>,
) -> InitState {
    let variant_keyed = ma
        .keys()
        .chain(mb.keys())
        .any(|k| matches!(k, InitSlot::Variant(_)));
    if variant_keyed {
        return join_variant_partials(ma, mb);
    }
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

/// Join of two enum-typed Partial maps. A variant key present on both
/// sides joins its payloads recursively. A variant key present on only
/// one side widens the union when its payload is fully initialized —
/// the other branch didn't reach this variant, but a subsequent switch
/// can still discriminate. If the one-sided payload isn't fully init,
/// the branches disagree on both the active variant and how much of
/// the payload is live; the whole enum widens to Diverged rather than
/// admitting a state that no subsequent operation can safely use.
fn join_variant_partials(
    ma: &BTreeMap<InitSlot, InitState>,
    mb: &BTreeMap<InitSlot, InitState>,
) -> InitState {
    let mut out: BTreeMap<InitSlot, InitState> = BTreeMap::new();
    let all_keys: BTreeSet<&InitSlot> = ma.keys().chain(mb.keys()).collect();
    for key in all_keys {
        match (ma.get(key), mb.get(key)) {
            (Some(va), Some(vb)) => {
                out.insert(key.clone(), join_state(va, vb));
            }
            (Some(v), None) | (None, Some(v)) => {
                if is_state_fully_init(v) {
                    out.insert(key.clone(), v.clone());
                } else {
                    return InitState::Diverged;
                }
            }
            (None, None) => unreachable!(),
        }
    }
    canonicalize(InitState::Partial(out))
}

pub(super) fn join_point(
    ctx: &PlaceStateContext<'_>,
    a: &PointState,
    b: &PointState,
) -> PointState {
    let locals: IndexMap<String, InitState> = a
        .locals
        .iter()
        .map(|(name, sa)| {
            let sb = b.locals.get(name).cloned().unwrap_or(InitState::NeverInit);
            (name.clone(), join_state(sa, &sb))
        })
        .collect();
    // Ref entries behind other references are materialized lazily. Before
    // joining, give each predecessor a chance to materialize keys observed on
    // the other side. This distinguishes "the branch never touched this
    // nested reference" from "the reference storage was consumed here".
    let mut left = a.clone();
    let mut right = b.clone();
    loop {
        let keys: BTreeSet<Place> = left.refs.keys().chain(right.refs.keys()).cloned().collect();
        let before = left.refs.len() + right.refs.len();
        for key in &keys {
            if !left.refs.contains_key(key) {
                let _ = ctx.ensure_ref_state(key, &mut left);
            }
            if !right.refs.contains_key(key) {
                let _ = ctx.ensure_ref_state(key, &mut right);
            }
        }
        if left.refs.len() + right.refs.len() == before {
            break;
        }
    }

    // Join pointee state rather than dropping a ref entry when branches
    // disagree. A later dereference then reports an inconsistent pointee
    // instead of accidentally re-materializing the declared entry state.
    let mut refs: IndexMap<Place, RefState> = IndexMap::new();
    for (place, ra) in &left.refs {
        if let Some(rb) = right.refs.get(place) {
            if ra.ends_init == rb.ends_init {
                refs.insert(
                    place.clone(),
                    RefState {
                        pointee: join_state(&ra.pointee, &rb.pointee),
                        ends_init: ra.ends_init,
                    },
                );
            }
        }
    }
    PointState { locals, refs }
}

// ---------- Path walks ----------

/// Apply a write of `leaf_state` at the given path from `state` (which is
/// the current state of the root Var). Promotes intermediate states to
/// Partial as needed. A Downcast step descends into the matching
/// `InitSlot::Variant` slot when the state tracks per-variant payload;
/// on an opaque enum state it is a no-op, matching the original model
/// where enum construction goes via `Name::V(...)`.
pub(super) fn write_at(
    state: &mut InitState,
    ty: &Type,
    path: &[PathStep],
    env: &IndexedProgram,
    leaf_state: InitState,
) {
    if path.is_empty() {
        *state = leaf_state;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = env.struct_fields(ty) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, &fields));
            }
            let field_ty = fields.into_iter().find(|fd| fd.name == *f).map(|fd| fd.ty);
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(&InitSlot::Field(f.clone())) {
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
                if let Some(slot_state) = map.get_mut(&InitSlot::Index(*k)) {
                    write_at(slot_state, &elem_ty, &path[1..], env, leaf_state);
                }
            }
        }
        PathStep::Downcast(v) => {
            let payload_ty = env.variant_payload_type(ty, v);
            if let (Some(payload_ty), InitState::Partial(map)) = (payload_ty, &mut *state) {
                if let Some(slot_state) = map.get_mut(&InitSlot::Variant(v.clone())) {
                    write_at(slot_state, &payload_ty, &path[1..], env, leaf_state);
                }
            }
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

/// Follow a single projection step through a type. Returns `None` when
/// the step is ill-typed against `ty` (type_check surfaces those errors
/// separately) or when the step is a raw dereference outside the tracked
/// projection model.
pub(super) fn advance_ty(ty: &Type, step: &PathStep, env: &IndexedProgram) -> Option<Type> {
    match step {
        PathStep::Field(f) => env.field_type(ty, f),
        PathStep::Index(_) => array_info(ty).map(|(elem, _)| elem),
        PathStep::Downcast(v) => env.variant_payload_type(ty, v),
        PathStep::Deref => None,
    }
}

/// Expand a uniform state into an array `Partial` with N slots keyed by
/// `InitSlot::Index(0..N)`.
pub(super) fn expand_uniform_array(state: &InitState, n: u64) -> BTreeMap<InitSlot, InitState> {
    (0..n)
        .map(|i| (InitSlot::Index(i), state.clone()))
        .collect()
}

/// Apply a move at the given path. Enum-typed places move atomically:
/// any Downcast step in the path collapses the whole enum to `Moved`
/// regardless of which variant the state currently tracks. Per-variant
/// partial moves would otherwise strand the enum in a disjunctive
/// `Partial` state that no subsequent CFG join can resolve.
pub(super) fn move_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &IndexedProgram) {
    if path.is_empty() {
        *state = InitState::Moved;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = env.struct_fields(ty) else {
                return;
            };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, &fields));
            }
            let field_ty = fields.into_iter().find(|fd| fd.name == *f).map(|fd| fd.ty);
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(&InitSlot::Field(f.clone())) {
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
                if let Some(slot_state) = map.get_mut(&InitSlot::Index(*k)) {
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
pub(super) fn read_at(
    state: &InitState,
    ty: &Type,
    path: &[PathStep],
    env: &IndexedProgram,
) -> InitState {
    if path.is_empty() {
        return state.clone();
    }
    match &path[0] {
        PathStep::Field(f) => match state {
            InitState::Init | InitState::NeverInit | InitState::Moved | InitState::Diverged => {
                state.clone()
            }
            InitState::Partial(map) => {
                let field_ty = env.field_type(ty, f);
                let field_state = map
                    .get(&InitSlot::Field(f.clone()))
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                match field_ty {
                    Some(ft) => read_at(&field_state, &ft, &path[1..], env),
                    None => field_state,
                }
            }
        },
        PathStep::Downcast(v) => match state {
            InitState::NeverInit | InitState::Moved | InitState::Diverged => state.clone(),
            InitState::Init => {
                // Opaque enum: assume the payload is Init.
                let payload_ty = env.variant_payload_type(ty, v);
                match payload_ty {
                    Some(pt) => read_at(&InitState::Init, &pt, &path[1..], env),
                    None => InitState::Init,
                }
            }
            InitState::Partial(map) => {
                let payload_ty = env.variant_payload_type(ty, v);
                let slot_state = map.get(&InitSlot::Variant(v.clone()));
                // When the map tracks per-variant payload, descend into
                // the requested variant's slot. Otherwise fall back to
                // the opaque-Init behavior — the checker's place walker
                // emits DowncastVariantNotRefined for that case.
                let payload_state = match slot_state {
                    Some(s) => s.clone(),
                    None => InitState::Init,
                };
                match payload_ty {
                    Some(pt) => read_at(&payload_state, &pt, &path[1..], env),
                    None => payload_state,
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
                    .get(&InitSlot::Index(*k))
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
pub fn block_entry_states(env: &IndexedProgram, func: &Function) -> IndexMap<String, PointState> {
    let Some(body) = &func.body else {
        return IndexMap::new();
    };
    if body.blocks.is_empty() {
        return IndexMap::new();
    }
    let locals = func.locals_map();
    let ctx = PlaceStateContext {
        env,
        locals: &locals,
    };
    run_fixpoint(&ctx, func, body)
}

/// Advance `state` silently through `stmt` (no diagnostics). Uses the
/// same transfer as the fixpoint. For callers that hold a per-block
/// entry state and want to reconstruct the state at any point inside
/// the block.
pub fn transfer_stmt_silent(
    env: &IndexedProgram,
    func: &Function,
    stmt: &Statement,
    state: &mut PointState,
) {
    let locals = func.locals_map();
    let ctx = PlaceStateContext {
        env,
        locals: &locals,
    };
    ctx.transfer_stmt(stmt, state);
}

pub fn states_before_returns<'a>(
    env: &IndexedProgram,
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
    let ctx = PlaceStateContext {
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

pub(super) fn boundary_state(
    func: &Function,
    body: &FunctionBody,
    env: &IndexedProgram,
) -> PointState {
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
    env: &IndexedProgram,
    visited: &mut BTreeSet<String>,
    refs: &mut IndexMap<Place, RefState>,
) {
    if let TypeKind::Ref(kind, _, _) = &ty.kind {
        if let Some(state) = RefState::from_kind(kind) {
            refs.insert(place, state);
        }
        return;
    }

    let TypeKind::Custom(Instance {
        name,
        type_args: args,
        ..
    }) = &ty.kind
    else {
        return;
    };
    if !visited.insert(name.clone()) {
        return;
    }
    if let Some(TypeDecl::Struct(def)) = env.types.get(name) {
        let fields: Option<Vec<_>> = def
            .fields
            .iter()
            .map(|field| {
                def.meta
                    .try_substitute_types(&field.ty, args)
                    .map(|ty| (field.name.clone(), ty))
            })
            .collect();
        if let Some(fields) = fields {
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
    }
    visited.remove(name);
}

pub(super) fn is_trivially_init(ty: &Type, env: &IndexedProgram) -> bool {
    match &ty.kind {
        TypeKind::Custom(Instance { name, .. }) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => s.fields.is_empty(),
            _ => false,
        },
        _ => false,
    }
}

/// Bridge between init_state's per-function context and the generic
/// dataflow framework. Instantiated per-function.
struct InitAnalysis<'a> {
    ctx: &'a PlaceStateContext<'a>,
    boundary: PointState,
}

impl<'a> dataflow::Analysis for InitAnalysis<'a> {
    type State = PointState;
    fn direction(&self) -> dataflow::Direction {
        dataflow::Direction::Forward
    }
    fn boundary_state(&self) -> Self::State {
        self.boundary.clone()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join_point(self.ctx, a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, _source: SourceInfo) {
        self.ctx.transfer_stmt(stmt, state)
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        self.ctx.transfer_terminator(term, state)
    }
    fn refine_edge(&self, state: &mut Self::State, block: &BasicBlock, succ_label: &str) {
        let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind else {
            return;
        };
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(variant) = cases
            .iter()
            .find_map(|(v, label)| (label == succ_label).then(|| v.clone()))
        else {
            return;
        };
        let Some(root_ty) = self.ctx.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root).cloned() else {
            return;
        };
        let leaf_state = read_at(&root_state, &root_ty, &path, self.ctx.env);
        // Leave the state untouched when the arm's variant isn't in the
        // pre-switch tracked set — that arm is dead code and refining
        // would strand the place in a NeverInit variant slot that fires
        // spurious diagnostics.
        let prior_payload = match variant_admissible_payload(&leaf_state, &variant) {
            Some(p) => p,
            None => return,
        };
        let mut refined = BTreeMap::new();
        refined.insert(InitSlot::Variant(variant), prior_payload);
        let mut updated = root_state;
        write_at(
            &mut updated,
            &root_ty,
            &path,
            self.ctx.env,
            InitState::Partial(refined),
        );
        state.locals.insert(root, updated);
    }
}

/// The payload state to use for a switch arm's variant, or `None` if
/// the pre-switch state can't be refined at all (empty / diverged).
/// Opaque `Init` admits any variant with `Init` payload. A refined
/// `Partial` returns the tracked payload for the requested variant if
/// present, or `Init` if not — the "not present" case is a dead arm
/// (reachability's `SwitchArmDeadCode` covers it), and returning `Init`
/// rather than nothing keeps the arm's tracked state a clean singleton
/// `{V: Init}` so loop back-edges don't leak stale variant info across
/// iterations.
fn variant_admissible_payload(state: &InitState, variant: &str) -> Option<InitState> {
    match state {
        InitState::Init => Some(InitState::Init),
        InitState::Partial(map) => Some(
            map.get(&InitSlot::Variant(variant.to_string()))
                .cloned()
                .unwrap_or(InitState::Init),
        ),
        InitState::NeverInit | InitState::Moved | InitState::Diverged => None,
    }
}

/// True when `state` proves the enum is exactly `variant`. A `Partial`
/// with a single `Variant(v)` key qualifies; an opaque `Init` (any
/// declared variant possible) does not, nor do multi-variant maps.
pub(super) fn state_refines_to_variant(state: &InitState, variant: &str) -> bool {
    match state {
        InitState::Partial(map) => {
            map.len() == 1 && map.contains_key(&InitSlot::Variant(variant.to_string()))
        }
        _ => false,
    }
}

pub(super) fn run_fixpoint(
    ctx: &PlaceStateContext,
    func: &Function,
    body: &FunctionBody,
) -> IndexMap<String, PointState> {
    let analysis = InitAnalysis {
        ctx,
        boundary: boundary_state(func, body, ctx.env),
    };
    dataflow::run(&analysis, body)
}

// ---------- Transfer (state updates) ----------

impl<'a> PlaceStateContext<'a> {
    pub(super) fn transfer_stmt(&self, stmt: &Statement, state: &mut PointState) {
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                self.materialize_moved_ref(rvalue, state);
                // Capture ref-state entries to transfer via `move src`
                // BEFORE apply_rvalue_moves removes them. If src has
                // ref-typed descendants (e.g. moving a whole struct),
                // each descendant's RefState transfers to the parallel
                // path under dst.
                let carried_refs = capture_carried_refs(target, rvalue, state);

                self.apply_rvalue_moves(rvalue, state);
                if is_static_place(target) {
                    close_refs_under(state, target);
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
        report: Option<(&Function, &BasicBlock, SourceInfo, &mut Diagnostics)>,
    ) {
        let leaf = rvalue_leaf_state(rvalue);
        if split_at_outermost_deref(target).is_some() {
            self.apply_deref_op(target, DerefOp::Write, state, report);
        } else {
            self.apply_write(target, state, leaf);
        }
        if is_static_place(target) {
            if let RValue::Ref(kind, place) = rvalue {
                if let Some(rs) = RefState::from_kind(kind) {
                    state.refs.insert(target.clone(), rs);
                }
                self.apply_eager_borrow_transition(kind, place, state);
            } else if let RValue::PtrCast(_, to_ty) = rvalue {
                if let TypeKind::Ref(kind, _, _) = &to_ty.kind {
                    if let Some(rs) = RefState::from_kind(kind) {
                        state.refs.insert(target.clone(), rs);
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
        report: Option<(&Function, &BasicBlock, SourceInfo, &mut Diagnostics)>,
    ) {
        if split_at_outermost_deref(place).is_some() {
            self.apply_deref_op(place, DerefOp::Move, state, report);
        } else {
            self.apply_move(place, state);
        }
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
                if split_at_outermost_deref(place).is_some() {
                    self.apply_deref_op(place, DerefOp::Move, state, None);
                } else {
                    self.apply_move(place, state);
                }
            }
            Operand::Take(_) => unreachable!(
                "place-state analysis saw unresolved `take` operand; copy relaxation should have resolved it"
            ),
            Operand::Const(_) => {}
        }
    }

    /// Ensure a directly moved reference value has a RefState before
    /// `capture_carried_refs` snapshots it. Nested reference states are
    /// otherwise created lazily on first dereference.
    pub(super) fn materialize_moved_ref(&self, rv: &RValue, state: &mut PointState) {
        let moved = match rv {
            RValue::Use(Operand::Move(place))
            | RValue::EnumConstr(_, _, _, Operand::Move(place))
            | RValue::PtrCast(Operand::Move(place), _) => place,
            _ => return,
        };
        let _ = self.ensure_ref_state(moved, state);
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
    pub(super) fn apply_pointee_write(
        &self,
        place: &Place,
        leaf: InitState,
        state: &mut PointState,
    ) {
        let Some((ref_place, sub_path, pointee_ty)) = self.resolve_pointee_target(place, state)
        else {
            return;
        };
        if sub_path
            .iter()
            .any(|step| matches!(step, PathStep::Deref | PathStep::Index(None)))
        {
            return;
        }
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
        if sub_path
            .iter()
            .any(|step| matches!(step, PathStep::Deref | PathStep::Index(None)))
        {
            return;
        }
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
        state: &mut PointState,
    ) -> Option<(Place, Vec<PathStep>, Type)> {
        let (ref_place, sub_path) = split_at_outermost_deref(place)?;
        self.ensure_ref_state(&ref_place, state)?;
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

/// Return dereference receiver places from root-nearest to leaf-nearest.
/// `r.*.next.*` yields `[r, r.*.next]`.
pub(super) fn deref_receivers(place: &Place) -> Vec<Place> {
    fn visit(place: &Place, out: &mut Vec<Place>) {
        match place {
            Place::Var(_) => {}
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
                visit(inner, out)
            }
            Place::Deref(inner) => {
                visit(inner, out);
                out.push((**inner).clone());
            }
        }
    }
    let mut out = Vec::new();
    visit(place, &mut out);
    out
}

/// Remove all ref-state entries at `consumed` or any static descendant.
/// Called at every consumption/overwrite site so an ancestor consume
/// cascades to all ref-typed values it holds, including behind references.
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

impl<'a> PlaceStateContext<'a> {
    /// Apply the state effect of an operation through an exclusive reference.
    /// Fields, downcasts, and constant indexes above the dereference are
    /// tracked within the pointee's `InitState` tree.
    ///
    /// When `report` is `Some`, precondition failures emit errors; when `None`
    /// the check is silent (used from the fixpoint transfer).
    ///
    /// Nested dereferences are resolved recursively through lazily materialized
    /// RefState entries. Dynamic indices remain outside the tracked subset.
    /// A write/move is rejected if *any* reference boundary in the access path
    /// is shared; exercising an exclusive capability through a shared outer
    /// reference would otherwise permit mutation through an alias.
    pub(super) fn apply_deref_op(
        &self,
        place: &Place,
        op: DerefOp,
        state: &mut PointState,
        mut report: Option<(&Function, &BasicBlock, SourceInfo, &mut Diagnostics)>,
    ) {
        let Some((inner_place, sub_path)) = split_at_outermost_deref(place) else {
            return;
        };
        if !is_static_place(place) {
            return;
        }

        // Check every dereference boundary, not only the final one. For
        // `r.*.*`, mutating through the inner &mut is still forbidden when
        // the path reaches that capability through an outer shared ref.
        if !matches!(op, DerefOp::Read) {
            for receiver in deref_receivers(place).into_iter().rev() {
                let Ok(receiver_ty) = self.env.type_of_place(&receiver, self.locals) else {
                    return;
                };
                if matches!(receiver_ty.kind, TypeKind::Ref(RefKind::Shared, _, _)) {
                    if let Some((func, block, source, d)) = report.take() {
                        let action = match op {
                            DerefOp::Move => "move out through",
                            DerefOp::Write => "write through",
                            DerefOp::Read => unreachable!(),
                        };
                        d.push_error(diag(
                            WriteThroughSharedRef,
                            source,
                            func,
                            block,
                            format!(
                                "cannot {} shared reference '{}'",
                                action,
                                format_place(&receiver)
                            ),
                        ));
                    }
                    return;
                }
                if matches!(receiver_ty.kind, TypeKind::RawPtr(_)) {
                    // Raw-pointer accesses are intentionally outside safe
                    // initialization tracking.
                    return;
                }
            }
        }

        let Ok(inner_ty) = self.env.type_of_place(&inner_place, self.locals) else {
            return;
        };
        let TypeKind::Ref(kind, _, pointee_ty) = inner_ty.kind else {
            // Raw-pointer accesses are unchecked.
            return;
        };

        if matches!(kind, RefKind::Shared) {
            // A read through a shared reference has no mutable pointee state.
            return;
        }

        let Some(rs) = self.ensure_ref_state(&inner_place, state) else {
            if let Some((func, block, source, d)) = report.take() {
                d.push_error(diag(
                    ReferenceStateUnknown,
                    source,
                    func,
                    block,
                    format!(
                        "cannot dereference '{}': reference state is unknown here",
                        format_place(&inner_place)
                    ),
                ));
            }
            return;
        };

        let required_init = match op {
            DerefOp::Read | DerefOp::Move => true,
            DerefOp::Write => false,
        };
        let current = read_at(&rs.pointee, &pointee_ty, &sub_path, self.env);
        let precondition_met = if required_init {
            matches!(current, InitState::Init)
        } else {
            matches!(current, InitState::NeverInit | InitState::Moved)
        };
        if !precondition_met {
            if let Some((func, block, source, d)) = report.take() {
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
                let actual = describe_pointee_state(&current);
                d.push_error(diag(
                    DerefPointeeStateMismatch,
                    source,
                    func,
                    block,
                    format!(
                        "cannot {} pointee of '{}': pointee must be {} here, but is {}",
                        action,
                        format_place(&inner_place),
                        expected,
                        actual
                    ),
                ));
            }
        }

        // Apply the transition. Do this even on precondition failure so
        // downstream analysis sees consistent state.
        let mut new_pointee = rs.pointee;
        match op {
            DerefOp::Read => {}
            DerefOp::Move => move_at(&mut new_pointee, &pointee_ty, &sub_path, self.env),
            DerefOp::Write => write_at(
                &mut new_pointee,
                &pointee_ty,
                &sub_path,
                self.env,
                InitState::Init,
            ),
        }
        new_pointee = canonicalize(new_pointee);
        state.refs.insert(
            inner_place.clone(),
            RefState {
                pointee: new_pointee,
                ends_init: rs.ends_init,
            },
        );
        if matches!(op, DerefOp::Move) {
            close_refs_under(state, place);
        }
    }

    /// Materialize the state of an exclusive reference value at a static
    /// access path. The containing storage's InitState decides whether the
    /// value exists; its declared kind supplies the initial pointee contract.
    /// Once materialized, subsequent operations update the stored state.
    pub(super) fn ensure_ref_state(
        &self,
        place: &Place,
        state: &mut PointState,
    ) -> Option<RefState> {
        if let Some(rs) = state.refs.get(place) {
            return Some(rs.clone());
        }
        if !is_static_place(place) {
            return None;
        }
        let ty = self.env.type_of_place(place, self.locals).ok()?;
        let TypeKind::Ref(kind, _, _) = &ty.kind else {
            return None;
        };
        let fresh = RefState::from_kind(kind)?;
        if !matches!(
            self.read_static_place_state(place, state),
            Some(InitState::Init)
        ) {
            return None;
        }
        state.refs.insert(place.clone(), fresh.clone());
        Some(fresh)
    }

    /// Read the initialization state of an arbitrary static place. Each
    /// dereference recursively consults the receiver's RefState; shared
    /// references contribute an always-initialized pointee.
    pub(super) fn read_static_place_state(
        &self,
        place: &Place,
        state: &mut PointState,
    ) -> Option<InitState> {
        if let Some((root, path)) = extract_path(place) {
            let root_ty = self.locals.get(&root)?;
            let root_state = state.locals.get(&root)?;
            return Some(read_at(root_state, root_ty, &path, self.env));
        }
        if !is_static_place(place) {
            return None;
        }
        let (receiver, sub_path) = split_at_outermost_deref(place)?;
        let receiver_ty = self.env.type_of_place(&receiver, self.locals).ok()?;
        let TypeKind::Ref(kind, _, pointee_ty) = receiver_ty.kind else {
            return None;
        };
        let pointee_state = if matches!(kind, RefKind::Shared) {
            InitState::Init
        } else {
            self.ensure_ref_state(&receiver, state)?.pointee
        };
        Some(read_at(&pointee_state, &pointee_ty, &sub_path, self.env))
    }

    /// Infer the type of a place, including arbitrary dereference depth.
    pub(super) fn infer_ref_place_type(&self, place: &Place) -> Option<Type> {
        self.env.type_of_place(place, self.locals).ok()
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
    /// Walk `place` down `state.locals` and clear variant refinement at
    /// the leaf without altering init/uninit structure. Handles direct
    /// and reborrow shapes uniformly via read/write on the appropriate
    /// state tree; a no-op for non-enum states.
    fn clear_variant_refinement_at(&self, place: &Place, state: &mut PointState) {
        // Reborrow through a reference: the refinement lives in the
        // ref's pointee state. Materialize the RefState if needed and
        // clear at that path.
        if let Some((inner, sub_path)) = split_at_outermost_deref(place) {
            let Some(mut rs) = self.ensure_ref_state(&inner, state) else {
                return;
            };
            let Ok(inner_ty) = self.env.type_of_place(&inner, self.locals) else {
                return;
            };
            let TypeKind::Ref(_, _, pointee_ty) = inner_ty.kind else {
                return;
            };
            let mut leaf = read_at(&rs.pointee, &pointee_ty, &sub_path, self.env);
            clear_variant_refinement(&mut leaf);
            write_at(&mut rs.pointee, &pointee_ty, &sub_path, self.env, leaf);
            state.refs.insert(inner, rs);
            return;
        }
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let root_state = state.locals.entry(root).or_insert(InitState::NeverInit);
        let mut leaf = read_at(root_state, &root_ty, &path, self.env);
        clear_variant_refinement(&mut leaf);
        write_at(root_state, &root_ty, &path, self.env, leaf);
    }

    pub(super) fn apply_eager_borrow_transition(
        &self,
        kind: &RefKind,
        place: &Place,
        state: &mut PointState,
    ) {
        // Exclusive borrows can reassign the pointee to a different
        // variant. Any per-variant refinement at the loaned place must
        // be cleared so post-loan reads see opaque `Init` rather than
        // the pre-borrow refinement. This is independent of the
        // init/uninit transition below — for `&mut` there is no init
        // transition, but the variant refinement still needs clearing.
        if matches!(
            kind,
            RefKind::Mut | RefKind::Out | RefKind::Drop | RefKind::Uninit
        ) {
            self.clear_variant_refinement_at(place, state);
        }
        let Some(leaf) = loan_post_leaf(kind) else {
            return;
        };
        if split_at_outermost_deref(place).is_some() {
            self.apply_pointee_write(place, leaf, state);
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

/// Drop any variant-refinement info at `state`, leaving init/uninit
/// structure alone. Applied on exclusive borrow creation: the borrower
/// can freely reassign the pointee to a different variant, so a
/// `Partial({Variant(V): ...})` at the loaned place must reset to opaque
/// `Init` when the loan expires. `NeverInit`, `Moved`, and struct/array
/// Partials are untouched — only enum refinement is invalidated.
pub(super) fn clear_variant_refinement(state: &mut InitState) {
    if let InitState::Partial(map) = state {
        if map.keys().all(|k| matches!(k, InitSlot::Variant(_))) {
            *state = InitState::Init;
        }
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
/// for paths containing a dynamic index.
pub(super) fn capture_carried_refs(
    target: &Place,
    rvalue: &RValue,
    state: &PointState,
) -> Vec<(Place, RefState)> {
    if !is_static_place(target) {
        return Vec::new();
    }
    let dst = target.clone();
    let (src, dst_effective) = match rvalue {
        RValue::Use(Operand::Move(src_place)) => {
            if !is_static_place(src_place) {
                return Vec::new();
            }
            (src_place.clone(), dst)
        }
        RValue::EnumConstr(_, _, variant, Operand::Move(src_place)) => {
            if !is_static_place(src_place) {
                return Vec::new();
            }
            (src_place.clone(), downcast_place(dst, variant.clone()))
        }
        RValue::PtrCast(Operand::Move(src_place), _) => {
            if !is_static_place(src_place) {
                return Vec::new();
            }
            (src_place.clone(), dst)
        }
        _ => return Vec::new(),
    };
    state
        .refs
        .iter()
        .filter_map(|(k, rs)| {
            let new_key = rekey_static_path(&src, &dst_effective, k)?;
            Some((new_key, rs.clone()))
        })
        .collect()
}

/// Re-key a static descendant from `src` to the parallel path under `dst`.
fn rekey_static_path(src: &Place, dst: &Place, key: &Place) -> Option<Place> {
    if !is_static_place(src) || !is_static_place(dst) || !is_static_place(key) {
        return None;
    }
    let (src_root, src_path) = extract_path_with_deref(src);
    let (key_root, key_path) = extract_path_with_deref(key);
    if src_root != key_root || src_path.len() > key_path.len() {
        return None;
    }
    if !src_path.iter().zip(&key_path).all(|(a, b)| a == b) {
        return None;
    }
    let mut out = dst.clone();
    for step in &key_path[src_path.len()..] {
        out = match step {
            PathStep::Field(field) => field_place(out, field.clone()),
            PathStep::Downcast(variant) => downcast_place(out, variant.clone()),
            PathStep::Deref => deref_place(out),
            PathStep::Index(Some(index)) => index_place(
                out,
                Operand::Const(ConstVal::Int {
                    bits: *index,
                    ty: IntTy::I64,
                }),
            ),
            PathStep::Index(None) => return None,
        };
    }
    Some(out)
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
pub(super) fn partial_is_uninit(fields: &BTreeMap<InitSlot, InitState>) -> bool {
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
