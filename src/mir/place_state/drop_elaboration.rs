//! Drop elaboration pass.
//!
//! Turns implicit cleanup into explicit consumption. `Drop` values use
//! `drop p`; otherwise an applicable `AutoDestroy` implementation is called
//! through a generated `&drop` receiver. Values supporting neither mechanism
//! remain for the place-state checker to reject. Both cleanup forms transition
//! the place to `Moved`, making the pass idempotent.

use super::analysis::{
    block_entry_states, is_state_fully_init, transfer_stmt_silent, InitSlot, InitState, PointState,
};
use crate::mir::ast::*;
use crate::mir::cfg_edit;
use crate::mir::env::{IndexedProgram, LocalEnv};
use crate::mir::helpers::*;
use indexmap::IndexMap;

/// Per-function plan for the elaboration pass.
#[derive(Default)]
struct FnPlan {
    /// (block_label, insert_pos) → places to clean up at that position.
    /// `insert_pos` is an index in `[0, N]`: 0 means "before the
    /// first statement", N (= number of statements) means "before
    /// the terminator". Statement indices refer to the ORIGINAL
    /// (pre-splice) list; apply sorts descending so splices don't
    /// invalidate earlier indices. Handles both Init → Uninit
    /// transitions mid-block (`&out place` on an initialized destructible place)
    /// AND end-of-block return cleanups uniformly: the terminator
    /// acts as a "use" that consumes any still-initialized destructible values.
    pre_stmt: IndexMap<(String, usize), Vec<Place>>,
    /// (block_label, statement_index) → replacement for the original
    /// statement at that index. Used for the downcast-target
    /// reassignment case (`X as V = <operand>` becomes
    /// `X = EnumName::V(<operand>)`), which pairs with a pre_stmt
    /// cleanup of `X as V`. Applied BEFORE splicing so indices remain
    /// valid for the pre_stmt phase.
    rewrite_stmt: IndexMap<(String, usize), Statement>,
    /// (pred, succ_return_block) → places to clean up on the split edge,
    /// for `Diverged` places whose predecessor-exit state was Init.
    /// Kept separate because insertion requires structurally
    /// splitting the CFG edge.
    cross_edge: IndexMap<(String, String), Vec<Place>>,
}

/// Insert implicit destruction in `program`.
pub fn elaborate(program: &mut IndexedProgram) {
    program.visit_function_bodies_mut(|env, func, body| {
        let plan = plan_for_function(env, func, body);
        apply_plan(env, func, body, &plan);
    });
}

fn apply_plan(env: LocalEnv<'_>, func: &Function, body: &mut FunctionBody, plan: &FnPlan) {
    // Statement rewrites first: replace in place, no index shift.
    // Pair with the pre-statement cleanup planned for the same index.
    for block in &mut body.blocks {
        for ((label, idx), new_stmt) in &plan.rewrite_stmt {
            if label != &block.label {
                continue;
            }
            let slot = block
                .statements
                .get_mut(*idx)
                .expect("cleanup planner records valid statement indices");
            *slot = new_stmt.clone();
        }
    }

    let mut emitter = CleanupEmitter {
        env,
        locals: body.locals_map(&func.params),
        generated_locals: Vec::new(),
        next_destroy: 0,
    };

    // Pre-stmt cleanups: splice into each block at the recorded
    // positions (0..=N, where pos=N means "before terminator").
    // Sort descending so earlier splices don't invalidate later
    // indices.
    for block in &mut body.blocks {
        let mut inserts: Vec<(usize, &Vec<Place>)> = plan
            .pre_stmt
            .iter()
            .filter(|((label, _), _)| label == &block.label)
            .map(|((_, pos), v)| (*pos, v))
            .collect();
        inserts.sort_by(|a, b| b.0.cmp(&a.0));
        for (pos, places) in inserts {
            let span = block
                .statements
                .get(pos)
                .map(|s| s.span())
                .unwrap_or(block.terminator.span());
            let items: Vec<Statement> = places
                .iter()
                .flat_map(|place| emitter.emit(place, span))
                .collect();
            block.statements.splice(pos..pos, items);
        }
    }

    // Cross-edge cleanup: split each edge (idempotent), then append.
    for ((pred, succ), places) in &plan.cross_edge {
        let split_label = cfg_edit::split_edge(body, pred, succ);
        let split_block = body
            .blocks
            .iter_mut()
            .find(|b| b.label == split_label)
            .expect("split_edge just guaranteed this block exists");
        let span = split_block.terminator.span();
        for place in places {
            split_block.statements.extend(emitter.emit(place, span));
        }
    }

    body.locals.extend(emitter.generated_locals);
}

struct CleanupEmitter<'a> {
    env: LocalEnv<'a>,
    locals: IndexMap<String, Type>,
    generated_locals: Vec<Local>,
    next_destroy: usize,
}

impl CleanupEmitter<'_> {
    fn emit(&mut self, place: &Place, span: Span) -> Vec<Statement> {
        let ty = self
            .env
            .type_of_place(place, &self.locals)
            .expect("cleanup planner records only well-typed places");
        let source = SourceInfo::generated(GeneratedKind::DropElaboration, span);
        if self.env.class_of(&ty).implies(Marker::Drop) {
            return vec![drop_stmt(place.clone(), source)];
        }
        assert!(
            self.env
                .has_applicable_trait_impl(&Instance::bare("AutoDestroy"), &ty),
            "cleanup planner recorded non-destructible place {}",
            format_place(place),
        );

        let recv_name = loop {
            let name = format!("$destroy_recv{}", self.next_destroy);
            self.next_destroy += 1;
            if !self.locals.contains_key(&name) {
                break name;
            }
        };
        let recv_ty = ref_ty(RefKind::Drop, ty.clone());
        let recv = var_place(recv_name.clone());
        let local = Local {
            name: recv_name.clone(),
            ty: recv_ty.clone(),
            source,
        };
        self.locals.insert(recv_name, recv_ty);
        self.generated_locals.push(local);

        vec![
            assign_stmt(recv.clone(), ref_rv(RefKind::Drop, place.clone()), source),
            call_stmt(
                const_op(ConstVal::TraitFn {
                    trait_path: Instance::bare("AutoDestroy"),
                    self_ty: ty,
                    method: Instance::bare("destroy"),
                }),
                vec![move_op(recv)],
                source,
            ),
        ]
    }
}

fn plan_for_function(env: LocalEnv<'_>, func: &Function, body: &FunctionBody) -> FnPlan {
    let mut plan = FnPlan::default();
    if body.blocks.is_empty() {
        return plan;
    }

    let entry_states = block_entry_states(env, func, body);
    let locals = body.locals_map(&func.params);
    // The cross-edge fallback below needs the state of the program it will
    // actually emit, including cleanup planned before ghost requirements.
    // Looking only at the original fixpoint state would schedule a second
    // cleanup after a predecessor has already satisfied `require_uninit`.
    let mut elaborated_exit_states = IndexMap::new();

    // Unified walk: for each block, walk forward from its entry state
    // and plan cleanup at each program point where an implicitly destructible
    // slot must transition Init → Uninit.
    //   - Mid-block: before an `Assign(_, Ref(Out|Uninit, place))`
    //     where `place` is initialized and destructible, clean it up so the
    //     Uninit precondition holds after elaboration.
    //   - Mid-block: before `require_uninit place`, insert cleanup that makes
    //     the assertion true without forgetting a non-destructible value.
    //   - End-of-block (return terminator): treat the return as a
    //     "use" that consumes every still-Init destructible local — insert
    //     cleanup in LIFO order right before the terminator.
    //
    // Planned cleanup applies to the running state (via silent transfer) so
    // return cleanup does not repeat work already planned before a statement.
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut state = entry.clone();
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let (drops, rewrite) = pre_stmt_transitions(stmt, &state, env, &locals);
            if !drops.is_empty() {
                for place in &drops {
                    transfer_stmt_silent(
                        env,
                        func,
                        body,
                        &drop_stmt(
                            place.clone(),
                            SourceInfo::generated(GeneratedKind::DropElaboration, stmt.span()),
                        ),
                        &mut state,
                    );
                }
                plan.pre_stmt.insert((block.label.clone(), stmt_idx), drops);
            }
            // Transfer whichever form we're going to leave in the
            // elaborated MIR: the rewrite if present, else the
            // original. Both should produce the same net state
            // effect, but we track the elaborated form for
            // correctness under later analysis.
            let effective = rewrite.clone().unwrap_or_else(|| stmt.clone());
            transfer_stmt_silent(env, func, body, &effective, &mut state);
            if let Some(new_stmt) = rewrite {
                plan.rewrite_stmt
                    .insert((block.label.clone(), stmt_idx), new_stmt);
            }
        }
        // Pre-terminator cleanup for return blocks.
        if matches!(block.terminator.kind, TerminatorKind::Return) {
            let drops = plan_drops_at_return(func, body, &state, env);
            if !drops.is_empty() {
                let insert_pos = block.statements.len();
                plan.pre_stmt
                    .insert((block.label.clone(), insert_pos), drops);
            }
        }
        elaborated_exit_states.insert(block.label.clone(), state);
    }

    // Cross-edge: at every return-reachable join with Diverged-at-entry paths,
    // split the Init-side predecessor edges and insert per-arm cleanup.
    // Restricting this to return blocks (the earlier shape) misses the case where a
    // value goes Init on one arm and NeverInit on another, joins into
    // an intermediate merge block (whose terminator is switchEnum,
    // goto, branch, ...) rather than return, and stays Diverged all the
    // way through — at the eventual return the direct preds already
    // have Diverged exit states, so the pred-Init check finds nothing
    // to clean up. Handling every join catches the transition at its
    // first occurrence. Its predecessor states include the intra-block
    // cleanup planned above, so an explicit requirement cannot be followed
    // by redundant edge cleanup.
    let return_reachable = body.return_reachable();
    for block in &body.blocks {
        if !return_reachable.contains(&block.label) {
            continue;
        }
        let Some(block_entry) = entry_states.get(&block.label) else {
            continue;
        };
        let diverged_paths = collect_diverged_paths(env.program(), &locals, block_entry);
        if diverged_paths.is_empty() {
            continue;
        }
        for pred_block in &body.blocks {
            if !terminator_successors(&pred_block.terminator)
                .iter()
                .any(|s| *s == block.label.as_str())
            {
                continue;
            }
            let Some(pred_exit) = elaborated_exit_states.get(&pred_block.label) else {
                continue;
            };
            for (path_place, ty) in &diverged_paths {
                if state_at(pred_exit, path_place) == Some(InitState::Init)
                    && is_implicitly_destructible(env, ty)
                {
                    plan.cross_edge
                        .entry((pred_block.label.clone(), block.label.clone()))
                        .or_default()
                        .push(path_place.clone());
                }
            }
        }
    }
    plan
}

/// Return `(places_to_clean_up_before, optional_statement_rewrite)` for
/// `stmt` given the init state at this program point.
///
/// Init → Uninit transition shapes:
///
/// - **Overwriting assign (Var/Field target)**: `target = <rvalue>`
///   where `target` is an owned path currently Init and its type is
///   implicitly destructible. Cleans up the old value before replacement.
/// - **Overwriting assign (Downcast target)**: `X as V = <operand>`
///   where the enum X is Init and V's payload is destructible. Rewrites the
///   assign into `X = EnumName::V(<operand>)` after cleaning up the old
///   payload. The whole-value reconstruction restores the enum after cleanup
///   marks it moved. Only operand rvalues are supported; other payload forms
///   must first be hoisted into a temporary.
/// - **`&out` / `&uninit` borrow of an initialized destructible place**:
///   cleanup establishes the borrow's Uninit precondition.
/// - **`require_uninit place`**: recursively cleans every initialized,
///   destructible leaf of the asserted owned path. The ghost statement
///   remains for the post-elaboration checker to prove.
///
/// Reborrow shapes (`&out *r`) remain governed by RefState. A
/// `require_uninit` on a dereference or dynamic index deliberately plans
/// nothing: those places are outside its statically-trackable contract and
/// the final checker reports that directly.
fn pre_stmt_transitions(
    stmt: &Statement,
    state: &PointState,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> (Vec<Place>, Option<Statement>) {
    if let StatementKind::RequireUninit(place) = &stmt.kind {
        return (plan_drops_for_requirement(place, state, env, locals), None);
    }

    let StatementKind::Assign(target, rvalue) = &stmt.kind else {
        return (Vec::new(), None);
    };
    let mut drops = Vec::new();

    // Downcast target with operand rvalue → rewrite to full-enum
    // reconstruction. Handled specially before the generic Case A
    // because Case A skips Downcast paths.
    if let (Place::Downcast(inner, variant), RValue::Use(operand)) = (target, rvalue) {
        if let Some(inner_owned) = as_owned_path(inner) {
            if let Ok(inner_ty) = env.type_of_place(inner, locals) {
                if let TypeKind::Custom(Instance {
                    name: enum_name, ..
                }) = &inner_ty.kind
                {
                    let payload_place = downcast_place(inner_owned.clone(), variant.clone());
                    if is_init_and_destructible(&payload_place, state, env, locals) {
                        drops.push(payload_place);
                        let rewrite = assign_stmt(
                            inner_owned,
                            enum_constr_rv(enum_name.clone(), variant.clone(), operand.clone()),
                            SourceInfo::generated(GeneratedKind::DropElaboration, stmt.span()),
                        );
                        return (drops, Some(rewrite));
                    }
                }
            }
        }
    }

    // Case A: overwriting an initialized, destructible owned path. Skip
    // Downcast-containing paths.
    if let Some(owned) = as_owned_path(target) {
        if !path_has_downcast(&owned) && is_init_and_destructible(&owned, state, env, locals) {
            drops.push(owned);
        }
    }

    // Case B: `&out` / `&uninit` on an initialized destructible place.
    if let RValue::Ref(RefKind::Out | RefKind::Uninit, place) = rvalue {
        if deref_inner(place).is_none() {
            if let Some(owned) = as_owned_path(place) {
                if !path_has_downcast(&owned)
                    && is_init_and_destructible(&owned, state, env, locals)
                    && !drops.contains(&owned)
                {
                    drops.push(owned);
                }
            }
        }
    }

    (drops, None)
}

/// Plan the cleanup needed immediately before `require_uninit place`.
///
/// This is intentionally narrower than a generic "make it uninitialized"
/// operation: only statically-owned paths participate, and every inserted
/// operation must be a legal trivial drop or AutoDestroy call. If a live leaf
/// supports neither, the requirement remains for the final checker to reject.
fn plan_drops_for_requirement(
    place: &Place,
    state: &PointState,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> Vec<Place> {
    let Some(owned) = as_owned_path(place) else {
        return Vec::new();
    };
    let Some((root, path)) = extract_path(&owned) else {
        return Vec::new();
    };
    let Some(root_state) = state.locals.get(&root) else {
        return Vec::new();
    };
    let Ok(ty) = env.type_of_place(&owned, locals) else {
        return Vec::new();
    };

    let state = read_state_at_path(root_state, &path);
    let mut drops = Vec::new();
    plan_drops_for_place(owned, &ty, &state, env, &mut drops);
    drops
}

/// True if `place`'s projection path contains a `Downcast` step.
/// Used to skip drop-elaboration for targets/borrowed places rooted
/// in an enum-variant projection.
fn path_has_downcast(place: &Place) -> bool {
    matches!(place, Place::Downcast(_, _))
        || match place {
            Place::Field(inner, _) | Place::Index(inner, _) | Place::Downcast(inner, _) => {
                path_has_downcast(inner)
            }
            Place::Var(_) | Place::Deref(_) => false,
        }
}

/// True iff `place` is fully initialized and supports implicit destruction.
fn is_init_and_destructible(
    place: &Place,
    state: &PointState,
    env: LocalEnv<'_>,
    locals: &IndexMap<String, Type>,
) -> bool {
    let Some((root, path)) = extract_path(place) else {
        return false;
    };
    let Some(root_state) = state.locals.get(&root) else {
        return false;
    };
    let leaf_state = read_state_at_path(root_state, &path);
    if !is_state_fully_init(&leaf_state) {
        return false;
    }
    let Ok(leaf_ty) = env.type_of_place(place, locals) else {
        return false;
    };
    is_implicitly_destructible(env, &leaf_ty)
}

fn is_implicitly_destructible(env: LocalEnv<'_>, ty: &Type) -> bool {
    env.class_of(ty).implies(Marker::Drop)
        || env.has_applicable_trait_impl(&Instance::bare("AutoDestroy"), ty)
}

/// Walk `state` looking for Diverged leaves, recursing into Partial
/// aggregates so a struct with only some fields Diverged emits per-
/// field entries rather than one aggregate. The caller then plans
/// per-arm drops at the granularity that the state actually diverged.
///
/// Non-obvious semantic to flag for future readers: the drops planned
/// from these entries run on the arm that *did* initialize the field.
/// If arm A does `p.y = ...` and arm B doesn't touch `p.y`, drop-elab
/// inserts `drop p.y` on the A → merge split edge — the destructor
/// fires on arm A precisely because arm B didn't do anything with
/// `p.y`. This is the only coherent merge semantics (Init sets have
/// to agree at joins), but the causal shape is inverted from what an
/// outsider expects. See
/// `tests/substructural/check/hll_drop_elab_gaps.si::struct_field_diverged`
/// for the positive fixture and
/// `tests/init_state/partial_init/hll_partial_init_use.si` for the
/// diagnostic on the paired misuse.
fn collect_diverged_paths(
    prog: &IndexedProgram,
    locals: &IndexMap<String, Type>,
    state: &PointState,
) -> Vec<(Place, Type)> {
    let mut out = Vec::new();
    for (name, ty) in locals {
        let Some(root_state) = state.locals.get(name) else {
            continue;
        };
        walk_diverged(prog, var_place(name.clone()), ty, root_state, &mut out);
    }
    out
}

fn walk_diverged(
    prog: &IndexedProgram,
    place: Place,
    ty: &Type,
    state: &InitState,
    out: &mut Vec<(Place, Type)>,
) {
    match state {
        InitState::NeverInit | InitState::Moved | InitState::Init => {}
        InitState::Diverged => out.push((place, ty.clone())),
        InitState::Partial(fields) => {
            // Recurse into fields so a Partial with heterogeneous Init
            // arms (e.g. `{x: Init, y: Init}` ⊔ `{x: Init, z: Init}` →
            // `{x: Init, y: Diverged, z: Diverged}`) drops each
            // diverged field on the arm that Init'd it. Without this
            // recursion the caller sees a whole-aggregate `Partial`
            // whose `state_at` at any pred exit reads back as `Partial`
            // rather than `Init`, and no per-field drop is planned.
            match &ty.kind {
                TypeKind::Custom(Instance {
                    name,
                    type_args: args,
                    ..
                }) => match prog.types.get(name) {
                    Some(TypeDecl::Struct(s)) => {
                        for f in &s.fields {
                            let Some(field_state) = fields.get(&InitSlot::Field(f.name.clone()))
                            else {
                                continue;
                            };
                            let Some(field_ty) = s.meta.try_substitute_types(&f.ty, args) else {
                                continue;
                            };
                            let sub_place = field_place(place.clone(), f.name.clone());
                            walk_diverged(prog, sub_place, &field_ty, field_state, out);
                        }
                    }
                    Some(TypeDecl::Enum(e)) => {
                        for v in &e.variants {
                            let Some(variant_state) =
                                fields.get(&InitSlot::Variant(v.name.clone()))
                            else {
                                continue;
                            };
                            let Some(variant_ty) = e.meta.try_substitute_types(&v.ty, args) else {
                                continue;
                            };
                            let sub_place = downcast_place(place.clone(), v.name.clone());
                            walk_diverged(prog, sub_place, &variant_ty, variant_state, out);
                        }
                    }
                    None => {}
                },
                TypeKind::Array(elem, n) => {
                    for k in 0..*n {
                        let Some(slot_state) = fields.get(&InitSlot::Index(k)) else {
                            continue;
                        };
                        let sub_place = index_place(
                            place.clone(),
                            Operand::Const(ConstVal::Int {
                                bits: k,
                                ty: IntTy::I64,
                            }),
                        );
                        walk_diverged(prog, sub_place, elem, slot_state, out);
                    }
                }
                // Non-aggregate types can only be Init/NeverInit/Moved
                // (see `analysis::expand_uniform` / `expand_uniform_array` —
                // Partial is only produced for structs, enums, and
                // arrays). A Partial state here would indicate a lattice
                // invariant violation upstream.
                _ => {}
            }
        }
    }
}

/// Return the init state at `place` within `state.locals`. Returns None
/// if the root Var isn't tracked.
fn state_at(state: &PointState, place: &Place) -> Option<InitState> {
    let (root, path) = extract_path(place)?;
    let root_state = state.locals.get(&root)?;
    Some(read_state_at_path(root_state, &path))
}

fn read_state_at_path(state: &InitState, path: &[PathStep]) -> InitState {
    if path.is_empty() {
        return state.clone();
    }
    match &path[0] {
        PathStep::Field(f) => match state {
            InitState::Partial(map) => {
                let sub = map
                    .get(&InitSlot::Field(f.clone()))
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Index(Some(k)) => match state {
            InitState::Partial(map) => {
                let sub = map
                    .get(&InitSlot::Index(*k))
                    .cloned()
                    .unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Downcast(v) => match state {
            InitState::NeverInit | InitState::Moved | InitState::Diverged => state.clone(),
            InitState::Partial(map) => {
                let sub = map
                    .get(&InitSlot::Variant(v.clone()))
                    .cloned()
                    .unwrap_or(InitState::Init);
                read_state_at_path(&sub, &path[1..])
            }
            InitState::Init => read_state_at_path(&InitState::Init, &path[1..]),
        },
        PathStep::Deref | PathStep::Index(None) => state.clone(),
    }
}

fn plan_drops_at_return(
    func: &Function,
    body: &FunctionBody,
    state: &PointState,
    env: LocalEnv<'_>,
) -> Vec<Place> {
    // Combined declaration order: params, then locals. LIFO drop = reverse.
    let mut order: Vec<(String, Type)> = Vec::new();
    for p in &func.params {
        order.push((p.name.clone(), p.ty.clone()));
    }
    for l in &body.locals {
        order.push((l.name.clone(), l.ty.clone()));
    }

    let mut drops = Vec::new();
    for (name, ty) in order.iter().rev() {
        let Some(s) = state.locals.get(name) else {
            continue;
        };
        // Refs with unfulfilled obligations must NOT be dropped: doing so
        // would silently violate their (cur, post). Skip; the leak check
        // will surface the missing consumption.
        if let Some(rs) = state.refs.get(&var_place(name.clone())) {
            if !rs.obligation_fulfilled() {
                continue;
            }
        }
        plan_drops_for_place(var_place(name.clone()), ty, s, env, &mut drops);
    }
    drops
}

/// Walk the init state at `place: ty` and append the cleanup sites needed to
/// leave every leaf `Moved`/`NeverInit`. Emitted in LIFO order — for a
/// `Partial`, fields are iterated in reverse declaration order.
///
/// `Diverged` sub-paths are skipped here because they require CFG edge
/// cleanup rather than an unconditional pre-statement operation. The cross-edge
/// phase handles the first divergent join; if no legal cleanup exists, the
/// final requirement check remains authoritative.
fn plan_drops_for_place(
    place: Place,
    ty: &Type,
    state: &InitState,
    env: LocalEnv<'_>,
    out: &mut Vec<Place>,
) {
    // A fully initialized aggregate is cleaned as one value. In particular,
    // AutoDestroy must receive a complete Self; only genuinely partial state
    // takes the structural path below.
    if is_state_fully_init(state) {
        if is_implicitly_destructible(env, ty) {
            out.push(place);
        }
        return;
    }
    match state {
        InitState::NeverInit | InitState::Moved | InitState::Diverged => {}
        InitState::Init => {
            if is_implicitly_destructible(env, ty) {
                out.push(place);
            }
        }
        InitState::Partial(fields) => {
            match &ty.kind {
                // Reverse declared field order = LIFO for that container.
                TypeKind::Custom(Instance {
                    name: struct_name,
                    type_args: args,
                    ..
                }) => {
                    // `None` on `env.types.get`: type not registered —
                    // type-check already reported. Non-Struct decl: an
                    // enum-typed Partial with variant-refinement is
                    // handled by the `is_state_fully_init` shortcut
                    // above; a Partial that reaches here on an enum
                    // has diverged or moved payload state and can't be
                    // safely per-variant dropped — the outer leak
                    // check remains authoritative.
                    let TypeDecl::Struct(s) = (match env.program().types.get(struct_name) {
                        Some(d) => d,
                        None => return,
                    }) else {
                        return;
                    };
                    // Substitute the outer args through each field's declared
                    // type — otherwise a `Bag<DropVal>.b` recurses with the raw
                    // `Param(T)`, which `class_of` resolves to empty markers
                    // under an empty scope and misses the drop.
                    let field_decls: Option<Vec<_>> = s
                        .fields
                        .iter()
                        .map(|f| {
                            s.meta
                                .try_substitute_types(&f.ty, args)
                                .map(|ty| (f.name.clone(), ty))
                        })
                        .collect();
                    let Some(field_decls) = field_decls else {
                        return;
                    };
                    for (name, field_ty) in field_decls.iter().rev() {
                        let Some(field_state) = fields.get(&InitSlot::Field(name.clone())) else {
                            continue;
                        };
                        let fp = field_place(place.clone(), name.clone());
                        plan_drops_for_place(fp, field_ty, field_state, env, out);
                    }
                }
                // Constant-index places are tracked independently. Reverse
                // element order gives the same deterministic LIFO rule as
                // fields and avoids making array cleanup a special case in
                // `require_uninit`.
                TypeKind::Array(elem, n) => {
                    for index in (0..*n).rev() {
                        let Some(element_state) = fields.get(&InitSlot::Index(index)) else {
                            continue;
                        };
                        let ip = index_place(
                            place.clone(),
                            Operand::Const(ConstVal::Int {
                                bits: index,
                                // Match the parser's unsuffixed integer
                                // literal type so inserted constant-index
                                // drops round-trip like their source places.
                                ty: IntTy::I64,
                            }),
                        );
                        plan_drops_for_place(ip, elem, element_state, env, out);
                    }
                }
                // A Partial state only arises on struct or array types
                // (write_at / move_at only promote to Partial for those
                // shapes). Enum-Custom variants use whole-value
                // construction (`Name::V(...)`), so Partial on an enum
                // is not reachable through the checker — the enum-Custom
                // fallthrough here is what makes Partial-on-enum a no-op
                // for drop planning. Scalar / ref / raw-ptr / fn / Param
                // types can't be Partial by construction. Any Partial
                // reaching here with those kinds is a bug upstream.
                TypeKind::Unit
                | TypeKind::Int(_)
                | TypeKind::Float(_)
                | TypeKind::Bool
                | TypeKind::Never
                | TypeKind::Param(_)
                | TypeKind::Ref(_, _, _)
                | TypeKind::RawPtr(_)
                | TypeKind::Fn(_) => {}
            }
        }
    }
}
