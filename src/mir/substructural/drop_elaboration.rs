//! Drop elaboration pass.
//!
//! Inserts explicit `drop p` statements before each `return` for every
//! variable whose init state is `Init` at that point and whose type is
//! Drop. Turns implicit forgets into explicit consumption so a
//! subsequent leak check can validate the elaborated MIR.
//!
//! **Design status:** in the final compiler pipeline, drop *placement*
//! is a HLL responsibility — the source language's scope rules dictate
//! LIFO order and when destructors run. This pass exists as (a) a
//! reference implementation for validating a frontend's drop insertion,
//! (b) a convenience for hand-written MIR test programs, and (c) an
//! exercise target for the leak checker. It emits drops in reverse
//! declaration order (locals reversed first, then params reversed) —
//! this agrees with LIFO for programs that init in declaration order,
//! which is the norm.
//!
//! **Handled:**
//!   * Simple return leaks — variable Init at return with a Drop type.
//!   * `Partial` states at return — per-leaf drops walking the struct
//!     field tree.
//!   * `Diverged` states — per-edge drops inserted via `cfg_edit` on the
//!     Init-side predecessors of a return block.
//!
//! **Not handled (delegated to the frontend or the checker):**
//!   * Pre-overwrite drops (`p = ...` where p was Init). The overwrite
//!     check in `init_state` rejects these as errors, expecting the
//!     frontend to emit `drop p` before the reassignment.
//!
//! **Idempotent**: rerunning the pass produces no additional drops. A
//! dropped variable transitions to `Moved` in the init dataflow, so a
//! second run finds nothing to insert.

use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::cfg_edit;
use crate::mir::init_state::{self, InitState, PointState};
use crate::mir::substructural::composition::{class_of, scope_from, ParamScope};
use crate::mir::type_check::{Env, TypeDecl};
use crate::mir::type_util::substitute_params;
use indexmap::IndexMap;

/// Per-function plan for the elaboration pass.
#[derive(Default)]
struct FnPlan {
    /// (block_label, insert_pos) → drops to splice at that position.
    /// `insert_pos` is an index in `[0, N]`: 0 means "before the
    /// first statement", N (= number of statements) means "before
    /// the terminator". Statement indices refer to the ORIGINAL
    /// (pre-splice) list; apply sorts descending so splices don't
    /// invalidate earlier indices. Handles both Init → Uninit
    /// transitions mid-block (`&out place` on an Init-Drop place)
    /// AND end-of-block return cleanups uniformly: the terminator
    /// acts as a "use" that consumes any still-Init Drop values.
    pre_stmt: IndexMap<(String, usize), Vec<Place>>,
    /// (block_label, statement_index) → replacement for the original
    /// statement at that index. Used for the downcast-target
    /// reassignment case (`X as V = <operand>` becomes
    /// `X = EnumName::V(<operand>)`), which pairs with a pre_stmt
    /// `drop (X as V)`. Applied BEFORE splicing so indices remain
    /// valid for the pre_stmt phase.
    rewrite_stmt: IndexMap<(String, usize), Statement>,
    /// (pred, succ_return_block) → drops to place on the split edge,
    /// for `Diverged` places whose predecessor-exit state was Init.
    /// Kept separate because insertion requires structurally
    /// splitting the CFG edge.
    cross_edge: IndexMap<(String, String), Vec<Place>>,
}

/// Insert return-leak drops in `program` using analysis state from `env`.
/// `env` should have been built from `program` before calling.
pub fn elaborate(program: &mut Program, env: &Env) {
    // Plan (immutable): compute the per-function insertion set.
    let mut plans: IndexMap<String, FnPlan> = IndexMap::new();
    for func in env.functions.values() {
        let plan = plan_for_function(env, func);
        if !plan.pre_stmt.is_empty()
            || !plan.rewrite_stmt.is_empty()
            || !plan.cross_edge.is_empty()
        {
            plans.insert(func.name.clone(), plan);
        }
    }

    // Apply (mutable): splice the planned changes into each body.
    for decl in &mut program.declarations {
        let Declaration::Fn(func) = decl else {
            continue;
        };
        let Some(plan) = plans.get(&func.name) else {
            continue;
        };
        let Some(body) = &mut func.body else {
            continue;
        };

        // Statement rewrites first: replace in place, no index shift.
        // Pair with the pre-stmt drops planned for the same index.
        for block in &mut body.blocks {
            for ((label, idx), new_stmt) in &plan.rewrite_stmt {
                if label != &block.label {
                    continue;
                }
                if let Some((slot, _)) = block.statements.get_mut(*idx) {
                    *slot = new_stmt.clone();
                }
            }
        }

        // Pre-stmt drops: splice into each block at the recorded
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
                    .map(|(_, s)| *s)
                    .unwrap_or(block.terminator_span);
                let items: Vec<(Statement, Span)> = places
                    .iter()
                    .map(|p| (drop_stmt(p.clone()), span))
                    .collect();
                block.statements.splice(pos..pos, items);
            }
        }

        // Cross-edge drops: split each edge (idempotent), then append.
        for ((pred, succ), places) in &plan.cross_edge {
            let split_label = cfg_edit::split_edge(body, pred, succ);
            let split_block = body
                .blocks
                .iter_mut()
                .find(|b| b.label == split_label)
                .expect("split_edge just guaranteed this block exists");
            let span = split_block.terminator_span;
            for p in places {
                split_block
                    .statements
                    .push((drop_stmt(p.clone()), span));
            }
        }
    }
}

fn plan_for_function(env: &Env, func: &Function) -> FnPlan {
    let mut plan = FnPlan::default();
    let Some(body) = &func.body else {
        return plan;
    };
    if body.blocks.is_empty() {
        return plan;
    }

    let entry_states = init_state::block_entry_states(env, func);
    let locals = func.locals_map();
    let scope = scope_from(&func.type_params);

    // Unified walk: for each block, walk forward from its entry state
    // and plan drops at each program point where a Drop-typed slot
    // transitions Init → Uninit.
    //   - Mid-block: before an `Assign(_, Ref(Out|Uninit, place))`
    //     where `place` is Init Drop, insert `drop place` so the
    //     Uninit precondition holds after elaboration.
    //   - End-of-block (return terminator): treat the return as a
    //     "use" that consumes every still-Init Drop local — insert
    //     drops in LIFO order right before the terminator.
    //
    // Planned drops apply to the running state (via silent transfer)
    // so the return-cleanup step doesn't re-drop something the pre-
    // stmt step already dropped.
    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else {
            continue;
        };
        let mut state = entry.clone();
        for (stmt_idx, (stmt, _)) in block.statements.iter().enumerate() {
            let (drops, rewrite) = pre_stmt_transitions(stmt, &state, env, &locals, &scope);
            if !drops.is_empty() {
                for place in &drops {
                    init_state::transfer_stmt_silent(
                        env,
                        func,
                        &Statement::Drop(place.clone()),
                        &mut state,
                    );
                }
                plan.pre_stmt
                    .insert((block.label.clone(), stmt_idx), drops);
            }
            // Transfer whichever form we're going to leave in the
            // elaborated MIR: the rewrite if present, else the
            // original. Both should produce the same net state
            // effect, but we track the elaborated form for
            // correctness under later analysis.
            let effective = rewrite.clone().unwrap_or_else(|| stmt.clone());
            init_state::transfer_stmt_silent(env, func, &effective, &mut state);
            if let Some(new_stmt) = rewrite {
                plan.rewrite_stmt
                    .insert((block.label.clone(), stmt_idx), new_stmt);
            }
        }
        // Pre-terminator cleanup for return blocks: drop everything
        // still Init-Drop at this point.
        if matches!(block.terminator, Terminator::Return) {
            let drops = plan_drops_at_return(func, &state, env, &scope);
            if !drops.is_empty() {
                let insert_pos = block.statements.len();
                plan.pre_stmt.insert((block.label.clone(), insert_pos), drops);
            }
        }
    }

    // Cross-edge: at every join with Diverged-at-entry paths, split the
    // Init-side predecessor edges and insert per-arm drops. Restricting
    // this to return blocks (the earlier shape) misses the case where a
    // value goes Init on one arm and NeverInit on another, joins into
    // an intermediate merge block (whose terminator is switchEnum,
    // goto, branch, ...) rather than return, and stays Diverged all the
    // way through — at the eventual return the direct preds already
    // have Diverged exit states, so the pred-Init check finds nothing
    // to drop. Handling every join catches the transition at its
    // first occurrence. Uses fixpoint entry states directly — the
    // pre-stmt drops above are intra-block, so predecessor exit states
    // are unaffected.
    for block in &body.blocks {
        let Some(block_entry) = entry_states.get(&block.label) else {
            continue;
        };
        let diverged_paths = collect_diverged_paths(func, block_entry);
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
            let Some(pred_entry) = entry_states.get(&pred_block.label) else {
                continue;
            };
            let mut pred_exit = pred_entry.clone();
            for (stmt, _) in &pred_block.statements {
                init_state::transfer_stmt_silent(env, func, stmt, &mut pred_exit);
            }
            for (path_place, ty) in &diverged_paths {
                if state_at(&pred_exit, path_place) == Some(InitState::Init)
                    && class_of(ty, env, &scope).implies(Marker::Drop)
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

/// Return `(drops_to_insert_before, optional_statement_rewrite)` for
/// `stmt` given the init state at this program point.
///
/// Three Init → Uninit transition shapes:
///
/// - **Overwriting assign (Var/Field target)**: `target = <rvalue>`
///   where `target` is an owned path currently Init and its type is
///   Drop. Inserts `drop target` so the old value's destructor
///   eventually runs (a no-op today with trivial bitwise-forget
///   `Drop`; correct once `Destroy` (pure custom destructor) lands).
/// - **Overwriting assign (Downcast target)**: `X as V = <operand>`
///   where the enum X is Init and V's payload is Drop. Rewrites the
///   assign into `X = EnumName::V(<operand>)` and inserts
///   `drop (X as V)` before. The rewrite bypasses the enum-
///   atomicity trap: `drop (X as V)` cascades X to Moved, and the
///   EnumConstr rebuilds it as variant V. Only fires when the
///   rvalue is an operand — for Ref/ArrayLit payloads, the frontend
///   still needs to hoist the payload into a temp (deferred).
/// - **`&out` / `&uninit` borrow of an Init Drop place**: `foo =
///   &out place` where `place` is Init Drop. Inserts `drop place`
///   so the Uninit precondition is satisfied.
///
/// All cases skip `Partial` states (per-leaf drops are complex; the
/// existing overwrite check handles the common non-Drop cases) and
/// reborrow shapes (`&out *r`) which are governed by RefState.
fn pre_stmt_transitions(
    stmt: &Statement,
    state: &PointState,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: ParamScope,
) -> (Vec<Place>, Option<Statement>) {
    let Statement::Assign(target, rvalue) = stmt else {
        return (Vec::new(), None);
    };
    let mut drops = Vec::new();

    // Downcast target with operand rvalue → rewrite to full-enum
    // reconstruction. Handled specially before the generic Case A
    // because Case A skips Downcast paths.
    if let (Place::Downcast(inner, variant), RValue::Use(operand)) = (target, rvalue) {
        if let Some(inner_owned) = as_owned_path(inner) {
            if let Ok(inner_ty) = env.type_of_place(inner, crate::mir::ast::Span::default(), locals) {
                if let Type::Custom(enum_name, _) = &inner_ty {
                    let payload_place =
                        downcast_place(inner_owned.clone(), variant.clone());
                    if is_init_and_drop(&payload_place, state, env, locals, scope) {
                        drops.push(payload_place);
                        let rewrite = assign_stmt(
                            inner_owned,
                            enum_constr_rv(enum_name.clone(), variant.clone(), operand.clone()),
                        );
                        return (drops, Some(rewrite));
                    }
                }
            }
        }
    }

    // Case A: overwriting an owned-path target whose leaf state is
    // Init and whose type is Drop. Skip Downcast-containing paths.
    if let Some(owned) = as_owned_path(target) {
        if !path_has_downcast(&owned) && is_init_and_drop(&owned, state, env, locals, scope) {
            drops.push(owned);
        }
    }

    // Case B: `&out` / `&uninit` on an Init Drop place.
    if let RValue::Ref(RefKind::Out | RefKind::Uninit, place) = rvalue {
        if deref_inner(place).is_none() {
            if let Some(owned) = as_owned_path(place) {
                if !path_has_downcast(&owned)
                    && is_init_and_drop(&owned, state, env, locals, scope)
                    && !drops.contains(&owned)
                {
                    drops.push(owned);
                }
            }
        }
    }

    (drops, None)
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

/// True iff `place` (an owned path) is fully `Init` at this state AND
/// its type is Drop. Used to decide whether an implicit drop should
/// be inserted for an Init → Uninit transition.
fn is_init_and_drop(
    place: &Place,
    state: &PointState,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: ParamScope,
) -> bool {
    let Some((root, path)) = extract_path(place) else {
        return false;
    };
    let Some(root_state) = state.locals.get(&root) else {
        return false;
    };
    let leaf_state = read_state_at_path(root_state, &path);
    if !matches!(leaf_state, InitState::Init) {
        return false;
    }
    let Ok(leaf_ty) = env.type_of_place(place, crate::mir::ast::Span::default(), locals) else {
        return false;
    };
    class_of(&leaf_ty, env, scope).implies(Marker::Drop)
}

/// Walk `state` looking for `Diverged` leaves (or Diverged aggregates
/// whose type is Drop). Returns each Diverged path with its type so the
/// caller can decide per-edge insertion.
fn collect_diverged_paths(func: &Function, state: &PointState) -> Vec<(Place, Type)> {
    let mut out = Vec::new();
    let locals = func.locals_map();
    for (name, ty) in &locals {
        let Some(root_state) = state.locals.get(name) else {
            continue;
        };
        walk_diverged(var_place(name.clone()), ty, root_state, &mut out);
    }
    out
}

fn walk_diverged(place: Place, ty: &Type, state: &InitState, out: &mut Vec<(Place, Type)>) {
    match state {
        InitState::NeverInit | InitState::Moved | InitState::Init => {}
        InitState::Diverged => out.push((place, ty.clone())),
        InitState::Partial(fields) => {
            // If any field is Diverged, recurse. Type resolution for
            // struct fields is done inline.
            let Type::Custom(struct_name, _) = ty else {
                return;
            };
            // We don't have env here — the caller resolves types below
            // via a separate path. Emit the whole Partial with its
            // struct type so the caller can walk field-by-field with env.
            let _ = struct_name;
            let _ = fields;
            out.push((place, ty.clone()));
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
                let sub = map.get(f).cloned().unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Index(Some(k)) => match state {
            InitState::Partial(map) => {
                let sub = map.get(&k.to_string()).cloned().unwrap_or(InitState::NeverInit);
                read_state_at_path(&sub, &path[1..])
            }
            other => other.clone(),
        },
        PathStep::Downcast(_) => match state {
            InitState::NeverInit | InitState::Moved | InitState::Diverged => state.clone(),
            _ => InitState::Init,
        },
        PathStep::Deref | PathStep::Index(None) => state.clone(),
    }
}

fn plan_drops_at_return(func: &Function, state: &PointState, env: &Env, scope: ParamScope) -> Vec<Place> {
    // Combined declaration order: params, then locals. LIFO drop = reverse.
    let mut order: Vec<(String, Type)> = Vec::new();
    for p in &func.params {
        order.push((p.name.clone(), p.ty.clone()));
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            order.push((l.name.clone(), l.ty.clone()));
        }
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
        plan_drops_for_place(var_place(name.clone()), ty, s, env, scope, &mut drops);
    }
    drops
}

/// Walk the init state at `place: ty` and append the drops needed to
/// leave every leaf `Moved`/`NeverInit`. Emitted in LIFO order — for a
/// `Partial`, fields are iterated in reverse declaration order.
///
/// `Diverged` sub-paths are skipped: the elaborator can't insert
/// unconditional drops there without splitting the join edges (a future
/// slice). The strict leak check will flag them.
fn plan_drops_for_place(
    place: Place,
    ty: &Type,
    state: &InitState,
    env: &Env,
    scope: ParamScope,
    out: &mut Vec<Place>,
) {
    match state {
        InitState::NeverInit | InitState::Moved | InitState::Diverged => {}
        InitState::Init => {
            if class_of(ty, env, scope).implies(Marker::Drop) {
                out.push(place);
            }
        }
        InitState::Partial(fields) => {
            // Reverse declared field order = LIFO for that container.
            let Type::Custom(struct_name, args) = ty else {
                return;
            };
            let TypeDecl::Struct(s) = (match env.types.get(struct_name) {
                Some(d) => d,
                None => return,
            }) else {
                return;
            };
            // Substitute the outer args through each field's declared
            // type — otherwise a `Bag<DropVal>.b` recurses with the raw
            // `Param(T)`, which `class_of` resolves to empty markers
            // under an empty scope and misses the drop.
            let type_params = s.type_params.clone();
            let field_decls: Vec<_> = s
                .fields
                .iter()
                .map(|f| (f.name.clone(), substitute_params(&f.ty, &type_params, args)))
                .collect();
            for (name, field_ty) in field_decls.iter().rev() {
                let Some(field_state) = fields.get(name) else {
                    continue;
                };
                let fp = field_place(place.clone(), name.clone());
                plan_drops_for_place(fp, field_ty, field_state, env, scope, out);
            }
        }
    }
}
