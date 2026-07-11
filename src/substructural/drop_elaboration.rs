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

use crate::ast::*;
use crate::cfg_edit;
use crate::init_state::{self, InitState, PointState};
use crate::substructural::composition::class_of;
use crate::type_check::Env;
use indexmap::IndexMap;

/// Per-function plan for the elaboration pass.
#[derive(Default)]
struct FnPlan {
    /// (return-block label) → drops to append inside that block, before
    /// the return terminator.
    in_return_block: IndexMap<String, Vec<Place>>,
    /// (pred, succ_return_block) → drops to place on the split edge,
    /// for `Diverged` places whose predecessor-exit state was Init.
    cross_edge: IndexMap<(String, String), Vec<Place>>,
}

/// Insert return-leak drops in `program` using analysis state from `env`.
/// `env` should have been built from `program` before calling.
pub fn elaborate(program: &mut Program, env: &Env) {
    // Phase 1 (immutable): plan per function.
    let mut plans: IndexMap<String, FnPlan> = IndexMap::new();
    for func in env.functions.values() {
        let plan = plan_for_function(env, func);
        if !plan.in_return_block.is_empty() || !plan.cross_edge.is_empty() {
            plans.insert(func.name.clone(), plan);
        }
    }

    // Phase 2 (mutable): apply plans.
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

        // In-block drops: append to each block before its terminator.
        for block in &mut body.blocks {
            let Some(drops) = plan.in_return_block.get(&block.label) else {
                continue;
            };
            let span = block.terminator_span;
            for place in drops {
                block
                    .statements
                    .push((Statement::Drop(place.clone()), span));
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
                    .push((Statement::Drop(p.clone()), span));
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

    // In-block: use the merged state at the return point (existing behavior).
    for (block, state) in init_state::states_before_returns(env, func) {
        let drops = plan_drops_at_return(func, &state, env);
        if !drops.is_empty() {
            plan.in_return_block.insert(block.label.clone(), drops);
        }

        // Cross-edge: for each Diverged path at the return-block entry,
        // find which predecessors were Init and split those edges.
        let Some(return_entry) = entry_states.get(&block.label) else {
            continue;
        };
        let diverged_paths = collect_diverged_paths(func, return_entry);
        if diverged_paths.is_empty() {
            continue;
        }
        // Determine predecessors and their exit states.
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
                    && class_of(ty, env).drop
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
        walk_diverged(Place::Var(name.clone()), ty, root_state, &mut out);
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
            let Type::Custom(struct_name) = ty else {
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

fn plan_drops_at_return(func: &Function, state: &PointState, env: &Env) -> Vec<Place> {
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
        if let Some(rs) = state.refs.get(&Place::Var(name.clone())) {
            if !rs.obligation_fulfilled() {
                continue;
            }
        }
        plan_drops_for_place(Place::Var(name.clone()), ty, s, env, &mut drops);
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
    out: &mut Vec<Place>,
) {
    match state {
        InitState::NeverInit | InitState::Moved | InitState::Diverged => {}
        InitState::Init => {
            if class_of(ty, env).drop {
                out.push(place);
            }
        }
        InitState::Partial(fields) => {
            // Reverse declared field order = LIFO for that container.
            let Type::Custom(struct_name) = ty else {
                return;
            };
            let field_decls = match env.types.get(struct_name) {
                Some(crate::type_check::TypeDecl::Struct(s)) => &s.fields,
                _ => return,
            };
            for f in field_decls.iter().rev() {
                let Some(field_state) = fields.get(&f.name) else {
                    continue;
                };
                let field_place = Place::Field(Box::new(place.clone()), f.name.clone());
                plan_drops_for_place(field_place, &f.ty, field_state, env, out);
            }
        }
    }
}
