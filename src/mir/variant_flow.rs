//! Enum-variant reachability analysis for `switchEnum`. Enforces:
//!
//!   - Every declared variant of the switched enum must appear as an arm.
//!   - No duplicate arm for the same variant.
//!   - An arm whose target block terminates in `unreachable` is valid only if
//!     the variant is provably unreachable at the switch point. Conversely, an
//!     arm targeting real code for a provably-unreachable variant is dead code
//!     — a warning, not an error.
//!
//! State lattice per (block-entry, place):
//!   * Absent from the map          = ⊤ (any variant possible)
//!   * `Some(subset)`               = tracked subset
//!   * The whole block unvisited by the fixed-point = ⊥ (skip; unreachable)
//!
//! We only track `Place::Var(_)`. Downcasts on projection paths
//! (`x.f as V`, `(x as U).f as V`, etc.) are rejected at check time —
//! nothing in this analysis proves the projection is the required
//! variant, so requiring an extract-to-local first keeps the checker
//! honest. Exclusive borrows (`&mut`/`&out`/`&drop`/`&uninit`) of a
//! tracked Var clobber that Var back to ⊤ for the rest of its
//! lifetime, since we can't see what the borrower does.

use crate::diagnostics::{DiagCode, Diagnostics};
use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction, WalkPoint};
use crate::mir::helpers::*;
use crate::mir::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// Machine-readable diagnostic codes emitted by the variant-flow pass.
///
/// Multiple push sites that surface the same conceptual failure share
/// a code (e.g. every "declared variant missing" arm produces one
/// `SwitchNotExhaustive` diagnostic).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantFlowCode {
    /// `place as V` where flow analysis hasn't refined `place`'s
    /// variant set to (a subset containing only) `V`. Usually needs a
    /// preceding `switchEnum` arm to narrow the state.
    DowncastVariantNotRefined,
    /// Downcast applied to a projection like `s.e as V`. Variant flow
    /// only tracks root `Var`s — copy through a local first.
    DowncastOnProjection,
    /// `switchEnum` with zero arms — no control-flow successor.
    SwitchNoArms,
    /// `switchEnum` doesn't cover every declared variant of the enum.
    /// Each missing variant reports its own diagnostic.
    SwitchNotExhaustive,
    /// `switchEnum` names the same variant twice. Each repeat reports
    /// its own diagnostic.
    SwitchDuplicateArm,
}

impl From<VariantFlowCode> for DiagCode {
    fn from(code: VariantFlowCode) -> DiagCode {
        DiagCode::VariantFlow(code)
    }
}
use VariantFlowCode::*;

/// State at one program point: per-Var variant set. Absent = ⊤.
type PointState = IndexMap<String, BTreeSet<String>>;

struct VariantFlow;

impl Analysis for VariantFlow {
    type State = PointState;
    fn direction(&self) -> Direction {
        Direction::Forward
    }
    fn boundary_state(&self) -> Self::State {
        PointState::new()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        join(a, b)
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, _source: SourceInfo) {
        transfer_stmt(stmt, state);
    }
    fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
    fn refine_edge(&self, state: &mut Self::State, block: &BasicBlock, succ: &str) {
        // switchEnum arm edges refine the switched Var to the matched variant.
        let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind else {
            return;
        };
        let Some(root) = root_var(place) else {
            return;
        };
        for (variant, label) in cases {
            if label == succ {
                let mut singleton = BTreeSet::new();
                singleton.insert(variant.clone());
                state.insert(root.to_string(), singleton);
                return;
            }
        }
    }
}

pub fn check_program(program: &Program, env: &Env, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let locals = func.locals_map();
    let entry_states = dataflow::run(&VariantFlow, body);

    dataflow::walk_forward(&VariantFlow, body, &entry_states, |pt| {
        if let WalkPoint::Terminator { block, .. } = pt {
            if let TerminatorKind::SwitchEnum { place, cases } = &block.terminator.kind {
                check_switch(env, func, &locals, block, place, cases, d);
            }
        }
    });
}

/// Strict Var-only extraction. Unlike `ast::extract_path`, this returns
/// `None` for any projection (field, downcast) — enum_variants tracks only
/// top-level Var variant sets, so refinement/clobbering must not attribute
/// sub-place operations to the root.
fn root_var(place: &Place) -> Option<&str> {
    match place {
        Place::Var(name) => Some(name.as_str()),
        _ => None,
    }
}

// Downcast-refinement diagnostics moved to place_state, which tracks
// per-variant payload state and covers projection places uniformly.

fn transfer_stmt(stmt: &Statement, state: &mut PointState) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // Exclusive borrow of a tracked Var → clobber it: we can't see
            // what the borrower does. Raw pointer creation clobbers
            // for the same reason (aliasing writes possible).
            let clobber_borrowed: Option<&Place> = match rvalue {
                RValue::Ref(kind, borrowed) if !matches!(kind, RefKind::Shared) => Some(borrowed),
                RValue::RawRef(borrowed) => Some(borrowed),
                _ => None,
            };
            if let Some(borrowed) = clobber_borrowed {
                if let Some(root) = root_var(borrowed) {
                    state.shift_remove(root);
                }
            }

            // Update state[target] iff target is a Var. Writes through
            // non-Var places don't refine any tracked Var (we don't do
            // aliasing here).
            let Place::Var(t) = target else {
                return;
            };
            match rvalue {
                RValue::EnumConstr(_, _, variant, _) => {
                    let mut set = BTreeSet::new();
                    set.insert(variant.clone());
                    state.insert(t.clone(), set);
                }
                RValue::Use(op) => match op {
                    Operand::Copy(Place::Var(src))
                    | Operand::Move(Place::Var(src))
                    | Operand::Take(Place::Var(src)) => {
                        if let Some(set) = state.get(src).cloned() {
                            state.insert(t.clone(), set);
                        } else {
                            state.shift_remove(t);
                        }
                    }
                    _ => {
                        state.shift_remove(t);
                    }
                },
                _ => {
                    state.shift_remove(t);
                }
            }
        }
        StatementKind::Call(_, _) => {
            // Return values flow through `&out` params; those references were
            // borrowed at some earlier assignment (which already clobbered
            // the underlying Var). Nothing to do here.
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            // Consumes the place — kill any variant refinement.
            if let Some(root) = root_var(place) {
                state.shift_remove(root);
            }
        }
        StatementKind::RequireUninit(_) => {
            // Ghost assertion; it has no transfer effect until place-state
            // elaboration materializes any required cleanup.
        }
    }
}

fn join(a: &PointState, b: &PointState) -> PointState {
    let mut out = PointState::new();
    for (var, va) in a {
        if let Some(vb) = b.get(var) {
            let mut u = va.clone();
            u.extend(vb.iter().cloned());
            out.insert(var.clone(), u);
        }
        // absent from b → ⊤ in b → ⊤ in join → omit
    }
    // vars only in b → ⊤ in a → ⊤ in join → omit
    out
}

fn check_switch(
    env: &Env,
    func: &Function,
    locals: &IndexMap<String, Type>,
    block: &BasicBlock,
    place: &Place,
    cases: &[(String, String)],
    d: &mut Diagnostics,
) {
    let terminator_source = block.terminator.source;
    if cases.is_empty() {
        d.push_error(diag(
            SwitchNoArms,
            terminator_source,
            func,
            block,
            "switchEnum requires at least one arm".to_string(),
        ));
    }

    let Some(enum_decl) = resolve_enum_of_place(env, locals, place) else {
        // Non-enum place (or unresolvable local) — tc reports it. Skip flow.
        return;
    };

    let declared: Vec<&str> = enum_decl.variants.iter().map(|v| v.name.as_str()).collect();
    let handled: BTreeSet<&str> = cases.iter().map(|(v, _)| v.as_str()).collect();

    // Exhaustiveness — report missing variants in declaration order.
    for variant in &declared {
        if !handled.contains(variant) {
            d.push_error(diag(
                SwitchNotExhaustive,
                terminator_source,
                func,
                block,
                format!(
                    "switchEnum on '{}' does not handle variant '{}'",
                    enum_decl.meta.name, variant
                ),
            ));
        }
    }

    // Duplicate arms — report each repeat, in occurrence order.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    for (variant, _) in cases {
        if !seen.insert(variant.as_str()) {
            d.push_error(diag(
                SwitchDuplicateArm,
                terminator_source,
                func,
                block,
                format!("switchEnum has duplicate arm for variant '{}'", variant),
            ));
        }
    }

    // Per-arm reachability (SwitchArmFalselyUnreachable / SwitchArmDeadCode)
    // lives in the reachability module now, keyed off place_state's
    // per-variant refinement rather than variant_flow's own dataflow.
    let _ = declared;
}

fn resolve_enum_of_place<'a>(
    env: &'a Env,
    locals: &IndexMap<String, Type>,
    place: &Place,
) -> Option<&'a EnumDecl> {
    // We only need the successful branch; span doesn't matter since
    // any error is discarded.
    let ty = env.type_of_place(place, locals).ok()?;
    let TypeKind::Custom(name, _, _) = ty.kind else {
        return None;
    };
    match env.types.get(&name) {
        Some(TypeDecl::Enum(e)) => Some(e),
        _ => None,
    }
}
