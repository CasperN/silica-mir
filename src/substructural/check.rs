//! Substructural checker for MIR statements.
//!
//! Verifies (a) that statements respect the substructural class of the types
//! they operate on and (b) that no value is silently forgotten at `return`.
//!
//! - `copy p` (operand position) requires `p`'s type to be `Copy`.
//! - `drop p` requires `p`'s type to be `Drop`.
//! - At `return`, any non-consumed path is a leak — no leniency for Drop
//!   types; the drop-elaboration pass is expected to have inserted the
//!   needed drops.
//!
//! The design is: `run_all_passes` runs the class checks *before*
//! elaboration and the leak check *after* elaboration. Errors on
//! elaborated output indicate the elaborator was unable to insert enough
//! drops (currently: Partial or Diverged states).
//!
//! Deferred: overwrite checks (`p = ...` where `p` was Init) and CFG-join
//! disagreement checks.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::init_state::{self, InitState, PointState};
use crate::push_error;
use crate::substructural::composition::class_of;
use crate::type_check::Env;
use indexmap::IndexMap;

/// Class-precondition checks over statements (does not include leak-at-
/// return, which callers run separately, typically after elaboration).
pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    let locals = func.locals_map();
    for block in &body.blocks {
        for (stmt, span) in &block.statements {
            check_stmt(env, func, block, &locals, stmt, *span, d);
        }
        check_terminator(env, func, block, &locals, d);
    }
}

fn check_stmt(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    stmt: &Statement,
    span: Span,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(_, rvalue) => check_rvalue(env, func, block, locals, rvalue, span, d),
        Statement::Call(target, args) => {
            check_operand(env, func, block, locals, target, span, d);
            for a in args {
                check_operand(env, func, block, locals, a, span, d);
            }
        }
        Statement::Drop(place) => {
            let Ok(ty) = env.infer_place_type(place, locals) else {
                return;
            };
            let c = class_of(&ty, env);
            if !c.drop {
                push_error!(d, span, func, block, "cannot drop non-Drop type {:?}", ty);
            }
        }
        Statement::Unborrow(_) => {
            // No class precondition — unborrow works on any reference
            // regardless of Drop marker. Its precondition (obligation
            // fulfilled) is checked by init_state.
        }
    }
}

fn check_rvalue(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    rv: &RValue,
    span: Span,
    d: &mut Diagnostics,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
            check_operand(env, func, block, locals, op, span, d)
        }
        RValue::Ref(_, _) => {}
    }
}

fn check_operand(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    op: &Operand,
    span: Span,
    d: &mut Diagnostics,
) {
    let (place, kind_name, needed) = match op {
        Operand::Copy(place) => (place, "copy", ClassMarker::Copy),
        Operand::Move(place) => (place, "move", ClassMarker::Move),
        Operand::Const(_) => return,
    };
    let Ok(ty) = env.infer_place_type(place, locals) else {
        return;
    };
    let c = class_of(&ty, env);
    let ok = match needed {
        ClassMarker::Copy => c.copy,
        ClassMarker::Move => c.mov,
    };
    if !ok {
        push_error!(
            d,
            span,
            func,
            block,
            "cannot {} non-{} type {:?}",
            kind_name,
            match needed {
                ClassMarker::Copy => "Copy",
                ClassMarker::Move => "Move",
            },
            ty
        );
    }
}

enum ClassMarker {
    Copy,
    Move,
}

fn check_terminator(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    d: &mut Diagnostics,
) {
    // `branch` uses an operand; `switchEnum` reads a place but does not
    // consume it, so no class check applies.
    if let Terminator::Branch { cond, .. } = &block.terminator {
        check_operand(env, func, block, locals, cond, block.terminator_span, d);
    }
}

// ---------- Leak-at-return ----------

/// For each `return` in each function, verify that every variable is
/// consumed (Moved or NeverInit) at that point. Any non-consumed path
/// is reported as a leak — this is the "strict" post-elaboration check.
pub fn check_return_leaks(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        if f.body.is_none() {
            continue;
        }
        let locals = f.locals_map();
        for (block, state) in init_state::states_before_returns(env, f) {
            check_leaks_in_state(env, f, block, &locals, &state, d);
        }
    }
}

fn check_leaks_in_state(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    state: &PointState,
    d: &mut Diagnostics,
) {
    for (var, s) in &state.locals {
        let Some(ty) = locals.get(var) else {
            continue;
        };
        // Reference-typed vars: their expiry rule is (cur, post) checked
        // separately below. Skip the linear-leak scan on the whole Var
        // if the Var itself is bound as a ref. (Ref-typed *fields* of a
        // struct are handled via the leak walk descending into fields;
        // Phase 2/4 will refine this to also inspect state.refs for
        // sub-paths.)
        if state.refs.contains_key(&Place::Var(var.clone())) {
            continue;
        }
        let mut path = vec![var.clone()];
        let mut leaks = Vec::new();
        find_leaks(env, s, ty, &mut path, &mut leaks);
        for (leaked_path, leaked_ty) in leaks {
            push_error!(
                d,
                block.terminator_span,
                func,
                block,
                "value '{}' of type {:?} is not consumed at return",
                leaked_path,
                leaked_ty
            );
        }
    }

    // Reference obligations: any ref-typed path whose is_init != ends_init
    // at return leaks — the loan wasn't discharged.
    for (place, rs) in &state.refs {
        if rs.obligation_fulfilled() {
            continue;
        }
        push_error!(
            d, block.terminator_span, func, block,
            "reference '{}' has unfulfilled obligation at return (is_init={}, ends_init={})",
            format_place(place), rs.is_init, rs.ends_init
        );
    }
}


/// Walk the init state in lockstep with its type, reporting every non-
/// consumed leaf. `Init` and `Diverged` at a leaf are leaks; `Partial`
/// recurses; `NeverInit`/`Moved` are consumed. No leniency for Drop —
/// elaboration is expected to have inserted the necessary drops.
fn find_leaks(
    env: &Env,
    state: &InitState,
    ty: &Type,
    path: &mut Vec<String>,
    out: &mut Vec<(String, Type)>,
) {
    match state {
        InitState::NeverInit | InitState::Moved => {}
        InitState::Init | InitState::Diverged => {
            out.push((path.join("."), ty.clone()));
        }
        InitState::Partial(fields) => {
            for (field_name, field_state) in fields {
                let Some(field_ty) = env.field_type(ty, field_name) else {
                    continue;
                };
                path.push(field_name.clone());
                find_leaks(env, field_state, &field_ty, path, out);
                path.pop();
            }
        }
    }
}