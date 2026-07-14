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
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::init_state::{self, InitState, InitStateCode, PointState};
use crate::substructural::composition::class_of;
use crate::type_check::Env;
use indexmap::IndexMap;

/// Machine-readable codes emitted by the substructural per-statement
/// checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubstructuralCheckCode {
    /// `drop p` where `p`'s type doesn't have the `Drop` marker.
    DropOfNonDrop,
    /// `copy p` operand where `p`'s type doesn't have the `Copy`
    /// marker.
    CopyOfNonCopy,
    /// `move p` operand where `p`'s type doesn't have the `Move`
    /// marker.
    MoveOfNonMove,
    /// At `return`, some non-ref path is still `Init` (or `Diverged`)
    /// — the value would leak. After elaboration, this means the
    /// drop-elaborator couldn't insert enough drops.
    ReturnValueLeak,
}

impl From<SubstructuralCheckCode> for DiagCode {
    fn from(code: SubstructuralCheckCode) -> DiagCode {
        DiagCode::SubstructuralCheck(code)
    }
}
use SubstructuralCheckCode::*;

fn diag(
    code: impl Into<DiagCode>,
    span: Span,
    func: &Function,
    block: &BasicBlock,
    msg: String,
) -> Diagnostic {
    Diagnostic::new(code, span, msg)
        .in_function(&func.name)
        .in_block(&block.label)
}

/// Class-precondition checks over statements (does not include
/// `check_return_leaks`, which callers run separately after elaboration).
pub fn check_statements(env: &Env, d: &mut Diagnostics) {
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
            let Ok(ty) = env.infer_place_type(place, span, locals) else {
                return;
            };
            let c = class_of(&ty, env);
            if !c.drop {
                d.push_error(
                    diag(
                        DropOfNonDrop,
                        span,
                        func,
                        block,
                        format!("cannot drop non-Drop type {}", ty),
                    )
                    .with_hint("only types implementing the Drop class can be explicitly dropped")
                );
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
        RValue::Ref(_, _) | RValue::RawRef(_) => {}
        RValue::ArrayLit(ops) => {
            for op in ops {
                check_operand(env, func, block, locals, op, span, d);
            }
        }
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
    let Ok(ty) = env.infer_place_type(place, span, locals) else {
        return;
    };
    let c = class_of(&ty, env);
    let ok = match needed {
        ClassMarker::Copy => c.copy,
        ClassMarker::Move => c.mov,
    };
    if !ok {
        let (code, marker_name, hint) = match needed {
            ClassMarker::Copy => (CopyOfNonCopy, "Copy", "since the type is not Copy, try moving it instead using 'move'"),
            ClassMarker::Move => (MoveOfNonMove, "Move", "linear types cannot be moved out of non-Move contexts"),
        };
        d.push_error(
            diag(
                code,
                span,
                func,
                block,
                format!("cannot {} non-{} type {}", kind_name, marker_name, ty),
            )
            .with_hint(hint)
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
            d.push_error(
                diag(
                    ReturnValueLeak,
                    block.terminator_span,
                    func,
                    block,
                    format!(
                        "value '{}' of type {} is not consumed at return",
                        leaked_path, leaked_ty
                    ),
                )
                .with_hint("linear values must be consumed or returned before function exit. Try moving or dropping it.")
            );
        }
    }

    // Reference obligations: any ref-typed path whose is_init != ends_init
    // at return leaks — the loan wasn't discharged. Shares the code with
    // the silent-forget sites in init_state (drop, overwrite, unborrow):
    // same obligation failure, just witnessed at a different point.
    for (place, rs) in &state.refs {
        if rs.obligation_fulfilled() {
            continue;
        }
        d.push_error(diag(
            InitStateCode::RefObligationUnfulfilled,
            block.terminator_span,
            func,
            block,
            format!(
                "reference '{}' has unfulfilled obligation at return (is_init={}, ends_init={})",
                format_place(place),
                rs.is_init,
                rs.ends_init
            ),
        ));
    }
}


#[cfg(test)]
mod tests {
    use crate::diagnostics::DiagCode;
    use crate::init_state::InitStateCode;
    use crate::test_util::*;

    /// Pins the interaction between NLL elaboration and the return-time
    /// obligation checks: for a struct-field ref with an unfulfilled
    /// obligation, exactly one error fires and it comes from init_state,
    /// not from `check_return_leaks`.
    ///
    /// The construction (`s.r = &drop x` with no later use) leaves
    /// `state.refs[s.r]` at `(is_init=true, ends_init=false)`. NLL then
    /// inserts `unborrow s.r` before `return`, and post-elab init_state
    /// fires `RefObligationUnfulfilled` at that inserted statement via
    /// `close_ref_if_present`. The unborrow also consumes s.r, so by
    /// the time `check_return_leaks` runs `s` is `Moved` (no value-
    /// leak report) and `state.refs` is empty (no obligation-loop
    /// report). If NLL ever stops inserting the unborrow, or
    /// `check_return_leaks` starts firing an independent report on the
    /// same failure, this test breaks and the interaction should be
    /// re-examined.
    #[test]
    fn return_leak_ref_field_reports_once_via_nll_unborrow() {
        let src = "
            struct S { r: &drop i64 }
            fn f(x: i64) {
              s: S;
              entry:
                s.r = &drop x;
                return
            }";
        let d = run_structured(src);

        let s_r_errs: Vec<_> = d
            .errors()
            .filter(|e| e.message().contains("'s.r'"))
            .collect();

        assert_eq!(
            s_r_errs.len(),
            1,
            "expected exactly one error mentioning 's.r', got {}:\n{}",
            s_r_errs.len(),
            format_errs(&d),
        );
        assert_eq!(
            s_r_errs[0].code(),
            DiagCode::InitState(InitStateCode::RefObligationUnfulfilled),
            "expected the obligation code (fired from init_state's \
             close_ref_if_present at the NLL-inserted unborrow), got {:?}",
            s_r_errs[0].code(),
        );
        // Not "at return" — the unborrow is a separate inserted stmt,
        // and init_state's message for close_ref_if_present says "here".
        assert!(
            s_r_errs[0].message().contains("unfulfilled obligation here"),
            "expected init_state's 'here' message, got: {}",
            s_r_errs[0].message(),
        );
    }

    fn format_errs(d: &crate::diagnostics::Diagnostics) -> String {
        d.errors()
            .map(|e| format!("  [{:?}] at {}: {}", e.code(), e.span(), e.message()))
            .collect::<Vec<_>>()
            .join("\n")
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