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
//! The design is: `elaborate_and_check_mir` runs the class checks
//! *before* elaboration and the leak check *after* elaboration. Errors
//! on elaborated output indicate the elaborator was unable to insert
//! enough drops (currently: Partial or Diverged states).
//!
//! Deferred: overwrite checks (`p = ...` where `p` was Init) and CFG-join
//! disagreement checks.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::init_state::{self, InitState, InitStateCode, PointState};
use crate::mir::substructural::composition::class_of;
use crate::mir::type_check::Env;
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
        .in_function(&func.meta.name)
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
        for stmt in &block.statements {
            check_stmt(env, func, block, &locals, stmt, stmt.span, d);
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
    match &stmt.kind {
        StatementKind::Assign(_, rvalue) => check_rvalue(env, func, block, locals, rvalue, span, d),
        StatementKind::Call(target, args) => {
            check_operand(env, func, block, locals, target, span, d);
            for a in args {
                check_operand(env, func, block, locals, a, span, d);
            }
        }
        StatementKind::Drop(place) => {
            let Ok(ty) = env.type_of_place(place, span, locals) else {
                return;
            };
            let scope = func.meta.param_scope();
            let c = class_of(&ty, env, &scope);
            if !c.implies(Marker::Drop) {
                d.push_error(
                    diag(
                        DropOfNonDrop,
                        span,
                        func,
                        block,
                        format!("cannot drop non-Drop type {}", ty),
                    )
                    .with_hint("only types implementing the Drop class can be explicitly dropped"),
                );
            }
        }
        StatementKind::Unborrow(_) => {
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
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
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
    let Ok(ty) = env.type_of_place(place, span, locals) else {
        return;
    };
    let scope = func.meta.param_scope();
    let c = class_of(&ty, env, &scope);
    let ok = match needed {
        ClassMarker::Copy => c.implies(Marker::Copy),
        ClassMarker::Move => c.implies(Marker::Move),
    };
    if !ok {
        let (code, marker_name, hint) = match needed {
            ClassMarker::Copy => (
                CopyOfNonCopy,
                "Copy",
                "since the type is not Copy, try moving it instead using 'move'",
            ),
            ClassMarker::Move => (
                MoveOfNonMove,
                "Move",
                "linear types cannot be moved out of non-Move contexts",
            ),
        };
        d.push_error(
            diag(
                code,
                span,
                func,
                block,
                format!("cannot {} non-{} type {}", kind_name, marker_name, ty),
            )
            .with_hint(hint),
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
    if let TerminatorKind::Branch { cond, .. } = &block.terminator.kind {
        check_operand(env, func, block, locals, cond, block.terminator.span, d);
    }
}

#[cfg(test)]
mod tests {
    use crate::diagnostics::DiagCode;
    use crate::mir::init_state::InitStateCode;
    use crate::mir::test_util::*;

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
        // Not "at return" — the unborrow is a separate inserted stmt.
        // init_state's message for close_ref_if_present phrases the
        // failure as "has unfulfilled obligation: pointee is …".
        assert!(
            s_r_errs[0]
                .message()
                .contains("has unfulfilled obligation: pointee is"),
            "expected init_state's obligation message, got: {}",
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

