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

use crate::diagnostics::{DiagCode, Diagnostics};
use crate::mir::ast::*;
use crate::mir::diagnostic_format::format_type_diagnostic;
use crate::mir::env::IndexedProgram;
use crate::mir::helpers::*;
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
}

impl From<SubstructuralCheckCode> for DiagCode {
    fn from(code: SubstructuralCheckCode) -> DiagCode {
        DiagCode::SubstructuralCheck(code)
    }
}
use SubstructuralCheckCode::*;

/// Class-precondition checks over statements (does not include
/// `check_return_leaks`, which callers run separately after elaboration).
pub fn check_statements(program: &IndexedProgram, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(program, f, d);
    }
}

fn check_function(env: &IndexedProgram, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    let locals = func.locals_map();
    for block in &body.blocks {
        for stmt in &block.statements {
            check_stmt(env, func, block, &locals, stmt, stmt.source, d);
        }
        check_terminator(env, func, block, &locals, d);
    }
}

fn check_stmt(
    env: &IndexedProgram,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    stmt: &Statement,
    source: SourceInfo,
    d: &mut Diagnostics,
) {
    match &stmt.kind {
        StatementKind::Assign(_, rvalue) => {
            check_rvalue(env, func, block, locals, rvalue, source, d)
        }
        StatementKind::Call(target, args) => {
            check_operand(env, func, block, locals, target, source, d);
            for a in args {
                check_operand(env, func, block, locals, a, source, d);
            }
        }
        StatementKind::Drop(place) => {
            let Ok(ty) = env.type_of_place(place, locals) else {
                return;
            };
            let c = env.class_of(&ty, &func.meta.params);
            if !c.implies(Marker::Drop) {
                d.push_error(format_type_diagnostic(&func.meta, &ty, |ty| {
                    diag(
                        DropOfNonDrop,
                        source,
                        func,
                        block,
                        format!("cannot drop non-Drop type {}", ty),
                    )
                    .with_hint("only types implementing the Drop class can be explicitly dropped")
                }));
            }
        }
        StatementKind::Unborrow(_) => {
            // No class precondition — unborrow works on any reference
            // regardless of Drop marker. Its precondition (obligation
            // fulfilled) is checked by init_state.
        }
        StatementKind::RequireUninit(_) => {
            // Place-state owns this ghost assertion's validation.
        }
    }
}

fn check_rvalue(
    env: &IndexedProgram,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    rv: &RValue,
    source: SourceInfo,
    d: &mut Diagnostics,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
            check_operand(env, func, block, locals, op, source, d)
        }
        RValue::Ref(_, _) | RValue::RawRef(_) => {}
        RValue::ArrayLit(ops) => {
            for op in ops {
                check_operand(env, func, block, locals, op, source, d);
            }
        }
    }
}

fn check_operand(
    env: &IndexedProgram,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    op: &Operand,
    source: SourceInfo,
    d: &mut Diagnostics,
) {
    let (place, kind_name, needed) = match op {
        Operand::Copy(place) => (place, "copy", ClassMarker::Copy),
        Operand::Move(place) => (place, "move", ClassMarker::Move),
        // `take` will specialize to `move` or `copy`; require at least one
        // of the two markers so a valid resolution exists. Copy is not a
        // subset of Move in Silica (the blanket impl is `Copy + Drop →
        // Move`, not `Copy → Move`), so both must be checked.
        Operand::Take(place) => (place, "take", ClassMarker::CopyOrMove),
        Operand::Const(_) => return,
    };
    let Ok(ty) = env.type_of_place(place, locals) else {
        return;
    };
    let c = env.class_of(&ty, &func.meta.params);
    let ok = match needed {
        ClassMarker::Copy => c.implies(Marker::Copy),
        ClassMarker::Move => c.implies(Marker::Move),
        ClassMarker::CopyOrMove => c.implies(Marker::Copy) || c.implies(Marker::Move),
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
            ClassMarker::CopyOrMove => (
                MoveOfNonMove,
                "Copy or Move",
                "`take` specializes to `copy` or `move`, so the type must support at least one",
            ),
        };
        d.push_error(format_type_diagnostic(&func.meta, &ty, |ty| {
            diag(
                code,
                source,
                func,
                block,
                format!("cannot {} non-{} type {}", kind_name, marker_name, ty),
            )
            .with_hint(hint)
        }));
    }
}

enum ClassMarker {
    Copy,
    Move,
    CopyOrMove,
}

fn check_terminator(
    env: &IndexedProgram,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    d: &mut Diagnostics,
) {
    // `branch` uses an operand; `switchEnum` reads a place but does not
    // consume it, so no class check applies.
    if let TerminatorKind::Branch { cond, .. } = &block.terminator.kind {
        check_operand(env, func, block, locals, cond, block.terminator.source, d);
    }
}

#[cfg(test)]
mod tests {
    use crate::diagnostics::DiagCode;
    use crate::mir::place_state::analysis::PlaceStateCode;
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
            DiagCode::PlaceState(PlaceStateCode::RefObligationUnfulfilled),
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
