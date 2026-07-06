//! Substructural checker for MIR statements.
//!
//! Verifies (a) that statements respect the substructural class of the types
//! they operate on and (b) that no *linear* value is silently forgotten at
//! `return`. Drop-classed leaks are permitted by default because the
//! drop-elaboration pass will make them explicit; that leniency is opt-out
//! via [`LeakMode::Strict`], which post-elaboration validation should use.
//!
//! - `copy p` (operand position) requires `p`'s type to be `Copy`.
//! - `drop p` requires `p`'s type to be `Drop`.
//! - At `return`, any Init/Diverged/Partial path whose leaf type is not
//!   `Drop`-classed is a leak.
//!
//! Deferred: overwrite checks (`p = ...` where `p` was Init) and CFG-join
//! disagreement checks. Both share the same "when is a state leaked?"
//! predicate implemented here.
//!
//! This file will likely move to `substructural/check.rs` alongside a
//! renamed `substructural/composition.rs` once elaboration machinery lands.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::init_state::{self, InitState, PointState};
use crate::marker_composition::class_of;
use crate::push_error;
use crate::type_check::Env;
use indexmap::IndexMap;

/// Whether the leak check permits Drop-classed leaks.
///
/// * `Lenient` — the default for `run_all_passes`. Emits errors only for
///   leaks whose leaf type is not `Drop`-classed. Drop-classed leaks are
///   accepted because the drop-elaboration pass would make them explicit.
/// * `Strict` — treats every Init/Diverged/Partial path at return as a
///   leak. Use to validate post-elaboration MIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LeakMode {
    Lenient,
    Strict,
}

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
    // TODO(elaboration): after drop-elaboration runs, invoke
    // `check_return_leaks(env, d, LeakMode::Strict)` here (or in a
    // dedicated validation pass) to prove no implicit forgets remain.
    check_return_leaks(env, d, LeakMode::Lenient);
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    let mut locals: IndexMap<String, Type> = IndexMap::new();
    for p in &func.params {
        locals.insert(p.name.clone(), p.ty.clone());
    }
    for l in &body.locals {
        locals.insert(l.name.clone(), l.ty.clone());
    }

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
            let Ok(ty) = env.infer_place_type(place, locals) else { return; };
            let c = class_of(&ty, env);
            if !c.drop {
                push_error!(d, span, func, block, "cannot drop non-Drop type {:?}", ty);
            }
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
    if let Operand::Copy(place) = op {
        let Ok(ty) = env.infer_place_type(place, locals) else { return; };
        let c = class_of(&ty, env);
        if !c.copy {
            push_error!(d, span, func, block, "cannot copy non-Copy type {:?}", ty);
        }
    }
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

/// For each `return` in each function, check every variable's init state
/// against `mode`. Emits errors for leaked paths.
pub fn check_return_leaks(env: &Env, d: &mut Diagnostics, mode: LeakMode) {
    for f in env.functions.values() {
        let Some(body) = &f.body else { continue; };
        let locals = build_locals(f, body);
        for (block, state) in init_state::states_before_returns(env, f) {
            check_leaks_in_state(env, f, block, &locals, &state, mode, d);
        }
    }
}

fn build_locals(func: &Function, body: &FunctionBody) -> IndexMap<String, Type> {
    let mut locals = IndexMap::new();
    for p in &func.params {
        locals.insert(p.name.clone(), p.ty.clone());
    }
    for l in &body.locals {
        locals.insert(l.name.clone(), l.ty.clone());
    }
    locals
}

fn check_leaks_in_state(
    env: &Env,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    state: &PointState,
    mode: LeakMode,
    d: &mut Diagnostics,
) {
    for (var, s) in state {
        let Some(ty) = locals.get(var) else { continue; };
        if is_leak(env, s, ty, mode) {
            push_error!(
                d, block.terminator_span, func, block,
                "value '{}' of type {:?} is not consumed at return (linear leak)",
                var, ty
            );
        }
    }
}

/// A variable at return leaks iff its state is non-consumed AND, under
/// lenient mode, its declared type is not `Drop`-classed. Marker
/// composition guarantees that if the root type is Drop, all sub-fields
/// are Drop too — so a partial/nested check is unnecessary. We report at
/// the root granularity in either mode.
fn is_leak(env: &Env, state: &InitState, ty: &Type, mode: LeakMode) -> bool {
    let non_consumed = !matches!(state, InitState::NeverInit | InitState::Moved);
    if !non_consumed { return false; }
    match mode {
        LeakMode::Lenient => !class_of(ty, env).drop,
        LeakMode::Strict => true,
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Copy: positives ----------

    #[test]
    fn copy_of_number_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              y: number;
              entry:
                y = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn copy_of_shared_ref_ok() {
        // `&T` is Copy Drop.
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              s: &number;
              entry:
                s = copy r;
                return
            }
            ",
        );
    }

    #[test]
    fn copy_of_copy_struct_ok() {
        assert_no_diagnostics(
            "
            struct Copy Drop P { x: number y: number }
            fn f(p: P) {
              q: P;
              entry:
                q = copy p;
                return
            }
            ",
        );
    }

    // ---------- Copy: negatives ----------

    #[test]
    fn copy_of_linear_struct_error() {
        // struct without markers = linear
        assert_err(
            "
            struct Linear { r: &out number }
            fn f(x: Linear) {
              y: Linear;
              entry:
                y = copy x;
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    #[test]
    fn copy_of_drop_only_struct_error() {
        // Marked `Drop` but not `Copy` — affine, not copyable.
        assert_err(
            "
            struct Drop D { x: number }
            fn f(a: D) {
              b: D;
              entry:
                b = copy a;
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    #[test]
    fn copy_of_mut_ref_error() {
        assert_err(
            "
            fn f(r: &mut number) {
              s: &mut number;
              entry:
                s = copy r;
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    #[test]
    fn copy_of_out_ref_error() {
        assert_err(
            "
            fn f(r: &out number) {
              s: &out number;
              entry:
                s = copy r;
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    #[test]
    fn copy_of_uninit_ref_error() {
        assert_err(
            "
            fn f(r: &uninit number) {
              s: &uninit number;
              entry:
                s = copy r;
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    // ---------- Copy in other operand positions ----------

    #[test]
    fn copy_in_call_arg_of_non_copy_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            extern fn take(x: Linear);
            fn f(x: Linear) {
              entry:
                call take(copy x);
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    #[test]
    fn copy_in_enum_payload_of_non_copy_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            enum Wrap { W: Linear }
            fn f(x: Linear) {
              w: Wrap;
              entry:
                w = Wrap::W(copy x);
                return
            }
            ",
            "cannot copy non-Copy type",
        );
    }

    // ---------- Move: always allowed ----------

    #[test]
    fn move_of_linear_ok() {
        // Substructural check permits moves of any class; only `copy`
        // demands Copy. Consume the moved-to `y` via a sink call so we
        // don't trip the leak-at-return check.
        assert_no_diagnostics(
            "
            struct Linear { r: &out number }
            extern fn sink(y: Linear);
            fn f(x: Linear) {
              y: Linear;
              entry:
                y = move x;
                call sink(move y);
                return
            }
            ",
        );
    }

    // ---------- Drop: positives ----------

    #[test]
    fn drop_of_number_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              entry:
                drop x;
                return
            }
            ",
        );
    }

    #[test]
    fn drop_of_shared_ref_ok() {
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              entry:
                drop r;
                return
            }
            ",
        );
    }

    #[test]
    fn drop_of_mut_ref_ok() {
        // `&mut T` is Drop (though not Copy) — the reference value may be
        // forgotten (the loan expires at the drop point).
        assert_no_diagnostics(
            "
            fn f(r: &mut number) {
              entry:
                drop r;
                return
            }
            ",
        );
    }

    #[test]
    fn drop_of_drop_struct_ok() {
        assert_no_diagnostics(
            "
            struct Drop D { x: number }
            fn f(d: D) {
              entry:
                drop d;
                return
            }
            ",
        );
    }

    // ---------- Drop: negatives ----------

    #[test]
    fn drop_of_linear_struct_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            fn f(x: Linear) {
              entry:
                drop x;
                return
            }
            ",
            "cannot drop non-Drop type",
        );
    }

    #[test]
    fn drop_of_out_ref_error() {
        assert_err(
            "
            fn f(r: &out number) {
              entry:
                drop r;
                return
            }
            ",
            "cannot drop non-Drop type",
        );
    }

    #[test]
    fn drop_of_drop_ref_error() {
        // `&drop T` is linear (obligation to deinit before expiry).
        assert_err(
            "
            fn f(r: &drop number) {
              entry:
                drop r;
                return
            }
            ",
            "cannot drop non-Drop type",
        );
    }

    // ---------- Leak at return (lenient by default) ----------

    #[test]
    fn linear_param_leak_at_return_error() {
        // A linear param left Init at return is a leak.
        assert_err(
            "
            struct Linear { r: &out number }
            fn f(x: Linear) {
              entry:
                return
            }
            ",
            "value 'x' of type Custom(\"Linear\") is not consumed at return",
        );
    }

    #[test]
    fn drop_classed_param_left_init_is_ok_lenient() {
        // number is Copy Drop; leaving it Init at return is permitted
        // under LeakMode::Lenient — the elaborator will drop it explicitly.
        assert_no_diagnostics(
            "
            fn f(x: number) {
              entry:
                return
            }
            ",
        );
    }

    #[test]
    fn linear_param_consumed_by_move_ok() {
        assert_no_diagnostics(
            "
            struct Linear { r: &out number }
            extern fn sink(x: Linear);
            fn f(x: Linear) {
              entry:
                call sink(move x);
                return
            }
            ",
        );
    }

    #[test]
    fn linear_local_leak_at_return_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            fn f(x: Linear) {
              y: Linear;
              entry:
                y = move x;
                return
            }
            ",
            "value 'y' of type Custom(\"Linear\") is not consumed at return",
        );
    }

    #[test]
    fn partial_init_of_linear_struct_leaks_root() {
        // A linear struct with any non-consumed sub-state leaks at the
        // root. Marker composition guarantees a Drop-classed root has
        // only Drop-classed fields, so we don't need per-field reporting
        // to be sound — the root granularity is correct.
        assert_err(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                return
            }
            ",
            "value 'p' of type Custom(\"P\")",
        );
    }

    #[test]
    fn multiple_returns_each_checked() {
        // Both blocks return with `x` Init; both should leak.
        let (errs, _) = run(
            "
            struct Linear { r: &out number }
            fn f(b: boolean, x: Linear) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        );
        // Two leak errors, one per return.
        let leak_errs: Vec<_> = errs
            .iter()
            .filter(|e| e.contains("is not consumed at return"))
            .collect();
        assert_eq!(leak_errs.len(), 2, "expected 2 leak errors, got {:?}", errs);
    }

    // ---------- Strict mode (direct call) ----------

    #[test]
    fn strict_mode_flags_drop_classed_leak() {
        use crate::diagnostics::Diagnostics;
        use crate::parser::Parser;
        use crate::type_check;
        use super::{check_return_leaks, LeakMode};

        // number is Drop-classed, so lenient permits the leak. Strict
        // mode should still flag it.
        let src = "fn f(x: number) { entry: return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program, &mut d);
        check_return_leaks(&env, &mut d, LeakMode::Strict);
        assert!(
            d.errors.iter().any(|e| e.contains("value 'x'") && e.contains("not consumed")),
            "expected leak error, got {:?}",
            d.errors
        );
    }

    #[test]
    fn strict_mode_ok_when_explicitly_dropped() {
        use crate::diagnostics::Diagnostics;
        use crate::parser::Parser;
        use crate::type_check;
        use super::{check_return_leaks, LeakMode};

        // After explicit `drop x`, strict mode should see no leaks.
        let src = "fn f(x: number) { entry: drop x; return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program, &mut d);
        check_return_leaks(&env, &mut d, LeakMode::Strict);
        let leak_errs: Vec<_> = d.errors
            .iter()
            .filter(|e| e.contains("not consumed at return"))
            .collect();
        assert!(leak_errs.is_empty(), "expected no leaks, got {:?}", d.errors);
    }
}
