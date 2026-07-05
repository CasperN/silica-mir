//! Substructural class checker for MIR statements (phase 1).
//!
//! Verifies that statements respect the substructural class of the types
//! they operate on:
//!   - `copy p` (in operand position) requires `p`'s type to be `Copy`.
//!   - `drop p` requires `p`'s type to be `Drop`.
//!
//! **Deferred to phase 2** (once the drop-elaboration pass exists): flow-
//! sensitive checks that no linear or Drop-only value is silently forgotten
//! at overwrites, CFG joins, or `return`. Those checks close the loop
//! between elaboration and the trusted checker.
//!
//! This file will likely move to `substructural/check.rs` alongside a
//! renamed `substructural/composition.rs` once the phase-2 machinery lands.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::marker_composition::class_of;
use crate::push_error;
use crate::type_check::Env;
use std::collections::HashMap;

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    let mut locals: HashMap<String, Type> = HashMap::new();
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
    locals: &HashMap<String, Type>,
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
    locals: &HashMap<String, Type>,
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
    locals: &HashMap<String, Type>,
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
    locals: &HashMap<String, Type>,
    d: &mut Diagnostics,
) {
    // `branch` uses an operand; `switchEnum` reads a place but does not
    // consume it, so no class check applies.
    if let Terminator::Branch { cond, .. } = &block.terminator {
        check_operand(env, func, block, locals, cond, block.terminator_span, d);
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
        // demands Copy.
        assert_no_diagnostics(
            "
            struct Linear { r: &out number }
            fn f(x: Linear) {
              y: Linear;
              entry:
                y = move x;
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
}
