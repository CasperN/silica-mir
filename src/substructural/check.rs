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
use crate::substructural::composition::class_of;
use crate::push_error;
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
    let Some(body) = &func.body else { return; };
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
            let Ok(ty) = env.infer_place_type(place, locals) else { return; };
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

/// For each `return` in each function, verify that every variable is
/// consumed (Moved or NeverInit) at that point. Any non-consumed path
/// is reported as a leak — this is the "strict" post-elaboration check.
pub fn check_return_leaks(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        if f.body.is_none() { continue; }
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
        let Some(ty) = locals.get(var) else { continue; };
        // Reference-typed vars: their expiry rule is (cur, post) checked
        // separately below. Skip the linear-leak scan to avoid double
        // reporting.
        if state.refs.contains_key(var) { continue; }
        let mut path = vec![var.clone()];
        let mut leaks = Vec::new();
        find_leaks(env, s, ty, &mut path, &mut leaks);
        for (leaked_path, leaked_ty) in leaks {
            push_error!(
                d, block.terminator_span, func, block,
                "value '{}' of type {:?} is not consumed at return",
                leaked_path, leaked_ty
            );
        }
    }

    // Reference obligations: any ref var whose is_init != ends_init at
    // return leaks — the loan wasn't discharged.
    for (var, rs) in &state.refs {
        if rs.obligation_fulfilled() { continue; }
        let Some(ty) = locals.get(var) else { continue; };
        push_error!(
            d, block.terminator_span, func, block,
            "reference '{}' of type {:?} has unfulfilled obligation at return (is_init={}, ends_init={})",
            var, ty, rs.is_init, rs.ends_init
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
                let Some(field_ty) = env.field_type(ty, field_name) else { continue; };
                path.push(field_name.clone());
                find_leaks(env, field_state, &field_ty, path, out);
                path.pop();
            }
        }
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
    fn copy_of_affine_struct_error() {
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


    #[test]
    fn scalar_param_untouched_is_lenient_ok() {
        // number is Copy Drop; leaving it Init at return is permitted under
        // the elaborator will insert an explicit drop.
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
    fn scalar_param_moved_ok() {
        assert_no_diagnostics(
            "
            extern fn take(a: number);
            fn f(x: number) {
              entry:
                call take(move x);
                return
            }
            ",
        );
    }

    #[test]
    fn scalar_param_explicitly_dropped_ok() {
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

    // === Scenario: `r: &out number` — linear reference param =============

    #[test]
    fn linear_ref_param_untouched_leaks() {
        // Refs are reported via the obligation check, not the linear-leak
        // check, because their expiry rule is the (cur, post) obligation.
        assert_err(
            "
            fn f(r: &out number) {
              entry:
                return
            }
            ",
            "reference 'r' of type Ref(Out, Number) has unfulfilled obligation at return",
        );
    }

    #[test]
    fn linear_ref_param_moved_ok() {
        assert_no_diagnostics(
            "
            extern fn take(r: &out number);
            fn f(r: &out number) {
              entry:
                call take(move r);
                return
            }
            ",
        );
    }

    // === Scenario: `struct P { x: number y: number }` — linear struct ====
    // ==== with Drop fields =======================================
    // Marker composition permits this: the fields are Drop, but the struct
    // itself isn't marked, so it's linear as a value. Partial init with
    // Drop leaves collapses to per-leaf leak checks.

    #[test]
    fn linear_struct_untouched_param_leaks() {
        // Whole-var Init of a linear type: leak.
        assert_err(
            "
            struct P { x: number y: number }
            fn f(p: P) {
              entry:
                return
            }
            ",
            "value 'p' of type Custom(\"P\") is not consumed at return",
        );
    }

    #[test]
    fn linear_struct_moved_whole_ok() {
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            extern fn take(p: P);
            fn f(p: P) {
              entry:
                call take(move p);
                return
            }
            ",
        );
    }

    #[test]
    fn linear_struct_partial_init_one_field_elaborated() {
        // `p.x = 1` → Partial({x: Init, y: NeverInit}). Elaboration walks
        // the partial state and inserts `drop p.x`; every leaf is then
        // consumed and strict passes. This works even though P is linear
        // because the container's linearity is redundant given all its
        // fields are Drop.
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                return
            }
            ",
        );
    }

    #[test]
    fn linear_struct_partial_init_then_drop_ok() {
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                drop p.x;
                return
            }
            ",
        );
    }

    #[test]
    fn linear_struct_both_fields_dropped_ok() {
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                p.y = 2;
                drop p.x;
                drop p.y;
                return
            }
            ",
        );
    }

    #[test]
    fn linear_struct_fully_constructed_leaks() {
        // `p.x = 1; p.y = 2` → Partial({x: Init, y: Init}) canonicalizes
        // to Init. Whole-var Init of a linear type: leak (the linearity
        // now applies at the container granularity — you completed a value
        // and never consumed it).
        assert_err(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                p.y = 2;
                return
            }
            ",
            "value 'p' of type Custom(\"P\") is not consumed at return",
        );
    }

    // === Scenario: `struct L { r: &out number }` — fully-linear struct ===
    // The container and its field are both linear; there's no "Drop leaf"
    // escape.

    #[test]
    fn fully_linear_struct_untouched_param_leaks() {
        assert_err(
            "
            struct L { r: &out number }
            fn f(x: L) {
              entry:
                return
            }
            ",
            "value 'x' of type Custom(\"L\") is not consumed at return",
        );
    }

    #[test]
    fn fully_linear_struct_moved_ok() {
        assert_no_diagnostics(
            "
            struct L { r: &out number }
            extern fn take(x: L);
            fn f(x: L) {
              entry:
                call take(move x);
                return
            }
            ",
        );
    }

    #[test]
    fn fully_linear_struct_partial_init_field_leaks() {
        // `x.r = ...`  wouldn't compile (can't assign a linear place),
        // but a fully-linear field with Init state at return is a
        // per-leaf leak whenever it appears — verified here via a local
        // that's partially inited via a moved-in field.
        assert_err(
            "
            struct L { r: &out number }
            struct Pair { a: L b: L }
            fn f(src: Pair) {
              p: Pair;
              entry:
                p.a = move src.a;
                return
            }
            ",
            "not consumed at return",
        );
    }

    #[test]
    fn multiple_returns_each_checked() {
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
        let leak_errs: Vec<_> = errs
            .iter()
            .filter(|e| e.contains("is not consumed at return"))
            .collect();
        assert_eq!(leak_errs.len(), 2, "expected 2 leak errors, got {:?}", errs);
    }

    #[test]
    fn direct_leak_check_flags_pre_elaboration_drop_leak() {
        // Invoking check_return_leaks on a NON-elaborated program: any Init
        // at return is a leak because nothing has inserted drops yet.
        use crate::diagnostics::Diagnostics;
        use crate::parser::Parser;
        use crate::type_check;
        use super::check_return_leaks;

        let src = "fn f(x: number) { entry: return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program, &mut d);
        check_return_leaks(&env, &mut d);
        assert!(
            d.errors.iter().any(|e| e.contains("value 'x'") && e.contains("not consumed")),
            "expected leak error, got {:?}",
            d.errors
        );
    }

    #[test]
    fn direct_leak_check_ok_when_explicitly_dropped() {
        use crate::diagnostics::Diagnostics;
        use crate::parser::Parser;
        use crate::type_check;
        use super::check_return_leaks;

        let src = "fn f(x: number) { entry: drop x; return }";
        let program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program, &mut d);
        check_return_leaks(&env, &mut d);
        let leak_errs: Vec<_> = d.errors
            .iter()
            .filter(|e| e.contains("not consumed at return"))
            .collect();
        assert!(leak_errs.is_empty(), "expected no leaks, got {:?}", d.errors);
    }
}
