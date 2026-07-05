//! Initialization-state dataflow for local variables (phase 1).
//!
//! Detects: use of uninitialized locals, use of moved-out locals, and use
//! where the init state is inconsistent across control-flow paths.
//!
//! Deferred to follow-ups:
//!   * field-granular tracking (`Partial(fields)`),
//!   * substructural-class-driven weakening at joins and leak check at
//!     `return`,
//!   * borrow init preconditions (`&out` requires uninit, etc.) and
//!     freeze/thaw state.
//!
//! Only `Place::Var(_)` locals are tracked. Non-Var LHS assignments do
//! not change any Var's state; moves through a subpath do not partially
//! uninit the root Var. Reads walk down to the root Var; if the chain
//! passes through a `Deref` the read is not checked (we don't follow
//! references at this level).

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::tc::Env;
use std::collections::{HashMap, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InitState {
    Uninit,
    Init,
    /// Predecessors disagree: reads become "may be uninitialized" errors.
    Diverged,
}

fn join_state(a: InitState, b: InitState) -> InitState {
    if a == b { a } else { InitState::Diverged }
}

type PointState = HashMap<String, InitState>;

fn join(a: &PointState, b: &PointState) -> PointState {
    a.iter()
        .map(|(name, sa)| {
            let sb = b.get(name).copied().unwrap_or(InitState::Uninit);
            (name.clone(), join_state(*sa, sb))
        })
        .collect()
}

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(f, d);
    }
}

fn check_function(func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    if body.blocks.is_empty() { return; }

    let entry_states = compute_entry_states(func, body);

    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else { continue; };
        let mut state = entry.clone();
        check_block(func, block, &mut state, d);
    }
}

fn initial_state(func: &Function, body: &FunctionBody) -> PointState {
    let mut s = PointState::new();
    for p in &func.params {
        s.insert(p.name.clone(), InitState::Init);
    }
    for l in &body.locals {
        s.insert(l.name.clone(), InitState::Uninit);
    }
    s
}

fn compute_entry_states(func: &Function, body: &FunctionBody) -> HashMap<String, PointState> {
    let mut states: HashMap<String, PointState> = HashMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), initial_state(func, body));
    worklist.push_back(entry_label);

    let blocks_by_label: HashMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();

    while let Some(label) = worklist.pop_front() {
        let block = blocks_by_label[label.as_str()];
        let mut state = states[&label].clone();
        for (stmt, _) in &block.statements {
            transfer_stmt(stmt, &mut state);
        }
        transfer_terminator(&block.terminator, &mut state);

        for succ in successors(&block.terminator) {
            if !blocks_by_label.contains_key(succ) { continue; }
            let new_state = match states.get(succ) {
                None => state.clone(),
                Some(existing) => join(existing, &state),
            };
            if states.get(succ).map_or(true, |e| e != &new_state) {
                states.insert(succ.to_string(), new_state);
                worklist.push_back(succ.to_string());
            }
        }
    }

    states
}

fn successors(term: &Terminator) -> Vec<&str> {
    match term {
        Terminator::Goto(label) => vec![label.as_str()],
        Terminator::Return | Terminator::Abort | Terminator::Unreachable => vec![],
        Terminator::Branch { true_label, false_label, .. } => {
            vec![true_label.as_str(), false_label.as_str()]
        }
        Terminator::SwitchEnum { cases, .. } => {
            cases.iter().map(|(_, label)| label.as_str()).collect()
        }
    }
}

fn root_var(place: &Place) -> Option<&str> {
    match place {
        Place::Var(name) => Some(name.as_str()),
        Place::Field(inner, _) => root_var(inner),
        Place::Downcast(inner, _) => root_var(inner),
        // `*p` steps through a reference — we don't track pointees here.
        Place::Deref(_) => None,
    }
}

// ---------- Transfer (state updates, no diagnostics) ----------

fn transfer_stmt(stmt: &Statement, state: &mut PointState) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            apply_rvalue_moves(rvalue, state);
            if let Place::Var(name) = target {
                state.insert(name.clone(), InitState::Init);
            }
        }
        Statement::Call(target, args) => {
            apply_operand_move(target, state);
            for a in args {
                apply_operand_move(a, state);
            }
        }
    }
}

fn transfer_terminator(term: &Terminator, state: &mut PointState) {
    if let Terminator::Branch { cond, .. } = term {
        apply_operand_move(cond, state);
    }
}

fn apply_rvalue_moves(rv: &RValue, state: &mut PointState) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => apply_operand_move(op, state),
        // Borrows don't move the base; init preconditions are deferred.
        RValue::Ref(_, _) => {}
    }
}

fn apply_operand_move(op: &Operand, state: &mut PointState) {
    if let Operand::Move(place) = op {
        if let Some(root) = root_var(place) {
            state.insert(root.to_string(), InitState::Uninit);
        }
    }
}

// ---------- Diagnostic pass (checks reads against state) ----------

fn check_block(func: &Function, block: &BasicBlock, state: &mut PointState, d: &mut Diagnostics) {
    for (stmt, span) in &block.statements {
        check_stmt(func, block, stmt, *span, state, d);
        transfer_stmt(stmt, state);
    }
    check_terminator(func, block, state, d);
    transfer_terminator(&block.terminator, state);
}

fn check_stmt(
    func: &Function,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(_, rvalue) => check_rvalue_reads(func, block, rvalue, span, state, d),
        Statement::Call(target, args) => {
            check_operand_read(func, block, target, span, state, d);
            for a in args {
                check_operand_read(func, block, a, span, state, d);
            }
        }
    }
}

fn check_rvalue_reads(
    func: &Function,
    block: &BasicBlock,
    rv: &RValue,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
            check_operand_read(func, block, op, span, state, d)
        }
        RValue::Ref(_, _) => {} // borrow init checks deferred
    }
}

fn check_operand_read(
    func: &Function,
    block: &BasicBlock,
    op: &Operand,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let place = match op {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Const(_) => return,
    };
    check_place_read(func, block, place, span, state, d);
}

fn check_place_read(
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some(root) = root_var(place) else { return; };
    // Undeclared root — tc has already complained; stay quiet.
    let Some(&s) = state.get(root) else { return; };
    match s {
        InitState::Init => {}
        InitState::Uninit => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' is used before initialization",
            span, func.name, block.label, root
        )),
        InitState::Diverged => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' may be used before initialization (init state inconsistent across paths)",
            span, func.name, block.label, root
        )),
    }
}

fn check_terminator(
    func: &Function,
    block: &BasicBlock,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let ts = block.terminator_span;
    match &block.terminator {
        Terminator::Branch { cond, .. } => check_operand_read(func, block, cond, ts, state, d),
        Terminator::SwitchEnum { place, .. } => check_place_read(func, block, place, ts, state, d),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Baseline ----------

    #[test]
    fn param_starts_init_ok() {
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
    fn write_then_read_ok() {
        assert_no_diagnostics(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                x = copy x;
                return
            }
            ",
        );
    }

    // ---------- Use-before-init ----------

    #[test]
    fn read_of_uninit_local_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              y: number;
              entry:
                y = copy x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'x' is used before initialization"],
        );
    }

    #[test]
    fn move_of_uninit_local_error() {
        let (errs, _) = run(
            "
            fn f() {
              x: number;
              y: number;
              entry:
                y = move x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'x' is used before initialization"],
        );
    }

    #[test]
    fn read_after_move_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                z = copy x;
                return
            }
            ",
        );
        assert_one_error_contains_all(
            &errs,
            &["variable 'x' is used before initialization"],
        );
    }

    #[test]
    fn copy_leaves_source_init_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = copy x;
                z = copy x;
                return
            }
            ",
        );
    }

    // ---------- Joins ----------

    #[test]
    fn join_agree_init_ok() {
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                x = 2;
                goto merge
              merge:
                y = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn join_disagreement_produces_diverged_error() {
        // On the false branch x is never initialized; the merge sees x as
        // Diverged, and the subsequent copy fails.
        let (errs, _) = run(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                goto merge
              merge:
                y = copy x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'x' may be used before initialization"],
        );
    }

    #[test]
    fn aborting_predecessor_doesnt_pollute_join() {
        // The false branch aborts (no successor edge to `merge`), so `x` at
        // `merge` is whatever the true branch says: Init.
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                abort
              merge:
                y = copy x;
                return
            }
            ",
        );
    }

    // ---------- Terminator reads ----------

    #[test]
    fn branch_reads_cond() {
        let (errs, _) = run(
            "
            fn f() {
              b: boolean;
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'b' is used before initialization"],
        );
    }

    #[test]
    fn switch_enum_reads_place() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                switchEnum(o) [None: end, Some: end]
              end:
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'o' is used before initialization"],
        );
    }

    // ---------- Places rooted through projections ----------

    #[test]
    fn field_read_checks_root_var() {
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              a: number;
              entry:
                a = copy p.x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'p' is used before initialization"],
        );
    }

    #[test]
    fn downcast_read_checks_root_var() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f() {
              o: Option;
              a: number;
              entry:
                a = copy o as Some;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'o' is used before initialization"],
        );
    }

    #[test]
    fn deref_read_is_not_checked() {
        // *r walks through a reference; phase 1 doesn't follow pointees, so
        // the local `r` being tracked isn't consulted here (and even if it
        // were, `r` is a parameter → Init).
        assert_no_diagnostics(
            "
            fn f(r: &number) {
              a: number;
              entry:
                a = copy *r;
                return
            }
            ",
        );
    }

    // ---------- Non-Var LHS ----------

    #[test]
    fn assignment_to_field_does_not_init_var() {
        // Writing `p.x = 1` does NOT mark `p` as Init — subsequent
        // read of `p` still fails. Documents the phase-1 limitation.
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              a: number;
              entry:
                p.x = 1;
                p.y = 2;
                a = copy p.x;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'p' is used before initialization"],
        );
    }

    // ---------- Calls ----------

    #[test]
    fn call_arg_read_of_uninit_error() {
        let (errs, _) = run(
            "
            extern fn takes_num(a: number);
            fn f() {
              x: number;
              entry:
                call takes_num(copy x);
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'x' is used before initialization"],
        );
    }

    #[test]
    fn call_target_check_of_uninit_error() {
        let (errs, _) = run(
            "
            fn f() {
              g: fn(number);
              entry:
                call copy g(1);
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'g' is used before initialization"],
        );
    }

    // ---------- Loops ----------

    #[test]
    fn loop_backedge_agrees_ok() {
        // At `head`, x reaches from `entry` (Init) and from `body` (Init after
        // the reassignment). Join is Init.
        assert_no_diagnostics(
            "
            fn f(b: boolean) {
              x: number;
              entry:
                x = 0;
                goto head
              head:
                branch(copy b) [true: body, false: done]
              body:
                x = 1;
                goto head
              done:
                return
            }
            ",
        );
    }

    #[test]
    fn loop_may_reach_uninit_error() {
        // In `body`, x may be uninit (from `entry` when b is false-then-true)
        // and init (from a prior loop iteration). Diverged at `body`.
        let (errs, _) = run(
            "
            fn f(b: boolean) {
              x: number;
              y: number;
              entry:
                branch(copy b) [true: body, false: done]
              body:
                y = copy x;
                x = 1;
                branch(copy b) [true: body, false: done]
              done:
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["variable 'x' may be used before initialization"],
        );
    }
}
