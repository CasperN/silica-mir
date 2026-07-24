//! Copy relaxation for MIR operands.
//!
//! The HLL may initially lower ordinary value uses as `move`. This pass
//! preserves an earlier use as `copy` when a later reachable use still needs
//! the same owned move path and that path's type implements `Copy`.
//!
//! It deliberately runs before NLL elaboration. Changing `move r` to
//! `copy r` changes whether moving `r` closes a loan, so NLL must compute
//! borrower liveness from the rewritten program rather than from a stale
//! move graph.
//!
//! The analysis is backward, with a may-demand set of owned paths. At a CFG
//! join the sets union: an operand must be preserved if either successor can
//! still use it. The first implementation only rewrites statically tracked
//! owned paths (locals, fields, downcasts, and constant indexes). Dynamic
//! indexes and dereferences still contribute conservative demand for their
//! owned base, but are not themselves rewrite candidates.

use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction};
use crate::mir::substructural::composition::class_of;
use crate::mir::type_check::Env;
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// Relax preserving moves in every function body. Idempotent: after a move
/// becomes a copy it is no longer a candidate on later runs.
pub fn elaborate(program: &mut Program, env: &Env) {
    for func in program.functions_mut() {
        elaborate_function(func, env);
    }
}

fn elaborate_function(func: &mut Function, env: &Env) {
    let locals = func.locals_map();
    let scope = func.meta.param_scope();
    let Some(body) = &mut func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let exits = dataflow::run(&MovePathDemand, body);
    for block in &mut body.blocks {
        let Some(exit_demand) = exits.get(&block.label) else {
            continue;
        };
        let mut demand = exit_demand.clone();
        relax_terminator(&mut block.terminator, &mut demand, env, &locals, &scope);
        for stmt in block.statements.iter_mut().rev() {
            relax_statement(stmt, &mut demand, env, &locals, &scope);
        }
    }
}

/// Backward may-demand for owned move paths. A member says that some
/// successor path needs this place initialized before a later overwrite.
struct MovePathDemand;

impl Analysis for MovePathDemand {
    type State = BTreeSet<Place>;

    fn direction(&self) -> Direction {
        Direction::Backward
    }

    fn initial_state(&self) -> Self::State {
        BTreeSet::new()
    }

    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        a.union(b).cloned().collect()
    }

    fn transfer_stmt(&self, demand: &mut Self::State, stmt: &Statement, _span: Span) {
        transfer_statement_demand(stmt, demand);
    }

    fn transfer_terminator(&self, demand: &mut Self::State, term: &Terminator) {
        transfer_terminator_demand(term, demand);
    }
}

fn transfer_statement_demand(stmt: &Statement, demand: &mut BTreeSet<Place>) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            kill_future_demand(demand, target);
            transfer_rvalue_demand(rvalue, demand);
            if as_owned_path(target).is_none() {
                add_place_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
            transfer_operand_demand(target, demand);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            add_place_demand(demand, place);
        }
        // This is a postcondition, not a value use. A preceding move should
        // remain a move when this is the only later statement mentioning it.
        StatementKind::RequireUninit(_) => {}
    }
}

fn transfer_terminator_demand(term: &Terminator, demand: &mut BTreeSet<Place>) {
    match &term.kind {
        TerminatorKind::Branch { cond, .. } => transfer_operand_demand(cond, demand),
        TerminatorKind::SwitchEnum { place, .. } => add_place_demand(demand, place),
        TerminatorKind::Goto(_) | TerminatorKind::Return | TerminatorKind::Abort | TerminatorKind::Unreachable => {}
    }
}

fn transfer_rvalue_demand(rvalue: &RValue, demand: &mut BTreeSet<Place>) {
    match rvalue {
        RValue::Use(operand) | RValue::EnumConstr(_, _, _, operand) | RValue::PtrCast(operand, _) => {
            transfer_operand_demand(operand, demand)
        }
        RValue::Ref(kind, place) => transfer_ref_demand(kind, place, demand),
        RValue::RawRef(_) => {}
        RValue::ArrayLit(operands) => {
            for operand in operands.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
        }
    }
}

fn transfer_operand_demand(operand: &Operand, demand: &mut BTreeSet<Place>) {
    if let Operand::Copy(place) | Operand::Move(place) = operand {
        add_place_demand(demand, place);
    }
}

/// An operation that establishes a new state for `place` makes any future
/// demand for that old state irrelevant on its input side.
fn kill_future_demand(demand: &mut BTreeSet<Place>, target: &Place) {
    let Some(owned) = as_owned_path(target) else {
        return;
    };
    demand.retain(|needed| !is_ancestor_or_self(&owned, needed));
}

/// Backward transfer for a borrow's pointee transition. This mirrors
/// init-state's eager loan transitions, restricted to statically-owned
/// paths: `&out` establishes Init, `&drop` establishes Uninit, and
/// `&uninit` requires/retains Uninit. Only ordinary and mutable borrows
/// merely read an existing value.
fn transfer_ref_demand(kind: &RefKind, place: &Place, demand: &mut BTreeSet<Place>) {
    match kind {
        RefKind::Shared | RefKind::Mut => add_place_demand(demand, place),
        RefKind::Drop => {
            kill_ref_transition_demand(demand, place);
            add_place_demand(demand, place);
        }
        RefKind::Out | RefKind::Uninit => kill_ref_transition_demand(demand, place),
    }
}

/// A reference state transition on a subplace also invalidates demand for a
/// containing aggregate. For example, after `&out p.field`, a future read of
/// `p` cannot justify preserving an earlier `move p`: the borrow itself
/// requires `p.field` to have been uninitialized. Ordinary assignment differs
/// here — overwriting a field of an already-preserved Copy aggregate is fine.
fn kill_ref_transition_demand(demand: &mut BTreeSet<Place>, place: &Place) {
    let Some(owned) = as_owned_path(place) else {
        return;
    };
    demand.retain(|needed| {
        !is_ancestor_or_self(&owned, needed) && !is_ancestor_or_self(needed, &owned)
    });
}

/// Add the nearest statically-owned base of `place` to the demand set.
/// A dynamic index therefore conservatively demands its array root; a
/// dereference demands the borrower that contains it.
fn add_place_demand(demand: &mut BTreeSet<Place>, place: &Place) {
    if let Some(owned) = nearest_owned_path(place) {
        demand.insert(owned);
    }
}

fn nearest_owned_path(place: &Place) -> Option<Place> {
    if let Some(owned) = as_owned_path(place) {
        return Some(owned);
    }
    match place {
        Place::Var(_) => None,
        Place::Field(inner, _)
        | Place::Downcast(inner, _)
        | Place::Deref(inner)
        | Place::Index(inner, _) => nearest_owned_path(inner),
    }
}

fn relax_statement(
    stmt: &mut Statement,
    demand: &mut BTreeSet<Place>,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match &mut stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            kill_future_demand(demand, target);
            relax_rvalue(rvalue, demand, env, locals, scope);
            if as_owned_path(target).is_none() {
                add_place_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter_mut().rev() {
                relax_operand(operand, demand, env, locals, scope);
            }
            relax_operand(target, demand, env, locals, scope);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            add_place_demand(demand, place);
        }
        StatementKind::RequireUninit(_) => {}
    }
}

fn relax_terminator(
    term: &mut Terminator,
    demand: &mut BTreeSet<Place>,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match &mut term.kind {
        TerminatorKind::Branch { cond, .. } => relax_operand(cond, demand, env, locals, scope),
        TerminatorKind::SwitchEnum { place, .. } => add_place_demand(demand, place),
        TerminatorKind::Goto(_) | TerminatorKind::Return | TerminatorKind::Abort | TerminatorKind::Unreachable => {}
    }
}

fn relax_rvalue(
    rvalue: &mut RValue,
    demand: &mut BTreeSet<Place>,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match rvalue {
        RValue::Use(operand) | RValue::EnumConstr(_, _, _, operand) | RValue::PtrCast(operand, _) => {
            relax_operand(operand, demand, env, locals, scope)
        }
        RValue::Ref(kind, place) => transfer_ref_demand(kind, place, demand),
        RValue::RawRef(_) => {}
        RValue::ArrayLit(operands) => {
            for operand in operands.iter_mut().rev() {
                relax_operand(operand, demand, env, locals, scope);
            }
        }
    }
}

fn relax_operand(
    operand: &mut Operand,
    demand: &mut BTreeSet<Place>,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    let Operand::Move(place) = operand else {
        if let Operand::Copy(place) = operand {
            add_place_demand(demand, place);
        }
        return;
    };

    let owned = as_owned_path(place);
    let needs_preserving = owned.as_ref().is_some_and(|moved| {
        demand
            .iter()
            .any(|needed| is_ancestor_or_self(moved, needed) || is_ancestor_or_self(needed, moved))
    });
    let is_copy = owned.as_ref().is_some_and(|moved| {
        env.type_of_place(moved, Span::default(), locals)
            .is_ok_and(|ty| class_of(&ty, env, scope).implies(Marker::Copy))
    });
    let place = place.clone();
    if needs_preserving && is_copy {
        *operand = Operand::Copy(place.clone());
    }
    add_place_demand(demand, &place);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::parser::Parser;

    fn elaborate_source(source: &str) -> Program {
        let mut program = Parser::new(source.to_owned()).parse().unwrap();
        let (env, errors) = Env::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");
        elaborate(&mut program, &env);
        program
    }

    fn call_arg<'a>(program: &'a Program, function: &str, statement: usize) -> &'a Operand {
        let func = program
            .functions()
            .find(|func| func.meta.name == function)
            .unwrap();
        let body = func.body.as_ref().unwrap();
        let StatementKind::Call(_, args) = &body.blocks[0].statements[statement].kind else {
            panic!("expected call statement");
        };
        &args[0]
    }

    fn call_arg_in_block<'a>(
        program: &'a Program,
        function: &str,
        block_label: &str,
        statement: usize,
    ) -> &'a Operand {
        let func = program
            .functions()
            .find(|func| func.meta.name == function)
            .unwrap();
        let block = func
            .body
            .as_ref()
            .unwrap()
            .blocks
            .iter()
            .find(|block| block.label == block_label)
            .unwrap();
        let StatementKind::Call(_, args) = &block.statements[statement].kind else {
            panic!("expected call statement");
        };
        &args[0]
    }

    #[test]
    fn relaxes_an_earlier_copyable_move_but_keeps_the_last_move() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(x: i64) {
              entry:
                call consume(move x);
                call consume(move x);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
        assert!(matches!(call_arg(&program, "f", 1), Operand::Move(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn preserves_a_move_when_only_a_sibling_field_is_later_used() {
        let program = elaborate_source(
            "
            struct Pair: Move { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn f(p: Pair) {
              entry:
                call consume(move p.left);
                call consume(move p.right);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn relaxes_a_move_needed_on_a_successor_path() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(b: bool, x: i64) {
              entry:
                call consume(move x);
                branch(copy b) [true: use_x, false: done]
              use_x:
                call consume(move x);
                goto done
              done:
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn relaxes_a_move_needed_on_a_loop_back_edge() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(b: bool, x: i64) {
              entry:
                goto loop
              loop:
                call consume(move x);
                branch(copy b) [true: loop, false: done]
              done:
                return
            }
            ",
        );
        assert!(matches!(
            call_arg_in_block(&program, "f", "loop", 0),
            Operand::Copy(Place::Var(x)) if x == "x"
        ));
    }

    #[test]
    fn uses_declared_copy_class_for_custom_types() {
        let program = elaborate_source(
            "
            struct Token: Copy + Drop { value: i64 }
            extern fn consume(x: Token);
            fn f(x: Token) {
              entry:
                call consume(move x);
                call consume(move x);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Copy(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn does_not_copy_an_exclusive_reference() {
        let program = elaborate_source(
            "
            extern fn consume(r: &mut i64);
            fn f(r: &mut i64) {
              entry:
                call consume(move r);
                call consume(move r);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(r)) if r == "r"));
    }

    #[test]
    fn does_not_preserve_a_value_for_an_out_borrow() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            extern fn finish(r: &out i64);
            fn f(x: i64) {
              r: &out i64;
              entry:
                call consume(move x);
                r = &out x;
                r.* = 1;
                call finish(move r);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(x)) if x == "x"));
    }

    #[test]
    fn out_borrow_reinitialization_kills_loop_carried_demand() {
        let program = elaborate_source(
            "
            extern fn fill(r: &out i64);
            extern fn consume(x: i64);
            fn f(again: bool, x: i64) {
              r: &out i64;
              entry:
                goto loop
              loop:
                r = &out x;
                call fill(move r);
                call consume(move x);
                branch(copy again) [true: loop, false: done]
              done:
                return
            }
            ",
        );
        assert!(matches!(
            call_arg_in_block(&program, "f", "loop", 2),
            Operand::Move(Place::Var(x)) if x == "x"
        ));
    }

    #[test]
    fn out_borrow_of_a_field_blocks_aggregate_preservation() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn take_pair(p: Pair);
            fn f(p: Pair) {
              r: &out i64;
              entry:
                call take_pair(move p);
                r = &out p.left;
                r.* = 1;
                call take_pair(move p);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(Place::Var(p)) if p == "p"));
    }

    #[test]
    fn elaboration_is_idempotent() {
        let mut program = Parser::new(
            "
            extern fn consume(x: i64);
            fn f(x: i64) {
              entry:
                call consume(move x);
                call consume(move x);
                return
            }
            "
            .to_owned(),
        )
        .parse()
        .unwrap();
        let (env, errors) = Env::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");

        elaborate(&mut program, &env);
        let once = program.clone();
        elaborate(&mut program, &env);
        assert_eq!(program, once);
    }
}
