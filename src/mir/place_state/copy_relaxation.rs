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
//! The analysis is backward, with separate may-demand sets for values and
//! the owned bases needed to access them. At a CFG join the sets union: an
//! operand must be preserved if either successor can still use it.
//!
//! Rewrite candidates are statically tracked paths through any number of
//! exclusive-reference dereferences. Fields, downcasts, and constant indexes
//! may appear anywhere in the path. Every dereference boundary must be
//! exclusive: `move r.*` through `&T` is illegal even if a later use could
//! otherwise justify preserving the pointee.
//!
//! Dynamic indexes and raw-pointer dereferences are not stable identities:
//! another write may retarget them without changing the syntactic path. They
//! still contribute conservative access demand, but are not rewrite
//! candidates.

use crate::mir::ast::*;
use crate::mir::dataflow::{self, Analysis, Direction};
use crate::mir::helpers::*;
use crate::mir::place_state::analysis::RefState;
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
    let return_obligations = collect_return_obligations(func);
    let Some(body) = &mut func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let analysis = MovePathDemand {
        return_obligations: &return_obligations,
    };
    let exits = dataflow::run(&analysis, body);
    for block in &mut body.blocks {
        let Some(exit_demand) = exits.get(&block.label) else {
            continue;
        };
        let mut demand = exit_demand.clone();
        analysis.transfer_terminator(&mut demand, &block.terminator);
        relax_terminator(&mut block.terminator, &mut demand, env, &locals, &scope);
        for stmt in block.statements.iter_mut().rev() {
            relax_statement(stmt, &mut demand, env, &locals, &scope);
        }
    }
}

/// Ref-typed places whose obligation requires an Init pointee at expiry.
/// Injected as backward demand at `Return`: keeping the pointee Init through
/// the tail of the function is what those references contracted for, so any
/// `move place.*` reaching `Return` unmodified must relax to `copy` when the
/// pointee type permits.
///
/// Local refs may not actually live to `Return` — a move to a callee ends
/// them earlier — but the write that transfers the ref also kills demand on
/// its pointee, so the injection is safe over-approximation.
fn collect_return_obligations(func: &Function) -> BTreeSet<Place> {
    let mut out = BTreeSet::new();
    for param in &func.params {
        collect_post_init_pointees(&var_place(param.name.clone()), &param.ty, &mut out);
    }
    if let Some(body) = &func.body {
        for local in &body.locals {
            collect_post_init_pointees(&var_place(local.name.clone()), &local.ty, &mut out);
        }
    }
    out
}

fn collect_post_init_pointees(place: &Place, ty: &Type, out: &mut BTreeSet<Place>) {
    if let TypeKind::Ref(kind, _, inner) = &ty.kind {
        if RefState::from_kind(kind).is_some_and(|state| state.ends_init) {
            let pointee = deref_place(place.clone());
            out.insert(pointee.clone());
            collect_post_init_pointees(&pointee, inner, out);
        }
    }
}

/// Backward may-demand. `values` names storage whose current value is needed
/// by a successor. `accesses` names owned reference/index bases that must stay
/// available merely to reach some projected place. Keeping these separate is
/// what prevents a later use of borrower `r` from preserving pointee `r.*`.
#[derive(Clone, Default, PartialEq, Eq)]
struct Demand {
    values: BTreeSet<Place>,
    accesses: BTreeSet<Place>,
}

/// Backward may-demand for move paths.
struct MovePathDemand<'a> {
    return_obligations: &'a BTreeSet<Place>,
}

impl<'a> Analysis for MovePathDemand<'a> {
    type State = Demand;

    fn direction(&self) -> Direction {
        Direction::Backward
    }

    fn initial_state(&self) -> Self::State {
        Demand::default()
    }

    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        Demand {
            values: a.values.union(&b.values).cloned().collect(),
            accesses: a.accesses.union(&b.accesses).cloned().collect(),
        }
    }

    fn transfer_stmt(&self, demand: &mut Self::State, stmt: &Statement, _span: Span) {
        transfer_statement_demand(stmt, demand);
    }

    fn transfer_terminator(&self, demand: &mut Self::State, term: &Terminator) {
        if matches!(term.kind, TerminatorKind::Return) {
            for place in self.return_obligations {
                demand.values.insert(place.clone());
            }
        }
        transfer_terminator_demand(term, demand);
    }
}

fn transfer_statement_demand(stmt: &Statement, demand: &mut Demand) {
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            kill_future_demand(demand, target);
            transfer_rvalue_demand(rvalue, demand);
            if as_owned_path(target).is_none() {
                add_access_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
            transfer_operand_demand(target, demand);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            add_value_demand(demand, place);
        }
        // This is a postcondition, not a value use. A preceding move should
        // remain a move when this is the only later statement mentioning it.
        StatementKind::RequireUninit(_) => {}
    }
}

fn transfer_terminator_demand(term: &Terminator, demand: &mut Demand) {
    match &term.kind {
        TerminatorKind::Branch { cond, .. } => transfer_operand_demand(cond, demand),
        TerminatorKind::SwitchEnum { place, .. } => add_value_demand(demand, place),
        TerminatorKind::Goto(_)
        | TerminatorKind::Return
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

fn transfer_rvalue_demand(rvalue: &RValue, demand: &mut Demand) {
    match rvalue {
        RValue::Use(operand)
        | RValue::EnumConstr(_, _, _, operand)
        | RValue::PtrCast(operand, _) => transfer_operand_demand(operand, demand),
        RValue::Ref(kind, place) => transfer_ref_demand(kind, place, demand),
        RValue::RawRef(_) => {}
        RValue::ArrayLit(operands) => {
            for operand in operands.iter().rev() {
                transfer_operand_demand(operand, demand);
            }
        }
    }
}

fn transfer_operand_demand(operand: &Operand, demand: &mut Demand) {
    match operand {
        Operand::Copy(place) => add_value_demand(demand, place),
        Operand::Move(place) => {
            // Move consumes `place`'s subtree — downstream demand for its
            // descendants is void after the move, so drop it as we cross
            // this operand backward. The read itself is still a demand for
            // `place` pre-move.
            kill_future_demand(demand, place);
            add_value_demand(demand, place);
        }
        Operand::Const(_) => {}
    }
}

/// An operation that establishes a new state for `place` makes any future
/// demand for that old state irrelevant on its input side.
fn kill_future_demand(demand: &mut Demand, target: &Place) {
    let Some(target_depth) = static_deref_depth(target) else {
        return;
    };

    // A write establishes a new value for the target. Any overlapping future
    // value at the same dereference depth (or deeper) is therefore not the old
    // value. Killing ancestors too is deliberately conservative: representing
    // "the old aggregate except this newly-written field" would require a
    // complement path set.
    demand
        .values
        .retain(|needed| !write_invalidates_demand(target, target_depth, needed));
    demand
        .accesses
        .retain(|needed| !write_invalidates_demand(target, target_depth, needed));
}

fn write_invalidates_demand(target: &Place, target_depth: usize, needed: &Place) -> bool {
    static_deref_depth(needed).is_some_and(|needed_depth| {
        needed_depth >= target_depth
            && (is_ancestor_or_self(target, needed) || is_ancestor_or_self(needed, target))
    })
}

fn paths_overlap(a: &Place, b: &Place) -> bool {
    is_ancestor_or_self(a, b) || is_ancestor_or_self(b, a)
}

fn demand_preserves(candidate: &Place, needed: &Place) -> bool {
    let Some(candidate_depth) = static_deref_depth(candidate) else {
        return false;
    };
    static_deref_depth(needed).is_some_and(|needed_depth| {
        needed_depth >= candidate_depth && paths_overlap(candidate, needed)
    })
}

fn is_static_access_path(place: &Place) -> bool {
    static_deref_depth(place).is_some()
}

/// Count dereference boundaries in a statically comparable place. Dynamic
/// indices return `None`: equality of `a[i]` at two program points is not
/// enough to prove that `i` still denotes the same slot.
fn static_deref_depth(place: &Place) -> Option<usize> {
    match place {
        Place::Var(_) => Some(0),
        Place::Field(inner, _) | Place::Downcast(inner, _) => static_deref_depth(inner),
        Place::Index(inner, operand) if const_int_operand(operand).is_some() => {
            static_deref_depth(inner)
        }
        Place::Index(_, _) => None,
        Place::Deref(inner) => static_deref_depth(inner).map(|depth| depth + 1),
    }
}

/// Backward transfer for a borrow's pointee transition. This mirrors
/// init-state's eager loan transitions, restricted to statically-owned
/// paths: `&out` establishes Init, `&drop` establishes Uninit, and
/// `&uninit` requires/retains Uninit. Only ordinary and mutable borrows
/// merely read an existing value.
fn transfer_ref_demand(kind: &RefKind, place: &Place, demand: &mut Demand) {
    match kind {
        RefKind::Shared | RefKind::Mut => add_value_demand(demand, place),
        RefKind::Drop => {
            kill_ref_transition_demand(demand, place);
            add_value_demand(demand, place);
        }
        RefKind::Out | RefKind::Uninit => {
            kill_ref_transition_demand(demand, place);
            if as_owned_path(place).is_none() {
                add_access_demand(demand, place);
            }
        }
    }
}

/// A reference state transition on a subplace also invalidates demand for a
/// containing aggregate. For example, after `&out p.field`, a future read of
/// `p` cannot justify preserving an earlier `move p`: the borrow itself
/// requires `p.field` to have been uninitialized. Ordinary assignment differs
/// here — overwriting a field of an already-preserved Copy aggregate is fine.
fn kill_ref_transition_demand(demand: &mut Demand, place: &Place) {
    let Some(depth) = static_deref_depth(place) else {
        return;
    };
    demand.values.retain(|needed| {
        !static_deref_depth(needed)
            .is_some_and(|needed_depth| needed_depth >= depth && paths_overlap(place, needed))
    });
    demand.accesses.retain(|needed| {
        !static_deref_depth(needed)
            .is_some_and(|needed_depth| needed_depth >= depth && paths_overlap(place, needed))
    });
}

/// Record that the current value of `place` is needed. Full logical places
/// are retained only when they are statically comparable.
fn add_value_demand(demand: &mut Demand, place: &Place) {
    if is_static_access_path(place) {
        demand.values.insert(place.clone());
    }
    add_access_demand(demand, place);
}

/// Record every reference value needed to evaluate or write `place`, without
/// claiming that the final pointee value is needed. For `r.*.next.*`, both
/// `r` and `r.*.next` are access carriers.
fn add_access_demand(demand: &mut Demand, place: &Place) {
    let mut cur = place;
    loop {
        match cur {
            Place::Var(_) => break,
            Place::Deref(inner) => {
                if is_static_access_path(inner) {
                    demand.accesses.insert((**inner).clone());
                }
                cur = inner;
            }
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
                cur = inner
            }
        }
    }
    if let Some(owned) = nearest_owned_path(place) {
        demand.accesses.insert(owned);
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
    demand: &mut Demand,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match &mut stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            kill_future_demand(demand, target);
            relax_rvalue(rvalue, demand, env, locals, scope);
            if as_owned_path(target).is_none() {
                add_access_demand(demand, target);
            }
        }
        StatementKind::Call(target, args) => {
            for operand in args.iter_mut().rev() {
                relax_operand(operand, demand, env, locals, scope);
            }
            relax_operand(target, demand, env, locals, scope);
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            add_value_demand(demand, place);
        }
        StatementKind::RequireUninit(_) => {}
    }
}

fn relax_terminator(
    term: &mut Terminator,
    demand: &mut Demand,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match &mut term.kind {
        TerminatorKind::Branch { cond, .. } => relax_operand(cond, demand, env, locals, scope),
        TerminatorKind::SwitchEnum { place, .. } => add_value_demand(demand, place),
        TerminatorKind::Goto(_)
        | TerminatorKind::Return
        | TerminatorKind::Abort
        | TerminatorKind::Unreachable => {}
    }
}

fn relax_rvalue(
    rvalue: &mut RValue,
    demand: &mut Demand,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    match rvalue {
        RValue::Use(operand)
        | RValue::EnumConstr(_, _, _, operand)
        | RValue::PtrCast(operand, _) => relax_operand(operand, demand, env, locals, scope),
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
    demand: &mut Demand,
    env: &Env,
    locals: &IndexMap<String, Type>,
    scope: &IndexMap<String, Markers>,
) {
    let Operand::Move(place) = operand else {
        if let Operand::Copy(place) = operand {
            add_value_demand(demand, place);
        }
        return;
    };

    let owned = as_owned_path(place);
    let is_exclusive_deref = static_deref_depth(place)
        .is_some_and(|depth| depth > 0 && all_dereferences_are_exclusive(place, env, locals));
    let is_candidate = owned.is_some() || is_exclusive_deref;
    let needs_preserving = is_candidate
        && (demand
            .values
            .iter()
            .any(|needed| demand_preserves(place, needed))
            || demand
                .accesses
                .iter()
                .any(|needed| demand_preserves(place, needed)));
    let is_copy = is_candidate
        && env
            .type_of_place(place, Span::default(), locals)
            .is_ok_and(|ty| class_of(&ty, env, scope).implies(Marker::Copy));
    let place = place.clone();
    if needs_preserving && is_copy {
        *operand = Operand::Copy(place.clone());
    }
    // If we kept the operand as a `move`, it consumes `place`'s subtree —
    // mirror the fixpoint's kill so descendants demanded post-move don't
    // bleed backward past this operand and preserve unrelated earlier
    // moves.
    if matches!(operand, Operand::Move(_)) {
        kill_future_demand(demand, &place);
    }
    add_value_demand(demand, &place);
}

/// A move through a shared reference is illegal, and a raw pointer does not
/// provide the stable identity needed by this liveness-based rewrite. Require
/// every dereference receiver in the path to be an exclusive reference.
fn all_dereferences_are_exclusive(
    place: &Place,
    env: &Env,
    locals: &IndexMap<String, Type>,
) -> bool {
    fn walk(place: &Place, env: &Env, locals: &IndexMap<String, Type>) -> bool {
        match place {
            Place::Var(_) => true,
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
                walk(inner, env, locals)
            }
            Place::Deref(inner) => {
                let exclusive = env
                    .type_of_place(inner, Span::default(), locals)
                    .is_ok_and(|ty| {
                        matches!(
                            ty.kind,
                            TypeKind::Ref(
                                RefKind::Mut | RefKind::Out | RefKind::Drop | RefKind::Uninit,
                                _,
                                _
                            )
                        )
                    });
                exclusive && walk(inner, env, locals)
            }
        }
    }

    walk(place, env, locals)
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
    fn relaxes_an_earlier_move_through_an_exclusive_reference() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut i64) {
              entry:
                call consume(move r.*);
                call consume(move r.*);
                r.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 1), Operand::Move(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn never_relaxes_a_move_through_a_shared_reference() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &i64) {
              entry:
                call consume(move r.*);
                call consume(copy r.*);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Move(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn relaxes_through_arbitrarily_nested_exclusive_references() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut &mut i64) {
              entry:
                call consume(move r.*.*.*);
                call consume(move r.*.*.*);
                r.*.*.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*.*.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 1), Operand::Move(place) if format_place(place) == "r.*.*.*")
        );
    }

    #[test]
    fn shared_reference_anywhere_in_a_nested_path_blocks_relaxation() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn shared_inner(r: &mut &i64) {
              entry:
                call consume(move r.*.*);
                call consume(copy r.*.*);
                return
            }
            fn shared_outer(r: &&mut i64) {
              entry:
                call consume(move r.*.*);
                call consume(copy r.*.*);
                return
            }
            ",
        );
        assert!(matches!(
            call_arg(&program, "shared_inner", 0),
            Operand::Move(_)
        ));
        assert!(matches!(
            call_arg(&program, "shared_outer", 0),
            Operand::Move(_)
        ));
    }

    #[test]
    fn replacing_an_intermediate_reference_kills_nested_demand() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut &mut i64, replacement: &mut i64) {
              entry:
                call consume(move r.*.*);
                r.* = move replacement;
                call consume(move r.*.*);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn relaxes_nested_paths_with_projections_between_dereferences() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            struct Link: Move { next: &mut Pair }
            enum Choice: Move { A: &mut i64 B: unit }
            extern fn consume(x: i64);
            fn field(r: &mut Link) {
              entry:
                call consume(move r.*.next.*.left);
                call consume(move r.*.next.*.left);
                r.*.next.*.left = 0;
                return
            }
            fn index(r: &mut [&mut i64; 2]) {
              entry:
                call consume(move r.*[0].*);
                call consume(move r.*[0].*);
                r.*[0].* = 0;
                return
            }
            fn downcast(r: &mut Choice) {
              entry:
                call consume(move r.* as A.*);
                call consume(move r.* as A.*);
                r.* as A.* = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "field", 0), Operand::Copy(place) if format_place(place) == "r.*.next.*.left")
        );
        assert!(
            matches!(call_arg(&program, "index", 0), Operand::Copy(place) if format_place(place) == "r.*[0].*")
        );
        assert!(
            matches!(call_arg(&program, "downcast", 0), Operand::Copy(place) if format_place(place) == "r.* as A.*")
        );
    }

    #[test]
    fn shallower_borrower_use_does_not_preserve_a_deeper_pointee() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            extern fn consume_ref(r: &mut i64);
            fn f(r: &mut &mut i64) {
              entry:
                call consume(move r.*.*);
                call consume_ref(move r.*);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn raw_pointer_dereferences_are_not_relaxation_candidates() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(p: **i64) {
              entry:
                call consume(move p.*.*);
                call consume(copy p.*.*);
                return
            }
            ",
        );
        assert!(matches!(call_arg(&program, "f", 0), Operand::Move(_)));
    }

    #[test]
    fn borrower_use_alone_does_not_preserve_its_pointee() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &drop i64) {
              s: &drop i64;
              entry:
                call consume(move r.*);
                s = move r;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Move(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn dereference_write_kills_old_pointee_demand() {
        // The write at index 1 kills demand for `r.*` backward from the
        // second call and from `r`'s post-Init obligation at Return, so
        // the earlier `move r.*` at index 0 sees no demand and stays as
        // move. The final `move r.*` at index 2 still relaxes to `copy`
        // — otherwise `r.*` would be Uninit at Return, violating the
        // &mut obligation.
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn f(r: &mut i64) {
              entry:
                call consume(move r.*);
                r.* = 1;
                call consume(move r.*);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Move(place) if format_place(place) == "r.*")
        );
        assert!(
            matches!(call_arg(&program, "f", 2), Operand::Copy(place) if format_place(place) == "r.*")
        );
    }

    #[test]
    fn relaxes_the_same_projected_pointee_but_not_a_sibling() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn same(r: &mut Pair) {
              entry:
                call consume(move r.*.left);
                call consume(move r.*.left);
                r.*.left = 0;
                return
            }
            fn sibling(r: &mut Pair) {
              entry:
                call consume(move r.*.left);
                call consume(move r.*.right);
                r.*.left = 0;
                r.*.right = 0;
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "same", 0), Operand::Copy(place) if format_place(place) == "r.*.left")
        );
        assert!(
            matches!(call_arg(&program, "sibling", 0), Operand::Move(place) if format_place(place) == "r.*.left")
        );
    }

    #[test]
    fn relaxes_a_constant_pointee_index_but_not_a_dynamic_index() {
        let program = elaborate_source(
            "
            extern fn consume(x: i64);
            fn constant(r: &mut [i64; 2]) {
              entry:
                call consume(move r.*[0]);
                call consume(move r.*[0]);
                r.*[0] = 0;
                return
            }
            fn dynamic(r: &mut [i64; 2], i: i64) {
              entry:
                call consume(move r.*[copy i]);
                call consume(move r.*[copy i]);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "constant", 0), Operand::Copy(place) if format_place(place) == "r.*[0]")
        );
        assert!(
            matches!(call_arg(&program, "dynamic", 0), Operand::Move(place) if format_place(place) == "r.*[?]")
        );
    }

    #[test]
    fn relaxes_a_downcast_pointee_projection() {
        let program = elaborate_source(
            "
            enum Choice: Copy + Drop { A: i64 B: i64 }
            extern fn consume(x: i64);
            fn f(r: &mut Choice) {
              entry:
                call consume(move r.* as A);
                call consume(move r.* as A);
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.* as A")
        );
    }

    #[test]
    fn relaxes_a_projected_pointee_on_a_successor_path() {
        let program = elaborate_source(
            "
            struct Pair: Copy + Drop { left: i64 right: i64 }
            extern fn consume(x: i64);
            fn f(r: &mut Pair, b: bool) {
              entry:
                call consume(move r.*.left);
                branch(copy b) [true: use_left, false: done]
              use_left:
                call consume(move r.*.left);
                r.*.left = 0;
                goto done
              done:
                return
            }
            ",
        );
        assert!(
            matches!(call_arg(&program, "f", 0), Operand::Copy(place) if format_place(place) == "r.*.left")
        );
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
