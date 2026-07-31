use crate::diagnostics::Diagnostics;
use crate::mir::ast::*;
use crate::mir::diagnostic_format::format_type_diagnostic;
use crate::mir::helpers::*;
use crate::mir::env::GlobalEnv;
use indexmap::IndexMap;

use super::analysis::{
    advance_ty, capture_carried_refs, describe_obligation_mismatch, describe_pointee_state,
    describe_state, extract_init_path, format_path, is_state_fully_init,
    partial_is_uninit, read_at, run_fixpoint, split_at_outermost_deref, state_refines_to_variant,
    states_before_returns, InitSlot, InitState, PlaceStateCode, PlaceStateCode::*, PlaceStateContext,
    PointState, RefState,
};

pub fn check_program(program: &Program, env: &GlobalEnv, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(env, f, d);
    }
    check_return_leaks(program, env, d);
}

/// Return validation is part of the single final place-state check.
pub(super) fn check_return_leaks(program: &Program, env: &GlobalEnv, d: &mut Diagnostics) {
    for (func, _body) in program.function_bodies() {
        let locals = func.locals_map();
        for (block, state) in states_before_returns(env, func) {
            check_return_state(env, func, block, &locals, &state, d);
        }
    }
}

fn check_return_state(
    env: &GlobalEnv,
    func: &Function,
    block: &BasicBlock,
    locals: &IndexMap<String, Type>,
    state: &PointState,
    d: &mut Diagnostics,
) {
    for (var, place_state) in &state.locals {
        let Some(ty) = locals.get(var) else {
            continue;
        };
        // A whole reference has a (cur, post) rule rather than the ordinary
        // value-leak rule. Ref fields are handled by the recursive walk and
        // by the obligation loop below.
        if state.refs.contains_key(&var_place(var.clone())) {
            continue;
        }
        let mut path = var.clone();
        let mut leaks = Vec::new();
        find_return_leaks(env, place_state, ty, &mut path, &mut leaks);
        for (leaked_path, leaked_ty) in leaks {
            let mut diagnostic = format_type_diagnostic(&func.meta, &leaked_ty, |ty| {
                diag(
                    ReturnValueLeak,
                    block.terminator.source,
                    func,
                    block,
                    format!(
                        "value '{}' of type {} is not consumed at return",
                        leaked_path, ty,
                    ),
                )
                .with_hint("linear values must be consumed or returned before function exit. Try moving or dropping it.")
            });
            let root_end = leaked_path
                .find(|c: char| c == '.' || c == '[')
                .unwrap_or(leaked_path.len());
            if let Some(source) = find_decl_source(func, &leaked_path[..root_end]) {
                diagnostic = diagnostic.with_secondary(source, "variable declared here");
            }
            d.push_error(diagnostic);
        }
    }

    for (place, rs) in &state.refs {
        if rs.obligation_fulfilled() {
            continue;
        }
        let (cur, expected) = describe_obligation_mismatch(rs);
        let mut diagnostic = diag(
            RefObligationUnfulfilled,
            block.terminator.source,
            func,
            block,
            format!(
                "reference '{}' has unfulfilled obligation at return: pointee is {}, but must be {}",
                format_place(place), cur, expected,
            ),
        );
        if let Some(source) = find_decl_source(func, place_root_var_name(place)) {
            diagnostic = diagnostic.with_secondary(source, "reference declared here");
        }
        d.push_error(diagnostic);
    }
}

fn find_return_leaks(
    env: &GlobalEnv,
    state: &InitState,
    ty: &Type,
    path: &mut String,
    out: &mut Vec<(String, Type)>,
) {
    match state {
        InitState::NeverInit | InitState::Moved => {}
        InitState::Init | InitState::Diverged => out.push((path.clone(), ty.clone())),
        InitState::Partial(fields) => {
            for (slot, sub_state) in fields {
                let sub_ty = match (&ty.kind, slot) {
                    (TypeKind::Array(elem, _), InitSlot::Index(_)) => (**elem).clone(),
                    (_, InitSlot::Field(f)) => match env.field_type(ty, f) {
                        Some(ft) => ft,
                        None => continue,
                    },
                    (_, InitSlot::Variant(v)) => match env.variant_payload_type(ty, v) {
                        Some(pt) => pt,
                        None => continue,
                    },
                    // Slot/type mismatch — expand_uniform/expand_uniform_array
                    // only emit matching shapes, so this only fires if the
                    // types have drifted since expansion (skip defensively).
                    _ => continue,
                };
                let saved_len = path.len();
                path.push_str(&slot.to_string());
                find_return_leaks(env, sub_state, &sub_ty, path, out);
                path.truncate(saved_len);
            }
        }
    }
}

pub(super) fn place_root_var_name(place: &Place) -> &str {
    match place {
        Place::Var(name) => name,
        Place::Field(base, _)
        | Place::Downcast(base, _)
        | Place::Deref(base)
        | Place::Index(base, _) => place_root_var_name(base),
    }
}

pub(super) fn find_decl_source(func: &Function, name: &str) -> Option<SourceInfo> {
    if let Some(param) = func.params.iter().find(|param| param.name == name) {
        return Some(param.source);
    }
    func.body
        .as_ref()?
        .locals
        .iter()
        .find(|local| local.name == name)
        .map(|local| local.source)
}

fn check_function(env: &GlobalEnv, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let locals = func.locals_map();
    let ctx = PlaceStateContext {
        env,
        locals: &locals,
    };
    let init_entry_states = run_fixpoint(&ctx, func, body);

    for block in &body.blocks {
        let Some(init_entry) = init_entry_states.get(&block.label) else {
            continue;
        };
        let mut state = init_entry.clone();
        ctx.check_block(func, block, &mut state, d);
    }
}

/// Walk (init state × type) tree together, invoking `report` on every
/// leaf whose state is Init or Diverged. `Partial` recurses per-field
/// for struct types and per-slot for array types; `NeverInit`/`Moved`
/// short-circuit (nothing to overwrite). Each recursion pushes a
/// formatted projection segment (`.field` or `[k]`) so the caller can
/// concatenate directly onto a place name to get a legal Silica path.
pub(super) fn walk_overwrite_leaves(
    state: &InitState,
    ty: &Type,
    env: &GlobalEnv,
    path: &mut String,
    report: &mut dyn FnMut(&str, &Type),
) {
    match state {
        InitState::NeverInit | InitState::Moved => {}
        InitState::Init | InitState::Diverged => report(path, ty),
        InitState::Partial(fields) => {
            for (slot, sub_state) in fields {
                let sub_ty = match (&ty.kind, slot) {
                    (TypeKind::Array(elem, _), InitSlot::Index(_)) => (**elem).clone(),
                    (_, InitSlot::Field(f)) => match env.field_type(ty, f) {
                        Some(ft) => ft,
                        None => continue,
                    },
                    (_, InitSlot::Variant(v)) => match env.variant_payload_type(ty, v) {
                        Some(pt) => pt,
                        None => continue,
                    },
                    _ => continue,
                };
                let saved_len = path.len();
                path.push_str(&slot.to_string());
                walk_overwrite_leaves(sub_state, &sub_ty, env, path, report);
                path.truncate(saved_len);
            }
        }
    }
}

/// True if `place`'s projection path contains any dynamic-index step
/// (`Index(None)`). Deref steps are included in the walk, so this
/// catches both direct places (`a[i]`) and reborrow shapes
/// (`r.*[i]`, `s.arr[i]`, ...).
pub(super) fn place_has_dynamic_index(place: &Place) -> bool {
    let (_, path) = extract_path_with_deref(place);
    path.iter().any(|s| matches!(s, PathStep::Index(None)))
}

/// Locate the declaration source for the root Var of `ref_place`. Used
/// to attach a secondary "reference declared here" span to obligation
/// diagnostics — the primary span sits at the point of failure (the
/// return, drop, or overwrite), which repeats across every case in a
/// fixture and doesn't distinguish which reference was involved.
pub(super) fn ref_root_decl_source(func: &Function, ref_place: &Place) -> Option<SourceInfo> {
    let (root, _) = extract_path_with_deref(ref_place);
    for p in &func.params {
        if p.name == root {
            return Some(p.source);
        }
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            if l.name == root {
                return Some(l.source);
            }
        }
    }
    None
}

// ---------- Diagnostic pass ----------

impl<'a> PlaceStateContext<'a> {
    pub(super) fn check_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        for stmt in &block.statements {
            self.check_downcast_refinements_in_stmt(func, block, stmt, state, d);
            self.check_and_transfer_stmt(func, block, stmt, state, d);
        }
        self.check_downcast_refinements_in_terminator(func, block, state, d);
        self.check_and_transfer_terminator(func, block, state, d);
    }

    /// Emit DowncastVariantNotRefined for each Downcast step in any
    /// place mentioned by this statement whose enclosing state doesn't
    /// refine to a singleton `{Variant(V): _}`. Runs before the transfer
    /// so the state reflects the pre-statement view — no operand's own
    /// moves have kicked in yet, so the check sees the same state a
    /// human reading the source would.
    fn check_downcast_refinements_in_stmt(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let source = stmt.source;
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                self.check_place_downcasts(func, block, target, source, state, d);
                match rvalue {
                    RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                        if let Some(p) = operand_place(op) {
                            self.check_place_downcasts(func, block, p, source, state, d);
                        }
                    }
                    RValue::Ref(_, p) | RValue::RawRef(p) => {
                        self.check_place_downcasts(func, block, p, source, state, d);
                    }
                    RValue::ArrayLit(ops) => {
                        for op in ops {
                            if let Some(p) = operand_place(op) {
                                self.check_place_downcasts(func, block, p, source, state, d);
                            }
                        }
                    }
                }
            }
            StatementKind::Call(target, args) => {
                if let Some(p) = operand_place(target) {
                    self.check_place_downcasts(func, block, p, source, state, d);
                }
                for a in args {
                    if let Some(p) = operand_place(a) {
                        self.check_place_downcasts(func, block, p, source, state, d);
                    }
                }
            }
            StatementKind::Drop(place)
            | StatementKind::Unborrow(place)
            | StatementKind::RequireUninit(place) => {
                self.check_place_downcasts(func, block, place, source, state, d);
            }
        }
    }

    fn check_downcast_refinements_in_terminator(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let source = block.terminator.source;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                if let Some(p) = operand_place(cond) {
                    self.check_place_downcasts(func, block, p, source, state, d);
                }
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                self.check_place_downcasts(func, block, place, source, state, d);
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable => {}
        }
    }

    fn check_place_downcasts(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        source: SourceInfo,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_init_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let mut prefix_ty = root_ty.clone();
        for (i, step) in path.iter().enumerate() {
            if let PathStep::Downcast(v) = step {
                // Downcast on a non-enum type is a type error already
                // reported by type_check; skip the refinement check
                // rather than pile on a misleading "not refined" message.
                if self.env.variant_payload_type(&prefix_ty, v).is_none() {
                    return;
                }
                let prefix_state = read_at(root_state, &root_ty, &path[..i], self.env);
                if !state_refines_to_variant(&prefix_state, v) {
                    let prefix = format_path(&root, &path[..i]);
                    d.push_error(diag(
                        PlaceStateCode::DowncastVariantNotRefined,
                        source,
                        func,
                        block,
                        format!(
                            "cannot downcast '{} as {}' here: '{}' is not refined to variant '{}'",
                            prefix, v, prefix, v
                        ),
                    ));
                    return;
                }
            }
            match advance_ty(&prefix_ty, step, self.env) {
                Some(next) => prefix_ty = next,
                None => return,
            }
        }
    }

    /// Combined check + transfer. Operands are consumed left-to-right so that a
    /// later operand in the same statement sees the state after prior moves —
    /// this is what makes `call f(move x, copy x)` correctly error on the second
    /// operand.
    fn check_and_transfer_stmt(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let source = stmt.source;
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                self.materialize_moved_ref(rvalue, state);
                // Capture ref-state entries to transfer via `move src`
                // BEFORE eval_rvalue runs. Cascade re-keys src.f → dst.f.
                let carried_refs = capture_carried_refs(target, rvalue, state);

                // A write to a dynamic-index target would transition one
                // runtime-chosen slot's state, and the lattice can't name
                // that slot. Reject direct assignment; users route slot
                // replacement through a reborrow, which puts the transition
                // on the reference's own per-ref pointee state and leaves
                // the array's per-slot lattice untouched:
                //     p = &mut a[i];  drop p.*;  p.* = new;
                if place_has_dynamic_index(target) {
                    d.push_error(diag(
                        DynamicIndexConsumption,
                        source,
                        func,
                        block,
                        format!(
                            "cannot assign to '{}': this changes one slot, but the index isn't known at compile time. To replace a slot at runtime, borrow it as `&mut` and write through the reference: `p = &mut a[i]; drop p.*; p.* = new_value;`",
                            format_place(target),
                        ),
                    ));
                }

                // Overwrite check runs BEFORE we mutate state: it looks
                // at the target's current state before the rvalue's
                // moves take effect, so that e.g. `y = move y.f` isn't
                // conflated (although that shape is not really valid).
                self.check_overwrite(func, block, target, source, state, d);

                self.eval_rvalue(func, block, rvalue, source, state, d);
                self.check_lhs_downcast(func, block, target, source, state, d);

                // Overwriting a bound ref var is a silent-forget of the
                // pointee obligation; error unless already fulfilled.
                self.close_ref_if_present(func, block, target, source, state, d);

                self.apply_target_write_state(
                    target,
                    rvalue,
                    carried_refs,
                    state,
                    Some((func, block, source, d)),
                );
            }
            StatementKind::Call(target, args) => {
                // Fire the call-boundary check BEFORE consumption so we
                // see each operand's live state. Every `move` operand
                // that carries a ref (or an aggregate containing one)
                // must be in its declared kind's entry state.
                if let Operand::Move(place) = target {
                    self.check_call_transfer(func, block, place, source, state, d);
                }
                self.eval_operand(func, block, target, source, state, d);
                for a in args {
                    if let Operand::Move(place) = a {
                        self.check_call_transfer(func, block, place, source, state, d);
                    }
                    self.eval_operand(func, block, a, source, state, d);
                }
            }
            StatementKind::Drop(place) => {
                // `drop a[i]` with dynamic i has the same untrackability
                // as `move a[i]`: exactly one runtime slot transitions,
                // and the per-slot lattice can't name it.
                if place_has_dynamic_index(place) {
                    d.push_error(diag(
                        DynamicIndexConsumption,
                        source,
                        func,
                        block,
                        format!(
                            "cannot `drop {}`: this consumes one slot, but the index isn't known at compile time. Drop by a constant index.",
                            format_place(place),
                        ),
                    ));
                }
                // Read the place, then consume it. Same effect on state as
                // `move`. The substructural checker (separate pass) is the
                // one that will require the type to be Drop. For a ref-typed
                // Var, also verify the pointee obligation before forgetting.
                self.check_place_read(func, block, place, source, state, d);
                self.close_ref_if_present(func, block, place, source, state, d);
                self.apply_consume_state(place, state, Some((func, block, source, d)));
            }
            StatementKind::Unborrow(place) => {
                // Explicit end-of-loan. Requires the borrower to be Init
                // and its (is_init, ends_init) obligation fulfilled — both
                // checked by close_ref_if_present. Then consume the borrower.
                self.check_place_read(func, block, place, source, state, d);
                self.close_ref_if_present(func, block, place, source, state, d);
                self.apply_move(place, state);
            }
            StatementKind::RequireUninit(place) => {
                self.check_require_uninit(func, block, place, source, state, d);
                // This prevents a later scope exit or return from repeating
                // the same leak diagnostic.
                self.apply_require_uninit_postcondition(place, state);
            }
        }
    }

    fn check_and_transfer_terminator(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let source = block.terminator.source;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                self.eval_operand(func, block, cond, source, state, d)
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                // Discriminant read: no move, no consumption.
                self.check_place_read(func, block, place, source, state, d);
                if split_at_outermost_deref(place).is_some() {
                    self.apply_deref_op(
                        place,
                        super::analysis::DerefOp::Read,
                        state,
                        Some((func, block, source, d)),
                    );
                }
            }
            // Goto/Return/Abort/Unreachable inspect no operand or place,
            // so no place-state check applies. `return` leaks are handled
            // separately by `check_return_leaks` after the per-block walk.
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Abort
            | TerminatorKind::Unreachable => {}
        }
    }

    fn eval_rvalue(
        &self,
        func: &Function,
        block: &BasicBlock,
        rv: &RValue,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        match rv {
            RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                self.eval_operand(func, block, op, source, state, d);
            }
            RValue::Ref(kind, place) => {
                self.check_borrow_precondition(func, block, kind, place, source, state, d);
            }
            RValue::RawRef(_) => {
                // No precondition — raw pointers can point at any
                // state (init, uninit, moved). Aliasing/lifetime are
                // the programmer's responsibility.
            }
            RValue::ArrayLit(ops) => {
                for op in ops {
                    self.eval_operand(func, block, op, source, state, d);
                }
            }
        }
    }

    fn eval_operand(
        &self,
        func: &Function,
        block: &BasicBlock,
        op: &Operand,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        self.check_operand_read(func, block, op, source, state, d);
        // Projected dereference operands carry their own pointee-state
        // transition. Owned operands use the ordinary locals-state transfer.
        match op {
            Operand::Copy(place) if split_at_outermost_deref(place).is_some() => {
                self.apply_deref_op(
                    place,
                    super::analysis::DerefOp::Read,
                    state,
                    Some((func, block, source, d)),
                );
            }
            Operand::Move(place) if split_at_outermost_deref(place).is_some() => {
                self.apply_deref_op(
                    place,
                    super::analysis::DerefOp::Move,
                    state,
                    Some((func, block, source, d)),
                );
            }
            _ => self.apply_operand_move(op, state),
        }
    }

    fn check_operand_read(
        &self,
        func: &Function,
        block: &BasicBlock,
        op: &Operand,
        source: SourceInfo,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Take(_) => unreachable!(
                "place-state check saw unresolved `take` operand; copy relaxation should have resolved it"
            ),
            Operand::Const(_) => return,
        };
        // `move a[i]` with dynamic i would consume one unidentified
        // slot; the per-slot lattice can't name it. (`copy` and shared
        // reads are fine — they don't change state.)
        if matches!(op, Operand::Move(_)) && place_has_dynamic_index(place) {
            d.push_error(diag(
                DynamicIndexConsumption,
                source,
                func,
                block,
                format!(
                    "cannot `move {}`: this consumes one slot, but the index isn't known at compile time. Move by a constant index, or move the whole array.",
                    format_place(place),
                ),
            ));
        }
        self.check_place_read(func, block, place, source, state, d);
    }

    /// Overwrite check: at `target = ...`, the storage covered by
    /// `target` is about to be clobbered. Any part currently `Init` (or
    /// `Diverged`) is a value that would be silently forgotten. Each
    /// such Init leaf's type must be `Drop`, or the caller must have
    /// consumed it first (e.g. via `drop target;`).
    ///
    /// Deref targets skip this: `*r = v` writes through the ref, and
    /// the pointee's obligation is tracked separately via RefState.
    ///
    /// `NeverInit` and `Moved` states are consumed (no clobber). `Partial`
    /// recurses into fields to find Init leaves.
    fn check_overwrite(
        &self,
        func: &Function,
        block: &BasicBlock,
        target: &Place,
        source: SourceInfo,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_init_path(target) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let target_state = read_at(root_state, &root_ty, &path, self.env);
        let Some(target_ty) = self.infer_ref_place_type(target) else {
            return;
        };
        walk_overwrite_leaves(
            &target_state,
            &target_ty,
            self.env,
            &mut String::new(),
            &mut |leaf_path, leaf_ty| {
                let c = self.env.class_of(leaf_ty, &func.meta.params);
                if !c.implies(Marker::Drop) {
                    let path_str = format!("{}{}", format_place(target), leaf_path);
                    d.push_error(format_type_diagnostic(&func.meta, leaf_ty, |ty| {
                        diag(
                            OverwriteWithoutDrop,
                            source,
                            func,
                            block,
                            format!(
                                "cannot overwrite '{}': type {} is not Drop and the value is still live (consume it via `drop {}` first)",
                                path_str, ty, path_str,
                            ),
                        )
                    }));
                }
            },
        );
    }

    /// If `place` is a whole-var ref binding with an outstanding obligation
    /// (`refs[name]` exists), verify its obligation is fulfilled and remove
    /// the entry. Called at any point where the reference value is being
    /// silently forgotten: `drop r`, or overwrite of `r`.
    fn close_ref_if_present(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        if !super::analysis::is_static_place(place) {
            return;
        }
        if split_at_outermost_deref(place).is_some() {
            let _ = self.ensure_ref_state(place, state);
        }
        // Cascade: closing/overwriting an ancestor implicitly forgets
        // every descendant ref. Each victim's obligation is checked.
        let victims: Vec<Place> = state
            .refs
            .keys()
            .filter(|k| is_ancestor_or_self(place, k))
            .cloned()
            .collect();
        for v in victims {
            let rs = state.refs[&v].clone();
            if !rs.obligation_fulfilled() {
                let (cur, expected) = describe_obligation_mismatch(&rs);
                let mut diagnostic = diag(
                    RefObligationUnfulfilled,
                    source,
                    func,
                    block,
                    format!(
                        "reference '{}' has unfulfilled obligation: pointee is {}, but must be {}",
                        format_place(&v),
                        cur,
                        expected,
                    ),
                );
                if let Some(decl_source) = ref_root_decl_source(func, &v) {
                    diagnostic = diagnostic.with_secondary(decl_source, "reference declared here");
                }
                d.push_error(diagnostic);
            }
            state.refs.shift_remove(&v);
        }
    }

    /// Verify that every ref-typed leaf reachable from `moved` is in
    /// its declared kind's *entry* state — the state the callee's
    /// signature will assume when it inherits the reference. Fires
    /// `RefCallEntryMismatch` on any leaf that has drifted.
    ///
    /// This is the call-boundary complement of `close_ref_if_present`'s
    /// expiry check. Both walk `state.refs` for descendants of the
    /// consumed place; they differ in the predicate:
    ///
    /// - `close_ref_if_present` checks `obligation_fulfilled()` — the
    ///   `(post)` side of the (cur, post) contract. Runs on drop,
    ///   unborrow, and assign-target overwrite.
    /// - `check_call_transfer` checks `pointee == from_kind(kind).pointee`
    ///   — the `(cur)` side. Runs only on `move` operands to `call`,
    ///   because that's the only site where a reference crosses to a
    ///   callee whose signature will treat it as freshly-received. An
    ///   intra-fn `y = move x` preserves actual state via
    ///   `capture_carried_refs`, so it doesn't need this check.
    fn check_call_transfer(
        &self,
        func: &Function,
        block: &BasicBlock,
        moved: &Place,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        if !super::analysis::is_static_place(moved) {
            return;
        }
        if split_at_outermost_deref(moved).is_some() {
            let _ = self.ensure_ref_state(moved, state);
        }
        let victims: Vec<Place> = state
            .refs
            .keys()
            .filter(|k| is_ancestor_or_self(moved, k))
            .cloned()
            .collect();
        for v in victims {
            let Some(ref_ty) = self.infer_ref_place_type(&v) else {
                continue;
            };
            let TypeKind::Ref(kind, _, _) = &ref_ty.kind else {
                continue;
            };
            let Some(declared) = RefState::from_kind(kind) else {
                continue;
            };
            let rs = &state.refs[&v];
            let matches = match declared.pointee {
                InitState::Init => rs.is_init(),
                InitState::NeverInit => rs.is_uninit(),
                // from_kind only returns Init or NeverInit as declared.
                _ => true,
            };
            if !matches {
                let current = describe_pointee_state(&rs.pointee);
                let expected = describe_pointee_state(&declared.pointee);
                let msg = format!(
                    "cannot transfer '{}' across call boundary: {} requires pointee {} at handoff, but pointee is {}",
                    format_place(&v),
                    kind,
                    expected,
                    current,
                );
                let mut diagnostic = diag(RefCallEntryMismatch, source, func, block, msg);
                if let Some(decl_source) = ref_root_decl_source(func, &v) {
                    diagnostic = diagnostic.with_secondary(decl_source, "reference declared here");
                }
                d.push_error(diagnostic);
            }
        }
    }

    /// If the LHS path contains a `Downcast`, the enum being downcast must be
    /// `Init` at that point — you can't refine an uninitialized enum by writing
    /// through a variant projection. Enum construction goes via `Name::V(...)`.
    fn check_lhs_downcast(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(idx) = path.iter().position(|s| matches!(s, PathStep::Downcast(_))) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let prefix_state = read_at(root_state, &root_ty, &path[..idx], self.env);
        if !is_state_fully_init(&prefix_state) {
            d.push_error(diag(
                WriteThroughUninitEnumProjection,
                source,
                func,
                block,
                format!(
                    "cannot write through variant projection: '{}' is not initialized here",
                    root
                ),
            ));
        }
    }

    fn check_place_read(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        source: SourceInfo,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some((root, path)) = extract_init_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let leaf = read_at(root_state, &root_ty, &path, self.env);
        if is_state_fully_init(&leaf) {
            return;
        }
        match leaf {
            InitState::Init => {}
            InitState::NeverInit => d.push_error(diag(
                UseBeforeInit,
                source,
                func,
                block,
                format!("variable '{}' is used before initialization", root),
            )),
            InitState::Moved => d.push_error(diag(
                UseAfterMove,
                source,
                func,
                block,
                format!("variable '{}' is used after move", root),
            )),
            InitState::Diverged => {
                // Diverged means the leaf was Init on some incoming path
                // and NeverInit / Moved on another. Point at every prior
                // write to *this exact path* as a secondary — those are
                // the arms where it WAS initialized; the fact that we
                // still see Diverged tells the reader at least one other
                // path skipped them all.
                let mut err = diag(
                    UseInconsistent,
                    source,
                    func,
                    block,
                    format!(
                        "'{}' may be used before initialization or after move (state inconsistent across paths)",
                        format_place(place)
                    ),
                );
                if let Some(body) = &func.body {
                    for b in &body.blocks {
                        for stmt in &b.statements {
                            if let StatementKind::Assign(target, _) = &stmt.kind {
                                if target == place {
                                    err = err.with_secondary(
                                        stmt.source,
                                        "initialized here on some path",
                                    );
                                }
                            }
                        }
                    }
                }
                d.push_error(err);
            }
            InitState::Partial(_) => d.push_error(diag(
                UsePartiallyInit,
                source,
                func,
                block,
                format!("variable '{}' is not fully initialized here", root),
            )),
        }
    }

    /// Verify that the state of the borrowed place matches the reference
    /// kind's creation-is_init:
    ///   * `&`, `&mut`, `&drop` require the pointee to be Init.
    ///   * `&out`, `&uninit` require the pointee to be uninitialized
    ///     (NeverInit or Moved).
    ///
    /// The check inspects the leaf state via [`read_at`]; partial and
    /// diverged states at the leaf never match either precondition, so
    /// they're rejected with a clear "not fully X" message.
    fn check_borrow_precondition(
        &self,
        func: &Function,
        block: &BasicBlock,
        kind: &RefKind,
        place: &Place,
        source: SourceInfo,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        let (requires_init, kind_str) = match kind {
            RefKind::Shared => (true, "&"),
            RefKind::Mut => (true, "&mut"),
            RefKind::Drop => (true, "&drop"),
            RefKind::Out => (false, "&out"),
            RefKind::Uninit => (false, "&uninit"),
        };

        // A state-changing borrow (`&out`, `&drop`) on a dynamic-index
        // place would leave exactly one unidentified slot transitioned to
        // the post state while the rest stay uniform. No widening can
        // recover which slot changed, so we reject outright — even under
        // a uniform pre-state.
        if matches!(kind, RefKind::Out | RefKind::Drop) && place_has_dynamic_index(place) {
            d.push_error(diag(
                BorrowDynamicIndexStateChanging,
                source,
                func,
                block,
                format!(
                    "cannot create {} of '{}': this borrow changes the slot's state, but the index isn't known at compile time. On a uniformly-initialized array, use `&mut a[i]` instead — it preserves the slot's state.",
                    kind_str,
                    format_place(place),
                ),
            ));
            return;
        }

        // Reborrow through an exclusive reference: the pointee's init state
        // lives in the parent RefState, including statically projected fields,
        // downcasts, and constant indexes.
        if let Some((parent, sub_path)) = split_at_outermost_deref(place) {
            let parent_str = format_place(&parent);
            let borrowed_str = if sub_path.is_empty() {
                format!("*{parent_str}")
            } else {
                format_place(place)
            };
            let Some(parent_ty) = self.infer_ref_place_type(&parent) else {
                return;
            };
            let TypeKind::Ref(_, _, pointee_ty) = parent_ty.kind else {
                // Raw-pointer dereferences carry no tracked initialization
                // state; unsafe source is responsible for their validity.
                return;
            };
            let Some(parent_rs) = self.ensure_ref_state(&parent, state) else {
                d.push_error(diag(
                    ReferenceStateUnknown,
                    source,
                    func,
                    block,
                    format!(
                        "cannot create {} of '*{}': parent reference '{}' is not bound here",
                        kind_str, parent_str, parent_str
                    ),
                ));
                return;
            };
            if sub_path
                .iter()
                .any(|step| matches!(step, PathStep::Deref | PathStep::Index(None)))
            {
                return;
            }
            let current = read_at(&parent_rs.pointee, &pointee_ty, &sub_path, self.env);
            let precondition_met = if requires_init {
                is_state_fully_init(&current)
            } else {
                matches!(current, InitState::NeverInit | InitState::Moved)
            };
            if !precondition_met {
                let expected = if requires_init {
                    "initialized"
                } else {
                    "uninitialized"
                };
                let actual = describe_pointee_state(&current);
                d.push_error(diag(
                    BorrowStateMismatch,
                    source,
                    func,
                    block,
                    format!(
                        "cannot create {} of '{}': pointee must be {} at borrow, but is {}",
                        kind_str, borrowed_str, expected, actual
                    ),
                ));
            }
            return;
        }

        // Dynamic-index widening: if the path contains an `Index(None)`,
        // we can't name a specific slot. Widen the precondition to the
        // *whole* containing array: every slot must uniformly satisfy
        // the pre-condition. Truncate the path at the first dynamic
        // index and check the array's state at that prefix.
        let (root_widen, path_widen) = extract_path_with_deref(place);
        if let Some(dyn_pos) = path_widen
            .iter()
            .position(|s| matches!(s, PathStep::Index(None)))
        {
            // Deref inside the prefix means this is a reborrow —
            // already handled above by deref_inner. Shouldn't reach
            // here for that shape, but guard anyway.
            if path_widen[..dyn_pos]
                .iter()
                .any(|s| matches!(s, PathStep::Deref))
            {
                return;
            }
            let Some(root_ty) = self.locals.get(&root_widen).cloned() else {
                return;
            };
            let Some(root_state) = state.locals.get(&root_widen) else {
                return;
            };
            let leaf = read_at(root_state, &root_ty, &path_widen[..dyn_pos], self.env);
            let ok = if requires_init {
                is_state_fully_init(&leaf)
            } else {
                matches!(leaf, InitState::NeverInit | InitState::Moved)
            };
            if ok {
                return;
            }
            let expected = if requires_init {
                "initialized"
            } else {
                "uninitialized"
            };
            let actual = describe_state(&leaf);
            d.push_error(diag(
                BorrowDynamicIndexNonUniform,
                source,
                func,
                block,
                format!(
                    "cannot create {} of '{}': dynamic index requires the containing array to be uniformly {}, but it is {}",
                    kind_str, format_place(place), expected, actual
                ),
            ));
            return;
        }

        let Some((root, path)) = extract_path(place) else {
            return;
        };
        let Some(root_ty) = self.locals.get(&root).cloned() else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };
        let leaf = read_at(root_state, &root_ty, &path, self.env);

        let ok = if requires_init {
            is_state_fully_init(&leaf)
        } else {
            matches!(leaf, InitState::NeverInit | InitState::Moved)
        };
        if ok {
            return;
        }

        // Drop-elaborable: for `&out` / `&uninit` on an Init place whose
        // leaf type is Drop, drop-elaboration will insert `drop place`
        // just before this borrow, transitioning `place` from Init to
        // Moved so the Uninit precondition is satisfied. Skip the
        // error here; post-elab init_state re-runs against the
        // elaborated MIR and will surface anything drop-elab missed.
        if !requires_init && is_state_fully_init(&leaf) {
            if let Ok(leaf_ty) = self.env.type_of_place(place, self.locals) {
                if self.env.class_of(&leaf_ty, &func.meta.params).implies(Marker::Drop) {
                    return;
                }
            }
        }

        let path_str = format_path(&root, &path);
        let expected = if requires_init {
            "initialized"
        } else {
            "uninitialized"
        };
        let actual = describe_state(&leaf);
        let mut diagnostic = diag(
            BorrowStateMismatch,
            source,
            func,
            block,
            format!(
                "cannot create {} of '{}': place must be {} at borrow, but is {}",
                kind_str, path_str, expected, actual
            ),
        );
        // Hint for `&out` / `&uninit` on Init non-Drop places: user
        // can't `drop X;` (type isn't Drop) so they must move the
        // value out first. Reachable only for non-Drop types — the
        // Drop-eligible case is silently drop-elaborated above.
        if !requires_init && is_state_fully_init(&leaf) {
            diagnostic = diagnostic.with_hint(format!(
                "move '{}' out first — linear values cannot be forgotten in place",
                path_str
            ));
        }
        d.push_error(diagnostic);
    }

    /// Verify a ghost `require_uninit place` assertion. Elaboration is
    /// responsible for inserting any cleanup needed to make this precondition
    /// true before the final checker runs. Once checked, the statement gives
    /// later analysis the postcondition that `place` is uninitialized.
    ///
    /// Requirements intentionally start with the same owned, statically
    /// trackable place domain as `state.refs`: locals and constant-index / field
    /// projections, but not dereferences or dynamic indices. HLL scope exits
    /// naturally emit roots in that domain. Broader projection semantics can
    /// be added with a corresponding place-state rule rather than silently
    /// widening the assertion.
    fn check_require_uninit(
        &self,
        func: &Function,
        block: &BasicBlock,
        place: &Place,
        source: SourceInfo,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some(owned) = as_owned_path(place) else {
            d.push_error(diag(
                RequireUninitNotSatisfied,
                source,
                func,
                block,
                format!(
                    "value '{}' must be fully uninitialized by this point, but its place is not statically trackable",
                    format_place(place)
                ),
            ));
            return;
        };
        let (root, path) = extract_path(&owned).expect("owned path has an init-state path");
        let Some(root_ty) = self.locals.get(&root) else {
            return;
        };
        let Some(root_state) = state.locals.get(&root) else {
            return;
        };

        let observed = read_at(root_state, root_ty, &path, self.env);
        let reason = match observed {
            InitState::NeverInit | InitState::Moved => None,
            // Partial records the history of independently tracked fields or
            // array slots. Once cleanup has consumed every initialized leaf,
            // a mixed NeverInit/Moved tree contains no owned value even
            // though it cannot be represented by either simple state alone.
            InitState::Partial(fields) if partial_is_uninit(&fields) => None,
            InitState::Init => Some("it is still initialized"),
            InitState::Partial(_) => Some("it is only partially consumed"),
            InitState::Diverged => Some("its state differs across control-flow paths"),
        };
        if let Some(reason) = reason {
            d.push_error(diag(
                RequireUninitNotSatisfied,
                source,
                func,
                block,
                format!(
                    "value '{}' must be fully uninitialized by this point, but {}",
                    format_place(place),
                    reason
                ),
            ));
        }

        // Check nested references before applying the requirement's recovery
        // postcondition. The postcondition removes their states, so checking
        // afterward would silently abandon any outstanding obligation.
        for (ref_place, rs) in state
            .refs
            .iter()
            .filter(|(ref_place, _)| is_ancestor_or_self(&owned, ref_place))
        {
            if rs.obligation_fulfilled() {
                continue;
            }
            let (cur, expected) = describe_obligation_mismatch(rs);
            let mut diagnostic = diag(
                RefObligationUnfulfilled,
                source,
                func,
                block,
                format!(
                    "reference '{}' has unfulfilled obligation: pointee is {}, but must be {}",
                    format_place(ref_place),
                    cur,
                    expected,
                ),
            );
            if let Some(decl_source) = ref_root_decl_source(func, ref_place) {
                diagnostic = diagnostic.with_secondary(decl_source, "reference declared here");
            }
            d.push_error(diagnostic);
        }
    }
}
