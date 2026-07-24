use crate::diagnostics::Diagnostics;
use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::substructural::composition::class_of;
use crate::mir::type_check::Env;
use indexmap::IndexMap;

use super::analysis::{
    capture_carried_refs, describe_obligation_mismatch, describe_pointee_state, describe_state,
    extract_init_path, format_path, partial_is_uninit, read_at, run_fixpoint,
    split_at_outermost_deref, states_before_returns, InitState, InitStateCode::*, InitStateContext,
    PointState, RefState,
};

pub fn check_program(program: &Program, env: &Env, d: &mut Diagnostics) {
    for f in program.functions() {
        check_function(env, f, d);
    }
    check_return_leaks(program, env, d);
}

/// Return validation is part of the single final place-state check.
pub(super) fn check_return_leaks(program: &Program, env: &Env, d: &mut Diagnostics) {
    for (func, _body) in program.function_bodies() {
        let locals = func.locals_map();
        for (block, state) in states_before_returns(env, func) {
            check_return_state(env, func, block, &locals, &state, d);
        }
    }
}

fn check_return_state(
    env: &Env,
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
        let mut path = vec![var.clone()];
        let mut leaks = Vec::new();
        find_return_leaks(env, place_state, ty, &mut path, &mut leaks);
        for (leaked_path, leaked_ty) in leaks {
            let mut diagnostic = diag(
                ReturnValueLeak,
                block.terminator.span,
                func,
                block,
                format!(
                    "value '{}' of type {} is not consumed at return",
                    leaked_path, leaked_ty
                ),
            )
            .with_hint("linear values must be consumed or returned before function exit. Try moving or dropping it.");
            if let Some(span) =
                find_decl_span(func, leaked_path.split('.').next().unwrap_or(&leaked_path))
            {
                diagnostic = diagnostic.with_secondary(span, "variable declared here");
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
            block.terminator.span,
            func,
            block,
            format!(
                "reference '{}' has unfulfilled obligation at return: pointee is {}, but must be {}",
                format_place(place), cur, expected,
            ),
        );
        if let Some(span) = find_decl_span(func, place_root_var_name(place)) {
            diagnostic = diagnostic.with_secondary(span, "reference declared here");
        }
        d.push_error(diagnostic);
    }
}

fn find_return_leaks(
    env: &Env,
    state: &InitState,
    ty: &Type,
    path: &mut Vec<String>,
    out: &mut Vec<(String, Type)>,
) {
    match state {
        InitState::NeverInit | InitState::Moved => {}
        InitState::Init | InitState::Diverged => out.push((path.join("."), ty.clone())),
        InitState::Partial(fields) => {
            for (field_name, field_state) in fields {
                let Some(field_ty) = env.field_type(ty, field_name) else {
                    continue;
                };
                path.push(field_name.clone());
                find_return_leaks(env, field_state, &field_ty, path, out);
                path.pop();
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

pub(super) fn find_decl_span(func: &Function, name: &str) -> Option<Span> {
    if let Some(param) = func.params.iter().find(|param| param.name == name) {
        return Some(param.span);
    }
    func.body
        .as_ref()?
        .locals
        .iter()
        .find(|local| local.name == name)
        .map(|local| local.span)
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else {
        return;
    };
    if body.blocks.is_empty() {
        return;
    }

    let locals = func.locals_map();
    let ctx = InitStateContext {
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
/// leaf whose state is Init or Diverged. `Partial` recurses per-field;
/// `NeverInit`/`Moved` short-circuit (nothing to overwrite).
pub(super) fn walk_overwrite_leaves(
    state: &InitState,
    ty: &Type,
    env: &Env,
    path: &mut Vec<String>,
    report: &mut dyn FnMut(&[String], &Type),
) {
    match state {
        InitState::NeverInit | InitState::Moved => {}
        InitState::Init | InitState::Diverged => report(path, ty),
        InitState::Partial(fields) => {
            for (field_name, field_state) in fields {
                let Some(field_ty) = env.field_type(ty, field_name) else {
                    continue;
                };
                path.push(field_name.clone());
                walk_overwrite_leaves(field_state, &field_ty, env, path, report);
                path.pop();
            }
        }
    }
}

/// Locate the declaration span for the root Var of `ref_place`. Used
/// to attach a secondary "reference declared here" span to obligation
/// diagnostics — the primary span sits at the point of failure (the
/// return, drop, or overwrite), which repeats across every case in a
/// fixture and doesn't distinguish which reference was involved.
pub(super) fn ref_root_decl_span(func: &Function, ref_place: &Place) -> Option<Span> {
    let (root, _) = extract_path_with_deref(ref_place);
    for p in &func.params {
        if p.name == root {
            return Some(p.span);
        }
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            if l.name == root {
                return Some(l.span);
            }
        }
    }
    None
}

// ---------- Diagnostic pass ----------

impl<'a> InitStateContext<'a> {
    pub(super) fn check_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        for stmt in &block.statements {
            self.check_and_transfer_stmt(func, block, stmt, state, d);
        }
        self.check_and_transfer_terminator(func, block, state, d);
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
        let span = stmt.span;
        match &stmt.kind {
            StatementKind::Assign(target, rvalue) => {
                self.materialize_moved_ref(rvalue, state);
                // Capture ref-state entries to transfer via `move src`
                // BEFORE eval_rvalue runs. Cascade re-keys src.f → dst.f.
                let carried_refs = capture_carried_refs(target, rvalue, state);

                // Overwrite check runs BEFORE we mutate state: it looks
                // at the target's current state before the rvalue's
                // moves take effect, so that e.g. `y = move y.f` isn't
                // conflated (although that shape is not really valid).
                self.check_overwrite(func, block, target, span, state, d);

                self.eval_rvalue(func, block, rvalue, span, state, d);
                self.check_lhs_downcast(func, block, target, span, state, d);

                // Overwriting a bound ref var is a silent-forget of the
                // pointee obligation; error unless already fulfilled.
                self.close_ref_if_present(func, block, target, span, state, d);

                self.apply_target_write_state(
                    target,
                    rvalue,
                    carried_refs,
                    state,
                    Some((func, block, span, d)),
                );
            }
            StatementKind::Call(target, args) => {
                // Fire the call-boundary check BEFORE consumption so we
                // see each operand's live state. Every `move` operand
                // that carries a ref (or an aggregate containing one)
                // must be in its declared kind's entry state.
                if let Operand::Move(place) = target {
                    self.check_call_transfer(func, block, place, span, state, d);
                }
                self.eval_operand(func, block, target, span, state, d);
                for a in args {
                    if let Operand::Move(place) = a {
                        self.check_call_transfer(func, block, place, span, state, d);
                    }
                    self.eval_operand(func, block, a, span, state, d);
                }
            }
            StatementKind::Drop(place) => {
                // Read the place, then consume it. Same effect on state as
                // `move`. The substructural checker (separate pass) is the
                // one that will require the type to be Drop. For a ref-typed
                // Var, also verify the pointee obligation before forgetting.
                self.check_place_read(func, block, place, span, state, d);
                self.close_ref_if_present(func, block, place, span, state, d);
                self.apply_consume_state(place, state, Some((func, block, span, d)));
            }
            StatementKind::Unborrow(place) => {
                // Explicit end-of-loan. Requires the borrower to be Init
                // and its (is_init, ends_init) obligation fulfilled — both
                // checked by close_ref_if_present. Then consume the borrower.
                self.check_place_read(func, block, place, span, state, d);
                self.close_ref_if_present(func, block, place, span, state, d);
                self.apply_move(place, state);
            }
            StatementKind::RequireUninit(place) => {
                self.check_require_uninit(func, block, place, span, state, d);
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
        let ts = block.terminator.span;
        match &block.terminator.kind {
            TerminatorKind::Branch { cond, .. } => {
                self.eval_operand(func, block, cond, ts, state, d)
            }
            TerminatorKind::SwitchEnum { place, .. } => {
                // Discriminant read: no move, no consumption.
                self.check_place_read(func, block, place, ts, state, d);
                if split_at_outermost_deref(place).is_some() {
                    self.apply_deref_op(
                        place,
                        super::analysis::DerefOp::Read,
                        state,
                        Some((func, block, ts, d)),
                    );
                }
            }
            _ => {}
        }
    }

    fn eval_rvalue(
        &self,
        func: &Function,
        block: &BasicBlock,
        rv: &RValue,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        match rv {
            RValue::Use(op) | RValue::EnumConstr(_, _, _, op) | RValue::PtrCast(op, _) => {
                self.eval_operand(func, block, op, span, state, d);
            }
            RValue::Ref(kind, place) => {
                self.check_borrow_precondition(func, block, kind, place, span, state, d);
            }
            RValue::RawRef(_) => {
                // No precondition — raw pointers can point at any
                // state (init, uninit, moved). Aliasing/lifetime are
                // the programmer's responsibility.
            }
            RValue::ArrayLit(ops) => {
                for op in ops {
                    self.eval_operand(func, block, op, span, state, d);
                }
            }
        }
    }

    fn eval_operand(
        &self,
        func: &Function,
        block: &BasicBlock,
        op: &Operand,
        span: Span,
        state: &mut PointState,
        d: &mut Diagnostics,
    ) {
        self.check_operand_read(func, block, op, span, state, d);
        // Projected dereference operands carry their own pointee-state
        // transition. Owned operands use the ordinary locals-state transfer.
        match op {
            Operand::Copy(place) if split_at_outermost_deref(place).is_some() => {
                self.apply_deref_op(
                    place,
                    super::analysis::DerefOp::Read,
                    state,
                    Some((func, block, span, d)),
                );
            }
            Operand::Move(place) if split_at_outermost_deref(place).is_some() => {
                self.apply_deref_op(
                    place,
                    super::analysis::DerefOp::Move,
                    state,
                    Some((func, block, span, d)),
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
        span: Span,
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
        self.check_place_read(func, block, place, span, state, d);
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
        span: Span,
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
        let scope = func.meta.param_scope();
        walk_overwrite_leaves(
            &target_state,
            &target_ty,
            self.env,
            &mut Vec::new(),
            &mut |leaf_path, leaf_ty| {
                let c = class_of(leaf_ty, self.env, &scope);
                if !c.implies(Marker::Drop) {
                    let path_str = if leaf_path.is_empty() {
                        format_place(target)
                    } else {
                        format!("{}.{}", format_place(target), leaf_path.join("."))
                    };
                    d.push_error(diag(
                        OverwriteWithoutDrop,
                        span,
                        func,
                        block,
                        format!(
                            "cannot overwrite '{}': type {} is not Drop and the value is still live (consume it via `drop {}` first)",
                            path_str, leaf_ty, path_str
                        ),
                    ));
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
        span: Span,
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
                    span,
                    func,
                    block,
                    format!(
                        "reference '{}' has unfulfilled obligation: pointee is {}, but must be {}",
                        format_place(&v),
                        cur,
                        expected,
                    ),
                );
                if let Some(decl_span) = ref_root_decl_span(func, &v) {
                    diagnostic = diagnostic.with_secondary(decl_span, "reference declared here");
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
        span: Span,
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
                let mut diagnostic = diag(RefCallEntryMismatch, span, func, block, msg);
                if let Some(decl_span) = ref_root_decl_span(func, &v) {
                    diagnostic = diagnostic.with_secondary(decl_span, "reference declared here");
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
        span: Span,
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
        if !matches!(prefix_state, InitState::Init) {
            d.push_error(diag(
                WriteThroughUninitEnumProjection,
                span,
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
        span: Span,
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
        match leaf {
            InitState::Init => {}
            InitState::NeverInit => d.push_error(diag(
                UseBeforeInit,
                span,
                func,
                block,
                format!("variable '{}' is used before initialization", root),
            )),
            InitState::Moved => d.push_error(diag(
                UseAfterMove,
                span,
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
                    span,
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
                                    err = err
                                        .with_secondary(stmt.span, "initialized here on some path");
                                }
                            }
                        }
                    }
                }
                d.push_error(err);
            }
            InitState::Partial(_) => d.push_error(diag(
                UsePartiallyInit,
                span,
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
        span: Span,
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
                    span,
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
                matches!(current, InitState::Init)
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
                    span,
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
                matches!(leaf, InitState::Init)
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
                span,
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
            matches!(leaf, InitState::Init)
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
        if !requires_init && matches!(leaf, InitState::Init) {
            if let Ok(leaf_ty) = self.env.type_of_place(place, span, self.locals) {
                let scope = func.meta.param_scope();
                if class_of(&leaf_ty, self.env, &scope).implies(Marker::Drop) {
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
            span,
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
        if !requires_init && matches!(leaf, InitState::Init) {
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
        span: Span,
        state: &PointState,
        d: &mut Diagnostics,
    ) {
        let Some(owned) = as_owned_path(place) else {
            d.push_error(diag(
                RequireUninitNotSatisfied,
                span,
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
                span,
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
                span,
                func,
                block,
                format!(
                    "reference '{}' has unfulfilled obligation: pointee is {}, but must be {}",
                    format_place(ref_place),
                    cur,
                    expected,
                ),
            );
            if let Some(decl_span) = ref_root_decl_span(func, ref_place) {
                diagnostic = diagnostic.with_secondary(decl_span, "reference declared here");
            }
            d.push_error(diagnostic);
        }
    }
}
