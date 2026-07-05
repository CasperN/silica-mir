//! Initialization-state dataflow for local variables.
//!
//! Detects: use of uninitialized locals, use of moved-out locals, use where
//! the init state is inconsistent across control-flow paths, and use of a
//! partially-initialized struct.
//!
//! State per root Var is a small lattice: `NeverInit | Moved | Init |
//! Partial(map) | Diverged`. `Partial(map)` records per-field state for
//! struct-typed places; nested Partials are permitted so `p.q.r = ...`
//! refines the state of `p.q.r` specifically. Canonicalization collapses a
//! Partial whose fields are all in the same simple state.
//!
//! Deferred to follow-ups:
//!   * substructural-class-driven weakening at joins and leak check at
//!     `return`,
//!   * borrow init preconditions (`&out` requires uninit, etc.) and
//!     freeze/thaw state.
//!
//! Paths through `Deref` are not tracked (we don't follow references here).
//! Downcast-in-move sets the whole enum to `Moved` (enum atomicity, per
//! README). Downcast-in-write does not change enum state.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::tc::{Env, TypeDecl};
use std::collections::{BTreeMap, HashMap, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
enum InitState {
    NeverInit,
    Moved,
    Init,
    /// Per-field state for a struct. Field list is complete when this
    /// variant is constructed. Nested Partials permitted for struct fields.
    Partial(BTreeMap<String, InitState>),
    /// Predecessors disagreed on the state at some CFG join.
    Diverged,
}

type PointState = HashMap<String, InitState>;

struct Ctx<'a> {
    env: &'a Env,
    locals: &'a HashMap<String, Type>,
}

// ---------- Type lookups ----------

fn struct_fields_of<'a>(ty: &Type, env: &'a Env) -> Option<&'a [StructField]> {
    let Type::Custom(name) = ty else { return None; };
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => Some(&s.fields),
        _ => None,
    }
}

fn enum_variant_payload_ty(ty: &Type, variant: &str, env: &Env) -> Option<Type> {
    let Type::Custom(name) = ty else { return None; };
    match env.types.get(name) {
        Some(TypeDecl::Enum(e)) => e.variants.iter()
            .find(|v| v.name == variant)
            .map(|v| v.ty.clone()),
        _ => None,
    }
}

// ---------- Canonicalization ----------

/// If a `Partial` has all fields at the same simple (non-Partial) state,
/// collapse to that state. Applied recursively to nested Partials.
fn canonicalize(state: InitState) -> InitState {
    if let InitState::Partial(mut m) = state {
        for v in m.values_mut() {
            let taken = std::mem::replace(v, InitState::NeverInit);
            *v = canonicalize(taken);
        }
        if m.is_empty() {
            return InitState::Init;
        }
        let first = m.values().next().unwrap().clone();
        let uniform = m.values().all(|v| *v == first);
        if uniform && !matches!(first, InitState::Partial(_)) {
            return first;
        }
        InitState::Partial(m)
    } else {
        state
    }
}

// ---------- Expansion ----------

/// Convert a uniform state to a Partial map with each of `fields` set to a
/// clone of the original state. Used when a field-refining transition needs
/// to see per-field granularity.
fn expand_uniform(state: &InitState, fields: &[StructField]) -> BTreeMap<String, InitState> {
    fields
        .iter()
        .map(|f| (f.name.clone(), state.clone()))
        .collect()
}

// ---------- Joins ----------

fn join_state(a: &InitState, b: &InitState) -> InitState {
    if a == b {
        return a.clone();
    }
    // Try to join field-wise when at least one side is Partial.
    match (a, b) {
        (InitState::Partial(ma), InitState::Partial(mb)) => {
            join_partials(ma, mb)
        }
        (InitState::Partial(ma), other) => {
            let mb = expand_from_partial_keys(other, ma);
            join_partials(ma, &mb)
        }
        (other, InitState::Partial(mb)) => {
            let ma = expand_from_partial_keys(other, mb);
            join_partials(&ma, mb)
        }
        _ => InitState::Diverged,
    }
}

fn expand_from_partial_keys(
    state: &InitState,
    template: &BTreeMap<String, InitState>,
) -> BTreeMap<String, InitState> {
    template
        .keys()
        .map(|k| (k.clone(), state.clone()))
        .collect()
}

fn join_partials(
    ma: &BTreeMap<String, InitState>,
    mb: &BTreeMap<String, InitState>,
) -> InitState {
    let mut out = BTreeMap::new();
    for (k, va) in ma {
        let vb = mb.get(k).cloned().unwrap_or(InitState::NeverInit);
        out.insert(k.clone(), join_state(va, &vb));
    }
    for (k, vb) in mb {
        if !ma.contains_key(k) {
            out.insert(k.clone(), vb.clone());
        }
    }
    canonicalize(InitState::Partial(out))
}

fn join_point(a: &PointState, b: &PointState) -> PointState {
    a.iter()
        .map(|(name, sa)| {
            let sb = b.get(name).cloned().unwrap_or(InitState::NeverInit);
            (name.clone(), join_state(sa, &sb))
        })
        .collect()
}

// ---------- Path walks ----------

/// Apply a write of `leaf_state` at the given path from `state` (which is
/// the current state of the root Var). Promotes intermediate states to
/// Partial as needed. Downcast steps in a write path do not update state.
fn write_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env, leaf_state: InitState) {
    if path.is_empty() {
        *state = leaf_state;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = struct_fields_of(ty, env) else { return; };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields.iter().find(|fd| fd.name == *f).map(|fd| fd.ty.clone());
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    write_at(field_state, &field_ty, &path[1..], env, leaf_state);
                }
            }
        }
        PathStep::Downcast(_) => {
            // Direct write into a variant payload does not initialize the
            // enum in our model (enum construction goes via `Name::V(...)`).
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Apply a move at the given path. Downcast steps set the whole enum to
/// `Moved` (enum atomicity).
fn move_at(state: &mut InitState, ty: &Type, path: &[PathStep], env: &Env) {
    if path.is_empty() {
        *state = InitState::Moved;
        return;
    }
    match &path[0] {
        PathStep::Field(f) => {
            let Some(fields) = struct_fields_of(ty, env) else { return; };
            if !matches!(state, InitState::Partial(_)) {
                *state = InitState::Partial(expand_uniform(state, fields));
            }
            let field_ty = fields.iter().find(|fd| fd.name == *f).map(|fd| fd.ty.clone());
            if let (Some(field_ty), InitState::Partial(map)) = (field_ty, &mut *state) {
                if let Some(field_state) = map.get_mut(f) {
                    move_at(field_state, &field_ty, &path[1..], env);
                }
            }
        }
        PathStep::Downcast(_) => {
            *state = InitState::Moved;
        }
    }
    let taken = std::mem::replace(state, InitState::NeverInit);
    *state = canonicalize(taken);
}

/// Return the effective state at the given path (for a read check).
fn read_at(state: &InitState, ty: &Type, path: &[PathStep], env: &Env) -> InitState {
    if path.is_empty() {
        return state.clone();
    }
    match &path[0] {
        PathStep::Field(f) => match state {
            InitState::Init
            | InitState::NeverInit
            | InitState::Moved
            | InitState::Diverged => state.clone(),
            InitState::Partial(map) => {
                let field_ty = struct_fields_of(ty, env)
                    .and_then(|fs| fs.iter().find(|fd| fd.name == *f))
                    .map(|fd| fd.ty.clone());
                let field_state = map.get(f).cloned().unwrap_or(InitState::NeverInit);
                match field_ty {
                    Some(ft) => read_at(&field_state, &ft, &path[1..], env),
                    None => field_state,
                }
            }
        },
        PathStep::Downcast(v) => match state {
            InitState::NeverInit | InitState::Moved | InitState::Diverged => state.clone(),
            InitState::Init | InitState::Partial(_) => {
                // Enum atomicity: if the enum is Init, the payload is Init.
                // (Partial on an enum is not expected but we treat it like Init.)
                let payload_ty = enum_variant_payload_ty(ty, v, env);
                match payload_ty {
                    Some(pt) => read_at(&InitState::Init, &pt, &path[1..], env),
                    None => InitState::Init,
                }
            }
        },
    }
}

// ---------- Top-level pipeline ----------

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for f in env.functions.values() {
        check_function(env, f, d);
    }
}

fn check_function(env: &Env, func: &Function, d: &mut Diagnostics) {
    let Some(body) = &func.body else { return; };
    if body.blocks.is_empty() { return; }

    let locals = collect_locals(func, body);
    let ctx = Ctx { env, locals: &locals };
    let entry_states = compute_entry_states(&ctx, func, body);

    for block in &body.blocks {
        let Some(entry) = entry_states.get(&block.label) else { continue; };
        let mut state = entry.clone();
        check_block(&ctx, func, block, &mut state, d);
    }
}

fn collect_locals(func: &Function, body: &FunctionBody) -> HashMap<String, Type> {
    let mut m = HashMap::new();
    for p in &func.params { m.insert(p.name.clone(), p.ty.clone()); }
    for l in &body.locals { m.insert(l.name.clone(), l.ty.clone()); }
    m
}

fn initial_state(func: &Function, body: &FunctionBody, env: &Env) -> PointState {
    let mut s = PointState::new();
    for p in &func.params {
        s.insert(p.name.clone(), InitState::Init);
    }
    for l in &body.locals {
        // A struct with zero declared fields is trivially initialized —
        // there's nothing to write. Same for any type reducing to one.
        let init = if is_trivially_init(&l.ty, env) {
            InitState::Init
        } else {
            InitState::NeverInit
        };
        s.insert(l.name.clone(), init);
    }
    s
}

fn is_trivially_init(ty: &Type, env: &Env) -> bool {
    match ty {
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => s.fields.is_empty(),
            _ => false,
        },
        _ => false,
    }
}

fn compute_entry_states(
    ctx: &Ctx,
    func: &Function,
    body: &FunctionBody,
) -> HashMap<String, PointState> {
    let mut states: HashMap<String, PointState> = HashMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), initial_state(func, body, ctx.env));
    worklist.push_back(entry_label);

    let blocks_by_label: HashMap<&str, &BasicBlock> =
        body.blocks.iter().map(|b| (b.label.as_str(), b)).collect();

    while let Some(label) = worklist.pop_front() {
        let block = blocks_by_label[label.as_str()];
        let mut state = states[&label].clone();
        for (stmt, _) in &block.statements {
            transfer_stmt(ctx, stmt, &mut state);
        }
        transfer_terminator(ctx, &block.terminator, &mut state);

        for succ in successors(&block.terminator) {
            if !blocks_by_label.contains_key(succ) { continue; }
            let new_state = match states.get(succ) {
                None => state.clone(),
                Some(existing) => join_point(existing, &state),
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

// ---------- Transfer (state updates) ----------

fn transfer_stmt(ctx: &Ctx, stmt: &Statement, state: &mut PointState) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            apply_rvalue_moves(ctx, rvalue, state);
            apply_write(ctx, target, state, InitState::Init);
        }
        Statement::Call(target, args) => {
            apply_operand_move(ctx, target, state);
            for a in args {
                apply_operand_move(ctx, a, state);
            }
        }
    }
}

fn transfer_terminator(ctx: &Ctx, term: &Terminator, state: &mut PointState) {
    if let Terminator::Branch { cond, .. } = term {
        apply_operand_move(ctx, cond, state);
    }
}

fn apply_rvalue_moves(ctx: &Ctx, rv: &RValue, state: &mut PointState) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => apply_operand_move(ctx, op, state),
        RValue::Ref(_, _) => {}
    }
}

fn apply_operand_move(ctx: &Ctx, op: &Operand, state: &mut PointState) {
    if let Operand::Move(place) = op {
        apply_move(ctx, place, state);
    }
}

fn apply_write(ctx: &Ctx, place: &Place, state: &mut PointState, leaf: InitState) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let root_state = state.entry(root).or_insert(InitState::NeverInit);
    write_at(root_state, &root_ty, &path, ctx.env, leaf);
}

fn apply_move(ctx: &Ctx, place: &Place, state: &mut PointState) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let root_state = state.entry(root).or_insert(InitState::NeverInit);
    move_at(root_state, &root_ty, &path, ctx.env);
}

// ---------- Diagnostic pass ----------

fn check_block(ctx: &Ctx, func: &Function, block: &BasicBlock, state: &mut PointState, d: &mut Diagnostics) {
    for (stmt, span) in &block.statements {
        check_and_transfer_stmt(ctx, func, block, stmt, *span, state, d);
    }
    check_and_transfer_terminator(ctx, func, block, state, d);
}

/// Combined check + transfer. Operands are consumed left-to-right so that a
/// later operand in the same statement sees the state after prior moves —
/// this is what makes `call f(move x, copy x)` correctly error on the second
/// operand.
fn check_and_transfer_stmt(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    stmt: &Statement,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    match stmt {
        Statement::Assign(target, rvalue) => {
            eval_rvalue(ctx, func, block, rvalue, span, state, d);
            check_lhs_downcast(ctx, func, block, target, span, state, d);
            apply_write(ctx, target, state, InitState::Init);
        }
        Statement::Call(target, args) => {
            eval_operand(ctx, func, block, target, span, state, d);
            for a in args {
                eval_operand(ctx, func, block, a, span, state, d);
            }
        }
    }
}

fn check_and_transfer_terminator(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    let ts = block.terminator_span;
    match &block.terminator {
        Terminator::Branch { cond, .. } => eval_operand(ctx, func, block, cond, ts, state, d),
        Terminator::SwitchEnum { place, .. } => {
            // Discriminant read: no move, no consumption.
            check_place_read(ctx, func, block, place, ts, state, d);
        }
        _ => {}
    }
}

fn eval_rvalue(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    rv: &RValue,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => {
            eval_operand(ctx, func, block, op, span, state, d);
        }
        RValue::Ref(_, _) => {}
    }
}

fn eval_operand(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    op: &Operand,
    span: Span,
    state: &mut PointState,
    d: &mut Diagnostics,
) {
    check_operand_read(ctx, func, block, op, span, state, d);
    apply_operand_move(ctx, op, state);
}

fn check_operand_read(
    ctx: &Ctx,
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
    check_place_read(ctx, func, block, place, span, state, d);
}

/// If the LHS path contains a `Downcast`, the enum being downcast must be
/// `Init` at that point — you can't refine an uninitialized enum by writing
/// through a variant projection. Enum construction goes via `Name::V(...)`.
fn check_lhs_downcast(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(idx) = path.iter().position(|s| matches!(s, PathStep::Downcast(_))) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let Some(root_state) = state.get(&root) else { return; };
    let prefix_state = read_at(root_state, &root_ty, &path[..idx], ctx.env);
    if !matches!(prefix_state, InitState::Init) {
        d.errors.push(format!(
            "at {}: In function '{}', block '{}': cannot write through variant projection: '{}' is not initialized here",
            span, func.name, block.label, root
        ));
    }
}

fn check_place_read(
    ctx: &Ctx,
    func: &Function,
    block: &BasicBlock,
    place: &Place,
    span: Span,
    state: &PointState,
    d: &mut Diagnostics,
) {
    let Some((root, path)) = extract_path(place) else { return; };
    let Some(root_ty) = ctx.locals.get(&root).cloned() else { return; };
    let Some(root_state) = state.get(&root) else { return; };
    let leaf = read_at(root_state, &root_ty, &path, ctx.env);
    match leaf {
        InitState::Init => {}
        InitState::NeverInit => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' is used before initialization",
            span, func.name, block.label, root
        )),
        InitState::Moved => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' is used after move",
            span, func.name, block.label, root
        )),
        InitState::Diverged => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' may be used before initialization or after move (state inconsistent across paths)",
            span, func.name, block.label, root
        )),
        InitState::Partial(_) => d.errors.push(format!(
            "at {}: In function '{}', block '{}': variable '{}' is not fully initialized here",
            span, func.name, block.label, root
        )),
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Baseline (unchanged from phase 1) ----------

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
        assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
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
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    #[test]
    fn join_disagreement_produces_diverged_error() {
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
        assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
    }

    // ---------- Partial init ----------

    #[test]
    fn field_writes_complete_init_ok() {
        // Writing every declared field of a struct-typed local promotes it
        // to fully Init.
        assert_no_diagnostics(
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
    }

    #[test]
    fn partial_field_write_leaves_root_partial_error() {
        // Only one field written; the whole struct is not fully init and
        // reading it errors.
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              q: P;
              entry:
                p.x = 1;
                q = copy p;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is not fully initialized here"]);
    }

    #[test]
    fn read_uninit_field_of_partial_struct_error() {
        // Field-granular: writing p.x doesn't init p.y — reading p.y errors.
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f() {
              p: P;
              a: number;
              entry:
                p.x = 1;
                a = copy p.y;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is used before initialization"]);
    }

    #[test]
    fn move_of_field_leaves_other_fields_init_ok() {
        // Struct comes in fully-init from a param; moving one field must
        // leave the other still readable.
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            fn f(p: P) {
              a: number;
              b: number;
              entry:
                a = move p.x;
                b = copy p.y;
                return
            }
            ",
        );
    }

    #[test]
    fn move_of_field_then_read_that_field_error() {
        let (errs, _) = run(
            "
            struct P { x: number y: number }
            fn f(p: P) {
              a: number;
              b: number;
              entry:
                a = move p.x;
                b = copy p.x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'p' is used after move"]);
    }

    #[test]
    fn nested_field_writes_complete_init_ok() {
        // Inner struct fields inited via nested paths; the whole outer
        // struct collapses to Init once every leaf is written.
        assert_no_diagnostics(
            "
            struct Inner { a: number b: number }
            struct Outer { i: Inner c: number }
            fn f() {
              o: Outer;
              n: number;
              entry:
                o.i.a = 1;
                o.i.b = 2;
                o.c = 3;
                n = copy o.i.a;
                return
            }
            ",
        );
    }

    #[test]
    fn nested_partial_read_of_uninit_inner_field_error() {
        let (errs, _) = run(
            "
            struct Inner { a: number b: number }
            struct Outer { i: Inner c: number }
            fn f() {
              o: Outer;
              n: number;
              entry:
                o.i.a = 1;
                o.c = 3;
                n = copy o.i.b;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    #[test]
    fn whole_struct_assign_after_partial_ok() {
        // Even if we partially init, a whole-struct assign resets to Init.
        assert_no_diagnostics(
            "
            struct P { x: number y: number }
            fn f(src: P) {
              p: P;
              a: number;
              entry:
                p.x = 1;
                p = move src;
                a = copy p.y;
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
    fn aborting_predecessor_doesnt_pollute_join() {
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
        assert_errors_contain(&errs, &["variable 'b' is used before initialization"]);
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
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    // ---------- Projections ----------

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
        assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
    }

    #[test]
    fn deref_read_is_not_checked() {
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

    // ---------- Downcast writes ----------

    #[test]
    fn downcast_write_on_init_enum_ok() {
        // Writing through a variant projection is fine when the enum is
        // Init AND refined to the correct variant.
        assert_no_diagnostics(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: s]
              s:
                o as Some = 7;
                return
              n: return
            }
            ",
        );
    }

    #[test]
    fn downcast_write_on_uninit_enum_error() {
        // Enum construction goes via `Name::V(...)`; refining an uninit
        // enum by writing a variant payload is not allowed.
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f() {
              o: Option;
              entry:
                o as Some = 7;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot write through variant projection: 'o' is not initialized here"],
        );
    }

    #[test]
    fn downcast_write_on_moved_enum_error() {
        let (errs, _) = run(
            "
            enum Option { None: unit Some: number }
            fn f(o: Option) {
              sink: Option;
              entry:
                sink = move o;
                o as Some = 7;
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &["cannot write through variant projection: 'o' is not initialized here"],
        );
    }

    // ---------- Empty struct ----------

    #[test]
    fn empty_struct_local_starts_init() {
        // A struct with zero fields has no components to write, so a
        // declared local of that type is trivially usable.
        assert_no_diagnostics(
            "
            struct Unit0 { }
            fn f() {
              u: Unit0;
              v: Unit0;
              entry:
                v = copy u;
                return
            }
            ",
        );
    }

    // ---------- Calls ----------

    #[test]
    fn call_target_of_uninit_error() {
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
        assert_errors_contain(&errs, &["variable 'x' is used before initialization"]);
    }

    // ---------- Loops ----------

    #[test]
    fn loop_backedge_agrees_ok() {
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

    // ---------- Reassignment / move ordering ----------

    #[test]
    fn reassign_after_move_ok() {
        assert_no_diagnostics(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                x = 42;
                z = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn move_then_move_error() {
        let (errs, _) = run(
            "
            fn f(x: number) {
              y: number;
              z: number;
              entry:
                y = move x;
                z = move x;
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    #[test]
    fn call_args_copy_then_move_ok() {
        // Copy first, then move — the copy sees Init, the move consumes.
        assert_no_diagnostics(
            "
            extern fn take_two(a: number, b: number);
            fn f(x: number) {
              entry:
                call take_two(copy x, move x);
                return
            }
            ",
        );
    }

    #[test]
    fn call_args_move_then_copy_error() {
        // Left-to-right operand evaluation: the second `copy` sees the
        // already-moved state and errors.
        let (errs, _) = run(
            "
            extern fn take_two(a: number, b: number);
            fn f(x: number) {
              entry:
                call take_two(move x, copy x);
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["variable 'x' is used after move"]);
    }

    // ---------- Loops ----------

    #[test]
    fn loop_may_reach_uninit_error() {
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
        assert_errors_contain(&errs, &["variable 'x' may be used before initialization"]);
    }
}
