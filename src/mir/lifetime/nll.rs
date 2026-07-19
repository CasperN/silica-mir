//! NLL-style lifetime elaboration.
//!
//! Inserts explicit `unborrow` statements at ASAP last-use points for
//! each borrower Var. Post-elaboration, the lifetime checker sees a
//! program where every loan-closing point is syntactically explicit.
//!
//! Structure mirrors `substructural::drop_elaboration`:
//! - Plan (immutable): compute per-function insertions using backward
//!   liveness over borrower Vars.
//! - Apply (mutable): splice statements and split critical edges via
//!   `cfg_edit::split_edge`.
//!
//! ## Semantics
//!
//! A "borrower" is a local or parameter of any `&`/`&mut`/`&out`/`&drop`/
//! `&uninit` type. From the loan tracker's view all five kinds are
//! equally exclusive (per lifetime/mod.rs); NLL inserts at last use
//! without caring which kind.
//!
//! Backward liveness state = set of borrower names live at the point.
//! - **use**: any place whose root Var is a borrower — includes deref
//!   (`*r`), field/downcast projections, and the borrower appearing
//!   directly. Reading through `*r` keeps `r` live.
//! - **def**: an `Assign(Var(r), _)` with `r` a borrower. Redefinition
//!   kills the old binding.
//! - Transfer: `pre = (post - defs) ∪ uses`.
//!
//! ## Insertion decisions
//!
//! Intra-block, per statement S with borrower r:
//! - Skip if S naturally consumes r (moved as operand, `drop r`, existing
//!   `unborrow r`, or `r = ...` redefinition).
//! - Otherwise, if r ∈ live_before(S) and r ∉ live_after(S), S is r's
//!   last use — insert `unborrow r` immediately after S.
//!
//! Cross-edge, per block B and successor S with borrower r:
//! - If r ∈ live_out(B) but r ∉ live_in(S), r dies on this edge —
//!   split the B→S edge and place `unborrow r` in the split block.
//!
//! ## Idempotence
//!
//! An already-inserted `unborrow r` shows up as a natural consumer at
//! the same last-use point, so a second run of this pass finds no
//! transitions to insert at.
//!
//! ## Interactions
//!
//! - **Substructural drop elaboration** runs after this pass. NLL leaves
//!   borrowers `Moved` at their last-use point, so drop-elab won't try
//!   to double-consume them.
//! - **`&out`/`&drop` obligations**: NLL doesn't check them; it inserts
//!   at last use even if the obligation is unfulfilled. The lifetime
//!   check (post-elab) then surfaces the error at the inserted unborrow.

use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::cfg_edit;
use crate::mir::dataflow::{self, Analysis, Direction};
use crate::mir::type_check::{Env, TypeDecl};
use crate::mir::type_util::substitute_params;
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// Elaborate `program` in place: insert `unborrow` statements at every
/// borrower's last-use points. Idempotent.
pub fn elaborate(program: &mut Program, env: &Env) {
    // Plan (immutable): compute the per-function insertion set.
    let mut plans: IndexMap<String, ElaborationPlan> = IndexMap::new();
    for func in env.functions.values() {
        if let Some(plan) = plan_for_function(func, env) {
            plans.insert(func.name.clone(), plan);
        }
    }

    // Apply (mutable): splice the planned statements and edge splits.
    for decl in &mut program.declarations {
        let Declaration::Fn(func) = decl else {
            continue;
        };
        let Some(plan) = plans.get(&func.name) else {
            continue;
        };
        let Some(body) = &mut func.body else {
            continue;
        };
        apply_plan(body, plan);
    }
}

/// Planned insertions for a single function.
#[derive(Default, Debug)]
struct ElaborationPlan {
    /// `(block_label, insert_pos)` -> borrower places to unborrow at
    /// that position. `insert_pos` is an index into the *original*
    /// block's statements: 0 = before first stmt, N (num_stmts) =
    /// before terminator.
    intra_block: IndexMap<(String, usize), Vec<Place>>,
    /// `(pred_label, succ_label)` -> borrower places to unborrow on this
    /// edge. Apply by splitting the edge and appending the unborrows
    /// in the split block.
    cross_edge: IndexMap<(String, String), Vec<Place>>,
}

fn plan_for_function(func: &Function, env: &Env) -> Option<ElaborationPlan> {
    let body = func.body.as_ref()?;
    if body.blocks.is_empty() {
        return None;
    }

    let borrowers = collect_borrowers(func, env);
    if borrowers.is_empty() {
        return None;
    }

    // Return-reachability waiver: NLL only inserts cleanup on paths that
    // can reach a `return` terminator. Paths that only reach `abort` or
    // `unreachable` are considered "the program dies before the caller
    // could observe missing initialization" and skip elaboration.
    let return_reachable = body.return_reachable();

    let reborrow_parent = collect_reborrow_parents(body);
    let analysis = BorrowerLiveness {
        borrowers: &borrowers,
        reborrow_parent: &reborrow_parent,
    };
    let live_out_per_block = dataflow::run(&analysis, body);

    // Compute live_in per block by walking backward through the block.
    let mut live_in_per_block: IndexMap<String, BTreeSet<Place>> = IndexMap::new();
    for block in &body.blocks {
        let Some(live_out) = live_out_per_block.get(&block.label) else {
            continue;
        };
        let mut state = live_out.clone();
        analysis.transfer_terminator(&mut state, &block.terminator);
        for stmt in block.statements.iter().rev() {
            analysis.transfer_stmt(&mut state, stmt, stmt.span);
        }
        live_in_per_block.insert(block.label.clone(), state);
    }

    let mut plan = ElaborationPlan::default();

    for block in &body.blocks {
        let Some(live_out) = live_out_per_block.get(&block.label) else {
            continue;
        };

        // Per-statement live sets: live_states[i] = live before stmt i
        // for i in 0..n_stmts. live_states[n_stmts] = live before
        // terminator = live after last statement.
        let mut live_states: Vec<BTreeSet<Place>> =
            Vec::with_capacity(block.statements.len() + 1);
        let mut cur = live_out.clone();
        analysis.transfer_terminator(&mut cur, &block.terminator);
        live_states.push(cur.clone());
        for stmt in block.statements.iter().rev() {
            analysis.transfer_stmt(&mut cur, stmt, stmt.span);
            live_states.push(cur.clone());
        }
        live_states.reverse();

        // Return-reachability waiver: skip intra-block insertions in
        // blocks that only lead to abort/unreachable.
        let block_reaches_return = return_reachable.contains(&block.label);

        // Intra-block insertions. See notes on the two rules
        // (transition, bind-and-dead) in the pre-refactor version.
        if block_reaches_return {
            for (i, stmt) in block.statements.iter().enumerate() {
                let live_before = &live_states[i];
                let live_after = &live_states[i + 1];
                for r in &borrowers {
                    let transition = !stmt_consumes(stmt, r)
                        && live_before.contains(r)
                        && !live_after.contains(r);
                    let bind_dead = stmt_binds_borrower(stmt, r) && !live_after.contains(r);
                    if transition || bind_dead {
                        plan.intra_block
                            .entry((block.label.clone(), i + 1))
                            .or_default()
                            .push(r.clone());
                    }
                }
            }
        }

        // Cross-edge: for each successor, borrowers live at B's exit
        // but not entering that successor die on this edge. Skip when
        // the successor doesn't reach return — insertion there would
        // be dead code from the type system's perspective.
        let live_before_term = live_states.last().unwrap();
        for succ in terminator_successors(&block.terminator) {
            if !return_reachable.contains(succ) {
                continue;
            }
            let Some(succ_live_in) = live_in_per_block.get(succ) else {
                continue;
            };
            for r in &borrowers {
                if live_before_term.contains(r) && !succ_live_in.contains(r) {
                    plan.cross_edge
                        .entry((block.label.clone(), succ.to_string()))
                        .or_default()
                        .push(r.clone());
                }
            }
        }
    }

    // Ref-parameter rule: a param of ref type is bound at function
    // entry. If it's not in live_in(entry_block), it's created-but-
    // never-used and needs an unborrow at the very start of entry.
    // Skip if the entry block doesn't reach return — the whole function
    // diverges and static obligations are waived.
    let entry_label = body.blocks[0].label.clone();
    if return_reachable.contains(&entry_label) {
        if let Some(entry_live_in) = live_in_per_block.get(&entry_label) {
            for p in &func.params {
                let param_place = var_place(p.name.clone());
                if !borrowers.contains(&param_place) {
                    continue;
                }
                if !entry_live_in.contains(&param_place) {
                    plan.intra_block
                        .entry((entry_label.clone(), 0))
                        .or_default()
                        .push(param_place);
                }
            }
        }
    }

    // Order each unborrow group by reborrow depth (children first,
    // parents last). When s reborrows r and both end at the same
    // point, `unborrow s` must run before `unborrow r` — while s's
    // loan on `*r` is active, `unborrow r` would fail loan check.
    for group in plan.intra_block.values_mut() {
        sort_by_reborrow_depth_desc(group, &reborrow_parent);
    }
    for group in plan.cross_edge.values_mut() {
        sort_by_reborrow_depth_desc(group, &reborrow_parent);
    }

    Some(plan)
}

/// Sort borrower places in place so that reborrow children (higher
/// parent-chain depth) come first. Ties broken by Ord for determinism.
fn sort_by_reborrow_depth_desc(names: &mut [Place], parents: &IndexMap<Place, Place>) {
    names.sort_by(|a, b| {
        let da = reborrow_depth(a, parents);
        let db = reborrow_depth(b, parents);
        db.cmp(&da).then_with(|| a.cmp(b))
    });
}

fn reborrow_depth(name: &Place, parents: &IndexMap<Place, Place>) -> usize {
    let mut depth = 0;
    let mut cur = name.clone();
    let limit = parents.len() + 1;
    while let Some(p) = parents.get(&cur) {
        depth += 1;
        if depth > limit {
            break;
        }
        cur = p.clone();
    }
    depth
}

fn apply_plan(body: &mut FunctionBody, plan: &ElaborationPlan) {
    for block in &mut body.blocks {
        let mut inserts: Vec<(usize, &Vec<Place>)> = plan
            .intra_block
            .iter()
            .filter(|((label, _), _)| label == &block.label)
            .map(|((_, pos), v)| (*pos, v))
            .collect();
        inserts.sort_by(|a, b| b.0.cmp(&a.0));

        for (pos, places) in inserts {
            let span = block
                .statements
                .get(pos)
                .map(|s| s.span)
                .unwrap_or(block.terminator.span);
            let items: Vec<Statement> = places
                .iter()
                .map(|p| unborrow_stmt(p.clone(), span))
                .collect();
            block.statements.splice(pos..pos, items);
        }
    }

    for ((pred, succ), places) in &plan.cross_edge {
        // Use succ's span so diagnostics land on the branch being
        // cut off, not on the predecessor's branch terminator.
        let succ_span = body
            .blocks
            .iter()
            .find(|b| b.label == *succ)
            .map(|b| b.terminator.span)
            .unwrap_or_default();
        let split_label = cfg_edit::split_edge(body, pred, succ);
        let split_block = body
            .blocks
            .iter_mut()
            .find(|b| b.label == split_label)
            .expect("split_edge just guaranteed this block exists");
        for p in places {
            split_block
                .statements
                .push(unborrow_stmt(p.clone(), succ_span));
        }
    }
}

// ---------- Backward liveness ----------

/// Backward liveness with reborrow-parent expansion. When a borrower
/// place is added to the live set, we also add its reborrow parent
/// transitively. Both borrowers and their parents are owned paths
/// (Var, struct field, or enum-variant downcast); nothing here works
/// at the Var-name level.
struct BorrowerLiveness<'a> {
    borrowers: &'a BTreeSet<Place>,
    /// `s -> r` when `s = &kind *r` (both owned paths). Chased
    /// transitively when expanding uses.
    reborrow_parent: &'a IndexMap<Place, Place>,
}

impl<'a> BorrowerLiveness<'a> {
    fn add_use(&self, state: &mut BTreeSet<Place>, u: &Place) {
        if !self.borrowers.contains(u) {
            return;
        }
        if !state.insert(u.clone()) {
            return;
        }
        // Chase reborrow parents.
        let mut cur = u.clone();
        while let Some(parent) = self.reborrow_parent.get(&cur) {
            if !state.insert(parent.clone()) {
                break;
            }
            cur = parent.clone();
        }
    }
}

impl<'a> Analysis for BorrowerLiveness<'a> {
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
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement, _span: Span) {
        // Backward transfer: pre = (post - defs) ∪ uses.
        for def in stmt_defs(stmt) {
            // A def at `def` kills the borrower entry at `def` AND any
            // borrower descendants (assigning to `b` overwrites `b.p`,
            // etc.).
            state.retain(|b| !is_ancestor_or_self(&def, b));
        }
        for u in stmt_uses(stmt, self.borrowers) {
            self.add_use(state, &u);
        }
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        for u in terminator_uses(term, self.borrowers) {
            self.add_use(state, &u);
        }
    }
}

// ---------- Use / def / consume helpers ----------

/// Scan `body` for reborrow patterns `s = &kind *r` where both `s` and
/// `r` are owned paths, and build the `s -> r` relation. `r` may be
/// any owned path (Var, field, downcast) — not just Var.
fn collect_reborrow_parents(body: &FunctionBody) -> IndexMap<Place, Place> {
    let mut map = IndexMap::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(target, RValue::Ref(_, place)) = &stmt.kind {
                let Some(s) = as_owned_path(target) else {
                    continue;
                };
                // Walk through `Downcast`/`Field`/`Index` projections
                // to find an inner `Deref`. `r = &mut *p` and
                // `r = &mut (*p) as V` both reborrow p.
                if let Some(parent) = deref_ancestor(place) {
                    map.insert(s, parent);
                }
            }
        }
    }
    map
}

/// If `place` contains a `Deref(inner)` step somewhere along its path
/// (past only `Field`/`Downcast`/`Index` projections), and `inner` is
/// an owned path, return `inner` — the borrower whose pointee the
/// original place refers to. Returns `None` otherwise.
fn deref_ancestor(place: &Place) -> Option<Place> {
    let mut cur = place;
    loop {
        match cur {
            Place::Deref(inner) => return as_owned_path(inner),
            Place::Field(inner, _)
            | Place::Downcast(inner, _)
            | Place::Index(inner, _) => cur = inner,
            Place::Var(_) => return None,
        }
    }
}

/// Enumerate every ref-typed owned path in `func`. A path is included
/// if its inferred type is a `Type::Ref(...)`. Recursion through
/// self-referential type declarations is bounded by tracking visited
/// type names on each root walk.
fn collect_borrowers(func: &Function, env: &Env) -> BTreeSet<Place> {
    let mut out = BTreeSet::new();
    let locals = func.locals_map();
    for (name, ty) in &locals {
        let mut visited = BTreeSet::new();
        walk_ref_paths(&var_place(name.clone()), ty, env, &mut visited, &mut out);
    }
    out
}

/// Walk a place's type, adding owned-path descendants of ref type.
/// Stops at Ref boundaries (we don't traverse a reference's pointee).
/// The visited-set is a defensive cycle guard; by-value type recursion
/// is banned upstream by `layout::check_program`, so this can only fire
/// if someone bypasses the standard pipeline.
fn walk_ref_paths(
    place: &Place,
    ty: &Type,
    env: &Env,
    visited: &mut BTreeSet<String>,
    out: &mut BTreeSet<Place>,
) {
    if matches!(ty, Type::Ref(_, _, _)) {
        out.insert(place.clone());
        return;
    }
    let Type::Custom(name, _, args) = ty else { return };
    if !visited.insert(name.clone()) {
        return;
    }
    // Substitute the outer args through each field / variant type — a
    // `Bag<&mut i64>.r` recursion with the raw `Param(T)` would miss the
    // ref and drop the borrower from NLL's tracked set.
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => {
            let type_params = s.type_params.clone();
            let fields: Vec<_> = s
                .fields
                .iter()
                .map(|f| (f.name.clone(), substitute_params(&f.ty, &type_params, args)))
                .collect();
            for (fname, fty) in fields {
                let sub = field_place(place.clone(), fname);
                walk_ref_paths(&sub, &fty, env, visited, out);
            }
        }
        Some(TypeDecl::Enum(e)) => {
            let type_params = e.type_params.clone();
            let variants: Vec<_> = e
                .variants
                .iter()
                .map(|v| (v.name.clone(), substitute_params(&v.ty, &type_params, args)))
                .collect();
            for (vname, vty) in variants {
                let sub = downcast_place(place.clone(), vname);
                walk_ref_paths(&sub, &vty, env, visited, out);
            }
        }
        _ => {}
    }
    visited.remove(name);
}


/// Enumerate borrower places used by referencing `place`. Yields any
/// borrower that shares storage with `place`:
///   - Owned-path prefixes of `place` (touching a field touches its
///     enclosing struct/enum).
///   - Owned-path descendants of `place` (touching `b` touches `b.p`,
///     because moving/reading b covers b.p's storage).
///
/// Examples with borrower set containing `b.p` and `b.q`:
///   - `b`: yields `b.p`, `b.q` (moving b covers both fields).
///   - `b.p`: yields `b.p`.
///   - `*b.p`: yields `b.p` (dereffing b.p uses the ref itself).
fn place_borrower_uses(place: &Place, borrowers: &BTreeSet<Place>, out: &mut Vec<Place>) {
    let mut cur = place;
    loop {
        if let Some(owned) = as_owned_path(cur) {
            // Prefixes (including owned itself).
            for prefix in owned_path_prefixes(&owned) {
                if borrowers.contains(&prefix) {
                    out.push(prefix);
                }
            }
            // Descendants of owned that are borrowers. Storage-covered.
            for b in borrowers {
                if b != &owned && is_ancestor_or_self(&owned, b) {
                    out.push(b.clone());
                }
            }
            return;
        }
        match cur {
            Place::Deref(inner)
            | Place::Field(inner, _)
            | Place::Downcast(inner, _)
            | Place::Index(inner, _) => {
                cur = inner;
            }
            Place::Var(_) => unreachable!("Var is always owned"),
        }
    }
}

fn stmt_uses(stmt: &Statement, borrowers: &BTreeSet<Place>) -> Vec<Place> {
    let mut out = Vec::new();
    match &stmt.kind {
        StatementKind::Assign(target, rvalue) => {
            // If target isn't an owned path (e.g. deref target), or has
            // projections, its structural parts are uses.
            match target {
                Place::Var(_) => {}
                _ => place_borrower_uses(target, borrowers, &mut out),
            }
            rvalue_uses(rvalue, borrowers, &mut out);
        }
        StatementKind::Call(target, args) => {
            operand_uses(target, borrowers, &mut out);
            for a in args {
                operand_uses(a, borrowers, &mut out);
            }
        }
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            place_borrower_uses(place, borrowers, &mut out);
        }
    }
    out
}

fn stmt_defs(stmt: &Statement) -> Vec<Place> {
    if let StatementKind::Assign(target, _) = &stmt.kind {
        if let Some(owned) = as_owned_path(target) {
            return vec![owned];
        }
    }
    Vec::new()
}

fn rvalue_uses(rv: &RValue, borrowers: &BTreeSet<Place>, out: &mut Vec<Place>) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) => operand_uses(op, borrowers, out),
        // For borrower-liveness purposes `&raw place` is the same as
        // `& place`: it uses (and keeps live) any borrower mentioned
        // inside `place`. The raw-vs-safe distinction only affects
        // loan tracking, not borrower liveness.
        RValue::Ref(_, place) | RValue::RawRef(place) => {
            place_borrower_uses(place, borrowers, out)
        }
        RValue::ArrayLit(ops) => {
            for op in ops {
                operand_uses(op, borrowers, out);
            }
        }
    }
}

fn operand_uses(op: &Operand, borrowers: &BTreeSet<Place>, out: &mut Vec<Place>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            place_borrower_uses(place, borrowers, out);
        }
        Operand::Const(_) => {}
    }
}

fn terminator_uses(term: &Terminator, borrowers: &BTreeSet<Place>) -> Vec<Place> {
    let mut out = Vec::new();
    match &term.kind {
        TerminatorKind::Branch { cond, .. } => operand_uses(cond, borrowers, &mut out),
        TerminatorKind::SwitchEnum { place, .. } => {
            place_borrower_uses(place, borrowers, &mut out);
        }
        _ => {}
    }
    out
}

/// True iff `stmt` is `Assign(target, _)` where `target` is or contains
/// borrower `r` as an owned prefix — the statement binds a new value
/// covering r's storage. Used by the bind-and-dead rule to catch
/// created-then-never-used borrowers.
fn stmt_binds_borrower(stmt: &Statement, r: &Place) -> bool {
    if let StatementKind::Assign(target, _) = &stmt.kind {
        if let Some(owned) = as_owned_path(target) {
            return is_ancestor_or_self(&owned, r);
        }
    }
    false
}

/// True iff `stmt` naturally closes/consumes borrower `r`.
fn stmt_consumes(stmt: &Statement, r: &Place) -> bool {
    match &stmt.kind {
        StatementKind::Drop(place) | StatementKind::Unborrow(place) => {
            if let Some(owned) = as_owned_path(place) {
                is_ancestor_or_self(&owned, r)
            } else {
                false
            }
        }
        StatementKind::Assign(target, rvalue) => {
            // Redefinition of r (or an ancestor) consumes r's old value.
            if let Some(owned) = as_owned_path(target) {
                if is_ancestor_or_self(&owned, r) {
                    return true;
                }
            }
            rvalue_moves(rvalue, r)
        }
        StatementKind::Call(target, args) => {
            operand_moves(target, r) || args.iter().any(|a| operand_moves(a, r))
        }
    }
}

fn rvalue_moves(rv: &RValue, r: &Place) -> bool {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, _, op) => operand_moves(op, r),
        RValue::Ref(_, _) | RValue::RawRef(_) => false,
        RValue::ArrayLit(ops) => ops.iter().any(|op| operand_moves(op, r)),
    }
}

fn operand_moves(op: &Operand, r: &Place) -> bool {
    match op {
        Operand::Move(place) => match as_owned_path(place) {
            Some(owned) => is_ancestor_or_self(&owned, r),
            None => false,
        },
        _ => false,
    }
}

