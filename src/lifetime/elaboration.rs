//! NLL-style lifetime elaboration.
//!
//! Inserts explicit `unborrow` statements at ASAP last-use points for
//! each borrower Var. Post-elaboration, the lifetime checker sees a
//! program where every loan-closing point is syntactically explicit.
//!
//! Structure mirrors `substructural::elaboration`:
//! - Phase 1 (immutable): plan per-function insertions using backward
//!   liveness over borrower Vars.
//! - Phase 2 (mutable): apply the plan — inserting statements and
//!   splitting critical edges via `cfg_edit::split_edge`.
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

use crate::ast::*;
use crate::cfg_edit;
use crate::dataflow::{self, Analysis, Direction};
use crate::type_check::Env;
use indexmap::IndexMap;
use std::collections::BTreeSet;

/// Elaborate `program` in place: insert `unborrow` statements at every
/// borrower's last-use points. Idempotent.
pub fn elaborate(program: &mut Program, env: &Env) {
    // Phase 1 (immutable): plan per-function.
    let mut plans: IndexMap<String, ElaborationPlan> = IndexMap::new();
    for func in env.functions.values() {
        if let Some(plan) = plan_for_function(func) {
            plans.insert(func.name.clone(), plan);
        }
    }

    // Phase 2 (mutable): apply.
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
    /// `(block_label, insert_pos)` -> borrower names to unborrow at that
    /// position. `insert_pos` is an index into the *original* block's
    /// statements, semantically "insert before original stmt N", so:
    /// - 0 means before the first stmt (block entry).
    /// - N (where N = num_stmts) means before the terminator (block end).
    intra_block: IndexMap<(String, usize), Vec<String>>,
    /// `(pred_label, succ_label)` -> borrower names to unborrow on this
    /// edge. Apply by splitting the edge and appending the unborrows
    /// in the split block.
    cross_edge: IndexMap<(String, String), Vec<String>>,
}

fn plan_for_function(func: &Function) -> Option<ElaborationPlan> {
    let body = func.body.as_ref()?;
    if body.blocks.is_empty() {
        return None;
    }

    let borrowers = collect_borrowers(func);
    if borrowers.is_empty() {
        return None;
    }

    let reborrow_parent = collect_reborrow_parents(body);
    let analysis = BorrowerLiveness {
        borrowers: &borrowers,
        reborrow_parent: &reborrow_parent,
    };
    let live_out_per_block = dataflow::run(&analysis, body);

    // Compute live_in per block by walking backward through the block.
    let mut live_in_per_block: IndexMap<String, BTreeSet<String>> = IndexMap::new();
    for block in &body.blocks {
        let Some(live_out) = live_out_per_block.get(&block.label) else {
            continue;
        };
        let mut state = live_out.clone();
        analysis.transfer_terminator(&mut state, &block.terminator);
        for (stmt, _) in block.statements.iter().rev() {
            analysis.transfer_stmt(&mut state, stmt);
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
        let mut live_states: Vec<BTreeSet<String>> =
            Vec::with_capacity(block.statements.len() + 1);
        let mut cur = live_out.clone();
        analysis.transfer_terminator(&mut cur, &block.terminator);
        live_states.push(cur.clone());
        for (stmt, _) in block.statements.iter().rev() {
            analysis.transfer_stmt(&mut cur, stmt);
            live_states.push(cur.clone());
        }
        live_states.reverse();

        // Intra-block insertions.
        //
        // Two rules cover the general "borrower r is bound but not
        // future-used" state, both inserting immediately after the
        // triggering statement:
        //
        //   (a) Transition: r was live before S and dies at S without S
        //       consuming it — S is r's last actual use.
        //   (b) Bind-and-dead: S binds r (assigns to a borrower target)
        //       but r has no future use — a created-then-forgotten
        //       borrower. Without this rule the transition never fires
        //       because r wasn't live before S (kill via def).
        //
        // Bind and transition can't fire for the same (S, r): if S binds
        // r then live_before excludes r (def kills it in the backward
        // transfer), so the transition test's r ∈ live_before is false.
        for (i, (stmt, _)) in block.statements.iter().enumerate() {
            let live_before = &live_states[i];
            let live_after = &live_states[i + 1];
            for r in &borrowers {
                // Transition rule cares about the r that was live going
                // into S — skip if S consumes/redefines that binding.
                // The bind rule looks at the NEW r that S binds and
                // stands apart from consumption of the old.
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

        // Cross-edge: for each successor, borrowers live at B's exit
        // but not entering that successor die on this edge.
        let live_before_term = live_states.last().unwrap();
        for succ in terminator_successors(&block.terminator) {
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
    // (Mirrors the intra-block bind rule but for the pre-entry binding
    // that isn't a real statement.)
    let entry_label = body.blocks[0].label.clone();
    if let Some(entry_live_in) = live_in_per_block.get(&entry_label) {
        for p in &func.params {
            if !borrowers.contains(&p.name) {
                continue;
            }
            if !entry_live_in.contains(&p.name) {
                plan.intra_block
                    .entry((entry_label.clone(), 0))
                    .or_default()
                    .push(p.name.clone());
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

/// Sort names in place so that reborrow children (higher parent-chain
/// depth) come first. Ties broken by name for determinism.
fn sort_by_reborrow_depth_desc(names: &mut [String], parents: &IndexMap<String, String>) {
    names.sort_by(|a, b| {
        let da = reborrow_depth(a, parents);
        let db = reborrow_depth(b, parents);
        db.cmp(&da).then_with(|| a.cmp(b))
    });
}

fn reborrow_depth(name: &str, parents: &IndexMap<String, String>) -> usize {
    let mut depth = 0;
    let mut cur = name.to_string();
    let limit = parents.len() + 1;
    while let Some(p) = parents.get(&cur) {
        depth += 1;
        if depth > limit {
            break; // cycle guard — shouldn't happen for well-formed programs
        }
        cur = p.clone();
    }
    depth
}

fn apply_plan(body: &mut FunctionBody, plan: &ElaborationPlan) {
    // Intra-block: sort inserts by descending position and splice —
    // later positions go first so lower positions' indices stay valid.
    for block in &mut body.blocks {
        let mut inserts: Vec<(usize, &Vec<String>)> = plan
            .intra_block
            .iter()
            .filter(|((label, _), _)| label == &block.label)
            .map(|((_, pos), v)| (*pos, v))
            .collect();
        inserts.sort_by(|a, b| b.0.cmp(&a.0));

        for (pos, names) in inserts {
            // Span: use the original stmt at `pos` (i.e. the stmt the
            // unborrow is inserted just before). At end-of-block
            // (pos = num_stmts) or in empty blocks, use the terminator.
            let span = block
                .statements
                .get(pos)
                .map(|(_, s)| *s)
                .unwrap_or(block.terminator_span);
            let items: Vec<(Statement, Span)> = names
                .iter()
                .map(|n| (Statement::Unborrow(Place::Var(n.clone())), span))
                .collect();
            block.statements.splice(pos..pos, items);
        }
    }

    // Cross-edge: split the edge (idempotent, so repeated NLL runs share
    // the block), then append unborrows.
    for ((pred, succ), names) in &plan.cross_edge {
        let split_label = cfg_edit::split_edge(body, pred, succ);
        let split_block = body
            .blocks
            .iter_mut()
            .find(|b| b.label == split_label)
            .expect("split_edge just guaranteed this block exists");
        let span = split_block.terminator_span;
        for n in names {
            split_block
                .statements
                .push((Statement::Unborrow(Place::Var(n.clone())), span));
        }
    }
}

// ---------- Backward liveness ----------

/// Backward liveness with reborrow-parent expansion. When a borrower
/// `s` is added to the live set, we also add its reborrow parent
/// (`r` such that `s = &kind *r`) transitively. This is how NLL
/// keeps `r` alive across `s`'s lifetime — otherwise NLL would
/// insert `unborrow r` right after the reborrow, before `s`'s uses.
struct BorrowerLiveness<'a> {
    borrowers: &'a BTreeSet<String>,
    /// `s -> r` when `s = &kind *r`. Chased transitively when
    /// expanding uses. Built once by the plan phase.
    reborrow_parent: &'a IndexMap<String, String>,
}

impl<'a> BorrowerLiveness<'a> {
    fn add_use(&self, state: &mut BTreeSet<String>, u: &str) {
        if !self.borrowers.contains(u) {
            return;
        }
        state.insert(u.to_string());
        // Chase reborrow parents. Bounded by the number of borrowers
        // because each step goes to a distinct name.
        let mut cur = u.to_string();
        while let Some(parent) = self.reborrow_parent.get(&cur) {
            if !state.insert(parent.clone()) {
                break;
            }
            cur = parent.clone();
        }
    }
}

impl<'a> Analysis for BorrowerLiveness<'a> {
    type State = BTreeSet<String>;
    fn direction(&self) -> Direction {
        Direction::Backward
    }
    fn initial_state(&self) -> Self::State {
        BTreeSet::new()
    }
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        a.union(b).cloned().collect()
    }
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement) {
        // Backward transfer: pre = (post - defs) ∪ uses.
        for def in stmt_defs(stmt) {
            if self.borrowers.contains(&def) {
                state.remove(&def);
            }
        }
        for u in stmt_uses(stmt) {
            self.add_use(state, &u);
        }
    }
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator) {
        for u in terminator_uses(term) {
            self.add_use(state, &u);
        }
    }
}

// ---------- Use / def / consume helpers ----------

/// Scan `body` for reborrow patterns `s = &kind *r` and build the
/// `s -> r` relation. Only handles the simple case (`Deref(Var(r))`
/// as the borrowed place); deeper paths like `(*r).field` are out of
/// scope for this slice.
///
/// Overwrites are not tracked separately: if `s` is later assigned a
/// new reborrow or a fresh borrow, the map's value is overwritten with
/// the latest parent. Since we only need this for a *static* liveness
/// approximation (any use of s must also count as a use of whichever r
/// s is currently reborrowing), a single most-recent mapping is
/// coarser but safe — it treats s as live whenever any of its potential
/// parents would be live.
fn collect_reborrow_parents(body: &FunctionBody) -> IndexMap<String, String> {
    let mut map = IndexMap::new();
    for block in &body.blocks {
        for (stmt, _) in &block.statements {
            if let Statement::Assign(Place::Var(s), RValue::Ref(_, place)) = stmt {
                if let Place::Deref(inner) = place {
                    if let Place::Var(r) = inner.as_ref() {
                        map.insert(s.clone(), r.clone());
                    }
                }
            }
        }
    }
    map
}

fn collect_borrowers(func: &Function) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for p in &func.params {
        if matches!(p.ty, Type::Ref(_, _)) {
            out.insert(p.name.clone());
        }
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            if matches!(l.ty, Type::Ref(_, _)) {
                out.insert(l.name.clone());
            }
        }
    }
    out
}

/// Root Var name of a place, following through `Deref` (unlike
/// `extract_path`, which stops at ref boundaries). Every mention of
/// a borrower via `*r`, `r.f`, `r as V`, `(*r).f`, etc. is a use of r.
fn place_root(place: &Place) -> Option<String> {
    let mut cur = place;
    loop {
        match cur {
            Place::Var(name) => return Some(name.clone()),
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Deref(inner) => cur = inner,
        }
    }
}

fn stmt_uses(stmt: &Statement) -> Vec<String> {
    let mut out = Vec::new();
    match stmt {
        Statement::Assign(target, rvalue) => {
            // Whole-Var target is a def, not a use of the old value.
            // Anything more structured (field/downcast/deref) is a use
            // because the surrounding path must be alive.
            if !matches!(target, Place::Var(_)) {
                if let Some(root) = place_root(target) {
                    out.push(root);
                }
            }
            rvalue_uses(rvalue, &mut out);
        }
        Statement::Call(target, args) => {
            operand_uses(target, &mut out);
            for a in args {
                operand_uses(a, &mut out);
            }
        }
        Statement::Drop(place) | Statement::Unborrow(place) => {
            if let Some(root) = place_root(place) {
                out.push(root);
            }
        }
    }
    out
}

fn stmt_defs(stmt: &Statement) -> Vec<String> {
    if let Statement::Assign(Place::Var(x), _) = stmt {
        vec![x.clone()]
    } else {
        Vec::new()
    }
}

fn rvalue_uses(rv: &RValue, out: &mut Vec<String>) {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => operand_uses(op, out),
        RValue::Ref(_, place) => {
            if let Some(root) = place_root(place) {
                out.push(root);
            }
        }
    }
}

fn operand_uses(op: &Operand, out: &mut Vec<String>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if let Some(root) = place_root(place) {
                out.push(root);
            }
        }
        Operand::Const(_) => {}
    }
}

fn terminator_uses(term: &Terminator) -> Vec<String> {
    let mut out = Vec::new();
    match term {
        Terminator::Branch { cond, .. } => operand_uses(cond, &mut out),
        Terminator::SwitchEnum { place, .. } => {
            if let Some(root) = place_root(place) {
                out.push(root);
            }
        }
        _ => {}
    }
    out
}

/// True iff `stmt` is `Assign(Var(r), _)` — the statement binds a
/// new value to borrower `r`. Used by the bind-and-dead rule to catch
/// created-then-never-used borrowers, which don't produce a live→dead
/// transition (backward-liveness def kills them so they're never in
/// live_before). Redefinitions of an already-bound r trigger this too,
/// but the earlier binding's own last-use scan handles the old value.
fn stmt_binds_borrower(stmt: &Statement, r: &str) -> bool {
    matches!(stmt, Statement::Assign(Place::Var(name), _) if name == r)
}

/// True iff `stmt` naturally closes/consumes borrower `r`. If so, NLL
/// skips inserting an `unborrow r` at the transition — the statement
/// already handles it.
fn stmt_consumes(stmt: &Statement, r: &str) -> bool {
    match stmt {
        Statement::Drop(Place::Var(name)) if name == r => true,
        Statement::Unborrow(Place::Var(name)) if name == r => true,
        Statement::Assign(Place::Var(name), _) if name == r => true,
        Statement::Assign(_, rvalue) => rvalue_moves(rvalue, r),
        Statement::Call(target, args) => {
            operand_moves(target, r) || args.iter().any(|a| operand_moves(a, r))
        }
        _ => false,
    }
}

fn rvalue_moves(rv: &RValue, r: &str) -> bool {
    match rv {
        RValue::Use(op) | RValue::EnumConstr(_, _, op) => operand_moves(op, r),
        RValue::Ref(_, _) => false,
    }
}

fn operand_moves(op: &Operand, r: &str) -> bool {
    matches!(op, Operand::Move(Place::Var(name)) if name == r)
}

#[cfg(test)]
mod tests;
