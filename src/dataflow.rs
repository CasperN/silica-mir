//! Generic worklist-driven CFG dataflow analysis.
//!
//! An `Analysis` provides a `State` lattice, direction, transfer functions,
//! and lattice join. `run` computes the fixed point.
//!
//! `run` returns the state at each block's "start point" wrt direction:
//!   * Forward: state at block entry (before the first statement).
//!   * Backward: state at block exit (after the terminator).
//!
//! Diagnostic emission is not part of the framework — passes typically
//! compute the fixed point silently, then re-walk each block starting
//! from the recorded state to emit diagnostics. For Forward analyses
//! whose diagnostic walk fits the "check preconditions at a program
//! point, then advance" shape, `walk_forward` supplies the loop so
//! the pass only writes the visitor.
//!
//! The fixpoint terminates provided the state lattice has finite height
//! along each ascending chain (the standard requirement).

use crate::ast::*;
use indexmap::IndexMap;
use std::collections::VecDeque;

pub enum Direction {
    Forward,
    Backward,
}

pub trait Analysis {
    /// Lattice element.
    type State: Clone + Eq;

    fn direction(&self) -> Direction;

    /// Seed state at the analysis start wrt direction:
    ///   * Forward: entry block's entry state.
    ///   * Backward: exit blocks' (Return/Abort/Unreachable) exit state.
    fn initial_state(&self) -> Self::State;

    /// Lattice join. Must be commutative, associative, and monotonic.
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State;

    /// Apply the statement's forward semantics. Framework iterates
    /// backward internally for backward direction.
    fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement);

    /// Apply the terminator's forward semantics.
    fn transfer_terminator(&self, state: &mut Self::State, term: &Terminator);

    /// Optionally refine `state` when propagating along an outgoing edge
    /// `block -> succ_label`. Default: no refinement. Used e.g. by
    /// `variant_flow` to pin a place to a specific enum variant on a
    /// `switchEnum` arm edge.
    fn refine_edge(&self, _state: &mut Self::State, _block: &BasicBlock, _succ_label: &str) {}
}

/// Fixed-point state at each block's start-wrt-direction.
pub type Results<S> = IndexMap<String, S>;

pub fn run<A: Analysis>(analysis: &A, body: &FunctionBody) -> Results<A::State> {
    if body.blocks.is_empty() {
        return IndexMap::new();
    }
    match analysis.direction() {
        Direction::Forward => run_forward(analysis, body),
        Direction::Backward => run_backward(analysis, body),
    }
}

/// A program point visited by [`walk_forward`]. Fields are all `pub`
/// for visitor destructuring; `#[allow(dead_code)]` because no current
/// visitor destructures every field, but they're API for callers.
#[allow(dead_code)]
pub enum WalkPoint<'a, S> {
    /// State just before `stmt` runs, in a forward walk.
    Stmt {
        state: &'a S,
        block: &'a BasicBlock,
        stmt: &'a Statement,
        span: Span,
    },
    /// State just before the terminator runs, in a forward walk.
    Terminator {
        state: &'a S,
        block: &'a BasicBlock,
        term: &'a Terminator,
        span: Span,
    },
}

/// Second-pass helper for Forward analyses. Walks each block (skipping
/// unreachable ones — i.e. those absent from `results`) starting from its
/// recorded entry state, calling `visit` at each program point BEFORE the
/// corresponding transfer runs, then advancing state via
/// `transfer_stmt` / `transfer_terminator`.
///
/// Passes whose diagnostics can be expressed as "check preconditions at
/// each program point, then advance" (e.g. `variant_flow`) can call this
/// instead of writing their own walk loop. Passes with finer-grained
/// interleaving of check and transfer (e.g. `init_state`, whose Call
/// handling checks operand N against state after operand N-1's move)
/// still write their own walk.
///
/// Backward walks are more subtle (state at exit vs. entry, reversed
/// iteration) and are intentionally not offered here; add a walker for
/// them when a real consumer needs one.
pub fn walk_forward<A, F>(
    analysis: &A,
    body: &FunctionBody,
    results: &Results<A::State>,
    mut visit: F,
) where
    A: Analysis,
    F: FnMut(WalkPoint<'_, A::State>),
{
    assert!(
        matches!(analysis.direction(), Direction::Forward),
        "walk_forward requires a Forward analysis"
    );
    for block in &body.blocks {
        let Some(entry) = results.get(&block.label) else {
            continue;
        };
        let mut state = entry.clone();
        for (stmt, span) in &block.statements {
            visit(WalkPoint::Stmt {
                state: &state,
                block,
                stmt,
                span: *span,
            });
            analysis.transfer_stmt(&mut state, stmt);
        }
        visit(WalkPoint::Terminator {
            state: &state,
            block,
            term: &block.terminator,
            span: block.terminator_span,
        });
        analysis.transfer_terminator(&mut state, &block.terminator);
    }
}

fn run_forward<A: Analysis>(analysis: &A, body: &FunctionBody) -> Results<A::State> {
    let mut states: Results<A::State> = IndexMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();

    let entry_label = body.blocks[0].label.clone();
    states.insert(entry_label.clone(), analysis.initial_state());
    worklist.push_back(entry_label);

    let blocks_by_label = body.blocks_by_label();

    while let Some(label) = worklist.pop_front() {
        let block = blocks_by_label[label.as_str()];
        let mut state = states[&label].clone();
        for (stmt, _) in &block.statements {
            analysis.transfer_stmt(&mut state, stmt);
        }
        analysis.transfer_terminator(&mut state, &block.terminator);

        for succ in terminator_successors(&block.terminator) {
            if !blocks_by_label.contains_key(succ) {
                continue;
            }
            let mut succ_state = state.clone();
            analysis.refine_edge(&mut succ_state, block, succ);
            let new_state = match states.get(succ) {
                None => succ_state,
                Some(existing) => analysis.join(existing, &succ_state),
            };
            if states.get(succ).map_or(true, |e| e != &new_state) {
                states.insert(succ.to_string(), new_state);
                worklist.push_back(succ.to_string());
            }
        }
    }

    states
}

#[cfg(test)]
mod tests {
    //! Framework unit tests. Each test writes a small `Analysis` impl and
    //! runs it on a hand-parsed MIR body, then asserts on the fixed-point
    //! output.

    use super::*;
    use crate::parser::Parser;
    use std::collections::BTreeSet;

    /// Parse `src` and return the body of the first function.
    fn body_of(src: &str) -> FunctionBody {
        let program = Parser::new(src.to_string()).parse().expect("parse");
        for decl in program.declarations {
            if let Declaration::Fn(f) = decl {
                if let Some(body) = f.body {
                    return body;
                }
            }
        }
        panic!("no function with a body in test source");
    }

    // ---------- Forward analysis: "vars assigned so far" ----------

    /// Trivial forward analysis over `BTreeSet<String>`. The state at any
    /// point is the set of local names that have appeared as an
    /// `Assign(Var(name), _)` target on every path reaching that point.
    struct AssignedVars;
    impl Analysis for AssignedVars {
        type State = BTreeSet<String>;
        fn direction(&self) -> Direction {
            Direction::Forward
        }
        fn initial_state(&self) -> Self::State {
            BTreeSet::new()
        }
        fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
            a.union(b).cloned().collect()
        }
        fn transfer_stmt(&self, state: &mut Self::State, stmt: &Statement) {
            if let Statement::Assign(Place::Var(name), _) = stmt {
                state.insert(name.clone());
            }
        }
        fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
    }

    #[test]
    fn forward_seeds_only_entry_block() {
        let body = body_of("fn f() { entry: return dead: return }");
        let r = run(&AssignedVars, &body);
        // Only entry is reachable; `dead` never appears in results.
        assert!(r.contains_key("entry"));
        assert!(!r.contains_key("dead"));
    }

    #[test]
    fn forward_transfers_and_joins_at_merge() {
        // Along the true path, `y` gets assigned. Along the false path,
        // `z` gets assigned. Both must show up at merge.
        let body = body_of(
            "
            fn f(a: boolean) {
              x: number;
              y: number;
              z: number;
              entry:
                x = 1;
                branch(copy a) [true: t, false: fbr]
              t:
                y = 2;
                goto merge
              fbr:
                z = 3;
                goto merge
              merge:
                return
            }
            ",
        );
        let r = run(&AssignedVars, &body);
        let expect =
            |labs: &[&str]| -> BTreeSet<String> { labs.iter().map(|s| s.to_string()).collect() };
        assert_eq!(r["entry"], expect(&[]));
        assert_eq!(r["t"], expect(&["x"]));
        assert_eq!(r["fbr"], expect(&["x"]));
        assert_eq!(r["merge"], expect(&["x", "y", "z"]));
    }

    #[test]
    fn forward_loop_reaches_fixed_point() {
        // Loop where `x` is written in body. Head sees `x` from both the
        // entry side (which writes x) and body (also x). Fixed point on
        // head = {x}; done inherits {x}.
        let body = body_of(
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
        let r = run(&AssignedVars, &body);
        let expect_x: BTreeSet<String> = ["x".to_string()].into_iter().collect();
        assert_eq!(r["entry"], BTreeSet::new());
        assert_eq!(r["head"], expect_x);
        assert_eq!(r["body"], expect_x);
        assert_eq!(r["done"], expect_x);
    }

    // ---------- Forward analysis: edge refinement ----------

    /// Every outgoing edge from a `Branch` inserts either "T" or "F"
    /// into successor state, based on which arm is taken.
    struct BranchLabel;
    impl Analysis for BranchLabel {
        type State = BTreeSet<String>;
        fn direction(&self) -> Direction {
            Direction::Forward
        }
        fn initial_state(&self) -> Self::State {
            BTreeSet::new()
        }
        fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
            a.union(b).cloned().collect()
        }
        fn transfer_stmt(&self, _: &mut Self::State, _: &Statement) {}
        fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
        fn refine_edge(&self, state: &mut Self::State, block: &BasicBlock, succ: &str) {
            if let Terminator::Branch {
                true_label,
                false_label,
                ..
            } = &block.terminator
            {
                if succ == true_label {
                    state.insert("T".to_string());
                }
                if succ == false_label {
                    state.insert("F".to_string());
                }
            }
        }
    }

    #[test]
    fn forward_refine_edge_applies_per_successor() {
        let body = body_of(
            "
            fn f(b: boolean) {
              entry: branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        );
        let r = run(&BranchLabel, &body);
        let s = |v: &str| -> BTreeSet<String> { v.chars().map(|c| c.to_string()).collect() };
        assert_eq!(r["entry"], BTreeSet::new());
        assert_eq!(r["t"], s("T"));
        assert_eq!(r["fbr"], s("F"));
    }

    // ---------- Backward analysis: simplified liveness ----------

    /// Backward "liveness of drops": a variable is live iff it will be
    /// consumed by a downstream `drop <Var>`. Not real liveness — just
    /// enough to exercise reverse transfer + terminal-block seeding +
    /// backward joins.
    struct DropLiveness;
    impl Analysis for DropLiveness {
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
            if let Statement::Drop(Place::Var(name)) = stmt {
                state.insert(name.clone());
            }
        }
        fn transfer_terminator(&self, _: &mut Self::State, _: &Terminator) {}
    }

    #[test]
    fn backward_seeds_all_terminal_blocks_and_propagates() {
        // t drops x before return; fbr just returns. Backward: at entry
        // block's exit, state = join(entry-state-of-t, entry-state-of-fbr)
        //                     = {x} ∪ {} = {x}.
        let body = body_of(
            "
            fn f(b: boolean) {
              x: number;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                drop x;
                return
              fbr:
                return
            }
            ",
        );
        let r = run(&DropLiveness, &body);
        // Terminal blocks: exit state is initial (empty).
        assert_eq!(r["t"], BTreeSet::new());
        assert_eq!(r["fbr"], BTreeSet::new());
        // entry's exit state = union of successor entry states.
        // t's entry state = {x} (reverse-walking `drop x`); fbr's = {}.
        let expect_x: BTreeSet<String> = ["x".to_string()].into_iter().collect();
        assert_eq!(r["entry"], expect_x);
    }

    #[test]
    fn backward_loop_converges() {
        // Body drops x; loop back-edge to head. head's exit state after
        // fixed point = {x} (body always propagates x back).
        let body = body_of(
            "
            fn f(b: boolean) {
              x: number;
              entry:
                goto head
              head:
                branch(copy b) [true: body, false: done]
              body:
                drop x;
                goto head
              done:
                return
            }
            ",
        );
        let r = run(&DropLiveness, &body);
        let expect_x: BTreeSet<String> = ["x".to_string()].into_iter().collect();
        assert_eq!(r["done"], BTreeSet::new());
        assert_eq!(r["body"], expect_x);
        assert_eq!(r["head"], expect_x);
        assert_eq!(r["entry"], expect_x);
    }

    // ---------- Corner cases ----------

    #[test]
    fn empty_body_returns_empty_results() {
        let body = FunctionBody {
            locals: vec![],
            blocks: vec![],
        };
        let r = run(&AssignedVars, &body);
        assert!(r.is_empty());
    }

    // ---------- walk_forward ----------

    #[test]
    fn walk_forward_visits_program_points_in_order_with_pre_transfer_state() {
        // Two-branch program: entry writes x, t writes y, fbr writes z, merge
        // reads them. Walk collects (block_label, kind, state_size) at each
        // point. State observed before a stmt/terminator should be the
        // pre-transfer state.
        let body = body_of(
            "
            fn f(a: boolean) {
              x: number;
              y: number;
              z: number;
              entry:
                x = 1;
                branch(copy a) [true: t, false: fbr]
              t:
                y = 2;
                goto merge
              fbr:
                z = 3;
                goto merge
              merge:
                return
            }
            ",
        );
        let results = run(&AssignedVars, &body);

        // Collect (label, kind, seen-vars) triples in visit order.
        let mut trace: Vec<(String, &'static str, BTreeSet<String>)> = Vec::new();
        walk_forward(&AssignedVars, &body, &results, |pt| match pt {
            WalkPoint::Stmt { state, block, .. } => {
                trace.push((block.label.clone(), "stmt", state.clone()));
            }
            WalkPoint::Terminator { state, block, .. } => {
                trace.push((block.label.clone(), "term", state.clone()));
            }
        });

        let expect: BTreeSet<String> = ["x".to_string(), "y".to_string(), "z".to_string()]
            .into_iter()
            .collect();
        // entry: stmt `x = 1` sees {}, then terminator sees {x}.
        assert_eq!(trace[0].0, "entry");
        assert_eq!(trace[0].1, "stmt");
        assert!(trace[0].2.is_empty());
        assert_eq!(trace[1].0, "entry");
        assert_eq!(trace[1].1, "term");
        assert_eq!(trace[1].2, ["x".to_string()].into_iter().collect());
        // At merge, only the terminator is visited (no stmts); state carries
        // the join {x, y, z}.
        let merge_term = trace
            .iter()
            .find(|(b, k, _)| b == "merge" && *k == "term")
            .unwrap();
        assert_eq!(merge_term.2, expect);
    }

    #[test]
    fn walk_forward_skips_unreachable_blocks() {
        // `dead` has no predecessor; it should not be visited.
        let body = body_of("fn f() { entry: return dead: return }");
        let results = run(&AssignedVars, &body);
        let mut visited: BTreeSet<String> = BTreeSet::new();
        walk_forward(&AssignedVars, &body, &results, |pt| match pt {
            WalkPoint::Stmt { block, .. } => {
                visited.insert(block.label.clone());
            }
            WalkPoint::Terminator { block, .. } => {
                visited.insert(block.label.clone());
            }
        });
        assert!(visited.contains("entry"));
        assert!(!visited.contains("dead"));
    }
}

fn run_backward<A: Analysis>(analysis: &A, body: &FunctionBody) -> Results<A::State> {
    let blocks_by_label = body.blocks_by_label();

    // Precompute predecessor map: succ -> [pred labels].
    let mut preds: IndexMap<String, Vec<String>> = IndexMap::new();
    for block in &body.blocks {
        for succ in terminator_successors(&block.terminator) {
            if !blocks_by_label.contains_key(succ) {
                continue;
            }
            preds
                .entry(succ.to_string())
                .or_default()
                .push(block.label.clone());
        }
    }

    let mut states: Results<A::State> = IndexMap::new();
    let mut worklist: VecDeque<String> = VecDeque::new();

    // Seed exit states of terminal blocks (no successors).
    for block in &body.blocks {
        if terminator_successors(&block.terminator).is_empty() {
            states.insert(block.label.clone(), analysis.initial_state());
            worklist.push_back(block.label.clone());
        }
    }

    while let Some(label) = worklist.pop_front() {
        let block = blocks_by_label[label.as_str()];
        // stored state = block's exit state. Walk backward through
        // terminator then statements (reversed) to get the entry state.
        let mut state = states[&label].clone();
        analysis.transfer_terminator(&mut state, &block.terminator);
        for (stmt, _) in block.statements.iter().rev() {
            analysis.transfer_stmt(&mut state, stmt);
        }
        // `state` is now the entry state of `block`.

        // Propagate to predecessors: `state` joins into each predecessor's
        // exit state. refine_edge is called on the pred_block -> label
        // edge — same signature/direction as forward, so a pass writes
        // one refinement in terms of "outgoing edge from block".
        let pred_labels: Vec<String> = preds.get(&label).into_iter().flatten().cloned().collect();
        for pred_label in pred_labels {
            let pred_block = blocks_by_label[pred_label.as_str()];
            let mut incoming = state.clone();
            analysis.refine_edge(&mut incoming, pred_block, &label);
            let new_state = match states.get(&pred_label) {
                None => incoming,
                Some(existing) => analysis.join(existing, &incoming),
            };
            if states.get(&pred_label).map_or(true, |e| e != &new_state) {
                states.insert(pred_label.clone(), new_state);
                worklist.push_back(pred_label);
            }
        }
    }

    states
}
