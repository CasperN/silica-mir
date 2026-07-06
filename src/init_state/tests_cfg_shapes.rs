//! Init state dataflow — CFG shape stress tests.
//!
//! Exercises the dataflow fixpoint on loops, sequential loops, aborts,
//! nested loops, irreducible flow, and switchEnum/borrow interactions.

use crate::test_util::*;

// ---------- CFG shape stress tests ----------

// Borrow created inside a loop body, used and consumed in same
// iteration. Loan should not accumulate across iterations. Note: r
// ends up Diverged at return (NeverInit vs Moved across iterations),
// which currently produces a linear leak — that's the "elaborator
// doesn't handle Diverged" punchlist item, not a bug in loan tracking.
// What we verify: no residual loan on x outside the loop.
#[test]
fn borrow_in_loop_body_no_residual_loan() {
    let (errs, _) = run(
        "
        extern fn use_ref(r: &mut number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            r = &mut x;
            call use_ref(move r);
            goto head
          done:
            x = 42;
            return
        }
        ",
    );
    assert!(
        !errs.iter().any(|e| e.contains("cannot write to 'x'")),
        "unexpected loan conflict on x at done: {:?}", errs
    );
}

// Borrow created before loop, held across iterations, consumed
// after. The loan is live throughout; reads through *r inside body
// are legal.
#[test]
fn borrow_across_loop_iterations_ok() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        extern fn use_num(n: number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            r = &mut x;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            call use_num(copy *r);
            goto head
          done:
            call sink(move r);
            return
        }
        ",
    );
}

// Loop where body may execute zero times. State at `done` must
// still be usable.
#[test]
fn zero_iteration_loop_ok() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(b: boolean, x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            goto head
          head:
            branch(copy b) [true: body, false: done]
          body:
            goto head
          done:
            call sink(move r);
            return
        }
        ",
    );
}

// Borrow taken and consumed inside one branch; the other branch
// takes and consumes the same. At merge, no loan is live and direct
// access to x is legal. Uses symmetric consumption to avoid a
// Diverged r side-issue.
#[test]
fn symmetric_borrow_then_gone_merge_access_ok() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            r = &mut x;
            call sink(move r);
            goto merge
          fbr:
            r = &mut x;
            call sink(move r);
            goto merge
          merge:
            x = 42;
            return
        }
        ",
    );
}

// Both branches create the same borrow and merge with the loan
// still live; consumed after the merge. Join preserves same-loan
// entries.
#[test]
fn symmetric_borrow_carried_through_merge_ok() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            r = &mut x;
            goto merge
          fbr:
            r = &mut x;
            goto merge
          merge:
            call sink(move r);
            return
        }
        ",
    );
}

// Move in one branch, read of the same var at merge — Diverged
// formation should catch this.
#[test]
fn move_in_one_branch_read_at_merge_error() {
    let (errs, _) = run(
        "
        extern fn take(y: number);
        extern fn use_num(n: number);
        fn f(x: number, b: boolean) {
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            call take(move x);
            goto merge
          fbr:
            goto merge
          merge:
            call use_num(copy x);
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["variable 'x' may be used before initialization or after move"],
    );
}

// Live borrow going into a branch where one arm aborts. Abort
// has no successors, so the loan doesn't leak into anything.
#[test]
fn abort_with_live_borrow_other_arm_returns_ok() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            r = &mut x;
            branch(copy b) [true: t, false: fbr]
          t:
            abort
          fbr:
            call sink(move r);
            return
        }
        ",
    );
}

// One arm creates a borrow then aborts; the other arm does not
// borrow. The loan from the aborting arm must not leak into the
// returning arm's state.
#[test]
fn borrow_before_abort_no_leak_into_sibling_ok() {
    assert_no_diagnostics(
        "
        extern fn use_num(n: number);
        fn f(x: number, b: boolean) {
          r: &mut number;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            r = &mut x;
            abort
          fbr:
            call use_num(copy x);
            return
        }
        ",
    );
}

// Borrow the payload of a refined enum variant; the other arm is
// `unreachable` (provably so, since o was constructed as Some).
#[test]
fn borrow_downcast_with_unreachable_sibling_ok() {
    assert_no_diagnostics(
        "
        enum Copy Drop Option { None: unit Some: number }
        extern fn sink(r: &mut number);
        fn f() {
          o: Option;
          r: &mut number;
          entry:
            o = Option::Some(1);
            switchEnum(o) [None: n_arm, Some: s_arm]
          s_arm:
            r = &mut o as Some;
            call sink(move r);
            return
          n_arm:
            unreachable
        }
        ",
    );
}

// Two switchEnum arms create the same borrow; the loan carries
// through the merge and is consumed once.
#[test]
fn switch_arms_same_borrow_carried_through_merge_ok() {
    assert_no_diagnostics(
        "
        enum Copy Drop Sel { A: unit B: unit }
        extern fn sink(r: &mut number);
        fn f(o: Sel, x: number) {
          r: &mut number;
          entry:
            switchEnum(o) [A: a_arm, B: b_arm]
          a_arm:
            r = &mut x;
            goto merge
          b_arm:
            r = &mut x;
            goto merge
          merge:
            call sink(move r);
            return
        }
        ",
    );
}

// Two sequential loops in one function. State between them
// should reset cleanly.
#[test]
fn two_sequential_loops_ok() {
    assert_no_diagnostics(
        "
        extern fn noop();
        fn f(b: boolean) {
          entry:
            goto head1
          head1:
            branch(copy b) [true: body1, false: done1]
          body1:
            call noop();
            goto head1
          done1:
            goto head2
          head2:
            branch(copy b) [true: body2, false: done2]
          body2:
            call noop();
            goto head2
          done2:
            return
        }
        ",
    );
}

// Move → reassign → move cycle on a value type. Tracker should
// cycle through Init → Moved → Init → Moved cleanly.
#[test]
fn move_reinit_move_cycle_ok() {
    assert_no_diagnostics(
        "
        extern fn use_num(n: number);
        fn f(x: number) {
          y: number;
          z: number;
          entry:
            y = move x;
            x = 1;
            z = move x;
            call use_num(move y);
            call use_num(move z);
            return
        }
        ",
    );
}


// ---------- Nested and irreducible CFG shapes ----------

#[test]
fn nested_loops_converge_ok() {
    // A loop inside a loop — the fixpoint over back-edges should
    // still converge and produce the expected states.
    assert_no_diagnostics(
        "
        extern fn noop();
        fn f(a: boolean, b: boolean) {
          entry:
            goto outer_head
          outer_head:
            branch(copy a) [true: inner_head, false: outer_done]
          inner_head:
            branch(copy b) [true: inner_body, false: outer_back]
          inner_body:
            call noop();
            goto inner_head
          outer_back:
            goto outer_head
          outer_done:
            return
        }
        ",
    );
}

#[test]
fn irreducible_control_flow_two_entry_points_ok() {
    // Both `l` and `m` have a predecessor from the other and from
    // entry — the loop has no single header (irreducible flow).
    // Fixpoint should still converge.
    assert_no_diagnostics(
        "
        extern fn noop();
        fn f(a: boolean, b: boolean) {
          entry:
            branch(copy a) [true: l, false: m]
          l:
            call noop();
            branch(copy b) [true: m, false: exit]
          m:
            call noop();
            branch(copy a) [true: l, false: exit]
          exit:
            return
        }
        ",
    );
}

#[test]
fn nested_loop_with_borrow_across_outer_iterations_ok() {
    // Borrow taken outside both loops, used through the inner loop,
    // consumed after both. Confirms loan persists through nested
    // back-edges without accumulating.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        extern fn use_num(n: number);
        fn f(x: number, a: boolean, b: boolean) {
          r: &mut number;
          entry:
            r = &mut x;
            goto outer_head
          outer_head:
            branch(copy a) [true: inner_head, false: outer_done]
          inner_head:
            branch(copy b) [true: inner_body, false: outer_back]
          inner_body:
            call use_num(copy *r);
            goto inner_head
          outer_back:
            goto outer_head
          outer_done:
            call sink(move r);
            return
        }
        ",
    );
}

// Full (cur, post) transition cycle through *r: move-out then
// write-back, using the freed pointee value.
#[test]
fn mut_ref_move_out_then_write_back_cycle_ok() {
    assert_no_diagnostics(
        "
        extern fn use_num(n: number);
        extern fn sink(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          y: number;
          entry:
            r = &mut x;
            y = move *r;
            *r = 42;
            call use_num(move y);
            call sink(move r);
            return
        }
        ",
    );
}

