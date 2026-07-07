//! Init state — reference `(cur, post)` obligation tracking.
//!
//! Each exclusive ref kind (`&mut`, `&out`, `&drop`, `&uninit`) carries
//! a (cur, post) init obligation on its pointee. `*r` operations
//! transition `cur`; the obligation is checked when the ref value is
//! consumed (by call, drop, unborrow, or overwrite) — cur must equal
//! post at that point. Shared refs (`&T`) carry no obligation.
//!
//! Tests organized by ref kind, then by the interesting operation
//! sequences (read, write, move, drop, overwrite, drop-through-deref).

use crate::test_util::*;

// === &mut: pointee starts Init, must stay Init at expiry ===

#[test]
fn mut_ref_read_then_return_ok() {
    // Read through &mut leaves cur=Init; obligation trivially met.
    assert_no_diagnostics(
        "
        fn f(r: &mut number) {
          x: number;
          entry:
            x = copy *r;
            return
        }
        ",
    );
}

#[test]
fn mut_ref_move_then_write_ok() {
    // Move-out drops cur to Uninit; write puts it back to Init;
    // obligation met at return.
    assert_no_diagnostics(
        "
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            *r = 42;
            return
        }
        ",
    );
}

#[test]
fn mut_ref_write_without_move_error() {
    // `*r = v` on an Init pointee would silently forget the old
    // value — rejected as pre-overwrite of the pointee.
    let (errs, _) = run("
        fn f(r: &mut number) {
          entry:
            *r = 42;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot write into pointee of 'r': pointee must be uninitialized here, but is initialized"],
    );
}

#[test]
fn mut_ref_moved_out_return_leaks() {
    // Move-out leaves cur=Uninit; not refilled → obligation unmet.
    let (errs, _) = run("
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

// === &out: pointee starts Uninit, must reach Init at expiry ===

#[test]
fn out_ref_write_then_return_ok() {
    assert_no_diagnostics(
        "
        fn f(r: &out number) {
          entry:
            *r = 42;
            return
        }
        ",
    );
}

#[test]
fn out_ref_unwritten_leaks() {
    let (errs, _) = run("
        fn f(r: &out number) {
          entry:
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

#[test]
fn out_ref_read_before_write_error() {
    // Can't read through &out — pointee is Uninit at creation.
    let (errs, _) = run("
        fn f(r: &out number) {
          x: number;
          entry:
            x = copy *r;
            *r = 42;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot read from pointee of 'r': pointee must be initialized here, but is uninitialized"],
    );
}

// === &drop: pointee starts Init, must reach Uninit at expiry ===

#[test]
fn drop_ref_move_out_then_return_ok() {
    assert_no_diagnostics(
        "
        fn f(r: &drop number) {
          x: number;
          entry:
            x = move *r;
            return
        }
        ",
    );
}

#[test]
fn drop_ref_unmoved_leaks() {
    let (errs, _) = run("
        fn f(r: &drop number) {
          entry:
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

// === &uninit: pointee starts Uninit, must stay Uninit at expiry ===

#[test]
fn uninit_ref_untouched_return_ok() {
    assert_no_diagnostics(
        "
        fn f(r: &uninit number) {
          entry:
            return
        }
        ",
    );
}

#[test]
fn uninit_ref_write_makes_it_drop_state() {
    // After `*r = v`, r is in `&drop` state (post=Uninit, cur=Init).
    // Must move-out again to satisfy post.
    assert_no_diagnostics(
        "
        fn f(r: &uninit number) {
          x: number;
          entry:
            *r = 42;
            x = move *r;
            return
        }
        ",
    );
}

#[test]
fn uninit_ref_write_without_moveback_leaks() {
    let (errs, _) = run("
        fn f(r: &uninit number) {
          entry:
            *r = 42;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

// === Local ref: create → use → move-to-call ===

#[test]
fn local_mut_ref_moved_to_call_ok() {
    assert_no_diagnostics(
        "
        extern fn use_mut(r: &mut number);
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            call use_mut(move r);
            return
        }
        ",
    );
}

#[test]
fn local_drop_ref_moved_to_call_ok() {
    // Create &drop, transfer via call. Loan obligation delegated to
    // the callee.
    assert_no_diagnostics(
        "
        extern fn consume(r: &drop number);
        fn f(x: number) {
          r: &drop number;
          entry:
            r = &drop x;
            call consume(move r);
            return
        }
        ",
    );
}

// === Shared refs: no obligation, no state tracking ===

#[test]
fn shared_ref_read_ok() {
    assert_no_diagnostics(
        "
        fn f(r: &number) {
          x: number;
          entry:
            x = copy *r;
            return
        }
        ",
    );
}

#[test]
fn shared_ref_write_error() {
    let (errs, _) = run("
        fn f(r: &number) {
          entry:
            *r = 1;
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot mutate through shared reference 'r'"]);
}

#[test]
fn shared_ref_left_bound_at_return_ok() {
    // `&T` is Copy Drop; no obligation on return.
    assert_no_diagnostics(
        "
        fn f(r: &number) {
          entry:
            return
        }
        ",
    );
}

// === Drop statement on refs (bitwise forget must satisfy post) ===

#[test]
fn drop_of_mut_ref_ok() {
    // &mut is (Init, Init) at every point; drop is trivially legal.
    assert_no_diagnostics(
        "
        fn f(r: &mut number) {
          entry:
            drop r;
            return
        }
        ",
    );
}

#[test]
fn drop_of_ref_with_unfulfilled_obligation_error() {
    // Move out through &mut leaves cur=Uninit; drop-forget then
    // errors because obligation not fulfilled.
    let (errs, _) = run("
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            drop r;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

// === Overwrite of a bound reference variable ===

#[test]
fn overwrite_bound_ref_with_fulfilled_obligation_ok() {
    // r's first binding is (Init, Init) — obligation fulfilled at
    // the overwrite point, so silently dropping the old ref is OK.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut number);
        fn f(x: number, y: number) {
          r: &mut number;
          entry:
            r = &mut x;
            r = &mut y;
            call sink(move r);
            return
        }
        ",
    );
}

#[test]
fn overwrite_bound_ref_with_unfulfilled_obligation_error() {
    // After `x = move *r`, r is (Uninit, Init); overwriting r would
    // silently forget the pending re-init obligation on the pointee.
    let (errs, _) = run("
        fn f(r: &mut number, z: number) {
          x: number;
          entry:
            x = move *r;
            r = &mut z;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}

// === Drop through a deref ===

#[test]
fn drop_deref_of_mut_ref_leaks_pointee() {
    // `drop *r` on r: &mut consumes the pointee, transitioning r to
    // (Uninit, Init). Without re-init, obligation at return is unmet.
    let (errs, _) = run("
        fn f(r: &mut number) {
          entry:
            drop *r;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["reference 'r' has unfulfilled obligation"],
    );
}
