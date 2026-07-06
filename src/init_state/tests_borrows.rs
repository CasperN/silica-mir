//! Init state dataflow — borrow-related tests.
//!
//! Covers borrow init preconditions (per ref kind), reference
//! (cur, post) obligation tracking including overwrite and `drop *r`,
//! and eager init transition of the loaned place at borrow time.

use crate::test_util::*;

// ---------- Borrow init preconditions ----------
//
// Each ref kind requires the borrowed place be in a specific init
// state at the point of borrow. Tests are organized by ref kind, then
// by the state combinations that are/aren't legal.

// === Scenario: `&q` (shared) — requires Init ===

#[test]
fn shared_borrow_of_init_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &number;
          entry:
            r = &x;
            return
        }
        ",
    );
}

#[test]
fn shared_borrow_of_never_init_error() {
    let (errs, _) = run(
        "
        fn f() {
          x: number;
          r: &number;
          entry:
            r = &x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create & of 'x': place must be initialized at borrow, but is not yet initialized"],
    );
}

#[test]
fn shared_borrow_of_moved_error() {
    let (errs, _) = run(
        "
        extern fn sink(x: number);
        fn f(x: number) {
          r: &number;
          entry:
            call sink(move x);
            r = &x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create & of 'x': place must be initialized at borrow, but is moved-from"],
    );
}

// === Scenario: `&mut q` — requires Init ===

#[test]
fn mut_borrow_of_init_ok() {
    assert_no_diagnostics(
        "
        fn f(x: number) {
          r: &mut number;
          entry:
            r = &mut x;
            return
        }
        ",
    );
}

#[test]
fn mut_borrow_of_never_init_error() {
    let (errs, _) = run(
        "
        fn f() {
          x: number;
          r: &mut number;
          entry:
            r = &mut x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &mut of 'x': place must be initialized at borrow, but is not yet initialized"],
    );
}

// === Scenario: `&drop q` — requires Init ===

#[test]
fn drop_borrow_of_init_ok() {
    assert_no_diagnostics(
        "
        extern fn take_drop(r: &drop number);
        fn f(x: number) {
          r: &drop number;
          entry:
            r = &drop x;
            call take_drop(move r);
            return
        }
        ",
    );
}

#[test]
fn drop_borrow_of_never_init_error() {
    let (errs, _) = run(
        "
        fn f() {
          x: number;
          r: &drop number;
          entry:
            r = &drop x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &drop of 'x': place must be initialized at borrow, but is not yet initialized"],
    );
}

// === Scenario: `&out q` — requires Uninit ===

#[test]
fn out_borrow_of_never_init_ok() {
    // A declared but never-written local is the classic &out target.
    // Slice 0a doesn't yet track that `init_number` initializes x via
    // the &out — so x stays NeverInit locally, which is fine at return.
    assert_no_diagnostics(
        "
        extern fn init_number(out: &out number);
        fn f() {
          x: number;
          r: &out number;
          entry:
            r = &out x;
            call init_number(move r);
            return
        }
        ",
    );
}

#[test]
fn out_borrow_of_moved_ok() {
    // After moving out, the place is uninitialized again — legal
    // target for &out. (Slice 0a doesn't track init through the &out
    // — x stays Moved locally, which is fine at return.)
    assert_no_diagnostics(
        "
        extern fn take(y: number);
        extern fn init(out: &out number);
        fn f(x: number) {
          r: &out number;
          entry:
            call take(move x);
            r = &out x;
            call init(move r);
            return
        }
        ",
    );
}

#[test]
fn out_borrow_of_init_error() {
    let (errs, _) = run(
        "
        fn f(x: number) {
          entry:
            x = 1;
            return
        }
        fn g(x: number) {
          r: &out number;
          entry:
            r = &out x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &out of 'x': place must be uninitialized at borrow, but is initialized"],
    );
}

// === Scenario: `&uninit q` — requires Uninit ===

#[test]
fn uninit_borrow_of_never_init_ok() {
    assert_no_diagnostics(
        "
        extern fn discard(r: &uninit number);
        fn f() {
          x: number;
          r: &uninit number;
          entry:
            r = &uninit x;
            call discard(move r);
            return
        }
        ",
    );
}

#[test]
fn uninit_borrow_of_init_error() {
    let (errs, _) = run(
        "
        fn f(x: number) {
          r: &uninit number;
          entry:
            r = &uninit x;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &uninit of 'x': place must be uninitialized at borrow, but is initialized"],
    );
}

// === Scenario: fields (Partial states) ===

#[test]
fn mut_borrow_of_init_field_ok() {
    // Field-granular tracking: p.x is Init (from `p.x = 1`), so
    // `&mut p.x` succeeds even though p is Partial as a whole.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        extern fn use_mut(r: &mut number);
        fn f() {
          p: P;
          r: &mut number;
          entry:
            p.x = 1;
            r = &mut p.x;
            call use_mut(move r);
            drop p.x;
            return
        }
        ",
    );
}

#[test]
fn mut_borrow_of_never_init_field_error() {
    let (errs, _) = run(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          entry:
            p.x = 1;
            p.y = copy p.x;
            p.y = 2;
            return
        }
        fn g() {
          p: P;
          r: &mut number;
          entry:
            p.x = 1;
            r = &mut p.y;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &mut of 'p.y': place must be initialized at borrow, but is not yet initialized"],
    );
}

#[test]
fn out_borrow_of_partial_error() {
    // Borrowing the whole `p` when only `p.x` was written: the leaf
    // read on `p` is Partial, not one of the accepted states.
    let (errs, _) = run(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          r: &out P;
          entry:
            p.x = 1;
            r = &out p;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &out of 'p': place must be uninitialized at borrow, but is partially initialized"],
    );
}

#[test]
fn shared_borrow_of_partial_error() {
    // `&` requires Init; Partial isn't Init.
    let (errs, _) = run(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          r: &P;
          entry:
            p.x = 1;
            r = &p;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create & of 'p': place must be initialized at borrow, but is partially initialized"],
    );
}

#[test]
fn drop_borrow_of_partial_error() {
    // `&drop` requires Init; Partial isn't Init.
    let (errs, _) = run(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          r: &drop P;
          entry:
            p.x = 1;
            r = &drop p;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot create &drop of 'p': place must be initialized at borrow, but is partially initialized"],
    );
}

// === Scenario: borrow through deref is not tracked (documents gap) ===

#[test]
fn borrow_through_deref_not_checked() {
    // `*r` isn't a followed path in slice 0a. Any borrow whose base
    // path contains a Deref is silently skipped. This documents the
    // gap; a later slice will handle reference-through-reference.
    assert_no_diagnostics(
        "
        fn f(r: &mut number) {
          s: &number;
          entry:
            s = &*r;
            return
        }
        ",
    );
}

// ---------- Reference (cur, post) state tracking ----------
//
// Slice 0b: transitions on `*r` operations, close-check on ref-var
// consumption, leak check at return for unfulfilled ref obligations.
//
// Tests organized by ref kind, then by the interesting sequences.

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
    let (errs, _) = run(
        "
        fn f(r: &mut number) {
          entry:
            *r = 42;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot write into pointee of 'r': pointee must be uninitialized here, but is initialized"],
    );
}

#[test]
fn mut_ref_moved_out_return_leaks() {
    // Move-out leaves cur=Uninit; not refilled → obligation unmet.
    let (errs, _) = run(
        "
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["reference 'r' of type Ref(Mut, Number) has unfulfilled obligation at return"],
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
    let (errs, _) = run(
        "
        fn f(r: &out number) {
          entry:
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["reference 'r' of type Ref(Out, Number) has unfulfilled obligation at return"],
    );
}

#[test]
fn out_ref_read_before_write_error() {
    // Can't read through &out — pointee is Uninit at creation.
    let (errs, _) = run(
        "
        fn f(r: &out number) {
          x: number;
          entry:
            x = copy *r;
            *r = 42;
            return
        }
        ",
    );
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
    let (errs, _) = run(
        "
        fn f(r: &drop number) {
          entry:
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["reference 'r' of type Ref(Drop, Number) has unfulfilled obligation at return"],
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
    let (errs, _) = run(
        "
        fn f(r: &uninit number) {
          entry:
            *r = 42;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["reference 'r' of type Ref(Uninit, Number) has unfulfilled obligation at return"],
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
    let (errs, _) = run(
        "
        fn f(r: &number) {
          entry:
            *r = 1;
            return
        }
        ",
    );
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
    let (errs, _) = run(
        "
        fn f(r: &mut number) {
          x: number;
          entry:
            x = move *r;
            drop r;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot forget reference 'r': obligation not fulfilled"],
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
    let (errs, _) = run(
        "
        fn f(r: &mut number, z: number) {
          x: number;
          entry:
            x = move *r;
            r = &mut z;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["cannot forget reference 'r': obligation not fulfilled"],
    );
}

// === Drop through a deref ===

#[test]
fn drop_deref_of_mut_ref_leaks_pointee() {
    // `drop *r` on r: &mut consumes the pointee, transitioning r to
    // (Uninit, Init). Without re-init, obligation at return is unmet.
    let (errs, _) = run(
        "
        fn f(r: &mut number) {
          entry:
            drop *r;
            return
        }
        ",
    );
    assert_errors_contain(
        &errs,
        &["reference 'r' of type Ref(Mut, Number) has unfulfilled obligation at return"],
    );
}

// ---------- Eager init transition at borrow ----------
//
// On borrow creation, the loaned place is eagerly transitioned to
// the loan's post state. This decouples init tracking from loan
// tracking: the init tracker never needs a "frozen" state — the
// loan tracker independently prevents direct access.

#[test]
fn out_borrow_of_local_marks_place_init() {
    // Post-borrow, x is Init (per the eager transition). After the
    // loan is consumed by the call, x remains Init and is dropped
    // by the elaborator at return.
    assert_no_diagnostics(
        "
        extern fn init(r: &out number);
        fn f() {
          x: number;
          r: &out number;
          entry:
            r = &out x;
            call init(move r);
            return
        }
        ",
    );
}

#[test]
fn drop_borrow_of_local_marks_place_moved() {
    // `&drop x` post-borrow leaves x Moved: no re-init needed at
    // return, and no leak.
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

#[test]
fn mut_borrow_does_not_change_place_state() {
    // `&mut` has post = Init and pointee was already Init; no
    // transition on the loaned place.
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

