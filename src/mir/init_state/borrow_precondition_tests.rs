//! Init state — borrow-time init state preconditions.
//!
//! Each ref kind requires the borrowed place to be in a specific init
//! state at the point of borrow:
//! - `&`, `&mut`, `&drop` require the pointee to be `Init`.
//! - `&out`, `&uninit` require the pointee to be `NeverInit` or `Moved`.
//! `Partial` never satisfies either side.
//!
//! Tests are organized by ref kind, then by the state combinations
//! that are/aren't legal. Reborrow (`&kind *r`) preconditions live in
//! `lifetime/tests_reborrow.rs` — they inspect ref state, not the
//! init tree.

use crate::mir::test_util::*;

// === Scenario: `&q` (shared) — requires Init ===

#[test]
fn shared_borrow_of_init_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &i64;
          entry:
            r = &x;
            return
        }
        ",
    );
}

#[test]
fn shared_borrow_of_never_init_error() {
    let (errs, _) = run("
        fn f() {
          x: i64;
          r: &i64;
          entry:
            r = &x;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create & of 'x': place must be initialized at borrow, but is not yet initialized"],
    );
}

#[test]
fn shared_borrow_of_moved_error() {
    let (errs, _) = run("
        extern fn sink(x: i64);
        fn f(x: i64) {
          r: &i64;
          entry:
            call sink(move x);
            r = &x;
            return
        }
        ");
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
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            return
        }
        ",
    );
}

#[test]
fn mut_borrow_of_never_init_error() {
    let (errs, _) = run("
        fn f() {
          x: i64;
          r: &mut i64;
          entry:
            r = &mut x;
            return
        }
        ");
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
        extern fn take_drop(r: &drop i64);
        fn f(x: i64) {
          r: &drop i64;
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
    let (errs, _) = run("
        fn f() {
          x: i64;
          r: &drop i64;
          entry:
            r = &drop x;
            return
        }
        ");
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
        extern fn init_number(out: &out i64);
        fn f() {
          x: i64;
          r: &out i64;
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
        extern fn take(y: i64);
        extern fn init(out: &out i64);
        fn f(x: i64) {
          r: &out i64;
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
fn out_borrow_of_init_drop_type_ok_via_elaboration() {
    // `x: i64` is Copy Drop, so `&out x` on an Init `x` is elaborated
    // into `drop x; r = &out x;` — the Uninit precondition is met
    // after the implicit drop. Post-elab init_state accepts the
    // rewritten program.
    assert_no_diagnostics("
        fn g(x: i64) {
          r: &out i64;
          entry:
            r = &out x;
            r.* = 2;
            return
        }
        ");
}

#[test]
fn out_borrow_of_init_non_drop_type_errors() {
    // A linear (non-Drop) value can't be silently forgotten, so
    // drop-elab has nothing to insert. The precondition failure
    // fires as before.
    let (errs, _) = run("
        struct Linear { r: &out i64 }
        fn f(x: Linear) {
          rr: &out Linear;
          entry:
            rr = &out x;
            return
        }
        ");
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
        extern fn discard(r: &uninit i64);
        fn f() {
          x: i64;
          r: &uninit i64;
          entry:
            r = &uninit x;
            call discard(move r);
            return
        }
        ",
    );
}

#[test]
fn uninit_borrow_of_init_drop_type_ok_via_elaboration() {
    // Same as the &out case above but for &uninit. Since `x: i64` is
    // Drop, drop-elab inserts `drop x` and the precondition is met.
    // `&uninit`'s post is Uninit, so the pointee stays uninit after
    // the borrow expires; the leak check catches that x remains
    // uninit-at-return, so we consume via move to keep it clean.
    assert_no_diagnostics("
        fn f(x: i64) {
          r: &uninit i64;
          entry:
            r = &uninit x;
            drop r;
            return
        }
        ");
}

#[test]
fn uninit_borrow_of_init_non_drop_type_errors() {
    // Linear payload → no drop to insert → precondition failure.
    let (errs, _) = run("
        struct Linear { r: &out i64 }
        fn f(x: Linear) {
          rr: &uninit Linear;
          entry:
            rr = &uninit x;
            return
        }
        ");
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
        struct Copy Drop P { x: i64 y: i64 }
        extern fn use_mut(r: &mut i64);
        fn f() {
          p: P;
          r: &mut i64;
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
    let (errs, _) = run("
        struct Copy Drop P { x: i64 y: i64 }
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
          r: &mut i64;
          entry:
            p.x = 1;
            r = &mut p.y;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create &mut of 'p.y': place must be initialized at borrow, but is not yet initialized"],
    );
}

#[test]
fn out_borrow_of_partial_error() {
    // Borrowing the whole `p` when only `p.x` was written: the leaf
    // read on `p` is Partial, not one of the accepted states.
    let (errs, _) = run("
        struct Copy Drop P { x: i64 y: i64 }
        fn f() {
          p: P;
          r: &out P;
          entry:
            p.x = 1;
            r = &out p;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create &out of 'p': place must be uninitialized at borrow, but is partially initialized"],
    );
}

#[test]
fn shared_borrow_of_partial_error() {
    // `&` requires Init; Partial isn't Init.
    let (errs, _) = run("
        struct Copy Drop P { x: i64 y: i64 }
        fn f() {
          p: P;
          r: &P;
          entry:
            p.x = 1;
            r = &p;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create & of 'p': place must be initialized at borrow, but is partially initialized"],
    );
}

#[test]
fn drop_borrow_of_partial_error() {
    // `&drop` requires Init; Partial isn't Init.
    let (errs, _) = run("
        struct Copy Drop P { x: i64 y: i64 }
        fn f() {
          p: P;
          r: &drop P;
          entry:
            p.x = 1;
            r = &drop p;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot create &drop of 'p': place must be initialized at borrow, but is partially initialized"],
    );
}
