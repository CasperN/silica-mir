//! Structured (code + span) assertions for init_state diagnostics.
//!
//! These verify both the machine-readable `InitStateCode` and the
//! primary span. Complements the string-based tests in the other
//! init_state test modules, which assert on user-facing message
//! substrings.

use crate::mir::init_state::InitStateCode;
use crate::mir::test_util::*;

#[test]
fn structured_use_before_init_at_stmt_span() {
    // `z` is declared but never assigned; `copy z` on line 6 col 17
    // triggers UseBeforeInit at the statement span.
    let src = "
            fn f() {
              x: i64;
              z: i64;
              entry:
                x = copy z;
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        InitStateCode::UseBeforeInit,
        (6, 17),
    );
}

#[test]
fn structured_use_after_move_at_call_span() {
    // First `call take(move x)` consumes `x`; the second one on
    // line 7 col 17 sees `x` in the `Moved` state.
    let src = "
            struct M: Move + Drop { a: i64 }
            extern fn take(m: M);
            fn f(x: M) {
              entry:
                call take(move x);
                call take(move x);
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        InitStateCode::UseAfterMove,
        (7, 17),
    );
}

#[test]
fn structured_overwrite_without_drop_at_stmt_span() {
    // `y` becomes Init after `y = move a1`; the overwrite on line 8
    // col 17 hits a live non-Drop value.
    let src = "
            struct A: Move { r: &out i64 }
            extern fn take(a: A);
            fn f(a1: A, a2: A) {
              y: A;
              entry:
                y = move a1;
                y = move a2;
                call take(move y);
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        InitStateCode::OverwriteWithoutDrop,
        (8, 17),
    );
}

#[test]
fn structured_ref_obligation_unfulfilled_at_drop_span() {
    // `move *r` transitions `r`'s pointee to Uninit; then `drop r`
    // silently forgets the obligation to leave the pointee Init.
    // The error fires on the `drop r;` statement (line 6 col 17).
    let src = "
            fn f(r: &mut i64) {
              x: i64;
              entry:
                x = move r.*;
                drop r;
                return
            }";
    let d = run_structured(src);
    assert_error_at(
        &d,
        InitStateCode::RefObligationUnfulfilled,
        (6, 17),
    );
}
