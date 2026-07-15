//! Init state — eager pointee transition at borrow creation.
//!
//! On borrow creation, the loaned place is *immediately* transitioned
//! to the loan's post state (rather than staying in a "frozen" state
//! until the loan expires). This decouples init tracking from loan
//! tracking: the init tracker never needs a Frozen variant, and the
//! lifetime pass independently prevents direct access while the loan
//! is live.

use crate::mir::test_util::*;

#[test]
fn out_borrow_of_local_marks_place_init() {
    // Post-borrow, x is Init (per the eager transition). After the
    // loan is consumed by the call, x remains Init and is dropped
    // by the elaborator at return.
    assert_no_diagnostics(
        "
        extern fn init(r: &out i64);
        fn f() {
          x: i64;
          r: &out i64;
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
        extern fn consume(r: &drop i64);
        fn f(x: i64) {
          r: &drop i64;
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
        extern fn use_mut(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            call use_mut(move r);
            return
        }
        ",
    );
}
