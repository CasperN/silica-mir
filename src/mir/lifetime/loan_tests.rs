//! Lifetime pass — loan conflict tests.
//!
//! Covers single-loan conflicts (exclusive vs shared vs mutable-reborrow),
//! field-level precision, ref transfer through moves, and multi-loan
//! (branch-of-borrows) conflicts.

use crate::test_util::*;

// ---------- Loan conflicts ----------
//
// Slice 1: a borrow of a place freezes it (whole-function
// conservative lifetime — the loan lasts until the borrower is
// consumed). Any direct access to the loaned place is a conflict,
// with the shared/shared exception for reads and shared reborrows.

// === Exclusive loan blocks direct access ===

#[test]
fn mut_loan_blocks_direct_write() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            x = 1;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

#[test]
fn mut_loan_blocks_direct_read() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy x;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'x': already borrowed by 'r'"]);
}

#[test]
fn mut_loan_blocks_direct_move() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        extern fn use_num(y: i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            call use_num(move x);
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot move from 'x': already borrowed by 'r'"]);
}

// === Shared loans permit reads and shared reborrows ===

#[test]
fn shared_loan_permits_read_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &i64;
          y: i64;
          entry:
            r = &x;
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn shared_loan_permits_shared_reborrow_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &i64;
          s: &i64;
          entry:
            r = &x;
            s = &x;
            return
        }
        ",
    );
}

#[test]
fn shared_loan_blocks_write() {
    // r kept alive through the conflicting write via a downstream use;
    // without it, NLL would close the loan before the write and there'd
    // be no conflict.
    let (errs, _) = run("
        extern fn read_ref(r: &i64);
        fn f(x: i64) {
          r: &i64;
          entry:
            r = &x;
            x = 1;
            call read_ref(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

#[test]
fn shared_loan_blocks_move() {
    let (errs, _) = run("
        extern fn take(y: i64);
        extern fn read_ref(r: &i64);
        fn f(x: i64) {
          r: &i64;
          entry:
            r = &x;
            call take(move x);
            call read_ref(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot move from 'x': already borrowed by 'r'"]);
}

#[test]
fn shared_loan_blocks_mut_reborrow() {
    let (errs, _) = run("
        extern fn read_ref(r: &i64);
        extern fn use_mut(r: &mut i64);
        fn f(x: i64) {
          r: &i64;
          s: &mut i64;
          entry:
            r = &x;
            s = &mut x;
            call read_ref(move r);
            call use_mut(move s);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot borrow as &mut 'x': already borrowed by 'r'"],
    );
}

#[test]
fn mut_loan_blocks_shared_reborrow() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          s: &i64;
          entry:
            r = &mut x;
            s = &x;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot borrow as & 'x': already borrowed by 'r'"]);
}

#[test]
fn mut_loan_blocks_mut_reborrow() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          s: &mut i64;
          entry:
            r = &mut x;
            s = &mut x;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot borrow as &mut 'x': already borrowed by 'r'"],
    );
}

// === Loan ends when borrower is consumed ===

#[test]
fn access_ok_after_borrower_moved_to_call() {
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            call sink(move r);
            x = 1;
            return
        }
        ",
    );
}

// === Field-level precision ===

#[test]
fn disjoint_field_borrows_ok() {
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: i64 b: i64 }
        extern fn sink(r: &mut i64);
        fn f(p: P) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut p.a;
            y = copy p.b;
            call sink(move r);
            return
        }
        ",
    );
}

#[test]
fn same_field_borrow_conflicts() {
    let (errs, _) = run("
        struct Copy Drop P { a: i64 b: i64 }
        extern fn sink(r: &mut i64);
        fn f(p: P) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut p.a;
            y = copy p.a;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'p.a': already borrowed by 'r'"]);
}

#[test]
fn access_to_parent_of_borrowed_field_conflicts() {
    // Borrowing a field freezes the whole path from that field
    // upward — moving the parent p would move the borrowed field.
    let (errs, _) = run("
        struct Copy Drop P { a: i64 b: i64 }
        extern fn sink(r: &mut i64);
        extern fn takep(p: P);
        fn f(p: P) {
          r: &mut i64;
          entry:
            r = &mut p.a;
            call takep(move p);
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot move from 'p': already borrowed by 'r'"]);
}

// === Access through borrower still allowed ===

#[test]
fn read_through_borrower_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          y: i64;
          entry:
            r = &mut x;
            y = copy r.*;
            return
        }
        ",
    );
}

// === Ref transfer via `dst = move src` ===

#[test]
fn ref_transfer_carries_obligation_ok() {
    // Moving an &out param to a local: the local inherits the
    // pointee obligation, satisfies it via *z = 42.
    assert_no_diagnostics(
        "
        fn f(x: &out i64) {
          z: &out i64;
          entry:
            z = move x;
            z.* = 42;
            return
        }
        ",
    );
}

#[test]
fn ref_transfer_leaves_source_moved_error_on_reuse() {
    // After transfer, x is Moved — can't use it again.
    let (errs, _) = run("
        extern fn sink(r: &out i64);
        fn f(x: &out i64) {
          z: &out i64;
          entry:
            z = move x;
            z.* = 1;
            call sink(move x);
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'x' is used after move"]);
}

#[test]
fn ref_transfer_preserves_loan_conflict() {
    // Local borrower r loans a. Transfer r to s. s still loans a;
    // direct access to a should still conflict.
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(a: i64) {
          r: &mut i64;
          s: &mut i64;
          entry:
            r = &mut a;
            s = move r;
            a = 1;
            call sink(move s);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'a': already borrowed by 's'"]);
}

#[test]
fn branch_of_ref_moves_both_params_leak() {
    // Program from a design discussion: which of x/y is initialized
    // depends on b. In each branch we init only one of them via z,
    // so the OTHER is a leak (its &out obligation is unmet on that
    // path). This program should be rejected.
    let (errs, _) = run("
        fn f(x: &out i64, y: &out i64, b: bool) {
          z: &out i64;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            z = move x;
            z.* = 1;
            goto end
          fbr:
            z = move y;
            z.* = 2;
            goto end
          end:
            return
        }
        ");
    // In `t`, y is untouched — unfulfilled obligation.
    // In `fbr`, x is untouched — unfulfilled obligation.
    // Both branches merge into `end` where refs are dropped from
    // the join (each side has different entries) but the linear-
    // leak scan catches Diverged params.
    let has_leak = errs
        .iter()
        .any(|e| e.contains("not consumed at return") || e.contains("has unfulfilled obligation"));
    assert!(
        has_leak,
        "expected some kind of leak/obligation error, got: {:?}",
        errs
    );
}

// ---------- Multi-loan (branch of borrows) ----------

#[test]
fn multi_loan_branch_of_borrows_a_or_b_ok() {
    // A branch-of-borrows: after the merge, r loans {a, b}. Both
    // are frozen. Consuming r via a call releases both. Direct
    // access to a or b after that is fine.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut i64);
        fn f(a: i64, b: i64, c: bool) {
          r: &mut i64;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            call sink(move r);
            a = 1;
            b = 2;
            return
        }
        ",
    );
}

#[test]
fn multi_loan_conflict_on_a_after_join() {
    // After the merge, r loans {a, b}. Writing directly to `a` is
    // a conflict — r may loan a.
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(a: i64, b: i64, c: bool) {
          r: &mut i64;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            a = 1;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'a': already borrowed by 'r'"]);
}

#[test]
fn multi_loan_conflict_on_b_after_join() {
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(a: i64, b: i64, c: bool) {
          r: &mut i64;
          entry:
            branch(copy c) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            b = 2;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'b': already borrowed by 'r'"]);
}

#[test]
fn multi_loan_disjoint_third_place_ok() {
    // r may loan {a, b}, but neither is c. Direct access to c is
    // fine.
    assert_no_diagnostics(
        "
        extern fn sink(r: &mut i64);
        fn f(a: i64, b: i64, c: i64, cond: bool) {
          r: &mut i64;
          entry:
            branch(copy cond) [true: t, false: fbr]
          t:
            r = &mut a;
            goto merge
          fbr:
            r = &mut b;
            goto merge
          merge:
            c = 3;
            call sink(move r);
            return
        }
        ",
    );
}

// ---------- Cross-kind exclusivity ----------
//
// All four exclusive kinds (&mut, &out, &drop, &uninit) are just
// "exclusive borrow" to the loan tracker — differ only in obligation.
// Each blocks direct write same as &mut.

#[test]
fn out_loan_blocks_direct_write() {
    let (errs, _) = run("
        extern fn take_out(r: &out i64);
        fn f() {
          x: i64;
          r: &out i64;
          entry:
            r = &out x;
            x = 42;
            call take_out(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

#[test]
fn drop_loan_blocks_direct_write() {
    let (errs, _) = run("
        extern fn take_drop(r: &drop i64);
        fn f(x: i64) {
          r: &drop i64;
          entry:
            r = &drop x;
            x = 42;
            call take_drop(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

#[test]
fn uninit_loan_blocks_direct_write() {
    let (errs, _) = run("
        extern fn take_uninit(r: &uninit i64);
        fn f() {
          x: i64;
          r: &uninit i64;
          entry:
            r = &uninit x;
            x = 42;
            call take_uninit(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

// ---------- Mixed-kind disjoint field loans ----------

#[test]
fn mixed_kind_disjoint_field_loans_ok() {
    // &mut p.a and &out p.b coexist — disjoint fields, kinds are
    // independent for exclusivity purposes.
    assert_no_diagnostics(
        "
        struct Copy Drop P { a: i64 b: i64 }
        extern fn use_mut(r: &mut i64);
        extern fn use_out(r: &out i64);
        fn f() {
          p: P;
          r: &mut i64;
          s: &out i64;
          entry:
            p.a = 1;
            r = &mut p.a;
            s = &out p.b;
            call use_mut(move r);
            call use_out(move s);
            return
        }
        ",
    );
}

// ---------- Nested field paths ----------
//
// paths_conflict compares steps one-by-one, so depth > 1 needs its
// own coverage.

#[test]
fn nested_field_ancestor_conflicts() {
    // Borrow p.a.x freezes p.a — reading p.a hits the loan.
    let (errs, _) = run("
        struct Copy Drop Inner { x: i64 y: i64 }
        struct Copy Drop Outer { i: Inner c: i64 }
        extern fn use_mut(r: &mut i64);
        fn f(o: Outer) {
          r: &mut i64;
          y: Inner;
          entry:
            r = &mut o.i.x;
            y = copy o.i;
            call use_mut(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'o.i': already borrowed by 'r'"]);
}

#[test]
fn nested_field_sibling_ok() {
    // p.a.x and p.a.y are disjoint — borrow of one lets the other be
    // read.
    assert_no_diagnostics(
        "
        struct Copy Drop Inner { x: i64 y: i64 }
        struct Copy Drop Outer { i: Inner c: i64 }
        extern fn use_mut(r: &mut i64);
        fn f(o: Outer) {
          r: &mut i64;
          z: i64;
          entry:
            r = &mut o.i.x;
            z = copy o.i.y;
            call use_mut(move r);
            return
        }
        ",
    );
}

#[test]
fn depth_three_field_sibling_ok_ancestor_conflicts() {
    // Borrowing `o.a.x.z` (depth 3) leaves `o.a.x.w` (sibling at
    // depth 3) readable, but `o.a.x` (ancestor at depth 2) still
    // conflicts. Confirms path-prefix comparison scales past depth 2.
    let (errs, _) = run("
        struct Copy Drop Innermost { z: i64 w: i64 }
        struct Copy Drop Inner { x: Innermost y: Innermost }
        struct Copy Drop Outer { a: Inner b: Inner }
        extern fn sink(r: &mut i64);
        extern fn take_i(i: Innermost);
        fn f(o: Outer) {
          r: &mut i64;
          y: Innermost;
          entry:
            r = &mut o.a.x.z;
            y = copy o.a.x;
            call sink(move r);
            call take_i(move y);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'o.a.x': already borrowed by 'r'"]);
}

// ---------- Borrower overwrite ----------

#[test]
fn borrower_overwrite_releases_old_loan_ok() {
    // r first borrows x, then is overwritten to borrow y. After the
    // overwrite, x is no longer loaned — direct write to x is fine.
    assert_no_diagnostics(
        "
        extern fn use_mut(r: &mut i64);
        fn f(x: i64, y: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            r = &mut y;
            x = 42;
            call use_mut(move r);
            return
        }
        ",
    );
}

#[test]
fn borrower_overwrite_new_loan_active() {
    // After the overwrite, y is loaned. Direct write to y conflicts.
    let (errs, _) = run("
        extern fn use_mut(r: &mut i64);
        fn f(x: i64, y: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            r = &mut y;
            y = 42;
            call use_mut(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'y': already borrowed by 'r'"]);
}

#[test]
fn field_borrower_overwrite_releases_old_loan_ok() {
    // Path-granular version of borrower_overwrite_releases_old_loan_ok:
    // b.p first borrows x, then is overwritten to borrow x2. After
    // the overwrite, x's loan is released — writing to x is legal.
    assert_no_diagnostics(
        "
        struct Move RefBox { p: &mut i64 }
        extern fn take_box(b: RefBox);
        fn f(x: i64, x2: i64) {
          b: RefBox;
          entry:
            b.p = &mut x;
            b.p = &mut x2;
            x = 42;
            call take_box(move b);
            return
        }
        ",
    );
}

// ---------- switchEnum access checked against loans ----------

#[test]
fn switch_on_loaned_enum_conflicts() {
    // switchEnum(e) is a discriminant read (AccessKind::Read); an
    // exclusive loan on e blocks it.
    let (errs, _) = run("
        enum Copy Drop Sel { A: unit B: unit }
        extern fn sink(r: &mut Sel);
        fn f(e: Sel) {
          r: &mut Sel;
          entry:
            r = &mut e;
            switchEnum(e) [A: a_lbl, B: b_lbl]
          a_lbl:
            call sink(move r);
            return
          b_lbl:
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot read 'e': already borrowed by 'r'"]);
}

// ---------- drop r vs drop *r ----------

#[test]
fn drop_borrower_closes_loan_ok() {
    // `drop r` consumes the borrower — its loan is released and
    // direct access to the previously-loaned place is legal.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            drop r;
            x = 42;
            return
        }
        ",
    );
}

#[test]
fn drop_deref_does_not_release_loan() {
    // `drop *r` consumes the pointee via r; the borrower r is still
    // live, so its loan on x still blocks direct access.
    let (errs, _) = run("
        extern fn sink(r: &mut i64);
        fn f(x: i64) {
          r: &mut i64;
          entry:
            r = &mut x;
            drop r.*;
            x = 42;
            call sink(move r);
            return
        }
        ");
    assert_errors_contain(&errs, &["cannot write to 'x': already borrowed by 'r'"]);
}

// ---------- Downcast projection borrows ----------
//
// TODO(reborrow): current behavior — extract_path treats Downcast as
// a regular path step, so loans on `o as V` are tracked at depth
// [Downcast(V)]. Same-projection access conflicts. Cross-variant
// projection is not testable today because a borrow clobbers the
// enum's refinement (variant_flow), so subsequent `o as W` fails
// on refinement grounds before reaching the loan tracker. Revisit
// this pinning when reborrow lands and variant-projected borrows
// can coexist through separate refinement lineages.

// ---------- Enum-payload loan transfer ----------
//
// Verifies that wrapping a live borrower into an enum variant correctly
// transfers and re-keys the loan under the variant path (e.g. `w as W`),
// so direct access to the originally-borrowed place still conflicts.
// Wrap needs `Move` because its payload is Move-only.

#[test]
fn enum_wrap_of_borrower_keeps_loan_active() {
    // Wrapping a live borrower into an enum variant re-keys the loan
    // from the source to the constructed variant path (e.g. `w as W`),
    // so direct access to the originally-borrowed place still
    // conflicts. Wrap needs `Move` because its payload is Move-only.
    let (errs, _) = run("
        enum Move Wrap { W: &mut i64 }
        extern fn take_wrap(w: Wrap);
        fn f(x: i64) {
          r: &mut i64;
          w: Wrap;
          entry:
            r = &mut x;
            w = Wrap::W(move r);
            x = 7;
            call take_wrap(move w);
            return
        }
        ");
    assert_errors_contain(&errs, &["already borrowed"]);
}

#[test]
fn enum_wrap_of_borrower_consumed_releases_loan() {
    // Positive path: after the enum-wrapped borrower is moved to a
    // callee, direct access to x is legal. Should pass today AND
    // after the loan re-key fix (loan is discharged either way).
    assert_no_diagnostics(
        "
        enum Move Wrap { W: &mut i64 }
        extern fn take_wrap(w: Wrap);
        fn f(x: i64) {
          r: &mut i64;
          w: Wrap;
          entry:
            r = &mut x;
            w = Wrap::W(move r);
            call take_wrap(move w);
            x = 7;
            return
        }
        ",
    );
}

// ---------- Struct-move re-key (positive path already supported) ----------

#[test]
fn struct_move_rekeys_field_loan() {
    // Moving a struct whose field holds a borrower re-keys the
    // field's loan onto the parallel path under the target
    // (`a.p` → `b.p`), so direct access to the borrowed place
    // still conflicts.
    let (errs, _) = run("
        struct Move RefBox { p: &mut i64 v: i64 }
        extern fn sink(y: RefBox);
        fn f(x: i64) {
          a: RefBox;
          b: RefBox;
          entry:
            a.p = &mut x;
            a.v = 0;
            b = move a;
            x = 42;
            call sink(move b);
            return
        }
        ");
    assert_errors_contain(&errs, &["already borrowed"]);
}

#[test]
fn downcast_projection_borrow_same_variant_conflicts() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: i64 }
        extern fn sink(r: &mut i64);
        fn f() {
          o: Option;
          r: &mut i64;
          y: i64;
          entry:
            o = Option::Some(1);
            switchEnum(o) [None: n_arm, Some: s_arm]
          s_arm:
            r = &mut o as Some;
            y = copy o as Some;
            call sink(move r);
            return
          n_arm:
            unreachable
        }
        ");
    // Substring — variant_flow may also error on the clobbered
    // refinement, but the loan conflict is what we're pinning here.
    assert_errors_contain(&errs, &["already borrowed by 'r'"]);
}
