//! Init state — `Partial` states for structs.
//!
//! Covers field-granular writes (per-field init tracking, promotion to
//! Init when every field is written), reads of partial structs (error
//! on the whole, error on uninit fields, OK on inited fields), moves of
//! fields (leaves siblings init), nested-struct partial paths, and
//! whole-struct reassignment after partial init.

use crate::test_util::*;

#[test]
fn field_writes_complete_init_ok() {
    // Writing every declared field of a struct-typed local promotes it
    // to fully Init.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f() {
          p: P;
          a: number;
          entry:
            p.x = 1;
            p.y = 2;
            a = copy p.x;
            return
        }
        ",
    );
}

#[test]
fn partial_field_write_leaves_root_partial_error() {
    // Only one field written; the whole struct is not fully init and
    // reading it errors.
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f() {
          p: P;
          q: P;
          entry:
            p.x = 1;
            q = copy p;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is not fully initialized here"]);
}

#[test]
fn read_uninit_field_of_partial_struct_error() {
    // Field-granular: writing p.x doesn't init p.y — reading p.y errors.
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f() {
          p: P;
          a: number;
          entry:
            p.x = 1;
            a = copy p.y;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is used before initialization"]);
}

#[test]
fn move_of_field_leaves_other_fields_init_ok() {
    // Struct comes in fully-init from a param; moving one field must
    // leave the other still readable. Elaboration inserts the drop
    // for the remaining p.y automatically.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f(p: P) {
          a: number;
          b: number;
          entry:
            a = move p.x;
            b = copy p.y;
            return
        }
        ",
    );
}

#[test]
fn move_of_field_then_read_that_field_error() {
    let (errs, _) = run("
        struct P { x: number y: number }
        fn f(p: P) {
          a: number;
          b: number;
          entry:
            a = move p.x;
            b = copy p.x;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'p' is used after move"]);
}

#[test]
fn nested_field_writes_complete_init_ok() {
    // Inner struct fields inited via nested paths; the whole outer
    // struct collapses to Init once every leaf is written.
    assert_no_diagnostics(
        "
        struct Copy Drop Inner { a: number b: number }
        struct Copy Drop Outer { i: Inner c: number }
        fn f() {
          o: Outer;
          n: number;
          entry:
            o.i.a = 1;
            o.i.b = 2;
            o.c = 3;
            n = copy o.i.a;
            return
        }
        ",
    );
}

#[test]
fn nested_partial_read_of_uninit_inner_field_error() {
    let (errs, _) = run("
        struct Inner { a: number b: number }
        struct Outer { i: Inner c: number }
        fn f() {
          o: Outer;
          n: number;
          entry:
            o.i.a = 1;
            o.c = 3;
            n = copy o.i.b;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

#[test]
fn whole_struct_assign_after_partial_ok() {
    // Even if we partially init, a whole-struct assign resets to Init.
    assert_no_diagnostics(
        "
        struct Copy Drop P { x: number y: number }
        fn f(src: P) {
          p: P;
          a: number;
          entry:
            p.x = 1;
            p = move src;
            a = copy p.y;
            return
        }
        ",
    );
}
