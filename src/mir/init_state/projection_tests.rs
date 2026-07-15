//! Init state — reads and writes through projections.
//!
//! Covers place-projection cases: `branch(op)` and `switchEnum(place)`
//! terminator reads, downcast reads (`p as V`), deref reads (`*r`, not
//! tracked because refs live outside the locals tree), and writes
//! through variant projection (`o as V = ...`) with init-state
//! prerequisites on the enum.

use crate::mir::test_util::*;

// ---------- Terminator reads ----------

#[test]
fn branch_reads_cond() {
    let (errs, _) = run("
        fn f() {
          b: bool;
          entry:
            branch(copy b) [true: t, false: fbr]
          t: return
          fbr: return
        }
        ");
    assert_errors_contain(&errs, &["variable 'b' is used before initialization"]);
}

#[test]
fn switch_enum_reads_place() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: i64 }
        fn f() {
          o: Option;
          entry:
            switchEnum(o) [None: end, Some: end]
          end:
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

// ---------- Downcast reads ----------

#[test]
fn downcast_read_checks_root_var() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: i64 }
        fn f() {
          o: Option;
          a: i64;
          entry:
            a = copy o as Some;
            return
        }
        ");
    assert_errors_contain(&errs, &["variable 'o' is used before initialization"]);
}

// ---------- Deref reads ----------

#[test]
fn deref_read_is_not_checked() {
    // `*r` deref-reads go through the ref; init_state doesn't track
    // pointee init on the locals side (the lifetime pass does via
    // RefState). So a Uninit-pointee deref through a well-formed ref
    // param doesn't error here — it errors in the ref-obligation check.
    assert_no_diagnostics(
        "
        fn f(r: &i64) {
          a: i64;
          entry:
            a = copy r.*;
            return
        }
        ",
    );
}

// ---------- Downcast writes ----------

#[test]
fn downcast_write_on_init_enum_ok() {
    // Writing through a variant projection is fine when the enum is
    // Init AND refined to the correct variant.
    assert_no_diagnostics(
        "
        enum Copy Drop Option { None: unit Some: i64 }
        fn f(o: Option) {
          entry:
            switchEnum(o) [None: n, Some: s]
          s:
            o as Some = 7;
            return
          n: return
        }
        ",
    );
}

#[test]
fn downcast_write_on_uninit_enum_error() {
    // Enum construction goes via `Name::V(...)`; refining an uninit
    // enum by writing a variant payload is not allowed.
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: i64 }
        fn f() {
          o: Option;
          entry:
            o as Some = 7;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot write through variant projection: 'o' is not initialized here"],
    );
}

#[test]
fn downcast_write_on_moved_enum_error() {
    let (errs, _) = run("
        enum Copy Drop Option { None: unit Some: i64 }
        fn f(o: Option) {
          sink: Option;
          entry:
            sink = move o;
            o as Some = 7;
            return
        }
        ");
    assert_errors_contain(
        &errs,
        &["cannot write through variant projection: 'o' is not initialized here"],
    );
}
