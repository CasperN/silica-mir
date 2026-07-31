use super::check::{check_program, check_return_leaks};
use super::drop_elaboration::*;
use crate::diagnostics::Diagnostics;
use crate::mir::env::IndexedProgram;
use crate::mir::parser::Parser;
use crate::mir::pretty_print::pretty_print;

/// Run the full parse → typecheck → elaborate pipeline, returning the
/// mutated program for inspection.
fn elaborate_src(src: &str) -> IndexedProgram {
    let program = Parser::parse_or_panic(src);
    let mut d = Diagnostics::default();
    let mut indexed = IndexedProgram::build(&program).0;
    indexed.typecheck(&mut d);
    elaborate(&mut indexed);
    indexed
}

/// Assert that elaborating `before` yields a program whose
/// pretty-printed form equals `expected` (leading/trailing whitespace
/// stripped on each). This pins the exact position, ordering, and
/// content of inserted drops.
#[track_caller]
fn assert_elaborated_eq(before: &str, expected: &str) {
    let program = elaborate_src(before);
    let got = pretty_print(&program);
    let a = got.trim();
    let b = expected.trim();
    if a != b {
        panic!(
            "elaborated output differs\n--- expected ---\n{}\n--- got ---\n{}",
            b, a
        );
    }
}

/// Check that the elaborated program passes strict leak-check.
fn assert_strict_clean_after_elaboration(src: &str) {
    let program = elaborate_src(src);
    let mut d = Diagnostics::default();
    check_return_leaks(&program, &mut d);
    let errs = d.errors_str();
    let leak_errs: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("not consumed at return"))
        .collect();
    assert!(
        leak_errs.is_empty(),
        "expected no leaks after elaboration; got:\n  {}",
        leak_errs
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n  ")
    );
}

// ---------- `require_uninit` cleanup ----------

#[test]
fn require_uninit_does_not_forget_a_linear_value() {
    // The requirement stays unsatisfied. This test deliberately inspects
    // elaboration only; the post-elaboration place-state checker owns the
    // diagnostic.
    assert_elaborated_eq(
        "
            struct Linear: Move { }
            fn f(x: Linear) {
              entry:
                require_uninit x;
                abort
            }
            ",
        "\
struct Linear: Move {
}

fn f(x: Linear) {
  entry:
    require_uninit x;
    abort
}",
    );
}

#[test]
fn linear_require_uninit_remains_an_error_after_elaboration() {
    let program = Parser::parse_or_panic(
        "
        struct Linear: Move { }
        fn f(x: Linear) {
          entry:
            require_uninit x;
            return
        }
        ",
    );
    let mut elaborated = IndexedProgram::build(&program).0;
    elaborate(&mut elaborated);

    let mut d = Diagnostics::default();
    check_program(&elaborated, &mut d);
    let errors = d.errors_str();
    assert!(
        errors
            .iter()
            .any(|error| error.contains("[PS-RequireUninitNotSatisfied]")),
        "linear value was silently accepted after elaboration: {errors:?}",
    );
    assert!(
        !errors
            .iter()
            .any(|error| error.contains("[PS-ReturnValueLeak]")),
        "require_uninit should be the single authoritative leak diagnostic: {errors:?}",
    );
}

#[test]
fn require_uninit_prevents_redundant_divergent_edge_cleanup() {
    // The requirement cleans the initialized arm before it reaches the join.
    // The legacy divergent-edge fallback must plan from that elaborated
    // predecessor state, rather than inserting a second `drop x` on a split
    // edge after the requirement.
    assert_elaborated_eq(
        "
            fn f(b: bool) {
              x: i64;
              entry:
                branch(copy b) [true: initialized, false: empty]
              initialized:
                x = 1;
                require_uninit x;
                goto join
              empty:
                goto join
              join:
                return
            }
            ",
        "\
fn f(b: bool) {
  x: i64;
  entry:
    branch(copy b) [true: initialized, false: empty]
  initialized:
    x = 1;
    drop x;
    require_uninit x;
    goto join
  empty:
    goto join
  join:
    drop b;
    return
}",
    );
}

#[test]
fn require_uninit_elaboration_is_idempotent() {
    assert_idempotent(
        "
            fn f(x: i64) {
              entry:
                require_uninit x;
                return
            }
            ",
    );
}

// ---------- Deferred behaviors (pins current semantics) ----------

#[test]
fn diverged_state_splits_edge_and_drops_on_init_side() {
    // Where predecessors disagree on a var's init state, the join
    // yields `Diverged`. The elaborator splits each Init-side edge
    // via cfg_edit and inserts a drop there. Here `x` is Init at
    // `t`'s exit and Moved (NeverInit) at `fbr`'s exit; the
    // t→merge edge gets the drop. `b` (copy'd) stays Init at merge
    // and is dropped in the merge block itself.
    assert_elaborated_eq(
        "
            fn f(b: bool) {
              x: i64;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                goto merge
              merge:
                return
            }
            ",
        "\
fn f(b: bool) {
  x: i64;
  entry:
    branch(copy b) [true: t, false: fbr]
  t:
    x = 1;
    goto $edge0
  $edge0:
    drop x;
    goto merge
  fbr:
    goto merge
  merge:
    drop b;
    return
}",
    );
}

#[test]
fn diverged_elab_idempotent() {
    // Run elaboration twice; second run should be a no-op because
    // the first run's inserted drops already satisfy the leak check.
    let src = "
            fn f(b: bool) {
              x: i64;
              entry:
                branch(copy b) [true: t, false: fbr]
              t:
                x = 1;
                goto merge
              fbr:
                goto merge
              merge:
                return
            }
            ";
    let once = elaborate_src(src);
    let twice = {
        let mut program = once.clone();
        elaborate(&mut program);
        program
    };
    assert_eq!(pretty_print(&once), pretty_print(&twice));
}

// ---------- Idempotency ----------

#[test]
fn elaboration_is_idempotent() {
    let src = "fn f(x: i64) { entry: return }";
    let once = elaborate_src(src);

    // Elaborate the already-elaborated program a second time and
    // compare via pretty-printed forms.
    let mut twice = once.clone();
    elaborate(&mut twice);

    assert_eq!(pretty_print(&once), pretty_print(&twice));
}

// ---------- Post-elaboration strict check ----------

#[test]
fn strict_check_passes_after_elaboration_simple() {
    assert_strict_clean_after_elaboration("fn f(x: i64) { entry: return }");
}

#[test]
fn strict_check_passes_after_elaboration_with_locals() {
    assert_strict_clean_after_elaboration(
        "
            fn f(x: i64) {
              y: i64;
              z: i64;
              entry:
                y = copy x;
                z = 42;
                return
            }
            ",
    );
}

#[test]
fn strict_check_passes_after_elaboration_with_shared_ref() {
    // `&T` is Copy Drop — elaboration should insert a drop for it.
    assert_strict_clean_after_elaboration("fn f(r: &i64) { entry: return }");
}

#[test]
fn strict_check_passes_after_elaboration_with_copy_drop_struct() {
    assert_strict_clean_after_elaboration(
        "
            struct P: Copy + Drop { x: i64 y: i64 }
            fn f(p: P) { entry: return }
            ",
    );
}

#[test]
fn strict_check_passes_after_elaboration_with_copy_drop_enum() {
    assert_strict_clean_after_elaboration(
        "
            enum Option: Copy + Drop { None: unit Some: i64 }
            fn f(o: Option) { entry: return }
            ",
    );
}

#[test]
fn strict_check_passes_after_elaboration_with_mut_ref() {
    // `&mut T` is Drop (not Copy). Elaboration inserts a drop.
    assert_strict_clean_after_elaboration("fn f(r: &mut i64) { entry: return }");
}

#[test]
fn strict_check_passes_after_elaboration_with_multi_return() {
    // Each return-block gets its own drops; strict validates both.
    assert_strict_clean_after_elaboration(
        "
            fn f(b: bool, x: i64) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
    );
}

#[test]
fn strict_check_passes_after_elaboration_with_multi_block() {
    // Local written in an intermediate block still gets dropped at
    // the terminal return.
    assert_strict_clean_after_elaboration(
        "
            fn f() {
              y: i64;
              entry:
                goto mid
              mid:
                y = 42;
                goto end
              end:
                return
            }
            ",
    );
}

// ---------- Idempotency (extended) ----------

/// Assert that elaborating `src` once and elaborating that result again
/// yields identical pretty-printed output.
#[track_caller]
fn assert_idempotent(src: &str) {
    let once = elaborate_src(src);
    let mut twice = once.clone();
    elaborate(&mut twice);
    assert_eq!(
        pretty_print(&once),
        pretty_print(&twice),
        "elaboration is not idempotent on:\n{}",
        src
    );
}

#[test]
fn idempotent_with_copy_drop_struct() {
    assert_idempotent(
        "
            struct P: Copy + Drop { x: i64 y: i64 }
            fn f(p: P) {
              q: P;
              entry:
                q = copy p;
                return
            }
            ",
    );
}

#[test]
fn idempotent_with_reassignment() {
    // `x = 1; x = 2` leaves x Init at return. One drop suffices; a
    // second pass finds x already scheduled to be dropped once.
    assert_idempotent(
        "
            fn f() {
              x: i64;
              entry:
                x = 1;
                x = 2;
                return
            }
            ",
    );
}

#[test]
fn idempotent_with_multi_return() {
    assert_idempotent(
        "
            fn f(b: bool, x: i64) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
    );
}

// ---------- Unborrow interaction ----------

#[test]
fn idempotent_with_unborrow() {
    assert_idempotent(
        "
            fn f(x: i64) {
              r: &mut i64;
              entry:
                r = &mut x;
                unborrow r;
                return
            }
            ",
    );
}

// ---------- Known limitation ----------

#[test]
fn init_order_differs_from_decl_order_uses_decl_order() {
    // The elaborator sorts drops by reverse combined declaration
    // order (locals reverse, then params reverse). If the program
    // *initializes* in a different order, the resulting drop order
    // is NOT true LIFO by initialization time — this pins that
    // limitation. Fix requires per-write sequence numbers.
    //
    // Here `b` is declared before `a` but initialized after; reverse
    // decl gives us `drop b; drop a;` even though `b`'s value is
    // "younger."
    assert_elaborated_eq(
        "
            fn f() {
              a: i64;
              b: i64;
              entry:
                b = 1;
                a = 2;
                return
            }
            ",
        "\
fn f() {
  a: i64;
  b: i64;
  entry:
    b = 1;
    a = 2;
    drop b;
    drop a;
    return
}",
    );
}

#[test]
fn strict_check_still_fails_for_linear_leak() {
    // Elaboration doesn't paper over linear leaks; strict should
    // still report them.
    let src = "
            struct Linear { r: &out i64 }
            fn f(x: Linear) {
              entry:
                return
            }
        ";
    let program = Parser::parse_or_panic(src);
    let mut d = Diagnostics::default();
    let mut elaborated = IndexedProgram::build(&program).0;
    elaborated.typecheck(&mut d);
    elaborate(&mut elaborated);

    let mut d2 = Diagnostics::default();
    check_return_leaks(&elaborated, &mut d2);

    let errs = d2.errors_str();
    assert!(
        errs.iter()
            .any(|e| e.contains("value 'x'") && e.contains("not consumed")),
        "expected linear leak to survive elaboration; got: {:?}",
        errs
    );
}
