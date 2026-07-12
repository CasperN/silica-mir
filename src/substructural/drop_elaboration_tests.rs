use super::drop_elaboration::*;
use crate::ast::Program;
use crate::diagnostics::Diagnostics;
use crate::parser::Parser;
use crate::pretty_print::pretty_print;
use crate::substructural::check::check_return_leaks;
use crate::type_check;

/// Run the full parse → typecheck → elaborate pipeline, returning the
/// mutated program for inspection.
fn elaborate_src(src: &str) -> Program {
    let mut program = Parser::new(src.to_string()).parse().unwrap();
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&program).0;
    env.typecheck(&mut d);
    elaborate(&mut program, &env);
    program
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
    let env = type_check::Env::build(&program).0;
    env.typecheck(&mut d);
    check_return_leaks(&env, &mut d);
    let leak_errs: Vec<&String> = d
        .errors
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

// ---------- Basic insertion ----------

#[test]
fn elaborates_single_drop_param() {
    assert_elaborated_eq(
        "fn f(x: i64) { entry: return }",
        "\
fn f(x: i64) {
  entry:
    drop x;
    return
}",
    );
}

#[test]
fn elaborates_multiple_vars_in_reverse_decl_order() {
    // Reverse combined order (locals first, then params): y, x, c, b, a.
    assert_elaborated_eq(
        "
            fn f(a: i64, b: i64, c: i64) {
              x: i64;
              y: i64;
              entry:
                x = 1;
                y = 2;
                return
            }
            ",
        "\
fn f(a: i64, b: i64, c: i64) {
  x: i64;
  y: i64;
  entry:
    x = 1;
    y = 2;
    drop y;
    drop x;
    drop c;
    drop b;
    drop a;
    return
}",
    );
}

#[test]
fn does_not_drop_linear_vars() {
    assert_elaborated_eq(
        "
            struct Linear { r: &out i64 }
            extern fn sink(x: Linear);
            fn f(x: Linear) {
              entry:
                call sink(move x);
                return
            }
            ",
        "\
struct Linear {
  r: &out i64
}

extern fn sink(x: Linear);

fn f(x: Linear) {
  entry:
    call sink(move x);
    return
}",
    );
}

#[test]
fn does_not_drop_moved_vars() {
    assert_elaborated_eq(
        "
            extern fn take(a: i64);
            fn f(x: i64) {
              entry:
                call take(move x);
                return
            }
            ",
        "\
extern fn take(a: i64);

fn f(x: i64) {
  entry:
    call take(move x);
    return
}",
    );
}

#[test]
fn does_not_drop_never_init_locals() {
    assert_elaborated_eq(
        "
            fn f() {
              x: i64;
              entry:
                return
            }
            ",
        "\
fn f() {
  x: i64;
  entry:
    return
}",
    );
}

// ---------- Different Drop types ----------

#[test]
fn elaborates_drop_struct() {
    assert_elaborated_eq(
        "
            struct Copy Drop P { x: i64 y: i64 }
            fn f(p: P) { entry: return }
            ",
        "\
struct Copy Drop P {
  x: i64
  y: i64
}

fn f(p: P) {
  entry:
    drop p;
    return
}",
    );
}

#[test]
fn elaborates_drop_enum() {
    assert_elaborated_eq(
        "
            enum Copy Drop Option { None: unit Some: i64 }
            fn f(o: Option) { entry: return }
            ",
        "\
enum Copy Drop Option {
  None: unit
  Some: i64
}

fn f(o: Option) {
  entry:
    drop o;
    return
}",
    );
}

#[test]
fn elaborates_mut_ref_param() {
    // `&mut T` is Drop (though not Copy) — reference value may be
    // forgotten. Elaboration inserts a drop for it.
    assert_elaborated_eq(
        "fn f(r: &mut i64) { entry: return }",
        "\
fn f(r: &mut i64) {
  entry:
    drop r;
    return
}",
    );
}

#[test]
fn does_not_drop_out_ref_param() {
    // `&out T` is linear — never silently dropped. (This program
    // leaks under the checker; we're only verifying the elaborator.)
    assert_elaborated_eq(
        "fn f(r: &out i64) { entry: return }",
        "\
fn f(r: &out i64) {
  entry:
    return
}",
    );
}

// ---------- Interaction with existing statements ----------

#[test]
fn respects_explicit_user_drop() {
    // User already dropped `x` — elaboration doesn't add a second one.
    assert_elaborated_eq(
        "
            fn f(x: i64) {
              entry:
                drop x;
                return
            }
            ",
        "\
fn f(x: i64) {
  entry:
    drop x;
    return
}",
    );
}

#[test]
fn reassignment_still_leaves_one_drop() {
    // `x = 1; x = 2;` is a single Init state at return — one drop.
    // Pre-overwrite drops are a future slice.
    assert_elaborated_eq(
        "
            fn f() {
              x: i64;
              entry:
                x = 1;
                x = 2;
                return
            }
            ",
        "\
fn f() {
  x: i64;
  entry:
    x = 1;
    x = 2;
    drop x;
    return
}",
    );
}

// ---------- Deferred behaviors (pins current phase-1 semantics) ----------

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
            fn f(b: boolean) {
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
fn f(b: boolean) {
  x: i64;
  entry:
    branch(copy b) [true: t, false: fbr]
  t:
    x = 1;
    goto t__to__merge
  t__to__merge:
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
fn extern_function_untouched() {
    assert_elaborated_eq("extern fn f(x: i64);", "extern fn f(x: i64);");
}

#[test]
fn diverged_on_multi_case_switch() {
    // switchEnum with two arms: one initializes `y`, one doesn't.
    // Elaborator splits the Init-side edge.
    assert_elaborated_eq(
        "
            enum Copy Drop Sel { A: unit B: unit }
            fn f(s: Sel) {
              y: i64;
              entry:
                switchEnum(s) [A: a_lbl, B: b_lbl]
              a_lbl:
                y = 1;
                goto end
              b_lbl:
                goto end
              end:
                return
            }
            ",
        "\
enum Copy Drop Sel {
  A: unit
  B: unit
}

fn f(s: Sel) {
  y: i64;
  entry:
    switchEnum(s) [A: a_lbl, B: b_lbl]
  a_lbl:
    y = 1;
    goto a_lbl__to__end
  a_lbl__to__end:
    drop y;
    goto end
  b_lbl:
    goto end
  end:
    drop s;
    return
}",
    );
}

#[test]
fn diverged_elab_idempotent() {
    // Run elaboration twice; second run should be a no-op because
    // the first run's inserted drops already satisfy the leak check.
    let src = "
            fn f(b: boolean) {
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
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program).0;
        env.typecheck(&mut d);
        elaborate(&mut program, &env);
        program
    };
    assert_eq!(pretty_print(&once), pretty_print(&twice));
}

#[test]
fn multi_block_return_sees_upstream_writes() {
    // Local `y` is written in `mid`; the return in `end` should still
    // find `y` Init and drop it.
    assert_elaborated_eq(
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
        "\
fn f() {
  y: i64;
  entry:
    goto mid
  mid:
    y = 42;
    goto end
  end:
    drop y;
    return
}",
    );
}

// ---------- Multiple returns ----------

#[test]
fn elaborates_each_return_independently() {
    // Two returns, each drops x and b (reverse decl order).
    assert_elaborated_eq(
        "
            fn f(b: boolean, x: i64) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
        "\
fn f(b: boolean, x: i64) {
  entry:
    branch(copy b) [true: t, false: fbr]
  t:
    drop x;
    drop b;
    return
  fbr:
    drop x;
    drop b;
    return
}",
    );
}

// ---------- Idempotency ----------

#[test]
fn elaboration_is_idempotent() {
    let src = "fn f(x: i64) { entry: return }";
    let once = elaborate_src(src);

    // Elaborate the already-elaborated program a second time and
    // compare via pretty-printed forms.
    let mut twice = once.clone();
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&twice).0;
    env.typecheck(&mut d);
    elaborate(&mut twice, &env);

    assert_eq!(pretty_print(&once), pretty_print(&twice));
}

// ---------- Partial-state elaboration ----------

#[test]
fn partial_state_emits_per_leaf_drop() {
    // Elaborator walks the Partial map and emits drops only for the
    // Init leaves — here just `p.x`, since `p.y` is NeverInit.
    assert_elaborated_eq(
        "
            struct Copy Drop P { x: i64 y: i64 }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                return
            }
            ",
        "\
struct Copy Drop P {
  x: i64
  y: i64
}

fn f() {
  p: P;
  entry:
    p.x = 1;
    drop p.x;
    return
}",
    );
}

#[test]
fn partial_after_field_move_emits_drop_for_remaining_field() {
    // Param `p` starts Init; moving p.x leaves state as
    // Partial({x: Moved, y: Init}). Only `p.y` needs a drop.
    assert_elaborated_eq(
        "
            struct Copy Drop P { x: i64 y: i64 }
            fn f(p: P) {
              a: i64;
              entry:
                a = move p.x;
                return
            }
            ",
        "\
struct Copy Drop P {
  x: i64
  y: i64
}

fn f(p: P) {
  a: i64;
  entry:
    a = move p.x;
    drop a;
    drop p.y;
    return
}",
    );
}

#[test]
fn nested_partial_walks_recursively() {
    // Inner struct has two i64 fields; only one is written. Elaborator
    // reaches through the outer Partial to the leaf.
    assert_elaborated_eq(
        "
            struct Copy Drop Inner { a: i64 b: i64 }
            struct Copy Drop Outer { i: Inner c: i64 }
            fn f() {
              o: Outer;
              entry:
                o.i.a = 1;
                return
            }
            ",
        "\
struct Copy Drop Inner {
  a: i64
  b: i64
}

struct Copy Drop Outer {
  i: Inner
  c: i64
}

fn f() {
  o: Outer;
  entry:
    o.i.a = 1;
    drop o.i.a;
    return
}",
    );
}

#[test]
fn partial_field_drop_lifo_order() {
    // Both fields Init → both dropped in reverse declaration order:
    // p.y before p.x.
    //
    // Note: `p.x = 1; p.y = 2` canonicalizes to whole-var Init (all
    // fields uniform), so the elaborator drops `p` as a single unit
    // rather than field-by-field. This test uses distinct init
    // sequences to keep the state Partial.
    assert_elaborated_eq(
        "
            struct Copy Drop P { x: i64 y: i64 }
            fn f(src: P) {
              p: P;
              a: i64;
              entry:
                a = move src.x;
                p.x = 1;
                p.y = copy src.y;
                return
            }
            ",
        "\
struct Copy Drop P {
  x: i64
  y: i64
}

fn f(src: P) {
  p: P;
  a: i64;
  entry:
    a = move src.x;
    p.x = 1;
    p.y = copy src.y;
    drop a;
    drop p;
    drop src.y;
    return
}",
    );
}

// ---------- Not-elaborated states ----------

#[test]
fn only_return_blocks_get_drops() {
    // `abort` and `unreachable` are not `return` — no drops inserted
    // (they're the escape hatches; obligations are waived).
    assert_elaborated_eq(
        "
            fn f(x: i64) {
              entry:
                abort
            }
            ",
        "\
fn f(x: i64) {
  entry:
    abort
}",
    );
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
            struct Copy Drop P { x: i64 y: i64 }
            fn f(p: P) { entry: return }
            ",
    );
}

#[test]
fn strict_check_passes_after_elaboration_with_copy_drop_enum() {
    assert_strict_clean_after_elaboration(
        "
            enum Copy Drop Option { None: unit Some: i64 }
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
            fn f(b: boolean, x: i64) {
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
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&twice).0;
    env.typecheck(&mut d);
    elaborate(&mut twice, &env);
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
            struct Copy Drop P { x: i64 y: i64 }
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
            fn f(b: boolean, x: i64) {
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
fn does_not_drop_unborrowed_ref() {
    // After `unborrow r`, the borrower is Moved — the elaborator
    // must not insert a `drop r`. It should still drop the (now
    // thawed and Init) pointee `x`.
    assert_elaborated_eq(
        "
            fn f(x: i64) {
              r: &mut i64;
              entry:
                r = &mut x;
                unborrow r;
                return
            }
            ",
        "\
fn f(x: i64) {
  r: &mut i64;
  entry:
    r = &mut x;
    unborrow r;
    drop x;
    return
}",
    );
}

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
    let mut program = Parser::new(src.to_string()).parse().unwrap();
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&program).0;
    env.typecheck(&mut d);
    elaborate(&mut program, &env);

    let mut d2 = Diagnostics::default();
    let env2 = type_check::Env::build(&program).0;
    env2.typecheck(&mut d2);
    check_return_leaks(&env2, &mut d2);

    assert!(
        d2.errors
            .iter()
            .any(|e| e.contains("value 'x'") && e.contains("not consumed")),
        "expected linear leak to survive elaboration; got: {:?}",
        d2.errors
    );
}

// ---------- Pre-overwrite drop (punch-list gap) ----------
//
// README punch list: "Elaborate `drop p` if `p` is initialized and
// being assigned to or sent to an `&out` function." Today, drop is a
// bitwise forget so overwriting a Drop-marked type silently succeeds
// with no destructor call. Once custom `Drop::drop` exists, the
// elaborator will need to insert `drop x` before the reassignment.
// This test pins today's behavior: no `drop` in the elaborated output
// between the two assigns.

#[test]
fn overwrite_of_drop_type_is_silently_bitwise_forgotten_today() {
    // Drop-marked struct — reassignment allowed without any inserted
    // drop. When custom destructors land, the elaborated form will
    // grow a `drop x;` between the two assigns.
    assert_elaborated_eq(
        "
        struct Copy Drop P { a: i64 }
        extern fn use_p(p: P);
        fn f(p1: P, p2: P) {
          x: P;
          entry:
            x = move p1;
            x = move p2;
            call use_p(move x);
            return
        }
        ",
        "\
struct Copy Drop P {
  a: i64
}

extern fn use_p(p: P);

fn f(p1: P, p2: P) {
  x: P;
  entry:
    x = move p1;
    x = move p2;
    call use_p(move x);
    return
}",
    );
}
