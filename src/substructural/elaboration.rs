//! Drop elaboration pass — slice 1: return-leak drops.
//!
//! Inserts explicit `drop p` statements before each `return` for every
//! variable whose init state is `Init` at that point and whose type is
//! Drop. Turns implicit forgets into explicit consumption so a
//! subsequent leak check can validate the elaborated MIR.
//!
//! Ordering: reverse combined declaration order (locals reverse first,
//! then params reverse). TODO(elaboration): per-write sequence numbers
//! would give true LIFO by *initialization* order, matching the README's
//! stated semantics. Declaration-order is a reasonable first cut and
//! agrees with LIFO for programs that init in declaration order.
//!
//! **Not yet handled** (future slices):
//!   * `Partial` states at return — need per-leaf drops walking the
//!     struct field tree.
//!   * `Diverged` states — need per-edge drops inserted on the divergent
//!     join predecessors.
//!   * Pre-overwrite drops (`p = ...` where p was Init).
//!   * CFG-join disagreement resolution, with critical-edge splitting.
//!
//! **Idempotent**: rerunning the pass produces no additional drops. A
//! dropped variable transitions to `Moved` in the init dataflow, so a
//! second run finds nothing to insert.

use crate::ast::*;
use crate::init_state::{self, InitState, PointState};
use crate::substructural::composition::class_of;
use crate::type_check::Env;
use indexmap::IndexMap;

/// Insert return-leak drops in `program` using analysis state from `env`.
/// `env` should have been built from `program` before calling; the returned
/// program will have additional `Statement::Drop` entries appended to blocks
/// that end in `Return`.
pub fn elaborate(program: &mut Program, env: &Env) {
    // Phase 1 (immutable): plan drops per function per return-block.
    let mut plans: IndexMap<String, IndexMap<String, Vec<Place>>> = IndexMap::new();
    for func in env.functions.values() {
        let mut fn_plans: IndexMap<String, Vec<Place>> = IndexMap::new();
        for (block, state) in init_state::states_before_returns(env, func) {
            let drops = plan_drops_at_return(func, &state, env);
            if !drops.is_empty() {
                fn_plans.insert(block.label.clone(), drops);
            }
        }
        if !fn_plans.is_empty() {
            plans.insert(func.name.clone(), fn_plans);
        }
    }

    // Phase 2 (mutable): apply planned insertions to `program`.
    for decl in &mut program.declarations {
        let Declaration::Fn(func) = decl else { continue; };
        let Some(fn_plans) = plans.get(&func.name) else { continue; };
        let Some(body) = &mut func.body else { continue; };
        for block in &mut body.blocks {
            let Some(drops) = fn_plans.get(&block.label) else { continue; };
            // Use the terminator's span as the synthetic span for inserted
            // drops — points the user at the return they're associated with.
            let span = block.terminator_span;
            for place in drops {
                block.statements.push((Statement::Drop(place.clone()), span));
            }
        }
    }
}

fn plan_drops_at_return(func: &Function, state: &PointState, env: &Env) -> Vec<Place> {
    // Combined declaration order: params, then locals. LIFO drop = reverse.
    let mut order: Vec<(String, Type)> = Vec::new();
    for p in &func.params {
        order.push((p.name.clone(), p.ty.clone()));
    }
    if let Some(body) = &func.body {
        for l in &body.locals {
            order.push((l.name.clone(), l.ty.clone()));
        }
    }

    let mut drops = Vec::new();
    for (name, ty) in order.iter().rev() {
        let Some(s) = state.get(name) else { continue; };
        // Slice 1 handles only whole-var Init. Partial/Diverged require
        // per-leaf or per-edge drops respectively — future slices.
        if !matches!(s, InitState::Init) { continue; }
        if !class_of(ty, env).drop { continue; }
        drops.push(Place::Var(name.clone()));
    }
    drops
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let env = type_check::Env::build(&program, &mut d);
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
        let env = type_check::Env::build(&program, &mut d);
        env.typecheck(&mut d);
        check_return_leaks(&env, &mut d);
        let leak_errs: Vec<&String> = d.errors.iter()
            .filter(|e| e.contains("not consumed at return"))
            .collect();
        assert!(
            leak_errs.is_empty(),
            "expected no leaks after elaboration; got:\n  {}",
            leak_errs.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n  ")
        );
    }

    // ---------- Basic insertion ----------

    #[test]
    fn elaborates_single_drop_param() {
        assert_elaborated_eq(
            "fn f(x: number) { entry: return }",
            "\
fn f(x: number) {
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
            fn f(a: number, b: number, c: number) {
              x: number;
              y: number;
              entry:
                x = 1;
                y = 2;
                return
            }
            ",
            "\
fn f(a: number, b: number, c: number) {
  x: number;
  y: number;
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
            struct Linear { r: &out number }
            extern fn sink(x: Linear);
            fn f(x: Linear) {
              entry:
                call sink(move x);
                return
            }
            ",
            "\
struct Linear {
  r: &out number
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
            extern fn take(a: number);
            fn f(x: number) {
              entry:
                call take(move x);
                return
            }
            ",
            "\
extern fn take(a: number);

fn f(x: number) {
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
              x: number;
              entry:
                return
            }
            ",
            "\
fn f() {
  x: number;
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
            struct Copy Drop P { x: number y: number }
            fn f(p: P) { entry: return }
            ",
            "\
struct Copy Drop P {
  x: number
  y: number
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
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) { entry: return }
            ",
            "\
enum Copy Drop Option {
  None: unit
  Some: number
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
            "fn f(r: &mut number) { entry: return }",
            "\
fn f(r: &mut number) {
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
            "fn f(r: &out number) { entry: return }",
            "\
fn f(r: &out number) {
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
            fn f(x: number) {
              entry:
                drop x;
                return
            }
            ",
            "\
fn f(x: number) {
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
              x: number;
              entry:
                x = 1;
                x = 2;
                return
            }
            ",
            "\
fn f() {
  x: number;
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
    fn diverged_state_not_elaborated_yet() {
        // Where predecessors disagree on a var's init state, the join
        // yields `Diverged`. Current elaborator doesn't emit drops for
        // those; a future slice will split edges and drop on the Init
        // side. Here `x` is Diverged at the merge; `b` (copy'd) stays
        // Init and gets dropped.
        assert_elaborated_eq(
            "
            fn f(b: boolean) {
              x: number;
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
  x: number;
  entry:
    branch(copy b) [true: t, false: fbr]
  t:
    x = 1;
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
        assert_elaborated_eq(
            "extern fn f(x: number);",
            "extern fn f(x: number);",
        );
    }

    #[test]
    fn multi_block_return_sees_upstream_writes() {
        // Local `y` is written in `mid`; the return in `end` should still
        // find `y` Init and drop it.
        assert_elaborated_eq(
            "
            fn f() {
              y: number;
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
  y: number;
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
            fn f(b: boolean, x: number) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
            }
            ",
            "\
fn f(b: boolean, x: number) {
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
        let src = "fn f(x: number) { entry: return }";
        let once = elaborate_src(src);

        // Elaborate the already-elaborated program a second time and
        // compare via pretty-printed forms.
        let mut twice = once.clone();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&twice, &mut d);
        env.typecheck(&mut d);
        elaborate(&mut twice, &env);

        assert_eq!(pretty_print(&once), pretty_print(&twice));
    }

    // ---------- Not-elaborated states ----------

    #[test]
    fn partial_state_not_elaborated_yet() {
        // Current elaborator doesn't emit drops for Partial states: the
        // partial-init `p` gets no drop even though its type is Drop.
        // Future slice will walk the field tree and emit per-leaf drops.
        assert_elaborated_eq(
            "
            struct Copy Drop P { x: number y: number }
            fn f() {
              p: P;
              entry:
                p.x = 1;
                return
            }
            ",
            "\
struct Copy Drop P {
  x: number
  y: number
}

fn f() {
  p: P;
  entry:
    p.x = 1;
    return
}",
        );
    }

    #[test]
    fn only_return_blocks_get_drops() {
        // `abort` and `unreachable` are not `return` — no drops inserted
        // (they're the escape hatches; obligations are waived).
        assert_elaborated_eq(
            "
            fn f(x: number) {
              entry:
                abort
            }
            ",
            "\
fn f(x: number) {
  entry:
    abort
}",
        );
    }

    // ---------- Post-elaboration strict check ----------

    #[test]
    fn strict_check_passes_after_elaboration_simple() {
        assert_strict_clean_after_elaboration(
            "fn f(x: number) { entry: return }",
        );
    }

    #[test]
    fn strict_check_passes_after_elaboration_with_locals() {
        assert_strict_clean_after_elaboration(
            "
            fn f(x: number) {
              y: number;
              z: number;
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
        assert_strict_clean_after_elaboration(
            "fn f(r: &number) { entry: return }",
        );
    }

    #[test]
    fn strict_check_passes_after_elaboration_with_copy_drop_struct() {
        assert_strict_clean_after_elaboration(
            "
            struct Copy Drop P { x: number y: number }
            fn f(p: P) { entry: return }
            ",
        );
    }

    #[test]
    fn strict_check_passes_after_elaboration_with_copy_drop_enum() {
        assert_strict_clean_after_elaboration(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) { entry: return }
            ",
        );
    }

    #[test]
    fn strict_check_passes_after_elaboration_with_mut_ref() {
        // `&mut T` is Drop (not Copy). Elaboration inserts a drop.
        assert_strict_clean_after_elaboration(
            "fn f(r: &mut number) { entry: return }",
        );
    }

    #[test]
    fn strict_check_passes_after_elaboration_with_multi_return() {
        // Each return-block gets its own drops; strict validates both.
        assert_strict_clean_after_elaboration(
            "
            fn f(b: boolean, x: number) {
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
              y: number;
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
        let env = type_check::Env::build(&twice, &mut d);
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
            struct Copy Drop P { x: number y: number }
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
              x: number;
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
            fn f(b: boolean, x: number) {
              entry:
                branch(copy b) [true: t, false: fbr]
              t: return
              fbr: return
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
              a: number;
              b: number;
              entry:
                b = 1;
                a = 2;
                return
            }
            ",
            "\
fn f() {
  a: number;
  b: number;
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
            struct Linear { r: &out number }
            fn f(x: Linear) {
              entry:
                return
            }
        ";
        let mut program = Parser::new(src.to_string()).parse().unwrap();
        let mut d = Diagnostics::default();
        let env = type_check::Env::build(&program, &mut d);
        env.typecheck(&mut d);
        elaborate(&mut program, &env);

        let mut d2 = Diagnostics::default();
        let env2 = type_check::Env::build(&program, &mut d2);
        env2.typecheck(&mut d2);
        check_return_leaks(&env2, &mut d2);

        assert!(
            d2.errors.iter().any(|e| e.contains("value 'x'") && e.contains("not consumed")),
            "expected linear leak to survive elaboration; got: {:?}",
            d2.errors
        );
    }
}
