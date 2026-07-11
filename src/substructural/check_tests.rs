use crate::test_util::*;
use super::check::check_return_leaks;
use crate::diagnostics::Diagnostics;
use crate::parser::Parser;
use crate::type_check;

// ---------- Copy: positives ----------

#[test]
fn copy_of_number_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
            y: i64;
            entry:
            y = copy x;
            return
        }
        ",
    );
}

#[test]
fn copy_of_shared_ref_ok() {
    // `&T` is Copy Drop.
    assert_no_diagnostics(
        "
        fn f(r: &i64) {
            s: &i64;
            entry:
            s = copy r;
            return
        }
        ",
    );
}

#[test]
fn copy_of_copy_struct_ok() {
    assert_no_diagnostics(
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

// ---------- Copy: negatives ----------

#[test]
fn copy_of_linear_struct_error() {
    // struct without markers = linear
    assert_err(
        "
        struct Linear { r: &out i64 }
        fn f(x: Linear) {
            y: Linear;
            entry:
            y = copy x;
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

#[test]
fn copy_of_affine_struct_error() {
    // Marked `Drop` but not `Copy` — affine, not copyable.
    assert_err(
        "
        struct Drop D { x: i64 }
        fn f(a: D) {
            b: D;
            entry:
            b = copy a;
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

#[test]
fn copy_of_mut_ref_error() {
    assert_err(
        "
        fn f(r: &mut i64) {
            s: &mut i64;
            entry:
            s = copy r;
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

#[test]
fn copy_of_out_ref_error() {
    assert_err(
        "
        fn f(r: &out i64) {
            s: &out i64;
            entry:
            s = copy r;
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

#[test]
fn copy_of_uninit_ref_error() {
    assert_err(
        "
        fn f(r: &uninit i64) {
            s: &uninit i64;
            entry:
            s = copy r;
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

// ---------- Copy in other operand positions ----------

#[test]
fn copy_in_call_arg_of_non_copy_error() {
    assert_err(
        "
        struct Linear { r: &out i64 }
        extern fn take(x: Linear);
        fn f(x: Linear) {
            entry:
            call take(copy x);
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

#[test]
fn copy_in_enum_payload_of_non_copy_error() {
    assert_err(
        "
        struct Linear { r: &out i64 }
        enum Wrap { W: Linear }
        fn f(x: Linear) {
            w: Wrap;
            entry:
            w = Wrap::W(copy x);
            return
        }
        ",
        "cannot copy non-Copy type",
    );
}

// ---------- Move: requires Move marker ----------

#[test]
fn move_of_linear_ok() {
    // A struct that gets moved must declare Move. Here `struct Move
    // Linear` composes fine because `&out T` is Move (linear
    // obligation, but movable — pointer relocates with obligation).
    assert_no_diagnostics(
        "
        struct Move Linear { r: &out i64 }
        extern fn sink(y: Linear);
        fn f(x: Linear) {
            y: Linear;
            entry:
            y = move x;
            call sink(move y);
            return
        }
        ",
    );
}

#[test]
fn move_of_non_move_struct_errors() {
    // Same shape, but no Move marker — moves are rejected.
    assert_err(
        "
        struct Linear { r: &out i64 }
        extern fn sink(y: Linear);
        fn f(x: Linear) {
            y: Linear;
            entry:
            y = move x;
            call sink(move y);
            return
        }
        ",
        "cannot move non-Move type",
    );
}

#[test]
fn move_of_ref_ok() {
    // All ref kinds are implicitly Move (the ref itself is a pointer;
    // its obligation transfers with the move).
    assert_no_diagnostics(
        "
        extern fn take(r: &mut i64);
        fn f(r: &mut i64) {
            entry:
            call take(move r);
            return
        }
        ",
    );
}

#[test]
fn move_of_copy_drop_struct_ok() {
    // Copy+Drop implies Move — no explicit Move marker needed.
    assert_no_diagnostics(
        "
        struct Copy Drop Point { x: i64 y: i64 }
        extern fn take(p: Point);
        fn f(p: Point) {
            entry:
            call take(move p);
            return
        }
        ",
    );
}

#[test]
fn move_of_copy_only_struct_errors() {
    // Copy alone doesn't imply Move — the type is bit-duplicable but
    // not relocatable.
    assert_err(
        "
        struct Copy PinnedShared { x: i64 }
        extern fn take(p: PinnedShared);
        fn f(p: PinnedShared) {
            entry:
            call take(move p);
            return
        }
        ",
        "cannot move non-Move type",
    );
}

// ---------- Drop: positives ----------

#[test]
fn drop_of_number_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
            entry:
            drop x;
            return
        }
        ",
    );
}

#[test]
fn drop_of_shared_ref_ok() {
    assert_no_diagnostics(
        "
        fn f(r: &i64) {
            entry:
            drop r;
            return
        }
        ",
    );
}

#[test]
fn drop_of_mut_ref_ok() {
    // `&mut T` is Drop (though not Copy) — the reference value may be
    // forgotten (the loan expires at the drop point).
    assert_no_diagnostics(
        "
        fn f(r: &mut i64) {
            entry:
            drop r;
            return
        }
        ",
    );
}

#[test]
fn drop_of_drop_struct_ok() {
    assert_no_diagnostics(
        "
        struct Drop D { x: i64 }
        fn f(d: D) {
            entry:
            drop d;
            return
        }
        ",
    );
}

// ---------- Drop: negatives ----------

#[test]
fn drop_of_linear_struct_error() {
    assert_err(
        "
        struct Linear { r: &out i64 }
        fn f(x: Linear) {
            entry:
            drop x;
            return
        }
        ",
        "cannot drop non-Drop type",
    );
}

#[test]
fn drop_of_out_ref_error() {
    assert_err(
        "
        fn f(r: &out i64) {
            entry:
            drop r;
            return
        }
        ",
        "cannot drop non-Drop type",
    );
}

#[test]
fn drop_of_drop_ref_error() {
    // `&drop T` is linear (obligation to deinit before expiry).
    assert_err(
        "
        fn f(r: &drop i64) {
            entry:
            drop r;
            return
        }
        ",
        "cannot drop non-Drop type",
    );
}

#[test]
fn scalar_param_untouched_is_lenient_ok() {
    // i64 is Copy Drop; leaving it Init at return is permitted under
    // the elaborator will insert an explicit drop.
    assert_no_diagnostics(
        "
        fn f(x: i64) {
            entry:
            return
        }
        ",
    );
}

#[test]
fn scalar_param_moved_ok() {
    assert_no_diagnostics(
        "
        extern fn take(a: i64);
        fn f(x: i64) {
            entry:
            call take(move x);
            return
        }
        ",
    );
}

#[test]
fn scalar_param_explicitly_dropped_ok() {
    assert_no_diagnostics(
        "
        fn f(x: i64) {
            entry:
            drop x;
            return
        }
        ",
    );
}

// === Scenario: `r: &out i64` — linear reference param =============

#[test]
fn linear_ref_param_untouched_leaks() {
    // Refs are reported via the obligation check, not the linear-leak
    // check, because their expiry rule is the (cur, post) obligation.
    assert_err(
        "
        fn f(r: &out i64) {
            entry:
            return
        }
        ",
        "reference 'r' has unfulfilled obligation",
    );
}

#[test]
fn linear_ref_param_moved_ok() {
    assert_no_diagnostics(
        "
        extern fn take(r: &out i64);
        fn f(r: &out i64) {
            entry:
            call take(move r);
            return
        }
        ",
    );
}

// === Scenario: `struct P { x: i64 y: i64 }` — linear struct ====
// ==== with Drop fields =======================================
// Marker composition permits this: the fields are Drop, but the struct
// itself isn't marked, so it's linear as a value. Partial init with
// Drop leaves collapses to per-leaf leak checks.

#[test]
fn linear_struct_untouched_param_leaks() {
    // Whole-var Init of a linear type: leak.
    assert_err(
        "
        struct P { x: i64 y: i64 }
        fn f(p: P) {
            entry:
            return
        }
        ",
        "value 'p' of type Custom(\"P\") is not consumed at return",
    );
}

#[test]
fn linear_struct_moved_whole_ok() {
    assert_no_diagnostics(
        "
        struct Move P { x: i64 y: i64 }
        extern fn take(p: P);
        fn f(p: P) {
            entry:
            call take(move p);
            return
        }
        ",
    );
}

#[test]
fn linear_struct_partial_init_one_field_elaborated() {
    // `p.x = 1` → Partial({x: Init, y: NeverInit}). Elaboration walks
    // the partial state and inserts `drop p.x`; every leaf is then
    // consumed and strict passes. This works even though P is linear
    // because the container's linearity is redundant given all its
    // fields are Drop.
    assert_no_diagnostics(
        "
        struct P { x: i64 y: i64 }
        fn f() {
            p: P;
            entry:
            p.x = 1;
            return
        }
        ",
    );
}

#[test]
fn linear_struct_partial_init_then_drop_ok() {
    assert_no_diagnostics(
        "
        struct P { x: i64 y: i64 }
        fn f() {
            p: P;
            entry:
            p.x = 1;
            drop p.x;
            return
        }
        ",
    );
}

#[test]
fn linear_struct_both_fields_dropped_ok() {
    assert_no_diagnostics(
        "
        struct P { x: i64 y: i64 }
        fn f() {
            p: P;
            entry:
            p.x = 1;
            p.y = 2;
            drop p.x;
            drop p.y;
            return
        }
        ",
    );
}

#[test]
fn linear_struct_fully_constructed_leaks() {
    // `p.x = 1; p.y = 2` → Partial({x: Init, y: Init}) canonicalizes
    // to Init. Whole-var Init of a linear type: leak (the linearity
    // now applies at the container granularity — you completed a value
    // and never consumed it).
    assert_err(
        "
        struct P { x: i64 y: i64 }
        fn f() {
            p: P;
            entry:
            p.x = 1;
            p.y = 2;
            return
        }
        ",
        "value 'p' of type Custom(\"P\") is not consumed at return",
    );
}

// === Scenario: `struct L { r: &out i64 }` — fully-linear struct ===
// The container and its field are both linear; there's no "Drop leaf"
// escape.

#[test]
fn fully_linear_struct_untouched_param_leaks() {
    assert_err(
        "
        struct L { r: &out i64 }
        fn f(x: L) {
            entry:
            return
        }
        ",
        "value 'x' of type Custom(\"L\") is not consumed at return",
    );
}

#[test]
fn fully_linear_struct_moved_ok() {
    assert_no_diagnostics(
        "
        struct Move L { r: &out i64 }
        extern fn take(x: L);
        fn f(x: L) {
            entry:
            call take(move x);
            return
        }
        ",
    );
}

#[test]
fn fully_linear_struct_partial_init_field_leaks() {
    // `x.r = ...` wouldn't compile (can't assign a linear place),
    // but a fully-linear field with Init state at return is a
    // per-leaf leak whenever it appears — verified here via a local
    // that's partially inited via a moved-in field. Both structs
    // need Move to permit `move src.a`.
    assert_err(
        "
        struct Move L { r: &out i64 }
        struct Move Pair { a: L b: L }
        fn f(src: Pair) {
            p: Pair;
            entry:
            p.a = move src.a;
            return
        }
        ",
        "not consumed at return",
    );
}

#[test]
fn multiple_returns_each_checked() {
    let (errs, _) = run("
        struct Linear { r: &out i64 }
        fn f(b: boolean, x: Linear) {
            entry:
            branch(copy b) [true: t, false: fbr]
            t: return
            fbr: return
        }
        ");
    let leak_errs: Vec<_> = errs
        .iter()
        .filter(|e| e.contains("is not consumed at return"))
        .collect();
    assert_eq!(leak_errs.len(), 2, "expected 2 leak errors, got {:?}", errs);
}

#[test]
fn direct_leak_check_flags_pre_elaboration_drop_leak() {
    // Invoking check_return_leaks on a NON-elaborated program: any Init
    // at return is a leak because nothing has inserted drops yet.

    let src = "fn f(x: i64) { entry: return }";
    let program = Parser::new(src.to_string()).parse().unwrap();
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&program).0;
    check_return_leaks(&env, &mut d);
    assert!(
        d.errors
            .iter()
            .any(|e| e.contains("value 'x'") && e.contains("not consumed")),
        "expected leak error, got {:?}",
        d.errors
    );
}

#[test]
fn direct_leak_check_ok_when_explicitly_dropped() {

    let src = "fn f(x: i64) { entry: drop x; return }";
    let program = Parser::new(src.to_string()).parse().unwrap();
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(&program).0;
    check_return_leaks(&env, &mut d);
    let leak_errs: Vec<_> = d
        .errors
        .iter()
        .filter(|e| e.contains("not consumed at return"))
        .collect();
    assert!(
        leak_errs.is_empty(),
        "expected no leaks, got {:?}",
        d.errors
    );
}
