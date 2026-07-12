//! Terminators: goto, branch (i1), abort (→ call+unreachable),
//! unreachable. Return is covered indirectly by every empty-fn test.

use super::test_util::*;

#[test]
fn goto_emits_br_label() {
    let ll = ll_of(
        "
        fn f() {
          entry: goto next
          next: return
        }
        ",
    );
    assert_contains(&ll, "br label %next");
}

#[test]
fn branch_emits_br_i1() {
    let ll = ll_of(
        "
        fn f(b: bool) {
          entry:
            branch(copy b) [true: t, false: fbr]
          t: return
          fbr: return
        }
        ",
    );
    assert_contains(&ll, "br i1 %t.0, label %t, label %fbr");
}

#[test]
fn abort_calls_abort_then_unreachable() {
    let ll = ll_of("fn f() { entry: abort }");
    assert_contains(&ll, "call void @abort()");
    assert_contains(&ll, "unreachable");
}

#[test]
fn unreachable_lowers_directly() {
    let ll = ll_of("fn f() { entry: unreachable }");
    assert_contains(&ll, "unreachable");
    assert!(
        !ll.contains("call void @abort()"),
        "unreachable shouldn't call abort:\n{}",
        ll
    );
}
