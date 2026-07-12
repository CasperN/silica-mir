//! Assign, call, drop, unborrow. Covers const materialization, copy
//! operand, and the erasure of drop/unborrow (POD-only world).

use super::test_util::*;

// ---------- Assign / operands / consts ----------

#[test]
fn assign_number_const() {
    let ll = ll_of(
        "
        fn f() {
          x: i64;
          entry:
            x = 42;
            return
        }
        ",
    );
    assert_contains(&ll, "store i64 42, ptr %local.x");
}

#[test]
fn assign_boolean_consts() {
    let ll = ll_of(
        "
        fn f() {
          a: boolean;
          b: boolean;
          entry:
            a = true;
            b = false;
            return
        }
        ",
    );
    assert_contains(&ll, "store i1 true, ptr %local.a");
    assert_contains(&ll, "store i1 false, ptr %local.b");
}

#[test]
fn copy_local_loads_then_stores() {
    let ll = ll_of(
        "
        fn f(x: i64) {
          y: i64;
          entry:
            y = copy x;
            return
        }
        ",
    );
    assert_contains(&ll, "load i64, ptr %local.x");
    assert_contains(&ll, "store i64 %t.0, ptr %local.y");
}

// ---------- Call ----------

#[test]
fn call_extern_with_const_arg() {
    let ll = ll_of(
        "
        extern fn callee(a: i64);
        fn f() {
          entry:
            call callee(1);
            return
        }
        ",
    );
    assert_contains(&ll, "call void @callee(i64 1)");
}

#[test]
fn call_via_fn_pointer_local() {
    let ll = ll_of(
        "
        extern fn callee(a: i64);
        fn f() {
          g: fn(i64);
          entry:
            g = callee;
            call copy g(1);
            return
        }
        ",
    );
    // g is a function-pointer local (ptr).
    assert_contains(&ll, "%local.g = alloca ptr");
    // The fn-name const is stored as a global reference.
    assert_contains(&ll, "store ptr @callee, ptr %local.g");
    // Call site loads g and calls indirectly.
    assert_contains(&ll, "load ptr, ptr %local.g");
    assert_contains(&ll, "call void %t.");
}

// ---------- Drop / Unborrow ----------

#[test]
fn drop_and_unborrow_are_erased() {
    // Both statements produce no instructions in the LLVM output.
    let ll = ll_of(
        "
        fn f(r: &i64) {
          x: i64;
          entry:
            x = 0;
            drop x;
            unborrow r;
            return
        }
        ",
    );
    assert!(!ll.contains("drop"), "drop should be erased:\n{}", ll);
    assert!(
        !ll.contains("unborrow"),
        "unborrow should be erased:\n{}",
        ll
    );
}
