//! Function definition scaffolding: `.init` block, param arg-to-alloca
//! stores, and local allocas.

use super::test_util::*;

#[test]
fn empty_fn_has_init_block_and_returns() {
    let ll = ll_of("fn f() { entry: return }");
    assert_contains(&ll, "define void @f()");
    assert_contains(&ll, ".init:");
    assert_contains(&ll, "br label %entry");
    assert_contains(&ll, "entry:");
    assert_contains(&ll, "ret void");
}

#[test]
fn params_get_alloca_and_arg_store() {
    let ll = ll_of("fn f(x: number) { entry: return }");
    assert_contains(&ll, "define void @f(i64 %arg.x)");
    assert_contains(&ll, "%local.x = alloca i64");
    assert_contains(&ll, "store i64 %arg.x, ptr %local.x");
}

#[test]
fn locals_get_alloca_no_arg_store() {
    let ll = ll_of(
        "
        fn f() {
          x: number;
          entry: return
        }
        ",
    );
    assert_contains(&ll, "%local.x = alloca i64");
    // No arg for a local:
    assert!(!ll.contains("store i64 %arg.x"));
}
