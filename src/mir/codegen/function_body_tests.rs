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
    let ll = ll_of("fn f(x: i64) { entry: return }");
    assert_contains(&ll, "define void @f(i64 %arg.x)");
    assert_contains(&ll, "%local.x = alloca i64");
    assert_contains(&ll, "store i64 %arg.x, ptr %local.x");
}

#[test]
fn locals_get_alloca_no_arg_store() {
    let ll = ll_of(
        "
        fn f() {
          x: i64;
          entry: return
        }
        ",
    );
    assert_contains(&ll, "%local.x = alloca i64");
    // No arg for a local:
    assert!(!ll.contains("store i64 %arg.x"));
}

#[test]
fn return_param_codegen() {
    assert_ll_eq(
        "
        fn f(x: i64, $return: &out i64) {
          entry:
            $return.* = copy x;
            return
        }
        ",
        "
; Generated from Silica-MIR
declare void @abort()

define i64 @f(i64 %arg.x) {
.init:
  %local.$return_val = alloca i64, align 8
  %local.$return = alloca ptr, align 8
  store ptr %local.$return_val, ptr %local.$return
  %local.x = alloca i64, align 8
  store i64 %arg.x, ptr %local.x
  br label %entry
entry:
  %t.0 = load i64, ptr %local.x
  %t.1 = load ptr, ptr %local.$return
  store i64 %t.0, ptr %t.1
  %t.2 = load i64, ptr %local.$return_val
  ret i64 %t.2
}
        ",
    );
}

#[test]
fn return_param_call_codegen() {
    assert_ll_eq(
        "
        fn callee($return: &out i64) {
          entry:
            $return.* = 42i64;
            return
        }
        fn caller(out: &out i64) {
          entry:
            call callee(move out);
            return
        }
        ",
        "
; Generated from Silica-MIR
declare void @abort()

define i64 @callee() {
.init:
  %local.$return_val = alloca i64, align 8
  %local.$return = alloca ptr, align 8
  store ptr %local.$return_val, ptr %local.$return
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.$return
  store i64 42, ptr %t.0
  %t.1 = load i64, ptr %local.$return_val
  ret i64 %t.1
}

define void @caller(ptr %arg.out) {
.init:
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.out
  %t.1 = call i64 @callee()
  store i64 %t.1, ptr %t.0
  ret void
}
        ",
    );
}

#[test]
fn return_param_extern_fn() {
    assert_ll_eq(
        "
        extern fn ext(x: i64, $return: &out i64);
        fn caller(out: &out i64) {
          entry:
            call ext(42i64, move out);
            return
        }
        ",
        "
; Generated from Silica-MIR
declare void @abort()

declare i64 @ext(i64)

define void @caller(ptr %arg.out) {
.init:
  %local.out = alloca ptr, align 8
  store ptr %arg.out, ptr %local.out
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.out
  %t.1 = call i64 @ext(i64 42)
  store i64 %t.1, ptr %t.0
  ret void
}
        ",
    );
}

