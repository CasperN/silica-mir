//! Place lowering: struct field GEP, deref load/store, and reference
//! creation (`&x`) storing the address of `x`.

use super::test_util::*;

#[test]
fn field_read_uses_gep() {
    let ll = ll_of(
        "
        struct P { x: i64 y: i64 }
        fn f(p: P) {
          n: i64;
          entry:
            n = copy p.y;
            return
        }
        ",
    );
    assert_contains(&ll, "getelementptr %P, ptr %local.p, i32 0, i32 1");
}

#[test]
fn field_write_uses_gep() {
    let ll = ll_of(
        "
        struct P { x: i64 y: i64 }
        fn f() {
          p: P;
          entry:
            p.x = 7;
            return
        }
        ",
    );
    assert_contains(&ll, "getelementptr %P, ptr %local.p, i32 0, i32 0");
    assert_contains(&ll, "store i64 7, ptr %t.0");
}

#[test]
fn deref_read_loads_pointer_then_pointee() {
    let ll = ll_of(
        "
        fn f(r: &i64) {
          x: i64;
          entry:
            x = copy r.*;
            return
        }
        ",
    );
    // First load: obtain the pointee's address from the ref slot.
    assert_contains(&ll, "load ptr, ptr %local.r");
    // Second load: obtain the pointee's value.
    assert_contains(&ll, "load i64, ptr %t.0");
}

#[test]
fn deref_write_stores_via_loaded_ptr() {
    let ll = ll_of(
        "
        fn f(r: &mut i64) {
          entry:
            r.* = 99;
            return
        }
        ",
    );
    assert_contains(&ll, "load ptr, ptr %local.r");
    assert_contains(&ll, "store i64 99, ptr %t.0");
}

#[test]
fn ref_stores_place_address() {
    let ll = ll_of(
        "
        fn f() {
          x: i64;
          r: &i64;
          entry:
            x = 0;
            r = &x;
            return
        }
        ",
    );
    assert_contains(&ll, "store ptr %local.x, ptr %local.r");
}

#[test]
fn all_ref_kinds_lower_to_ptr() {
    let ll = ll_of(
        "
        fn f() {
          x: i64;
          a: &i64;
          b: &mut i64;
          c: &out i64;
          d: &drop i64;
          e: &uninit i64;
          entry:
            x = 0;
            a = &x;
            b = &mut x;
            return
        }
        ",
    );
    assert_contains(&ll, "%local.a = alloca ptr");
    assert_contains(&ll, "%local.b = alloca ptr");
    assert_contains(&ll, "%local.c = alloca ptr");
    assert_contains(&ll, "%local.d = alloca ptr");
    assert_contains(&ll, "%local.e = alloca ptr");
}
