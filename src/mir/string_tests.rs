//! End-to-end tests for byte-string literals (`b"..."`). Value type
//! is `[u8; N]` — reuses the existing array machinery in codegen,
//! init tracking, and lifetime passes.

use crate::mir::test_util::*;

#[test]
fn simple_byte_string_ok() {
    assert_no_diagnostics(
        r#"
        fn f() {
          hello: [u8; 5];
          world: [u8; 5];
          entry:
            hello = b"hello";
            world = b"world";
            return
        }
        "#,
    );
}

#[test]
fn empty_byte_string_is_zero_length_array() {
    assert_no_diagnostics(
        r#"
        fn f() {
          e: [u8; 0];
          entry:
            e = b"";
            return
        }
        "#,
    );
}

// ---------- Escape sequences ----------

#[test]
fn newline_escape_ok() {
    // `b"a\nb"` = 3 bytes: 'a', 0x0A, 'b'.
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 3];
          entry:
            s = b"a\nb";
            return
        }
        "#,
    );
}

#[test]
fn all_backslash_escapes_ok() {
    // `\n`, `\t`, `\r`, `\0`, `\\`, `\"` — 6 bytes.
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 6];
          entry:
            s = b"\n\t\r\0\\\"";
            return
        }
        "#,
    );
}

#[test]
fn hex_escape_ok() {
    // `\xFF\x00\x7E` — 3 bytes.
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 3];
          entry:
            s = b"\xFF\x00\x7E";
            return
        }
        "#,
    );
}

#[test]
fn null_terminator_makes_c_string() {
    // `b"hi\0"` — 3 bytes; users add `\0` explicitly for C interop.
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 3];
          entry:
            s = b"hi\0";
            return
        }
        "#,
    );
}

// ---------- Length mismatch ----------

#[test]
fn wrong_target_length_errors() {
    let (errs, _) = run(
        r#"
        fn f() {
          s: [u8; 4];
          entry:
            s = b"hello";
            return
        }
        "#,
    );
    assert!(
        errs.iter().any(|e| e.contains("Type mismatch")),
        "expected length mismatch, got: {:?}",
        errs
    );
}

#[test]
fn wrong_element_type_errors() {
    // `[i64; N]` doesn't match `[u8; N]`.
    let (errs, _) = run(
        r#"
        fn f() {
          s: [i64; 5];
          entry:
            s = b"hello";
            return
        }
        "#,
    );
    assert!(
        errs.iter().any(|e| e.contains("Type mismatch")),
        "expected element-type mismatch, got: {:?}",
        errs
    );
}

// ---------- Bounds check (bonus, cheap) ----------

#[test]
fn const_index_in_bounds_ok() {
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 5];
          b: u8;
          entry:
            s = b"hello";
            b = copy s[0u64];
            return
        }
        "#,
    );
}

#[test]
fn const_index_out_of_bounds_errors() {
    // `s[5]` on `[u8; 5]` — slot 5 doesn't exist. Should be
    // rejected at check time by the const-index bounds check.
    let (errs, _) = run(
        r#"
        fn f() {
          s: [u8; 5];
          b: u8;
          entry:
            s = b"hello";
            b = copy s[5u64];
            return
        }
        "#,
    );
    assert!(
        errs.iter().any(|e| e.contains("out of bounds")),
        "expected out-of-bounds error, got: {:?}",
        errs
    );
}

// ---------- Read individual bytes ----------

#[test]
fn read_bytes_via_const_index() {
    assert_no_diagnostics(
        r#"
        fn f() {
          s: [u8; 5];
          h: u8;
          o: u8;
          entry:
            s = b"hello";
            h = copy s[0u64];
            o = copy s[4u64];
            return
        }
        "#,
    );
}

// ---------- Byte character literal `b'X'` ----------

#[test]
fn byte_char_literal_ok() {
    // `b'X'` is a `u8` const.
    assert_no_diagnostics(
        r#"
        fn f() {
          x: u8;
          entry:
            x = b'A';
            return
        }
        "#,
    );
}

#[test]
fn byte_char_with_escape_ok() {
    // Escape sequences work in byte chars too.
    assert_no_diagnostics(
        r#"
        fn f() {
          nl: u8;
          nul: u8;
          bs: u8;
          quote: u8;
          apos: u8;
          hex: u8;
          entry:
            nl = b'\n';
            nul = b'\0';
            bs = b'\\';
            quote = b'"';
            apos = b'\'';
            hex = b'\xFF';
            return
        }
        "#,
    );
}

#[test]
fn byte_char_wrong_type_target_errors() {
    // `b'A'` has type `u8`, not `i64`.
    let (errs, _) = run(
        r#"
        fn f() {
          x: i64;
          entry:
            x = b'A';
            return
        }
        "#,
    );
    assert!(
        errs.iter().any(|e| e.contains("Type mismatch")),
        "expected type mismatch, got: {:?}",
        errs
    );
}

// ---------- End-to-end: hello + world = "hello world" ----------

#[test]
fn concat_hello_world_via_dynamic_indexing() {
    // Interleaves both byte strings plus a literal space, indexed
    // dynamically by a u64 counter in a loop. Exercises:
    // - Byte strings (`b"hello"`, `b"world"`).
    // - Byte char literal (`b' '`).
    // - Dynamic-index read (`hello[copy i]`).
    // - Dynamic-index write (`hello_world[copy i] = ...`).
    // - `$u64_lt`, `$u64_eq`, `$u64_add`, `$u64_sub` intrinsics.
    // - Nested branching + loop structure.
    assert_no_diagnostics(
        r#"
        fn f() {
          hello: [u8; 5];
          world: [u8; 5];
          hello_world: [u8; 11];
          i: u64;
          cond: bool;
          is_five: bool;
          add_out: &out u64;
          sub_out: &out u64;
          lt_out: &out bool;
          eq_out: &out bool;
          src_idx: u64;
          next_i: u64;
          entry:
            hello = b"hello";
            world = b"world";
            i = 0u64;
            goto head
          head:
            lt_out = &out cond;
            call $u64_lt(copy i, 11u64, move lt_out);
            branch(copy cond) [true: body, false: done]
          body:
            drop cond;
            lt_out = &out cond;
            call $u64_lt(copy i, 5u64, move lt_out);
            branch(copy cond) [true: from_hello, false: at_or_after_five]
          from_hello:
            drop cond;
            hello_world[copy i] = copy hello[copy i];
            goto step
          at_or_after_five:
            drop cond;
            eq_out = &out is_five;
            call $u64_eq(copy i, 5u64, move eq_out);
            branch(copy is_five) [true: space, false: from_world]
          space:
            drop is_five;
            hello_world[copy i] = b' ';
            goto step
          from_world:
            drop is_five;
            sub_out = &out src_idx;
            call $u64_sub(copy i, 6u64, move sub_out);
            hello_world[copy i] = copy world[copy src_idx];
            drop src_idx;
            goto step
          step:
            add_out = &out next_i;
            call $u64_add(copy i, 1u64, move add_out);
            drop i;
            i = copy next_i;
            drop next_i;
            goto head
          done:
            drop cond;
            return
        }
        "#,
    );
}

// ---------- Bad escapes ----------

#[test]
fn unknown_escape_is_parse_error() {
    use crate::mir::parser::Parser;
    let src = r#"
        fn f() {
          s: [u8; 1];
          entry:
            s = b"\q";
            return
        }
    "#;
    let result = Parser::new(src.to_string()).parse();
    // Tree-sitter accepts the token (matches `\.`); our decoder
    // rejects it. The error surfaces as a parse error from
    // `Parser::parse` via `map_const`.
    assert!(
        result.is_err(),
        "expected parse error for unknown escape, got: {:?}",
        result
    );
}
