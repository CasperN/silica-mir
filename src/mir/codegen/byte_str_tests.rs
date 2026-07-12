//! LLVM lowering for byte string literals (`b"..."`). Value semantics
//! — the literal materializes as an LLVM aggregate constant
//! (`c"..."`) that gets stored into the target's alloca.

use super::test_util::*;

// ---------- Basic emission ----------

#[test]
fn byte_str_lowers_to_aggregate_constant_store() {
    let ll = ll_of(
        r#"
        fn f() {
          s: [u8; 5];
          entry:
            s = b"hello";
            return
        }
        "#,
    );
    // The `.init` alloca uses `[N x i8]`, align 1 (u8 alignment).
    assert_contains(&ll, "%local.s = alloca [5 x i8], align 1");
    // The literal is inlined as an LLVM aggregate constant and stored
    // in a single instruction.
    assert_contains(&ll, r#"store [5 x i8] c"hello", ptr %local.s"#);
}

#[test]
fn empty_byte_str_stores_empty_aggregate() {
    let ll = ll_of(
        r#"
        fn f() {
          s: [u8; 0];
          entry:
            s = b"";
            return
        }
        "#,
    );
    assert_contains(&ll, "%local.s = alloca [0 x i8], align 1");
    // Zero-length aggregate constant.
    assert_contains(&ll, r#"store [0 x i8] c"""#);
}

// ---------- Escape rendering ----------

#[test]
fn newline_becomes_llvm_0a_escape() {
    let ll = ll_of(
        r#"
        fn f() {
          s: [u8; 3];
          entry:
            s = b"a\nb";
            return
        }
        "#,
    );
    // LLVM's byte-string escape syntax uses `\XX` with uppercase hex.
    assert_contains(&ll, r#"c"a\0Ab""#);
}

#[test]
fn high_bytes_use_llvm_hex_escapes() {
    let ll = ll_of(
        r#"
        fn f() {
          s: [u8; 3];
          entry:
            s = b"\xFF\x00\x7E";
            return
        }
        "#,
    );
    // 0xFF → \FF; 0x00 → \00; 0x7E is printable ~ (kept verbatim).
    assert_contains(&ll, r#"c"\FF\00~""#);
}

#[test]
fn quote_and_backslash_escape() {
    // The literal contains `"` and `\` — both must be LLVM-escaped
    // in the emitted aggregate constant.
    let ll = ll_of(
        r#"
        fn f() {
          s: [u8; 2];
          entry:
            s = b"\"\\";
            return
        }
        "#,
    );
    // 0x22 (") → \22; 0x5C (\) → \5C.
    assert_contains(&ll, r#"c"\22\5C""#);
}

// ---------- Golden IR ----------

#[test]
fn snapshot_hello_world_full_ir() {
    // Byte string in a fn body — one alloca, one aggregate store.
    // Pins the full lowering for the "hello world" archetype.
    assert_ll_eq(
        r#"
        fn f() {
          s: [u8; 5];
          entry:
            s = b"hello";
            return
        }
        "#,
        r#"; Generated from Silica-MIR
declare void @abort()

define void @f() {
.init:
  %local.s = alloca [5 x i8], align 1
  br label %entry
entry:
  store [5 x i8] c"hello", ptr %local.s
  ret void
}"#,
    );
}
