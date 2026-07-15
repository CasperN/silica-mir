//! `fn main` renaming + `i32 @main()` wrapper synthesis.

use super::test_util::*;

// ---------- Rename ----------

#[test]
fn silica_main_is_renamed_in_definition() {
    let ll = ll_of("fn main() { entry: return }");
    assert_contains(&ll, "define void @silica.main()");
    // The unqualified `main` symbol should only appear as the C-level
    // wrapper.
    assert!(
        !ll.contains("define void @main("),
        "Silica main should be renamed away from @main:\n{}",
        ll
    );
}

#[test]
fn user_fn_named_something_else_is_not_renamed() {
    let ll = ll_of("fn foo() { entry: return }");
    assert_contains(&ll, "define void @foo()");
    // No wrapper because there's no `main`.
    assert!(
        !ll.contains("define i32 @main()"),
        "no wrapper should be emitted when program has no main:\n{}",
        ll
    );
}

// ---------- Wrapper: void main ----------

#[test]
fn void_main_wrapper_returns_zero() {
    let ll = ll_of("fn main() { entry: return }");
    assert_contains(&ll, "define i32 @main()");
    assert_contains(&ll, "call void @silica.main()");
    assert_contains(&ll, "ret i32 0");
}

#[test]
fn void_main_wrapper_does_not_alloca() {
    let ll = ll_of("fn main() { entry: return }");
    // The void wrapper has no state — just call + ret.
    let wrapper_start = ll.find("define i32 @main()").unwrap();
    let wrapper_end = ll[wrapper_start..].find("\n}").unwrap() + wrapper_start;
    let wrapper = &ll[wrapper_start..wrapper_end];
    assert!(
        !wrapper.contains("alloca"),
        "void main wrapper should not alloca:\n{}",
        wrapper
    );
}

// ---------- Wrapper: `&out i32` main ----------

#[test]
fn out_i32_main_wrapper_returns_loaded_value() {
    let ll = ll_of(
        "
        fn main(exit: &out i32) {
          entry:
            exit.* = 42i32;
            return
        }
        ",
    );
    // Signature has one ptr param (the &out).
    assert_contains(&ll, "define void @silica.main(ptr");
    // Wrapper: alloca + store 0 default + call + load + ret.
    assert_contains(&ll, "%exit = alloca i32, align 4");
    assert_contains(&ll, "store i32 0, ptr %exit");
    assert_contains(&ll, "call void @silica.main(ptr %exit)");
    assert_contains(&ll, "%code = load i32, ptr %exit");
    assert_contains(&ll, "ret i32 %code");
}

// ---------- Full-IR snapshot ----------

#[test]
fn snapshot_void_main_full_ir() {
    assert_eq!(
        ll_of("fn main() { entry: return }").trim(),
        "\
; Generated from Silica-MIR
declare void @abort()

define void @silica.main() {
.init:
  br label %entry
entry:
  ret void
}

define i32 @main() {
  call void @silica.main()
  ret i32 0
}"
    );
}

#[test]
fn snapshot_out_i32_main_full_ir() {
    assert_eq!(
        ll_of(
            "
            fn main(exit: &out i32) {
              entry:
                exit.* = 7i32;
                return
            }
            "
        )
        .trim(),
        "\
; Generated from Silica-MIR
declare void @abort()

define void @silica.main(ptr %arg.exit) {
.init:
  %local.exit = alloca ptr, align 8
  store ptr %arg.exit, ptr %local.exit
  br label %entry
entry:
  %t.0 = load ptr, ptr %local.exit
  store i32 7, ptr %t.0
  ret void
}

define i32 @main() {
  %exit = alloca i32, align 4
  store i32 0, ptr %exit
  call void @silica.main(ptr %exit)
  %code = load i32, ptr %exit
  ret i32 %code
}"
    );
}

// ---------- Type-check enforcement ----------

/// Codegen tests bypass the checker (see `test_util::ll_of`), so we
/// exercise the signature check via the crate-level `run` helper
/// which drives the full pipeline.
#[test]
fn bad_main_signature_i64_param_rejected() {
    let (errs, _) = crate::mir::test_util::run(
        "
        fn main(exit: &out i64) {
          entry:
            exit.* = 0;
            return
        }
        ",
    );
    let matches: Vec<_> = errs
        .iter()
        .filter(|e| e.contains("In function 'main'") && e.contains("must be '&out i32'"))
        .collect();
    assert!(
        !matches.is_empty(),
        "expected 'main must be &out i32' error, got {:?}",
        errs
    );
}

#[test]
fn bad_main_signature_extra_params_rejected() {
    let (errs, _) = crate::mir::test_util::run(
        "
        fn main(a: i32, b: i32) {
          entry: return
        }
        ",
    );
    let matches: Vec<_> = errs
        .iter()
        .filter(|e| e.contains("In function 'main'") && e.contains("at most one parameter"))
        .collect();
    assert!(
        !matches.is_empty(),
        "expected 'at most one parameter' error, got {:?}",
        errs
    );
}

#[test]
fn valid_void_main_passes_check() {
    let (errs, _) = crate::mir::test_util::run("fn main() { entry: return }");
    assert!(errs.is_empty(), "expected clean check, got: {:?}", errs);
}

#[test]
fn valid_out_i32_main_passes_check() {
    let (errs, _) = crate::mir::test_util::run(
        "
        fn main(exit: &out i32) {
          entry:
            exit.* = 42i32;
            return
        }
        ",
    );
    assert!(errs.is_empty(), "expected clean check, got: {:?}", errs);
}
