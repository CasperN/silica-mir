//! Substructural class check for declared types.
//!
//! **Scope note:** this file only checks that a declaration's `Copy` /
//! `Drop` markers are compositionally consistent — a struct marked `Copy`
//! must not contain a non-Copy field, etc. Its siblings in this module
//! handle statement-level class checks (`check`) and drop insertion
//! (`elaboration`).
//!
//! Silica's `Copy` / `Drop` markers on struct and enum declarations classify
//! the type as (respectively) copyable and forgettable. This pass verifies
//! that a declaration's markers are compositionally consistent: a struct
//! marked `Copy` must not contain a non-Copy field, and same for `Drop` (and
//! same for enum variants against their payload types).
//!
//! Class assignment (per README):
//!   - Scalars (`number`, `boolean`, `unit`) and `fn(...)` : `Copy Drop`
//!   - `&T`               : `Copy Drop`
//!   - `&mut`, `&uninit`  : `Drop`, not `Copy`
//!   - `&out`, `&drop`    : neither (linear)
//!   - Custom (struct/enum): as declared by its own markers
//!
//! Self-referential and mutually recursive types resolve without a fixpoint:
//! we use the declared markers of a `Custom` name verbatim, which is
//! sufficient for compositional checks.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::type_check::{Env, TypeDecl};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Class {
    pub copy: bool,
    pub drop: bool,
}

pub fn class_of(ty: &Type, env: &Env) -> Class {
    match ty {
        Type::Number | Type::Boolean | Type::Unit | Type::Fn(_) => Class {
            copy: true,
            drop: true,
        },
        Type::Ref(kind, _) => match kind {
            RefKind::Shared => Class {
                copy: true,
                drop: true,
            },
            RefKind::Mut | RefKind::Uninit => Class {
                copy: false,
                drop: true,
            },
            RefKind::Out | RefKind::Drop => Class {
                copy: false,
                drop: false,
            },
        },
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => Class {
                copy: s.markers.copy,
                drop: s.markers.drop,
            },
            Some(TypeDecl::Enum(e)) => Class {
                copy: e.markers.copy,
                drop: e.markers.drop,
            },
            // Unknown name — tc has already reported "undeclared type".
            // Fall back to linear so we don't fabricate a Copy/Drop claim.
            None => Class {
                copy: false,
                drop: false,
            },
        },
    }
}

pub fn check_program(env: &Env, d: &mut Diagnostics) {
    for type_decl in env.types.values() {
        match type_decl {
            TypeDecl::Struct(s) => check_struct(s, env, d),
            TypeDecl::Enum(e) => check_enum(e, env, d),
        }
    }
}

fn check_struct(s: &StructDecl, env: &Env, d: &mut Diagnostics) {
    for f in &s.fields {
        let c = class_of(&f.ty, env);
        if s.markers.copy && !c.copy {
            d.errors.push(format!(
                "at {}: In struct '{}' (marked Copy), field '{}' has type {:?} which is not Copy",
                f.span, s.name, f.name, f.ty
            ));
        }
        if s.markers.drop && !c.drop {
            d.errors.push(format!(
                "at {}: In struct '{}' (marked Drop), field '{}' has type {:?} which is not Drop",
                f.span, s.name, f.name, f.ty
            ));
        }
    }
}

fn check_enum(e: &EnumDecl, env: &Env, d: &mut Diagnostics) {
    for v in &e.variants {
        let c = class_of(&v.ty, env);
        if e.markers.copy && !c.copy {
            d.errors.push(format!(
                "at {}: In enum '{}' (marked Copy), variant '{}' payload type {:?} is not Copy",
                v.span, e.name, v.name, v.ty
            ));
        }
        if e.markers.drop && !c.drop {
            d.errors.push(format!(
                "at {}: In enum '{}' (marked Drop), variant '{}' payload type {:?} is not Drop",
                v.span, e.name, v.name, v.ty
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::*;

    // ---------- Positive: markers consistent with content ----------

    #[test]
    fn struct_copy_drop_of_scalars_ok() {
        assert_no_diagnostics(
            "
            struct Copy Drop Point { x: number y: boolean }
            ",
        );
    }

    #[test]
    fn struct_no_markers_permits_any_field() {
        // With no markers, the struct is linear — no obligations to satisfy.
        assert_no_diagnostics(
            "
            struct Container { r: &out number }
            ",
        );
    }

    #[test]
    fn struct_copy_shared_ref_ok() {
        // `&T` is Copy Drop so a Copy struct may hold one.
        assert_no_diagnostics(
            "
            struct Copy S { r: &number x: number }
            ",
        );
    }

    #[test]
    fn nested_copy_struct_ok() {
        assert_no_diagnostics(
            "
            struct Copy A { x: number }
            struct Copy B { a: A y: number }
            ",
        );
    }

    #[test]
    fn recursive_copy_drop_enum_ok() {
        // Marker-declared class is used verbatim for `Loop` when checking
        // variant payloads that reference `Loop`.
        assert_no_diagnostics(
            "
            enum Copy Drop Loop { A: unit B: Loop }
            ",
        );
    }

    #[test]
    fn enum_copy_drop_scalar_variants_ok() {
        assert_no_diagnostics(
            "
            enum Copy Drop Tag { N: number B: boolean U: unit }
            ",
        );
    }

    // ---------- Copy composition errors ----------

    #[test]
    fn struct_copy_with_mut_ref_error() {
        // `&mut T` is Drop but not Copy.
        assert_err(
            "
            struct Copy Bad { r: &mut number }
            ",
            "In struct 'Bad' (marked Copy), field 'r'",
        );
    }

    #[test]
    fn struct_copy_with_linear_field_error() {
        // `&out T` is neither Copy nor Drop; the Copy check reports.
        assert_err(
            "
            struct Copy Bad { r: &out number }
            ",
            "In struct 'Bad' (marked Copy), field 'r'",
        );
    }

    #[test]
    fn nested_copy_struct_with_non_copy_field_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            struct Copy Outer { inner: Linear }
            ",
            "In struct 'Outer' (marked Copy), field 'inner'",
        );
    }

    #[test]
    fn enum_copy_with_non_copy_payload_error() {
        assert_err(
            "
            enum Copy Bad { A: &mut number }
            ",
            "In enum 'Bad' (marked Copy), variant 'A'",
        );
    }

    // ---------- Drop composition errors ----------

    #[test]
    fn struct_drop_with_out_ref_error() {
        // `&out T` is linear (not Drop).
        assert_err(
            "
            struct Drop Bad { r: &out number }
            ",
            "In struct 'Bad' (marked Drop), field 'r'",
        );
    }

    #[test]
    fn struct_drop_containing_linear_struct_error() {
        assert_err(
            "
            struct Linear { r: &out number }
            struct Drop Outer { inner: Linear }
            ",
            "In struct 'Outer' (marked Drop), field 'inner'",
        );
    }

    #[test]
    fn enum_drop_with_out_ref_payload_error() {
        assert_err(
            "
            enum Drop Bad { A: &out number }
            ",
            "In enum 'Bad' (marked Drop), variant 'A'",
        );
    }

    // ---------- Both markers fail on linear content ----------

    #[test]
    fn copy_drop_struct_with_linear_field_reports_both() {
        let (errs, _) = run("
            struct Copy Drop Bad { r: &out number }
            ");
        assert_errors_contain(
            &errs,
            &[
                "In struct 'Bad' (marked Copy), field 'r'",
                "In struct 'Bad' (marked Drop), field 'r'",
            ],
        );
    }

    // ---------- Reference kinds ----------

    #[test]
    fn struct_drop_with_mut_ref_ok() {
        // `&mut T` is Drop (though not Copy).
        assert_no_diagnostics(
            "
            struct Drop S { r: &mut number }
            ",
        );
    }

    #[test]
    fn struct_drop_with_uninit_ref_ok() {
        assert_no_diagnostics(
            "
            struct Drop S { r: &uninit number }
            ",
        );
    }
}
