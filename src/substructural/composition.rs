//! Substructural class check for declared types.
//!
//! **Scope note:** this file only checks that a declaration's markers
//! (`Copy`, `Drop`, `Move`) are compositionally consistent. Its siblings
//! in this module handle statement-level class checks (`check`) and drop
//! insertion (`elaboration`).
//!
//! A type marker on a struct/enum declaration classifies the type as
//! (respectively) copyable, forgettable, or relocatable. This pass
//! verifies that a declaration's markers are compositionally consistent:
//! a struct marked `Copy` must not contain a non-Copy field, and same
//! for `Drop` and `Move`.
//!
//! Class assignment (per README):
//!   - Scalars (`number`, `boolean`, `unit`) and `fn(...)` : `Copy Drop Move`
//!   - `&T`               : `Copy Drop Move`
//!   - `&mut`, `&uninit`  : `Drop Move`
//!   - `&out`, `&drop`    : `Move` only (linear obligation, but relocatable)
//!   - Custom (struct/enum): as declared, with the rule that
//!     `Copy` + `Drop` implies `Move` (blanket impl in the README).
//!
//! Self-referential and mutually recursive types resolve without a
//! fixpoint: we use the declared markers of a `Custom` name verbatim,
//! which is sufficient for compositional checks.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::type_check::{Env, TypeDecl};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Class {
    pub copy: bool,
    pub drop: bool,
    pub mov: bool,
}

pub fn class_of(ty: &Type, env: &Env) -> Class {
    match ty {
        Type::Number | Type::Boolean | Type::Unit | Type::Fn(_) => Class {
            copy: true,
            drop: true,
            mov: true,
        },
        // Never is uninhabited: the substructural rules quantify over
        // values, and there are none. All three ops apply vacuously.
        Type::Never => Class {
            copy: true,
            drop: true,
            mov: true,
        },
        Type::Ref(kind, _) => match kind {
            // Shared refs are unrestricted and relocatable.
            RefKind::Shared => Class {
                copy: true,
                drop: true,
                mov: true,
            },
            // Exclusive mutable/uninit refs: affine + movable. The ref
            // itself is a pointer we can freely relocate; the referent's
            // obligation goes with it.
            RefKind::Mut | RefKind::Uninit => Class {
                copy: false,
                drop: true,
                mov: true,
            },
            // `&out` / `&drop` carry linear obligations, but the
            // reference value itself is a pointer that can be relocated
            // (obligation transfers with the ref).
            RefKind::Out | RefKind::Drop => Class {
                copy: false,
                drop: false,
                mov: true,
            },
        },
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => Class {
                copy: s.markers.copy,
                drop: s.markers.drop,
                mov: s.markers.effective_move(),
            },
            Some(TypeDecl::Enum(e)) => Class {
                copy: e.markers.copy,
                drop: e.markers.drop,
                mov: e.markers.effective_move(),
            },
            // Unknown name — tc has already reported "undeclared type".
            None => Class {
                copy: false,
                drop: false,
                mov: false,
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
        // Only check explicit Move against fields — an implicit Move
        // via Copy+Drop is guaranteed to succeed because those fields
        // are already Copy AND Drop, hence Move.
        if s.markers.mov && !c.mov {
            d.errors.push(format!(
                "at {}: In struct '{}' (marked Move), field '{}' has type {:?} which is not Move",
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
        if e.markers.mov && !c.mov {
            d.errors.push(format!(
                "at {}: In enum '{}' (marked Move), variant '{}' payload type {:?} is not Move",
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
    fn recursive_via_reference_copy_drop_enum_ok() {
        // Recursion through `&T` doesn't require size resolution — `&T`
        // is Copy Drop regardless of `T`. Verifies composition uses the
        // declared markers for a Custom name without needing a fixpoint.
        assert_no_diagnostics(
            "
            enum Copy Drop List { Nil: unit Cons: &List }
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

    // ---------- Move: explicit marker ----------

    #[test]
    fn struct_move_of_scalars_ok() {
        assert_no_diagnostics(
            "
            struct Move Point { x: number y: boolean }
            ",
        );
    }

    #[test]
    fn struct_move_with_ref_fields_ok() {
        // All ref kinds are Move (the reference is a movable pointer).
        assert_no_diagnostics(
            "
            struct Move S { a: &mut number b: &out number c: &drop number
                            d: &uninit number e: &number }
            ",
        );
    }

    #[test]
    fn struct_move_with_non_move_field_error() {
        assert_err(
            "
            struct Inner { r: &out number }
            struct Move Outer { i: Inner }
            ",
            "In struct 'Outer' (marked Move), field 'i'",
        );
    }

    #[test]
    fn enum_move_of_non_move_payload_error() {
        assert_err(
            "
            struct Inner { r: &out number }
            enum Move Wrap { W: Inner }
            ",
            "In enum 'Wrap' (marked Move), variant 'W'",
        );
    }

    // ---------- Copy + Drop implies Move ----------

    #[test]
    fn copy_drop_struct_is_effectively_move() {
        // A struct marked `Copy Drop` doesn't need explicit `Move`;
        // it's implicitly Move via the blanket rule.
        assert_no_diagnostics(
            "
            struct Copy Drop Point { x: number y: number }
            struct Move Outer { p: Point }
            ",
        );
    }
}
