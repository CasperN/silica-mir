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
//!   - Scalars (`i64`, `bool`, `unit`) and `fn(...)` : `Copy Drop Move`
//!   - `&T`               : `Copy Drop Move`
//!   - `&mut`, `&uninit`  : `Drop Move`
//!   - `&out`, `&drop`    : `Move` only (linear obligation, but relocatable)
//!   - Custom (struct/enum): as declared, with the rule that
//!     `Copy` + `Drop` implies `Move` (blanket impl in the README).
//!
//! Self-referential and mutually recursive types resolve without a
//! fixpoint: we use the declared markers of a `Custom` name verbatim,
//! which is sufficient for compositional checks.

use crate::mir::ast::*;
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::type_check::{Env, TypeDecl};

/// Machine-readable codes emitted by the class-composition check. Each
/// variant flags "declared marker M on container C isn't satisfied by
/// content X". The variant discriminates *which* marker was violated;
/// the message discriminates *which* container and content.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubstructuralCompositionCode {
    /// Struct/enum is marked `Copy` but a field/variant payload is
    /// not `Copy`.
    CopyMarkerNotSatisfied,
    /// Struct/enum is marked `Drop` but a field/variant payload is
    /// not `Drop`.
    DropMarkerNotSatisfied,
    /// Struct/enum is marked `Move` but a field/variant payload is
    /// not `Move`.
    MoveMarkerNotSatisfied,
}

impl From<SubstructuralCompositionCode> for DiagCode {
    fn from(code: SubstructuralCompositionCode) -> DiagCode {
        DiagCode::SubstructuralComposition(code)
    }
}
use SubstructuralCompositionCode::*;

/// Declaration-scope diagnostic builder: no function or block context
/// exists at this point in the pipeline (composition runs on type
/// declarations before any function body is checked).
fn diag(code: impl Into<DiagCode>, span: Span, msg: String) -> Diagnostic {
    Diagnostic::new(code, span, msg)
}

/// Return the substructural class of `ty` as a `Markers` value.
///
/// Callers query the result via `implies(Marker::X)` — this bakes in
/// both the vertical closure (higher tiers imply lower) and the
/// horizontal closure (Copy + Drop → Move). Composition uses the raw
/// `declared` on the *declaration's* markers to phrase errors; that
/// pass reads `s.markers.declared(_)` directly, not through here.
pub fn class_of(ty: &Type, env: &Env) -> Markers {
    let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
    match ty {
        Type::Int(_) | Type::Float(_) | Type::Bool | Type::Unit | Type::Fn(_) => all(),
        // Never is uninhabited: the substructural rules quantify over
        // values, and there are none. All three ops apply vacuously.
        Type::Never => all(),
        // Raw pointers are unrestricted (aliasable, forgettable,
        // relocatable) — same class as shared refs. No loan / no
        // obligation, so no linearity to worry about.
        Type::RawPtr(_) => all(),
        Type::Ref(kind, _) => match kind {
            // Shared refs are unrestricted and relocatable.
            RefKind::Shared => all(),
            // Exclusive mutable/uninit refs: affine + movable. The ref
            // itself is a pointer we can freely relocate; the referent's
            // obligation goes with it.
            RefKind::Mut | RefKind::Uninit => {
                Markers::from_iter([Marker::Drop, Marker::Move])
            }
            // `&out` / `&drop` carry linear obligations, but the
            // reference value itself is a pointer that can be relocated
            // (obligation transfers with the ref).
            RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
        },
        Type::Custom(name, _args) => match env.types.get(name) {
            // For a generic instantiation, the declared markers on the
            // decl are the type's markers regardless of the args — the
            // decl-side check verified those markers under the params'
            // bounds. Per-instantiation "does Foo<T> imply M" folds to
            // "did Foo declare M?" once bounds pass. Substitution into
            // fields lands with the semantic pass; args are ignored here.
            Some(TypeDecl::Struct(s)) => s.markers,
            Some(TypeDecl::Enum(e)) => e.markers,
            // Unknown name — tc has already reported "undeclared type".
            None => Markers::empty(),
        },
        // A generic type parameter's class comes from its declared
        // bounds. Phase 1 doesn't thread the type-param scope through
        // class_of, so any TypeVar reached here is treated as linear.
        // Semantically wrong for generic bodies, but generic bodies
        // aren't checked in phase 1 — parse/roundtrip only.
        Type::TypeVar(_) => Markers::empty(),
        // Array class inherits from its element type. Zero-length
        // arrays are trivially Copy Drop Move (no elements to worry
        // about) — treat like the element class regardless.
        Type::Array(elem, _) => class_of(elem, env),
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
        // `declared` on the struct + `implies` on the field: only
        // fire on markers the user actually wrote (avoids redundant
        // errors on closure-derived markers), and let the field's
        // closure satisfy the requirement (a field that's Copy + Drop
        // implies Move without needing explicit Move).
        if s.markers.declared(Marker::Copy) && !c.implies(Marker::Copy) {
            d.push_error(diag(
                CopyMarkerNotSatisfied,
                f.span,
                format!(
                    "In struct '{}' (marked Copy), field '{}' has type {} which is not Copy",
                    s.name, f.name, f.ty
                ),
            ));
        }
        if s.markers.declared(Marker::Drop) && !c.implies(Marker::Drop) {
            d.push_error(diag(
                DropMarkerNotSatisfied,
                f.span,
                format!(
                    "In struct '{}' (marked Drop), field '{}' has type {} which is not Drop",
                    s.name, f.name, f.ty
                ),
            ));
        }
        // Only check explicit Move against fields — an implicit Move
        // via Copy+Drop is guaranteed to succeed because those fields
        // are already Copy AND Drop, hence Move.
        if s.markers.declared(Marker::Move) && !c.implies(Marker::Move) {
            d.push_error(diag(
                MoveMarkerNotSatisfied,
                f.span,
                format!(
                    "In struct '{}' (marked Move), field '{}' has type {} which is not Move",
                    s.name, f.name, f.ty
                ),
            ));
        }
    }
}

fn check_enum(e: &EnumDecl, env: &Env, d: &mut Diagnostics) {
    for v in &e.variants {
        let c = class_of(&v.ty, env);
        if e.markers.declared(Marker::Copy) && !c.implies(Marker::Copy) {
            d.push_error(diag(
                CopyMarkerNotSatisfied,
                v.span,
                format!(
                    "In enum '{}' (marked Copy), variant '{}' payload type {} is not Copy",
                    e.name, v.name, v.ty
                ),
            ));
        }
        if e.markers.declared(Marker::Drop) && !c.implies(Marker::Drop) {
            d.push_error(diag(
                DropMarkerNotSatisfied,
                v.span,
                format!(
                    "In enum '{}' (marked Drop), variant '{}' payload type {} is not Drop",
                    e.name, v.name, v.ty
                ),
            ));
        }
        if e.markers.declared(Marker::Move) && !c.implies(Marker::Move) {
            d.push_error(diag(
                MoveMarkerNotSatisfied,
                v.span,
                format!(
                    "In enum '{}' (marked Move), variant '{}' payload type {} is not Move",
                    e.name, v.name, v.ty
                ),
            ));
        }
    }
}

