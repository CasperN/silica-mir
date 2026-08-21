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
//!
//! Generics: the declaration-side check uses a [`LocalEnv`] containing
//! the declaration's generic parameters, so a `Param(T)` reads its declared
//! bounds as its class. The dual use-site check lives in
//! [`LocalEnv::validate_type`] —
//! together they mean `class_of(Custom(_, args))` can return the
//! decl's declared markers without inspecting the args.

use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::diagnostic_format::format_type_diagnostic;
use crate::mir::env::{IndexedProgram, LocalEnv};

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
fn diag(code: impl Into<DiagCode>, source: SourceInfo, msg: String) -> Diagnostic {
    Diagnostic::new(code, source, msg)
}

pub fn check_program(prog: &IndexedProgram, d: &mut Diagnostics) {
    for type_decl in prog.types.values() {
        match type_decl {
            TypeDecl::Struct(s) => check_struct(s, prog, d),
            TypeDecl::Enum(e) => check_enum(e, prog, d),
        }
    }
    for ((trait_path, _), imp) in &prog.impls {
        if let Some(marker) = Marker::from_name(&trait_path.name) {
            check_marker_impl(imp, trait_path, marker, prog, d);
        }
    }
}

fn marker_composition_code(m: Marker) -> SubstructuralCompositionCode {
    match m {
        Marker::Copy => CopyMarkerNotSatisfied,
        Marker::Drop => DropMarkerNotSatisfied,
        Marker::Move => MoveMarkerNotSatisfied,
    }
}

fn check_marker_impl(
    imp: &ImplBlock,
    _trait_path: &Instance,
    marker: Marker,
    prog: &IndexedProgram,
    d: &mut Diagnostics,
) {
    let env = LocalEnv::for_decl(prog, &imp.params);
    let code = marker_composition_code(marker);
    match &imp.target.kind {
        TypeKind::Custom(instance) => {
            if let Some(TypeDecl::Struct(s)) = prog.types.get(&instance.name) {
                for f in &s.fields {
                    let field_ty = s
                        .meta
                        .try_substitute_types(&f.ty, &instance.type_args)
                        .unwrap_or_else(|| f.ty.clone());
                    let c = env.class_of(&field_ty);
                    if !c.implies(marker) {
                        d.push_error(diag(
                            code,
                            f.ty.source,
                            format!(
                                "In 'impl {} for {}', field '{}' has type {} which is not {}",
                                marker.name(),
                                imp.target,
                                f.name,
                                field_ty,
                                marker.name(),
                            ),
                        ));
                    }
                }
            } else if let Some(TypeDecl::Enum(e)) = prog.types.get(&instance.name) {
                for v in &e.variants {
                    let v_ty = e
                        .meta
                        .try_substitute_types(&v.ty, &instance.type_args)
                        .unwrap_or_else(|| v.ty.clone());
                    let c = env.class_of(&v_ty);
                    if !c.implies(marker) {
                        d.push_error(diag(
                            code,
                            v.ty.source,
                            format!(
                                "In 'impl {} for {}', variant '{}' payload type {} is not {}",
                                marker.name(),
                                imp.target,
                                v.name,
                                v_ty,
                                marker.name(),
                            ),
                        ));
                    }
                }
            }
        }
        TypeKind::Array(elem, _) => {
            let c = env.class_of(elem);
            if !c.implies(marker) {
                d.push_error(diag(
                    code,
                    elem.source,
                    format!(
                        "In 'impl {} for {}', element type {} is not {}",
                        marker.name(),
                        imp.target,
                        elem,
                        marker.name(),
                    ),
                ));
            }
        }
        TypeKind::Ref(kind, _, _) => {
            if !kind.value_markers().implies(marker) {
                d.push_error(diag(
                    code,
                    imp.params.source,
                    format!(
                        "Cannot implement {} for reference type {}",
                        marker.name(),
                        imp.target,
                    ),
                ));
            }
        }
        TypeKind::Param(_) => {
            let c = env.class_of(&imp.target);
            if !c.implies(marker) {
                d.push_error(diag(
                    code,
                    imp.params.source,
                    format!(
                        "Cannot implement {} for unconstrained type parameter {}",
                        marker.name(),
                        imp.target,
                    ),
                ));
            }
        }
        _ => {}
    }
}

/// For each marker declared on `decl_meta`, if `class` doesn't imply it,
/// push a diagnostic built by `make_msg(marker)`. `declared` on the
/// container + `implies` on the content: only fires on markers the user
/// actually wrote (avoids redundant errors on closure-derived markers),
/// and lets the content's closure satisfy the requirement (a field that's
/// Copy + Drop implies Move without needing explicit Move).
fn check_markers_against(
    decl_meta: &DeclMeta,
    class: Markers,
    source: SourceInfo,
    diagnostic_ty: &Type,
    make_msg: impl Fn(Marker, String) -> String,
    d: &mut Diagnostics,
) {
    const CHECKS: [(Marker, SubstructuralCompositionCode); 3] = [
        (Marker::Copy, CopyMarkerNotSatisfied),
        (Marker::Drop, DropMarkerNotSatisfied),
        (Marker::Move, MoveMarkerNotSatisfied),
    ];
    for (marker, code) in CHECKS {
        if decl_meta.markers.declared(marker) && !class.implies(marker) {
            d.push_error(format_type_diagnostic(decl_meta, diagnostic_ty, |ty| {
                diag(code, source, make_msg(marker, ty))
            }));
        }
    }
}

fn check_struct(s: &StructDecl, prog: &IndexedProgram, d: &mut Diagnostics) {
    let env = LocalEnv::for_decl(prog, &s.meta.params);
    for f in &s.fields {
        let c = env.class_of(&f.ty);
        check_markers_against(
            &s.meta,
            c,
            f.ty.source,
            &f.ty,
            |m, ty| {
                format!(
                    "In struct '{}' (marked {}), field '{}' has type {} which is not {}",
                    s.meta.name,
                    m.name(),
                    f.name,
                    ty,
                    m.name(),
                )
            },
            d,
        );
    }
}

fn check_enum(e: &EnumDecl, prog: &IndexedProgram, d: &mut Diagnostics) {
    let env = LocalEnv::for_decl(prog, &e.meta.params);
    for v in &e.variants {
        let c = env.class_of(&v.ty);
        check_markers_against(
            &e.meta,
            c,
            v.ty.source,
            &v.ty,
            |m, ty| {
                format!(
                    "In enum '{}' (marked {}), variant '{}' payload type {} is not {}",
                    e.meta.name,
                    m.name(),
                    v.name,
                    ty,
                    m.name(),
                )
            },
            d,
        );
    }
}
