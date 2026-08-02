//! Type-level predicates and helpers shared across passes.
//!
//! Cross-cutting queries about MIR `Type`s that don't belong to any
//! single pass, primarily generic parameter substitution.

use crate::common::Lifetime;
use crate::mir::ast::{
    ConstVal, DeclMeta, GenericParams, Instance, Operand, RValue, Statement, StatementKind,
    Terminator, Type, TypeKind, TypeParam,
};
use crate::mir::helpers::{assign_stmt, call_stmt, drop_stmt, require_uninit_stmt, unborrow_stmt};
use crate::mir::type_check::{IndexedProgram, TypeDecl};
use crate::mir::type_fold::TypeFolder;

impl GenericParams {
    /// Substitute the decl's declared lifetime and type parameters in
    /// `ty` with the args at a use site.
    pub fn substitute(&self, ty: &Type, lifetime_args: &[Lifetime], type_args: &[Type]) -> Type {
        let lifetime_params = self.lifetime_names();
        substitute_all(
            ty,
            &lifetime_params,
            lifetime_args,
            &self.type_params,
            type_args,
        )
    }

    /// Type-only degenerate case of [`GenericParams::substitute`] for callers
    /// that only have `type_args` on hand.
    pub fn substitute_types(&self, ty: &Type, type_args: &[Type]) -> Type {
        substitute_params(ty, &self.type_params, type_args)
    }

    /// Fallible substitution for callers that walk parser-produced use
    /// sites. Returns `None` when the use-site arity doesn't match.
    pub fn try_substitute(
        &self,
        ty: &Type,
        lifetime_args: &[Lifetime],
        type_args: &[Type],
    ) -> Option<Type> {
        if lifetime_args.len() != self.lifetime_params.len()
            || type_args.len() != self.type_params.len()
        {
            return None;
        }
        Some(self.substitute(ty, lifetime_args, type_args))
    }

    /// Fallible type-only substitution — pair to [`GenericParams::substitute_types`].
    pub fn try_substitute_types(&self, ty: &Type, type_args: &[Type]) -> Option<Type> {
        if type_args.len() != self.type_params.len() {
            return None;
        }
        Some(self.substitute_types(ty, type_args))
    }

    pub fn lifetime_names(&self) -> Vec<Lifetime> {
        self.lifetime_params
            .iter()
            .map(|param| param.lifetime.clone())
            .collect()
    }
}

impl DeclMeta {
    pub fn substitute(&self, ty: &Type, lifetime_args: &[Lifetime], type_args: &[Type]) -> Type {
        self.params.substitute(ty, lifetime_args, type_args)
    }

    pub fn substitute_types(&self, ty: &Type, type_args: &[Type]) -> Type {
        self.params.substitute_types(ty, type_args)
    }

    pub fn try_substitute(
        &self,
        ty: &Type,
        lifetime_args: &[Lifetime],
        type_args: &[Type],
    ) -> Option<Type> {
        self.params.try_substitute(ty, lifetime_args, type_args)
    }

    pub fn try_substitute_types(&self, ty: &Type, type_args: &[Type]) -> Option<Type> {
        self.params.try_substitute_types(ty, type_args)
    }

    pub fn lifetime_names(&self) -> Vec<Lifetime> {
        self.params.lifetime_names()
    }
}

/// Substitute type-parameter references in `ty` with the concrete
/// arguments at a use site. Given a declaration's `type_params` and
/// the args on `Custom(name, args)`, replaces every `TypeKind::Param(T)`
/// in `ty` with the corresponding arg.
///
/// Arity is a caller precondition — callers must validate before
/// invoking (e.g. via `LocalEnv::validate_type` or the trait/impl arity
/// checks in type_check). A mismatch here would silently leak the
/// declaration's own lifetime/type params into the use-site scope,
/// so we panic to surface the bug at the call boundary rather than
/// after downstream analyses have consumed a nonsensical type.
///
pub fn substitute_params(ty: &Type, type_params: &[TypeParam], args: &[Type]) -> Type {
    assert_eq!(
        args.len(),
        type_params.len(),
        "substitute_params arity mismatch on type {:?}: {} params, {} args",
        ty,
        type_params.len(),
        args.len(),
    );
    substitute(ty, &[], &[], type_params, args)
}

/// Substitute both lifetime and type parameter references in `ty`. Use
/// when a decl carries both `<'a, T>` lifetimes and type parameters and
/// a use site supplies both.
pub fn substitute_all(
    ty: &Type,
    lifetime_params: &[Lifetime],
    lifetime_args: &[Lifetime],
    type_params: &[TypeParam],
    type_args: &[Type],
) -> Type {
    assert_eq!(
        lifetime_args.len(),
        lifetime_params.len(),
        "substitute_all lifetime arity mismatch on type {:?}: {} params, {} args",
        ty,
        lifetime_params.len(),
        lifetime_args.len(),
    );
    assert_eq!(
        type_args.len(),
        type_params.len(),
        "substitute_all type arity mismatch on type {:?}: {} params, {} args",
        ty,
        type_params.len(),
        type_args.len(),
    );
    substitute(ty, lifetime_params, lifetime_args, type_params, type_args)
}

fn substitute(
    ty: &Type,
    lifetime_params: &[Lifetime],
    lifetime_args: &[Lifetime],
    type_params: &[TypeParam],
    type_args: &[Type],
) -> Type {
    SubstituteFolder {
        lifetime_params,
        lifetime_args,
        type_params,
        type_args,
    }
    .fold_type(ty)
}

struct SubstituteFolder<'a> {
    lifetime_params: &'a [Lifetime],
    lifetime_args: &'a [Lifetime],
    type_params: &'a [TypeParam],
    type_args: &'a [Type],
}

impl TypeFolder for SubstituteFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        let TypeKind::Param(name) = &ty.kind else {
            return None;
        };
        self.type_params
            .iter()
            .zip(self.type_args)
            .find_map(|(param, argument)| (param.name == *name).then(|| argument.clone()))
    }

    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        for (param, argument) in self.lifetime_params.iter().zip(self.lifetime_args) {
            if param == lifetime {
                return argument.clone();
            }
        }
        lifetime.clone()
    }
}

/// Substitute type parameters in every Type-carrying position inside a
/// statement. Dispatches to [`substitute_rvalue_types`] / [`substitute_operand_types`]
/// for the embedded slots; statement kinds that carry no types
/// (`Drop`, `Unborrow`, `RequireUninit`) clone through.
pub fn substitute_stmt_types(s: &Statement, type_params: &[TypeParam], args: &[Type]) -> Statement {
    match &s.kind {
        StatementKind::Assign(p, r) => assign_stmt(
            p.clone(),
            substitute_rvalue_types(r, type_params, args),
            s.source,
        ),
        StatementKind::Call(callee, cargs) => call_stmt(
            substitute_operand_types(callee, type_params, args),
            cargs
                .iter()
                .map(|a| substitute_operand_types(a, type_params, args))
                .collect(),
            s.source,
        ),
        StatementKind::Drop(p) => drop_stmt(p.clone(), s.source),
        StatementKind::Unborrow(p) => unborrow_stmt(p.clone(), s.source),
        StatementKind::RequireUninit(p) => require_uninit_stmt(p.clone(), s.source),
    }
}

/// Substitute type parameters in the Type slots of an rvalue: enum
/// construction type args, the type argument of a `PtrCast`, and any
/// operand-embedded types (see [`substitute_operand_types`]).
pub fn substitute_rvalue_types(r: &RValue, type_params: &[TypeParam], args: &[Type]) -> RValue {
    match r {
        RValue::EnumConstr(name, targs, variant, payload) => RValue::EnumConstr(
            name.clone(),
            targs
                .iter()
                .map(|a| substitute_params(a, type_params, args))
                .collect(),
            variant.clone(),
            substitute_operand_types(payload, type_params, args),
        ),
        RValue::Use(op) => RValue::Use(substitute_operand_types(op, type_params, args)),
        RValue::Ref(k, p) => RValue::Ref(*k, p.clone()),
        RValue::RawRef(p) => RValue::RawRef(p.clone()),
        RValue::ArrayLit(ops) => RValue::ArrayLit(
            ops.iter()
                .map(|o| substitute_operand_types(o, type_params, args))
                .collect(),
        ),
        RValue::PtrCast(op, ty) => RValue::PtrCast(
            substitute_operand_types(op, type_params, args),
            substitute_params(ty, type_params, args),
        ),
    }
}

/// Substitute type parameters in the Type slots of an operand: the
/// type-arg list of an `FnName` const and the type slots of qualified method
/// constants. All other operand shapes have no embedded types.
pub fn substitute_operand_types(op: &Operand, type_params: &[TypeParam], args: &[Type]) -> Operand {
    match op {
        Operand::Const(ConstVal::FnName(instance)) => Operand::Const(ConstVal::FnName(Instance {
            name: instance.name.clone(),
            lifetime_args: instance.lifetime_args.clone(),
            type_args: instance
                .type_args
                .iter()
                .map(|a| substitute_params(a, type_params, args))
                .collect(),
        })),
        Operand::Const(ConstVal::InherentFn { self_ty, method }) => {
            Operand::Const(ConstVal::InherentFn {
                self_ty: substitute_params(self_ty, type_params, args),
                method: Instance {
                    name: method.name.clone(),
                    lifetime_args: method.lifetime_args.clone(),
                    type_args: method
                        .type_args
                        .iter()
                        .map(|arg| substitute_params(arg, type_params, args))
                        .collect(),
                },
            })
        }
        Operand::Const(ConstVal::TraitFn {
            trait_path,
            self_ty,
            method,
        }) => Operand::Const(ConstVal::TraitFn {
            trait_path: Instance {
                name: trait_path.name.clone(),
                lifetime_args: trait_path.lifetime_args.clone(),
                type_args: trait_path
                    .type_args
                    .iter()
                    .map(|a| substitute_params(a, type_params, args))
                    .collect(),
            },
            self_ty: substitute_params(self_ty, type_params, args),
            method: Instance {
                name: method.name.clone(),
                lifetime_args: method.lifetime_args.clone(),
                type_args: method
                    .type_args
                    .iter()
                    .map(|a| substitute_params(a, type_params, args))
                    .collect(),
            },
        }),
        _ => op.clone(),
    }
}

/// Substitute type parameters in the Type slots of a terminator. No
/// terminator variant carries a `Type` today — `Branch`'s condition is
/// a bool operand, `SwitchEnum` names the scrutinee by `Place`, and
/// the rest are leaf variants — so this is a shape-preserving clone.
/// Callers still route through it so that adding a Type slot to any
/// terminator has a single extension point.
pub fn substitute_terminator_types(
    t: &Terminator,
    _type_params: &[TypeParam],
    _args: &[Type],
) -> Terminator {
    t.clone()
}

/// Compute the type of `place` inside `func`. Walks the place's
/// projections against the locals map + the program's declaration table, substituting
/// both type and lifetime parameters at each `Custom` boundary.
/// Returns None if the place is malformed (missing local, unknown
/// field/variant, etc.).
pub fn place_type(
    locals: &indexmap::IndexMap<String, Type>,
    prog: &IndexedProgram,
    place: &crate::mir::ast::Place,
) -> Option<Type> {
    use crate::mir::ast::{extract_path_with_deref, PathStep};
    let (root, steps) = extract_path_with_deref(place);
    let mut ty = locals.get(&root)?.clone();
    for step in steps {
        ty = match (step, ty.kind) {
            (
                PathStep::Field(f),
                TypeKind::Custom(Instance {
                    name,
                    lifetime_args: lts,
                    type_args: args,
                }),
            ) => {
                let TypeDecl::Struct(s) = prog.types.get(&name)? else {
                    return None;
                };
                let field = s.fields.iter().find(|fd| fd.name == f)?;
                // Arity mismatch is already reported; fall back to the
                // raw type so downstream sees the projection shape.
                s.meta
                    .try_substitute(&field.ty, &lts, &args)
                    .unwrap_or_else(|| field.ty.clone())
            }
            (
                PathStep::Downcast(v),
                TypeKind::Custom(Instance {
                    name,
                    lifetime_args: lts,
                    type_args: args,
                }),
            ) => {
                let TypeDecl::Enum(e) = prog.types.get(&name)? else {
                    return None;
                };
                let variant = e.variants.iter().find(|vd| vd.name == v)?;
                e.meta
                    .try_substitute(&variant.ty, &lts, &args)
                    .unwrap_or_else(|| variant.ty.clone())
            }
            (PathStep::Deref, TypeKind::Ref(_, _, inner)) => *inner,
            (PathStep::Deref, TypeKind::RawPtr(inner)) => *inner,
            (PathStep::Index(_), TypeKind::Array(elem, _)) => *elem,
            _ => return None,
        };
    }
    Some(ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::helpers::*;

    #[test]
    fn substitute_params_preserves_ref_lifetime() {
        use crate::common::Lifetime;
        use crate::mir::ast::RefKind;
        let ty = named_ref_ty(RefKind::Shared, Lifetime("a".into()), i64_ty());
        let out = substitute_params(&ty, &[], &[]);
        assert_eq!(
            out, ty,
            "substitute_params must not drop the ref's lifetime"
        );
    }

    #[test]
    fn substitute_params_preserves_custom_lifetime_args() {
        use crate::common::Lifetime;
        let ty = custom_ty_generic("Wrap", vec![Lifetime("a".into())], vec![]);
        let out = substitute_params(&ty, &[], &[]);
        assert_eq!(
            out, ty,
            "substitute_params must not drop Custom's lifetime args"
        );
    }

    #[test]
    fn substitute_params_still_substitutes_nested_type_params() {
        use crate::common::{GeneratedKind, Lifetime, SourceInfo, Span};
        use crate::mir::ast::{RefKind, TypeParam};
        let tp = TypeParam {
            name: "T".into(),
            bounds: crate::mir::ast::Bounds::default(),
            source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
        };
        let ty = named_ref_ty(RefKind::Shared, Lifetime("a".into()), param_ty("T"));
        let out = substitute_params(&ty, &[tp], &[i64_ty()]);
        assert_eq!(
            out,
            named_ref_ty(RefKind::Shared, Lifetime("a".into()), i64_ty()),
        );
    }

    #[test]
    fn substitution_preserves_container_and_argument_provenance() {
        use crate::common::{GeneratedKind, SourceInfo, Span};

        let container_source = SourceInfo::generated(
            GeneratedKind::TypeSynthesis,
            Span {
                line: 3,
                col: 5,
                end_line: 3,
                end_col: 10,
            },
        );
        let argument_source = SourceInfo::written(Span {
            line: 8,
            col: 12,
            end_line: 8,
            end_col: 16,
        });
        let ty = Type::new(
            TypeKind::Array(Box::new(param_ty("T")), 1),
            container_source,
        );
        let param = TypeParam {
            name: "T".into(),
            bounds: crate::mir::ast::Bounds::default(),
            source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
        };
        let argument = Type::new(TypeKind::Int(crate::common::IntTy::I64), argument_source);

        let substituted = substitute_params(&ty, &[param], &[argument]);
        let TypeKind::Array(element, _) = &substituted.kind else {
            panic!("expected array type");
        };
        assert_eq!(substituted.source, container_source);
        assert_eq!(element.source, argument_source);
    }

    #[test]
    fn substitute_all_replaces_ref_lifetime() {
        use crate::mir::ast::RefKind;
        let ty = named_ref_ty(RefKind::Shared, Lifetime("a".into()), i64_ty());
        let out = substitute_all(
            &ty,
            &[Lifetime("a".into())],
            &[Lifetime("b".into())],
            &[],
            &[],
        );
        assert_eq!(
            out,
            named_ref_ty(RefKind::Shared, Lifetime("b".into()), i64_ty()),
        );
    }

    #[test]
    fn substitute_all_replaces_custom_lifetime_args() {
        let ty = custom_ty_generic("Wrap", vec![Lifetime("a".into())], vec![]);
        let out = substitute_all(
            &ty,
            &[Lifetime("a".into())],
            &[Lifetime("x".into())],
            &[],
            &[],
        );
        assert_eq!(
            out,
            custom_ty_generic("Wrap", vec![Lifetime("x".into())], vec![]),
        );
    }

    #[test]
    fn substitute_all_no_op_when_lifetime_not_in_params() {
        let ty = custom_ty_generic("Wrap", vec![Lifetime("other".into())], vec![]);
        let out = substitute_all(
            &ty,
            &[Lifetime("a".into())],
            &[Lifetime("x".into())],
            &[],
            &[],
        );
        assert_eq!(out, ty);
    }
}
