//! Type-level predicates and helpers shared across passes.
//!
//! Cross-cutting queries about MIR `Type`s that don't belong to any
//! single pass: inhabitedness, generic parameter substitution, etc.

use crate::common::Lifetime;
use crate::mir::ast::{
    ConstVal, DeclMeta, Instance, Operand, RValue, Statement, StatementKind, Terminator, Type,
    TypeKind, TypeParam,
};
use crate::mir::helpers::{
    assign_stmt, call_stmt, drop_stmt, require_uninit_stmt, unborrow_stmt,
};
use crate::mir::type_check::{Env, TypeDecl};
use crate::mir::type_fold::TypeFolder;
use std::collections::BTreeSet;

impl DeclMeta {
    /// Substitute the decl's declared lifetime and type parameters in
    /// `ty` with the args at a use site. Convenience wrapper around
    /// [`substitute_all`] so callers don't have to spell the four
    /// slices in the right order every time.
    ///
    /// Panics on arity mismatch — callers post-typecheck should already
    /// have validated the use-site's arity. Elaboration walks that see
    /// parser output (which may contain arity errors reported by
    /// typecheck) should use [`DeclMeta::try_substitute`] instead.
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

    /// Type-only degenerate case of [`DeclMeta::substitute`] for callers
    /// that only have `type_args` on hand (a decl with no lifetime
    /// parameters, or a caller that doesn't need lifetime substitution).
    pub fn substitute_types(&self, ty: &Type, type_args: &[Type]) -> Type {
        substitute_params(ty, &self.type_params, type_args)
    }

    /// Fallible substitution for callers that walk parser-produced use
    /// sites. Returns `None` when the use-site arity doesn't match the
    /// decl's — typecheck reported the mismatch; recursion through this
    /// slot has no meaningful continuation, so the walker skips it.
    /// Callers that panic on mismatch use [`DeclMeta::substitute`].
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

    /// Fallible type-only substitution — pair to [`DeclMeta::substitute_types`]
    /// for walkers over parser data. Returns `None` on type-arg arity
    /// mismatch.
    pub fn try_substitute_types(&self, ty: &Type, type_args: &[Type]) -> Option<Type> {
        if type_args.len() != self.type_params.len() {
            return None;
        }
        Some(self.substitute_types(ty, type_args))
    }

    fn lifetime_names(&self) -> Vec<Lifetime> {
        self.lifetime_params
            .iter()
            .map(|param| param.lifetime.clone())
            .collect()
    }
}

/// Substitute type-parameter references in `ty` with the concrete
/// arguments at a use site. Given a declaration's `type_params` and
/// the args on `Custom(name, args)`, replaces every `TypeKind::Param(T)`
/// in `ty` with the corresponding arg.
///
/// Arity is a caller precondition — callers must validate before
/// invoking (e.g. via `Env::validate_type` or the trait/impl arity
/// checks in type_check). A mismatch here would silently leak the
/// declaration's own lifetime/type params into the use-site scope,
/// so we panic to surface the bug at the call boundary rather than
/// after downstream analyses have consumed a nonsensical type.
///
/// TODO: replace the two-slice signature with a `Substitution` struct
/// holding `Vec<(TypeParam, Type)>` (and its lifetime counterpart) so
/// callers can't construct mismatched pairs. Validation moves to the
/// constructor, substitute becomes total.
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
pub fn substitute_stmt_types(
    s: &Statement,
    type_params: &[TypeParam],
    args: &[Type],
) -> Statement {
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
pub fn substitute_rvalue_types(
    r: &RValue,
    type_params: &[TypeParam],
    args: &[Type],
) -> RValue {
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
/// type-arg list of an `FnName` const, and the `self_ty` and trait-ref
/// type args of a `TraitFn` const. All other operand shapes have no
/// embedded types.
pub fn substitute_operand_types(
    op: &Operand,
    type_params: &[TypeParam],
    args: &[Type],
) -> Operand {
    match op {
        Operand::Const(ConstVal::FnName(name, targs)) => Operand::Const(ConstVal::FnName(
            name.clone(),
            targs
                .iter()
                .map(|a| substitute_params(a, type_params, args))
                .collect(),
        )),
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
/// projections against the locals map + env's decl table, substituting
/// both type and lifetime parameters at each `Custom` boundary.
/// Returns None if the place is malformed (missing local, unknown
/// field/variant, etc.).
pub fn place_type(
    locals: &indexmap::IndexMap<String, Type>,
    env: &Env,
    place: &crate::mir::ast::Place,
) -> Option<Type> {
    use crate::mir::ast::{extract_path_with_deref, PathStep};
    let (root, steps) = extract_path_with_deref(place);
    let mut ty = locals.get(&root)?.clone();
    for step in steps {
        ty = match (step, ty.kind) {
            (PathStep::Field(f), TypeKind::Custom(Instance { name, lifetime_args: lts, type_args: args })) => {
                let TypeDecl::Struct(s) = env.types.get(&name)? else {
                    return None;
                };
                let field = s.fields.iter().find(|fd| fd.name == f)?;
                // Arity mismatch is already reported; fall back to the
                // raw type so downstream sees the projection shape.
                s.meta
                    .try_substitute(&field.ty, &lts, &args)
                    .unwrap_or_else(|| field.ty.clone())
            }
            (PathStep::Downcast(v), TypeKind::Custom(Instance { name, lifetime_args: lts, type_args: args })) => {
                let TypeDecl::Enum(e) = env.types.get(&name)? else {
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

/// True if a value of `ty` cannot be constructed. Uninhabited types:
/// - `never` — the axiom.
/// - Struct where any field is uninhabited (whole-value construction
///   requires every field).
/// - Enum where every variant's payload is uninhabited (no variant
///   is constructible → the enum is empty).
/// - Non-empty array of an uninhabited element type. `[T; 0]` is
///   inhabited (the empty array literal has no elements to construct).
///
/// References, raw pointers, function pointers, scalars, `unit`, and
/// `bool` are always inhabited. Recursive struct/enum types are
/// bounded by the visited set — a Custom name seen twice in the
/// same walk conservatively returns false (inhabited) rather than
/// looping.
pub fn is_type_uninhabited(ty: &Type, env: &Env) -> bool {
    fn walk(ty: &Type, env: &Env, visited: &mut BTreeSet<String>) -> bool {
        match &ty.kind {
            TypeKind::Never => true,
            TypeKind::Custom(Instance { name, .. }) => {
                if !visited.insert(name.clone()) {
                    return false;
                }
                let out = match env.types.get(name) {
                    Some(TypeDecl::Struct(s)) => s.fields.iter().any(|f| walk(&f.ty, env, visited)),
                    // An enum is uninhabited when EVERY variant is
                    // uninhabited. Vacuous truth handles the empty
                    // enum (no variants → all() returns true).
                    Some(TypeDecl::Enum(e)) => e.variants.iter().all(|v| walk(&v.ty, env, visited)),
                    None => false,
                };
                visited.remove(name);
                out
            }
            TypeKind::Array(elem, n) => *n > 0 && walk(elem, env, &mut BTreeSet::new()),
            _ => false,
        }
    }
    walk(ty, env, &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::ast::Program;
    use crate::mir::helpers::*;
    use crate::mir::parser::Parser;

    /// Build an Env from MIR source, discarding any diagnostics.
    fn env_of(src: &str) -> Env {
        let program: Program = Parser::parse_or_panic(src);
        Env::build(&program).0
    }

    #[test]
    fn never_is_uninhabited() {
        let env = env_of("fn f() { entry: return }");
        assert!(is_type_uninhabited(&never_ty(), &env));
    }

    #[test]
    fn scalars_are_inhabited() {
        let env = env_of("fn f() { entry: return }");
        assert!(!is_type_uninhabited(&i64_ty(), &env));
        assert!(!is_type_uninhabited(&bool_ty(), &env));
        assert!(!is_type_uninhabited(&unit_ty(), &env));
    }

    #[test]
    fn struct_with_never_field_is_uninhabited() {
        let env = env_of("struct S { a: i64 b: never } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("S"), &env));
    }

    #[test]
    fn struct_with_all_inhabited_fields_is_inhabited() {
        let env = env_of("struct S { a: i64 b: bool } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&custom_ty("S"), &env));
    }

    #[test]
    fn empty_enum_is_uninhabited() {
        // No variants → vacuous truth: every variant is uninhabited.
        let env = env_of("enum E { } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn enum_with_one_inhabited_variant_is_inhabited() {
        let env = env_of("enum E { A: i64 B: never } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn enum_with_all_never_variants_is_uninhabited() {
        let env = env_of("enum E { A: never B: never } fn f() { entry: return }");
        assert!(is_type_uninhabited(&custom_ty("E"), &env));
    }

    #[test]
    fn zero_length_array_of_never_is_inhabited() {
        // `[Never; 0]` has no elements to construct — trivially inhabited
        // by the empty array literal.
        let env = env_of("fn f() { entry: return }");
        let ty = array_ty(never_ty(), 0);
        assert!(!is_type_uninhabited(&ty, &env));
    }

    #[test]
    fn nonempty_array_of_never_is_uninhabited() {
        let env = env_of("fn f() { entry: return }");
        let ty = array_ty(never_ty(), 3);
        assert!(is_type_uninhabited(&ty, &env));
    }

    #[test]
    fn recursive_via_reference_does_not_loop() {
        // A recursive-through-reference struct: the walker must not
        // infinitely recurse into `S`'s own name; the visited set
        // conservatively treats a second occurrence as inhabited.
        let env = env_of("struct S { r: &S } fn f() { entry: return }");
        assert!(!is_type_uninhabited(&custom_ty("S"), &env));
    }

    #[test]
    fn references_are_always_inhabited() {
        // Even a reference to Never is a fine reference value.
        let env = env_of("fn f() { entry: return }");
        let ty = shared_ref_ty(never_ty());
        assert!(!is_type_uninhabited(&ty, &env));
    }

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
