use std::collections::HashSet;

use indexmap::IndexSet;

use crate::common::{LifetimeParam, Marker, Markers};
use crate::diagnostics::Diagnostics;
use crate::hll::ast::{
    impl_method_context, trait_method_context, Declaration, ImplBlock, Instance, Program, Type,
    TypeKind, TypeParam,
};

pub mod casts;
pub(crate) mod closures;
pub(crate) mod dispatch;
pub mod env;
pub(crate) mod infer;
pub mod mod_types;
pub mod subst;
pub mod traits;
pub(crate) mod validation;

pub use casts::{cast_intrinsic_name, is_cast_supported};
pub use env::{
    ClosureCapture, ClosureInfo, ExpressionTypes, GenericClosureCall, ReceiverAdjustment,
    ResolvedMethodTarget, ResolvedReceiverCall, ResolvedReceiverTarget, TypeCheckResults, TypeEnv,
};
pub use mod_types::{source_diagnostic, HllTypeCheckCode};
pub use subst::{Subst, UnifyError};
pub use traits::{class_of, type_satisfies_trait, type_satisfies_trait_with_scope};

use closures::assign_closure_capture_lifetimes;
use env::type_params_scope;
use infer::check_fn_body;
use traits::instantiate_trait_self_bound;
use validation::{
    validate_bounds, validate_fn_modifiers, validate_fn_signature, validate_impl_method_safety,
    validate_trait_bound_cycles, validate_type, validate_type_param_bounds, FnDeclSite,
};

/// Run HLL type-checking, pushing errors into `d`. Returns resolved expression
/// types and function instantiations; errors accumulate in `d`.
pub fn run_type_check(program: &Program, d: &mut Diagnostics) -> Option<TypeCheckResults> {
    let types = typecheck_program_collect(program, d);
    if d.has_errors() {
        None
    } else {
        Some(types)
    }
}

/// Test-facing wrapper — sibling modules under `hll::*` use this to
/// stage a typecheck without needing a `Diagnostics` container.
/// Production callers should use `run_type_check`.
#[cfg(test)]
pub(super) fn typecheck_program(program: &Program) -> Diagnostics {
    let mut d = Diagnostics::default();
    typecheck_program_collect(program, &mut d);
    d
}

/// Run HLL type-checking, pushing all errors into `d` and returning its results
/// unconditionally. Production callers should use `run_type_check`.
pub(super) fn typecheck_program_collect(
    program: &Program,
    d: &mut Diagnostics,
) -> TypeCheckResults {
    let mut env = TypeEnv::new();
    let mut reserved_lifetime_names = HashSet::new();
    for declaration in &program.declarations {
        match declaration {
            Declaration::Struct(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Enum(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Fn(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Trait(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .chain(
                            declaration
                                .methods
                                .iter()
                                .flat_map(|method| method.lifetime_params.iter()),
                        )
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Impl(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .chain(
                            declaration
                                .methods
                                .iter()
                                .flat_map(|method| method.lifetime_params.iter()),
                        )
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
        }
    }
    let mut types = TypeCheckResults {
        reserved_lifetime_names,
        ..TypeCheckResults::default()
    };

    // Preload prelude wrappers (`size_of<T>`, `ptr_offset<T>`) so user
    // code can spell them by name. Bodies live at the MIR level; here
    // we only need the surface signatures.
    for f in crate::hll::prelude::prelude_fn_decls() {
        env.functions.insert(f.name.clone(), f);
    }
    for trait_decl in crate::hll::prelude::prelude_trait_decls() {
        env.traits.insert(trait_decl.name.clone(), trait_decl);
    }
    for imp in crate::hll::prelude::prelude_impl_decls() {
        env.impls.push(imp);
    }

    // Populate top-level declarations
    for decl in &program.declarations {
        match decl {
            Declaration::Struct(s) => {
                env.structs.insert(s.name.clone(), s.clone());
            }
            Declaration::Enum(e) => {
                env.enums.insert(e.name.clone(), e.clone());
            }
            Declaration::Fn(f) => {
                env.functions.insert(f.name.clone(), f.clone());
            }
            Declaration::Trait(t) => {
                env.traits.insert(t.name.clone(), t.clone());
            }
            Declaration::Impl(i) => {
                env.impls.push(i.clone());
            }
        }
    }

    validate_trait_bound_cycles(program, &env, d);
    validate_impl_method_safety(&env, d);

    // Validate every decl-level type
    for decl in &program.declarations {
        match decl {
            Declaration::Struct(s) => {
                let scope = type_params_scope(&s.type_params);
                validate_type_param_bounds(&env, &s.type_params, &scope, d);
                for f in &s.fields {
                    validate_type(&env, &f.ty, &scope, d);
                }
            }
            Declaration::Enum(e) => {
                let scope = type_params_scope(&e.type_params);
                validate_type_param_bounds(&env, &e.type_params, &scope, d);
                for v in &e.variants {
                    validate_type(&env, &v.ty, &scope, d);
                }
            }
            Declaration::Fn(f) => {
                let scope = type_params_scope(&f.type_params);
                validate_type_param_bounds(&env, &f.type_params, &scope, d);
                let errors_before = d.error_count();
                for p in &f.params {
                    validate_type(&env, &p.ty, &scope, d);
                }
                validate_type(&env, &f.ret_ty, &scope, d);
                d.annotate_errors_in_function(errors_before, &f.name);
            }
            Declaration::Trait(t) => {
                let mut trait_scope = type_params_scope(&t.type_params);
                trait_scope.insert("Self".to_string(), t.self_bounds.clone());
                validate_type_param_bounds(&env, &t.type_params, &trait_scope, d);
                validate_bounds(
                    &env,
                    &format!("trait '{}'", t.name),
                    &t.self_bounds,
                    &trait_scope,
                    d,
                );
                for method in &t.methods {
                    let mut params = t.type_params.clone();
                    params.push(TypeParam {
                        name: "Self".to_string(),
                        bounds: t.self_bounds.clone(),
                        source: t.source,
                    });
                    params.extend(method.type_params.clone());
                    let scope = type_params_scope(&params);
                    validate_type_param_bounds(&env, &method.type_params, &scope, d);
                    let context = trait_method_context(&t.name, &method.name);
                    validate_fn_modifiers(method, FnDeclSite::TraitMethod, &context, d);
                    validate_fn_signature(&env, method, &params, &context, d);
                }
            }
            Declaration::Impl(i) => {
                let impl_scope = type_params_scope(&i.type_params);
                validate_type_param_bounds(&env, &i.type_params, &impl_scope, d);
                validate_type(&env, &i.target, &impl_scope, d);
                if let Some(trait_path) = &i.trait_path {
                    for arg in &trait_path.type_args {
                        validate_type(&env, arg, &impl_scope, d);
                    }
                    if let Some(trait_decl) = env.traits.get(&trait_path.name) {
                        for marker in trait_decl.self_bounds.markers.iter_declared() {
                            if !env.class_of(&i.target, &impl_scope).implies(marker) {
                                d.push_error(source_diagnostic(
                                    HllTypeCheckCode::BoundNotSatisfied,
                                    i.source,
                                    format!(
                                        "impl of '{}' for {} requires Self: {}",
                                        trait_path,
                                        i.target,
                                        marker.name()
                                    ),
                                ));
                            }
                        }
                        for bound in &trait_decl.self_bounds.traits {
                            let required = instantiate_trait_self_bound(
                                trait_decl, trait_path, &i.target, bound,
                            );
                            if !type_satisfies_trait_with_scope(&env, &i.target, &required, &impl_scope) {
                                d.push_error(source_diagnostic(
                                    HllTypeCheckCode::BoundNotSatisfied,
                                    i.source,
                                    format!(
                                        "impl of '{}' for {} requires Self: {}",
                                        trait_path, i.target, required
                                    ),
                                ));
                            }
                        }
                    }
                }
                for method in &i.methods {
                    let mut params = i.type_params.clone();
                    params.extend(method.type_params.clone());
                    let scope = type_params_scope(&params);
                    validate_type_param_bounds(&env, &method.type_params, &scope, d);
                    let context =
                        impl_method_context(&i.target, i.trait_path.as_ref(), &method.name);
                    validate_fn_signature(&env, method, &params, &context, d);
                }
            }
        }
    }

    // Typecheck function bodies
    for decl in &program.declarations {
        match decl {
            Declaration::Fn(f) => {
                validate_fn_modifiers(f, FnDeclSite::Free, &f.name, d);
                check_fn_body(&mut env, &mut types, f, &[], &[], &f.name, d);
            }
            Declaration::Impl(i) => {
                for method in &i.methods {
                    let context =
                        impl_method_context(&i.target, i.trait_path.as_ref(), &method.name);
                    validate_fn_modifiers(method, FnDeclSite::ImplMethod, &context, d);
                    check_fn_body(
                        &mut env,
                        &mut types,
                        method,
                        &i.lifetime_params,
                        &i.type_params,
                        &context,
                        d,
                    );
                }
            }
            Declaration::Struct(_) | Declaration::Enum(_) | Declaration::Trait(_) => {}
        }
    }

    for closure in types.closures.values_mut() {
        let scope = closure
            .type_params
            .iter()
            .map(|p| (p.name.clone(), p.bounds.clone()))
            .collect::<std::collections::HashMap<_, _>>();
        for c in &mut closure.captures {
            let field_markers = env.class_of(&c.ty, &scope);
            c.is_copy = field_markers.declared(Marker::Copy);
            c.is_drop = field_markers.declared(Marker::Drop);
        }
        let mut lts = IndexSet::new();
        let mut counter = 0;
        for c in &mut closure.captures {
            assign_closure_capture_lifetimes(&mut c.ty, &mut lts, &mut counter);
        }
        closure.lifetime_args = lts.into_iter().collect();
        closure.lifetime_params = closure
            .lifetime_args
            .iter()
            .map(|lt| {
                LifetimeParam::generated(
                    lt.clone(),
                    crate::common::GeneratedKind::HllDesugaring,
                    closure.source.span(),
                )
            })
            .collect();

        let mut is_copy = true;
        let mut is_drop = true;
        let mut is_move = true;
        for c in &closure.captures {
            let field_markers = env.class_of(&c.ty, &scope);
            if !field_markers.declared(Marker::Copy) {
                is_copy = false;
            }
            if !field_markers.declared(Marker::Drop) {
                is_drop = false;
            }
            if !field_markers.declared(Marker::Move) {
                is_move = false;
            }
        }
        let mut derived = Vec::new();
        if is_copy {
            derived.push(Marker::Copy);
        }
        if is_drop {
            derived.push(Marker::Drop);
        }
        if is_move {
            derived.push(Marker::Move);
        }
        closure.markers = Markers::from_iter(derived);
        closure.fn_kind =
            crate::hll::derive::infer_closure_fn_kind(&closure.captures, &closure.body, &env);
        let struct_decl = closure.to_struct_decl();
        env.structs.insert(struct_decl.name.clone(), struct_decl.clone());
        env.closures.insert(closure.struct_name.clone(), closure.clone());
        if !closure.markers.declared(Marker::Copy)
            && crate::hll::derive::can_derive_auto_clone(&struct_decl, &env)
        {
            closure.is_auto_clone = true;
            let target_ty = Type::synthesized(TypeKind::Custom(Instance::new(
                closure.struct_name.clone(),
                closure.lifetime_args.clone(),
                closure.type_args.clone(),
            )));
            env.impls.push(ImplBlock {
                lifetime_params: closure.lifetime_params.clone(),
                outlives: Vec::new(),
                type_params: closure.type_params.clone(),
                trait_path: Some(Instance::bare("AutoClone")),
                target: target_ty,
                methods: Vec::new(),
                source: closure.source,
            });
        }
        if !closure.markers.declared(Marker::Drop)
            && crate::hll::derive::can_derive_auto_destroy(&struct_decl, &env)
        {
            closure.is_auto_destroy = true;
            let target_ty = Type::synthesized(TypeKind::Custom(Instance::new(
                closure.struct_name.clone(),
                closure.lifetime_args.clone(),
                closure.type_args.clone(),
            )));
            env.impls.push(ImplBlock {
                lifetime_params: closure.lifetime_params.clone(),
                outlives: Vec::new(),
                type_params: closure.type_params.clone(),
                trait_path: Some(Instance::bare("AutoDestroy")),
                target: target_ty,
                methods: Vec::new(),
                source: closure.source,
            });
        }
    }
    types.closures_by_struct.clear();
    for closure in types.closures.values() {
        types.closures_by_struct.insert(closure.struct_name.clone(), closure.clone());
    }
    types.pending_instantiations.clear();
    env.current_type_params.clear();
    env.current_lifetimes.clear();
    env.current_function = None;
    env.current_ret_ty = None;
    env.in_unsafe = false;
    types.env = env;
    types
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::common::{GeneratedKind, IntTy, Lifetime, RefKind, SourceInfo, Span};
    use crate::diagnostics::DiagCode;
    use crate::hll::ast::{ExprKind, Stmt, TypeKind};
    use crate::hll::helpers::*;
    use crate::hll::parser::Parser;
    use crate::hll::type_check::env::substitute;

    fn test_source(line: u32) -> SourceInfo {
        SourceInfo::written(Span {
            line,
            col: 1,
            end_line: line,
            end_col: 2,
        })
    }

    fn metadata_bearing_type(leaf: Type, outer_source: SourceInfo, ref_source: SourceInfo) -> Type {
        Type::new(
            TypeKind::Custom(Instance::new(
                "Wrap",
                vec![Lifetime("outer".into())],
                vec![Type::new(
                    TypeKind::Ref(
                        RefKind::Shared,
                        Some(Lifetime("inner".into())),
                        Box::new(leaf),
                    ),
                    ref_source,
                )],
            )),
            outer_source,
        )
    }

    fn assert_metadata_preserved(
        ty: &Type,
        outer_source: SourceInfo,
        ref_source: SourceInfo,
        leaf_source: SourceInfo,
    ) {
        assert_eq!(ty.source, outer_source);
        let TypeKind::Custom(Instance {
            name,
            lifetime_args: lifetimes,
            type_args: args,
        }) = &ty.kind
        else {
            panic!("expected custom type");
        };
        assert_eq!(name, "Wrap");
        assert_eq!(lifetimes, &[Lifetime("outer".into())]);
        let [arg] = args.as_slice() else {
            panic!("expected one custom type argument");
        };
        assert_eq!(arg.source, ref_source);
        let TypeKind::Ref(RefKind::Shared, lifetime, pointee) = &arg.kind else {
            panic!("expected shared reference argument");
        };
        assert_eq!(lifetime, &Some(Lifetime("inner".into())));
        assert_eq!(pointee.source, leaf_source);
        assert_eq!(pointee.kind, TypeKind::Int(IntTy::I64));
    }

    #[test]
    fn compatibility_probe_discards_successful_and_partial_bindings() {
        let mut subst = Subst::new();
        let variable = subst.fresh_var();

        assert!(subst.can_unify(&variable, &i64_ty()));
        assert_eq!(subst.resolve(&variable), variable);

        let expected = fn_ty(crate::common::Abi::Silica, vec![variable.clone(), bool_ty()], unit_ty());
        let found = fn_ty(crate::common::Abi::Silica, vec![i64_ty(), i64_ty()], unit_ty());
        assert!(!subst.can_unify(&expected, &found));
        assert_eq!(subst.resolve(&variable), variable);
    }

    #[test]
    fn substitution_preserves_lifetimes_and_sources() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let parameter_source = test_source(3);
        let argument_source = test_source(4);
        let declared = metadata_bearing_type(
            Type::new(TypeKind::Param("T".into()), parameter_source),
            outer_source,
            ref_source,
        );
        let argument = Type::new(TypeKind::Int(IntTy::I64), argument_source);
        let mapping = HashMap::from([("T".to_string(), argument)]);

        let substituted = substitute(&declared, &mapping);
        assert_metadata_preserved(&substituted, outer_source, ref_source, argument_source);
    }

    #[test]
    fn resolution_preserves_lifetimes_and_sources() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let variable_source = test_source(3);
        let resolved_source = test_source(4);
        let unresolved = metadata_bearing_type(
            Type::new(TypeKind::Var(0), variable_source),
            outer_source,
            ref_source,
        );
        let mut subst = Subst::new();
        subst
            .map
            .insert(0, Type::new(TypeKind::Int(IntTy::I64), resolved_source));

        let resolved = subst.resolve(&unresolved);
        assert_metadata_preserved(&resolved, outer_source, ref_source, resolved_source);
    }

    #[test]
    fn default_resolution_defaults_variables_without_dropping_container_metadata() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let variable_source = test_source(3);
        let intermediate_source = test_source(4);
        let defaulted_variable_source = test_source(5);
        let unresolved = metadata_bearing_type(
            Type::new(TypeKind::Var(0), variable_source),
            outer_source,
            ref_source,
        );
        let mut subst = Subst::new();
        subst.map.insert(
            0,
            Type::new(
                TypeKind::Ref(
                    RefKind::Shared,
                    None,
                    Box::new(Type::new(TypeKind::IntVar(1), defaulted_variable_source)),
                ),
                // This replacement intentionally adds another structural layer so
                // `resolve_default` must recurse through a resolved variable.
                intermediate_source,
            ),
        );

        let resolved = subst.resolve_default(&unresolved);
        assert_eq!(resolved.source, outer_source);
        let TypeKind::Custom(Instance {
            lifetime_args: outer_lifetimes,
            type_args: outer_args,
            ..
        }) = &resolved.kind
        else {
            panic!("expected custom type");
        };
        assert_eq!(outer_lifetimes, &[Lifetime("outer".into())]);
        let TypeKind::Ref(_, inner_lifetime, first_pointee) = &outer_args[0].kind else {
            panic!("expected original reference layer");
        };
        assert_eq!(outer_args[0].source, ref_source);
        assert_eq!(inner_lifetime, &Some(Lifetime("inner".into())));
        let TypeKind::Ref(_, None, second_pointee) = &first_pointee.kind else {
            panic!("expected resolved reference layer");
        };
        assert_eq!(first_pointee.source, intermediate_source);
        assert_eq!(second_pointee.kind, TypeKind::Int(IntTy::I64));
    }

    #[test]
    fn unify_mismatch_retains_structured_types_and_sources() {
        let expected_source = test_source(1);
        let found_source = test_source(2);
        let expected = Type::new(TypeKind::Bool, expected_source);
        let found = Type::new(TypeKind::Int(IntTy::I64), found_source);

        let error = Subst::new()
            .unify(&expected, &found)
            .expect_err("bool and i64 must not unify");
        let UnifyError::Mismatch {
            expected: retained_expected,
            found: retained_found,
        } = error
        else {
            panic!("expected a structured mismatch");
        };
        assert_eq!(retained_expected.kind, TypeKind::Bool);
        assert_eq!(retained_expected.source, expected_source);
        assert_eq!(retained_found.kind, TypeKind::Int(IntTy::I64));
        assert_eq!(retained_found.source, found_source);
    }

    #[test]
    fn numeric_unify_mismatch_retains_the_found_type() {
        let variable_source = test_source(1);
        let found_source = test_source(2);
        let integer_variable = Type::new(TypeKind::IntVar(0), variable_source);
        let found = Type::new(TypeKind::Bool, found_source);

        let error = Subst::new()
            .unify(&integer_variable, &found)
            .expect_err("an integer variable must not unify with bool");
        let UnifyError::ExpectedInteger { found: retained } = error else {
            panic!("expected an integer-category mismatch");
        };
        assert_eq!(retained.kind, TypeKind::Bool);
        assert_eq!(retained.source, found_source);
    }

    #[test]
    fn implicit_else_type_mismatch_preserves_generated_source() {
        let program = Parser::parse_or_panic("fn f() -> i64 { if true { 1 } }");

        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].code(),
            DiagCode::HllTypeCheck(HllTypeCheckCode::TypeMismatch)
        );
        assert_eq!(
            errors[0].source().generated_kind(),
            Some(GeneratedKind::HllDesugaring)
        );
    }

    #[test]
    fn ambiguous_generated_expression_preserves_its_source() {
        let mut program = Parser::parse_or_panic("fn f() { let x = []; }");
        let [Declaration::Fn(function)] = program.declarations.as_mut_slice() else {
            panic!("expected one function declaration");
        };
        let Some(body) = &mut function.body else {
            panic!("expected a function body");
        };
        let ExprKind::Block(statements, _, _) = &mut body.kind else {
            panic!("expected a block body");
        };
        let [Stmt::Let {
            init: Some(initializer),
            ..
        }] = statements.as_mut_slice()
        else {
            panic!("expected one initialized let statement");
        };
        let generated_source =
            SourceInfo::generated(GeneratedKind::HllDesugaring, initializer.source.span());
        initializer.source = generated_source;

        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].code(),
            DiagCode::HllTypeCheck(HllTypeCheckCode::AmbiguousType)
        );
        assert_eq!(errors[0].source(), generated_source);
    }

    fn check_program(source: &str) -> Result<(), String> {
        let mut parse_d = Diagnostics::default();
        let program = Parser::new(source)
            .parse(&mut parse_d)
            .ok_or_else(|| parse_d.errors_str().join("\n"))?;
        let d = typecheck_program(&program);
        if d.has_errors() {
            Err(d.errors_str().join("\n"))
        } else {
            Ok(())
        }
    }

    #[test]
    fn test_valid_program() {
        let source = "
            struct Point { x: i64, y: i64 }
            fn add(p: Point) -> i64 {
                let x = p.x;
                let y = p.y;
                x
            }
        ";
        assert!(check_program(source).is_ok());
    }

    #[test]
    fn test_type_mismatch() {
        let source = "
            fn check() -> i64 {
                true
            }
        ";
        let res = check_program(source);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("type mismatch"));
    }

    #[test]
    fn test_undeclared_variable() {
        let source = "
            fn check() -> i64 {
                let a = b;
                a
            }
        ";
        let res = check_program(source);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("undeclared variable"));
    }

    #[test]
    fn invalid_nested_declared_type_uses_its_own_source() {
        let source = "fn f(x: &Nope) {}";
        let program = Parser::parse_or_panic(source);
        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].span(),
            Span {
                line: 1,
                col: 10,
                end_line: 1,
                end_col: 14,
            }
        );
    }

    #[test]
    fn test_field_access_on_non_struct() {
        let source = "
            fn check(a: i64) -> i64 {
                return a.x;
            }
        ";
        let res = check_program(source);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("expected struct type"));
    }

    #[test]
    fn test_typecheck_constructors_and_arrays() {
        let source = "
            struct Point { x: i64, y: i64 }
            enum Option { None: (), Some: i64 }
            fn check(arr: [i64; 3]) -> i64 {
                let p = Point { x: 1, y: 2 };
                let o = Option::Some(42);
                let a = [1, 2, 3];
                let val = arr[0];
                val
            }
        ";
        let res = check_program(source);
        assert!(res.is_ok(), "Expected success, got: {:?}", res);
    }

    #[test]
    fn typecheck_call_through_fn_typed_param() {
        let source = "
            fn caller(f: fn(i64) -> i64) -> i64 {
                let x: i64 = f(42);
                x
            }
        ";
        assert!(check_program(source).is_ok(), "expected type-check success");
    }

    #[test]
    fn typecheck_fn_typed_param_return_type_mismatch_is_error() {
        let source = "
            fn caller(f: fn(i64) -> i64) -> bool {
                let b: bool = f(1);
                b
            }
        ";
        let res = check_program(source);
        assert!(res.is_err(), "expected type mismatch, got Ok");
        let err = res.unwrap_err();
        assert!(
            err.contains("type mismatch") || err.contains("expected"),
            "expected a type mismatch message, got: {}",
            err
        );
    }

    #[test]
    fn typecheck_fn_typed_param_arity_mismatch_is_error() {
        let source = "
            fn caller(f: fn(i64, bool) -> i64) -> i64 {
                f(1)
            }
        ";
        let res = check_program(source);
        assert!(res.is_err(), "expected arity error");
    }

    #[test]
    fn typecheck_binary_arithmetic_and_comparison() {
        let valid = "
            fn check(a: i64, b: i64) -> bool {
                let x = a + b * 2;
                x < 10
            }
        ";
        assert!(check_program(valid).is_ok());

        let invalid = "
            fn check(a: i64, b: bool) -> i64 {
                a + b
            }
        ";
        let res = check_program(invalid);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("type mismatch"));

        let invalid_bool_op = "
            fn check(a: bool, b: bool) -> bool {
                a == b
            }
        ";
        let res = check_program(invalid_bool_op);
        assert!(res.is_err());
        assert!(res.unwrap_err().contains("only supported on numeric types"));
    }

    #[test]
    fn test_defer_with_nested_loop_ok() {
        let source = "
            fn check() {
                defer {
                    loop {
                        break;
                    };
                };
            }
        ";
        assert!(check_program(source).is_ok());
    }
}
