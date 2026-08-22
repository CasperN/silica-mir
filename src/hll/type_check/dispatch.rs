use std::collections::{BTreeMap, HashMap};

use crate::common::{Abi, Lifetime, SourceInfo};
use crate::diagnostics::Diagnostics;
use crate::hll::ast::{
    impl_method_context, FnDecl, GenericArgs, ImplBlock, Instance, Type, TypeKind,
};
use crate::hll::helpers::*;
use crate::hll::type_check::env::{
    build_lifetime_mapping, build_subst_map, substitute_all, PendingInstantiation,
    ReceiverAdjustment, ResolvedMethodTarget, ResolvedReceiverCall, ResolvedReceiverTarget,
    TypeCheckResults, TypeEnv,
};
use crate::hll::type_check::mod_types::{source_diagnostic, HllTypeCheckCode};
use crate::hll::type_check::subst::Subst;
use crate::hll::type_check::traits::{
    impl_bindings, implied_trait_paths, match_impl_method_receiver, substitute_impl_instance,
    type_satisfies_trait_with_scope, ImplBindings,
};
use crate::hll::type_check::validation::{validate_trait_instance, validate_type};

pub(crate) fn instantiate_function(
    env: &TypeEnv,
    subst: &mut Subst,
    name: &str,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Instance)> {
    let signature = env.functions.get(name)?.clone();

    if !generics.lifetimes.is_empty()
        && generics.lifetimes.len() != signature.lifetime_params.len()
    {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::LifetimeArgArityMismatch,
            source,
            format!(
                "function '{}' takes {} lifetime argument(s), found {}",
                name,
                signature.lifetime_params.len(),
                generics.lifetimes.len()
            ),
        ));
        return None;
    }
    for lifetime in &generics.lifetimes {
        if !env.current_lifetimes.contains(lifetime) {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredLifetime,
                source,
                format!("undeclared lifetime {}", lifetime),
            ));
        }
    }

    let type_args = if generics.types.is_empty() {
        signature
            .type_params
            .iter()
            .map(|_| subst.fresh_var())
            .collect::<Vec<_>>()
    } else {
        if generics.types.len() != signature.type_params.len() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::TypeArgArityMismatch,
                source,
                format!(
                    "function '{}' takes {} type argument(s), found {}",
                    name,
                    signature.type_params.len(),
                    generics.types.len()
                ),
            ));
            return None;
        }
        for argument in &generics.types {
            validate_type(env, argument, &env.current_type_params, d);
        }
        generics.types.clone()
    };

    let mapping: HashMap<String, Type> = signature
        .type_params
        .iter()
        .map(|parameter| &parameter.name)
        .cloned()
        .zip(type_args.iter().cloned())
        .collect();
    let lifetime_args = if generics.lifetimes.is_empty() {
        signature
            .lifetime_params
            .iter()
            .map(|_| types.fresh_inferred_lifetime(env, subst, source))
            .collect::<Option<Vec<_>>>()?
    } else {
        generics.lifetimes.clone()
    };
    let lifetime_mapping = signature
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(lifetime_args.iter().cloned())
        .collect();
    let params = signature
        .params
        .iter()
        .map(|parameter| substitute_all(&parameter.ty, &mapping, &lifetime_mapping))
        .collect();
    let ret = substitute_all(&signature.ret_ty, &mapping, &lifetime_mapping);

    let instance = Instance::new(name.to_string(), lifetime_args, type_args.clone());
    types.pending_instantiations.push(PendingInstantiation {
        source,
        function_name: name.to_string(),
        caller_type_params: env.current_type_params.clone(),
        type_params: signature.type_params,
        type_args,
        type_mapping: mapping,
        lifetime_mapping,
    });
    Some((fn_ty(signature.abi, params, ret), instance))
}

pub(crate) fn receiver_adjustment_for_fn(
    subst: &Subst,
    function_ty: &Type,
    receiver_ty: &Type,
) -> ReceiverAdjustment {
    let TypeKind::Fn { params, ret: _, .. } = &subst.resolve(function_ty).kind else {
        return ReceiverAdjustment::None;
    };
    let Some(receiver_param) = params.first() else {
        return ReceiverAdjustment::None;
    };
    if subst.can_unify(receiver_param, receiver_ty) {
        return ReceiverAdjustment::None;
    }
    let TypeKind::Ref(kind, _, pointee) = &receiver_param.kind else {
        return ReceiverAdjustment::None;
    };
    if subst.can_unify(pointee, receiver_ty) {
        ReceiverAdjustment::Borrow(*kind)
    } else {
        ReceiverAdjustment::None
    }
}

pub(crate) fn receiver_adjustment_for_expected(
    subst: &Subst,
    expected: &Type,
    actual: &Type,
) -> Option<ReceiverAdjustment> {
    if subst.can_unify(expected, actual) {
        return Some(ReceiverAdjustment::None);
    }
    let TypeKind::Ref(kind, _, pointee) = &expected.kind else {
        return None;
    };
    subst
        .can_unify(pointee, actual)
        .then_some(ReceiverAdjustment::Borrow(*kind))
}

enum TraitReceiverCandidate<'a> {
    Bound {
        trait_path: Instance,
        self_ty: Type,
        method: &'a FnDecl,
        mapping: HashMap<String, Type>,
        lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
        adjustment: ReceiverAdjustment,
    },
    Impl {
        impl_block: &'a ImplBlock,
        method: &'a FnDecl,
        trait_path: Instance,
        self_ty: Type,
        bindings: ImplBindings,
        adjustment: ReceiverAdjustment,
        is_unsafe: bool,
    },
}

impl TraitReceiverCandidate<'_> {
    fn adjustment(&self) -> ReceiverAdjustment {
        match self {
            Self::Bound { adjustment, .. } | Self::Impl { adjustment, .. } => *adjustment,
        }
    }

    fn identity(&self) -> (&Instance, &Type, &str) {
        match self {
            Self::Bound {
                trait_path,
                self_ty,
                method,
                ..
            }
            | Self::Impl {
                trait_path,
                self_ty,
                method,
                ..
            } => (trait_path, self_ty, &method.name),
        }
    }

    fn context(&self) -> String {
        match self {
            Self::Bound {
                trait_path,
                self_ty,
                method,
                ..
            } => impl_method_context(self_ty, Some(trait_path), &method.name),
            Self::Impl {
                impl_block,
                trait_path,
                method,
                ..
            } => impl_method_context(&impl_block.target, Some(trait_path), &method.name),
        }
    }
}

pub(crate) fn instantiate_method(
    env: &TypeEnv,
    subst: &mut Subst,
    impl_block: &ImplBlock,
    bindings: &ImplBindings,
    method: &FnDecl,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Instance)> {
    let mapping = bindings
        .types
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect::<HashMap<_, _>>();
    if !impl_block.type_params.is_empty() {
        let impl_type_args = impl_block
            .type_params
            .iter()
            .map(|tp| {
                bindings
                    .types
                    .get(&tp.name)
                    .cloned()
                    .unwrap_or_else(|| Type::synthesized(TypeKind::Error))
            })
            .collect::<Vec<_>>();
        types.pending_instantiations.push(PendingInstantiation {
            source,
            function_name: format!("<{}>", impl_block.target),
            caller_type_params: env.current_type_params.clone(),
            type_params: impl_block.type_params.clone(),
            type_args: impl_type_args,
            type_mapping: mapping.clone(),
            lifetime_mapping: bindings.lifetimes.clone(),
        });
    }
    instantiate_method_signature(
        env,
        subst,
        method,
        mapping,
        bindings.lifetimes.clone(),
        generics,
        source,
        types,
        d,
    )
}

pub(crate) fn instantiate_method_signature(
    env: &TypeEnv,
    subst: &mut Subst,
    method: &FnDecl,
    mut mapping: HashMap<String, Type>,
    mut lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Instance)> {
    if !generics.lifetimes.is_empty() && generics.lifetimes.len() != method.lifetime_params.len() {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::LifetimeArgArityMismatch,
            source,
            format!(
                "method '{}' takes {} lifetime argument(s), found {}",
                method.name,
                method.lifetime_params.len(),
                generics.lifetimes.len()
            ),
        ));
        return None;
    }
    for lifetime in &generics.lifetimes {
        if !env.current_lifetimes.contains(lifetime) {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredLifetime,
                source,
                format!("undeclared lifetime {}", lifetime),
            ));
        }
    }
    let method_type_args = if generics.types.is_empty() {
        method
            .type_params
            .iter()
            .map(|_| subst.fresh_var())
            .collect::<Vec<_>>()
    } else {
        if generics.types.len() != method.type_params.len() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::TypeArgArityMismatch,
                source,
                format!(
                    "method '{}' takes {} type argument(s), found {}",
                    method.name,
                    method.type_params.len(),
                    generics.types.len()
                ),
            ));
            return None;
        }
        for argument in &generics.types {
            validate_type(env, argument, &env.current_type_params, d);
        }
        generics.types.clone()
    };
    mapping.extend(
        method
            .type_params
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(method_type_args.iter().cloned()),
    );
    let method_lifetime_args = if generics.lifetimes.is_empty() {
        method
            .lifetime_params
            .iter()
            .map(|_| types.fresh_inferred_lifetime(env, subst, source))
            .collect::<Option<Vec<_>>>()?
    } else {
        generics.lifetimes.clone()
    };
    lifetime_mapping.extend(
        method
            .lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(method_lifetime_args.iter().cloned()),
    );
    let params = method
        .params
        .iter()
        .map(|parameter| substitute_all(&parameter.ty, &mapping, &lifetime_mapping))
        .collect();
    let ret = substitute_all(&method.ret_ty, &mapping, &lifetime_mapping);
    types.pending_instantiations.push(PendingInstantiation {
        source,
        function_name: method.name.clone(),
        caller_type_params: env.current_type_params.clone(),
        type_params: method.type_params.clone(),
        type_args: method_type_args.clone(),
        type_mapping: mapping,
        lifetime_mapping,
    });
    Some((
        fn_ty(method.abi, params, ret),
        Instance::new(method.name.clone(), method_lifetime_args, method_type_args),
    ))
}

pub(crate) fn resolve_field_access(
    env: &TypeEnv,
    subst: &mut Subst,
    target_ty: &Type,
    target_source: SourceInfo,
    field: &str,
    source: SourceInfo,
    d: &mut Diagnostics,
) -> Type {
    let resolved = subst.resolve(target_ty);
    if resolved.kind == TypeKind::Error {
        return error_ty();
    }
    let struct_ty = match &resolved.kind {
        TypeKind::Ref(_, _, inner) => subst.resolve(inner),
        _ => resolved.clone(),
    };
    if let TypeKind::Tuple(elems) = &struct_ty.kind {
        if let Ok(idx) = field.parse::<usize>() {
            if idx < elems.len() {
                return elems[idx].clone();
            } else {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::NoSuchField,
                    target_source,
                    format!("tuple of length {} has no field '{}'", elems.len(), field),
                ));
                return error_ty();
            }
        } else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::NoSuchField,
                target_source,
                format!("tuple type {} has no field '{}'", struct_ty, field),
            ));
            return error_ty();
        }
    }
    if let TypeKind::Custom(Instance {
        name: struct_name,
        lifetime_args,
        type_args: args,
    }) = &struct_ty.kind
    {
        if let Some(s_decl) = env.structs.get(struct_name).cloned() {
            if let Some(field_decl) = s_decl.fields.iter().find(|decl| decl.name == field) {
                let Some(mapping) =
                    build_subst_map(struct_name, &s_decl.type_params, args, source, d)
                else {
                    return error_ty();
                };
                let Some(lifetime_mapping) =
                    build_lifetime_mapping(&s_decl.lifetime_params, lifetime_args)
                else {
                    return error_ty();
                };
                substitute_all(&field_decl.ty, &mapping, &lifetime_mapping)
            } else {
                let mut diag = source_diagnostic(
                    HllTypeCheckCode::NoSuchField,
                    target_source,
                    format!("struct '{}' has no field '{}'", struct_name, field),
                );
                if let Some(suggestion) =
                    crate::diagnostics::find_best_match(field, s_decl.fields.iter().map(|f| &f.name))
                {
                    diag = diag.with_hint(format!("a field with a similar name exists: '{}'", suggestion));
                }
                d.push_error(diag);
                error_ty()
            }
        } else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredStruct,
                target_source,
                format!("undeclared struct '{}'", struct_name),
            ));
            error_ty()
        }
    } else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ExpectedStruct,
            target_source,
            format!("expected struct type, found {}", resolved),
        ));
        error_ty()
    }
}

pub(crate) fn receiver_field_type(
    env: &TypeEnv,
    subst: &Subst,
    receiver_ty: &Type,
    field: &str,
) -> Option<Type> {
    let resolved = subst.resolve(receiver_ty);
    let struct_ty = match &resolved.kind {
        TypeKind::Ref(_, _, inner) => subst.resolve(inner),
        _ => resolved,
    };
    if let TypeKind::Tuple(elems) = &struct_ty.kind {
        let idx = field.parse::<usize>().ok()?;
        return elems.get(idx).cloned();
    }
    let TypeKind::Custom(Instance {
        name,
        lifetime_args,
        type_args: args,
    }) = &struct_ty.kind
    else {
        return None;
    };
    let s_decl = env.structs.get(name)?;
    let field_decl = s_decl.fields.iter().find(|decl| decl.name == field)?;
    let mapping = s_decl
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(args.iter().cloned())
        .collect::<HashMap<_, _>>();
    let lifetime_mapping = s_decl
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(lifetime_args.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    Some(substitute_all(
        &field_decl.ty,
        &mapping,
        &lifetime_mapping,
    ))
}

pub(crate) fn resolve_qualified_call(
    env: &TypeEnv,
    subst: &mut Subst,
    self_ty: &Type,
    trait_path: Option<&Instance>,
    method_name: &str,
    generics: &GenericArgs,
    method_source: SourceInfo,
    selector_source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<Type> {
    let errors_before = d.error_count();
    validate_type(env, self_ty, &env.current_type_params, d);
    let self_ty = subst.resolve(self_ty);

    let (fn_ty, target) = if let Some(trait_path) = trait_path {
        for lifetime in &trait_path.lifetime_args {
            if !env.current_lifetimes.contains(lifetime) {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UndeclaredLifetime,
                    selector_source,
                    format!("undeclared lifetime {}", lifetime),
                ));
            }
        }
        validate_trait_instance(
            env,
            "qualified method",
            "trait",
            trait_path,
            selector_source,
            &env.current_type_params,
            d,
        );
        if d.error_count() != errors_before {
            return None;
        }
        let trait_decl = env.traits.get(&trait_path.name)?;
        let Some(method) = trait_decl
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)
        else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnresolvedQualifiedMethod,
                method_source,
                format!("trait '{}' has no method '{}'", trait_path, method_name),
            ));
            return None;
        };
        if !type_satisfies_trait_with_scope(env, &self_ty, trait_path, &env.current_type_params) {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::BoundNotSatisfied,
                selector_source,
                format!(
                    "type '{}' does not satisfy trait '{}' required by qualified method",
                    self_ty, trait_path
                ),
            ));
            return None;
        }
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe trait method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let mut mapping = trait_decl
            .type_params
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(trait_path.type_args.iter().cloned())
            .collect::<HashMap<_, _>>();
        mapping.insert("Self".to_string(), self_ty.clone());
        let lifetime_mapping = trait_decl
            .lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(trait_path.lifetime_args.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let (fn_ty, method) = instantiate_method_signature(
            env,
            subst,
            method,
            mapping,
            lifetime_mapping,
            generics,
            method_source,
            types,
            d,
        )?;
        (
            fn_ty,
            ResolvedMethodTarget::Trait {
                trait_path: trait_path.clone(),
                self_ty,
                method,
            },
        )
    } else {
        if d.error_count() != errors_before {
            return None;
        }
        let candidates = env
            .impls
            .iter()
            .filter(|impl_block| impl_block.trait_path.is_none())
            .filter_map(|impl_block| {
                let bindings = impl_bindings(impl_block, &self_ty, env)?;
                let method = impl_block
                    .methods
                    .iter()
                    .find(|candidate| candidate.name == method_name)?;
                Some((impl_block, method, bindings))
            })
            .collect::<Vec<_>>();
        if candidates.len() > 1 {
            let candidates = candidates
                .iter()
                .map(|(impl_block, method, _)| {
                    impl_method_context(&impl_block.target, None, &method.name)
                })
                .collect::<Vec<_>>()
                .join(", ");
            d.push_error(source_diagnostic(
                HllTypeCheckCode::AmbiguousReceiverCall,
                method_source,
                format!(
                    "qualified call '<{}>::{}' is ambiguous; inherent candidates: {}",
                    self_ty, method_name, candidates
                ),
            ));
            return None;
        }
        let Some((impl_block, method, bindings)) = candidates.into_iter().next() else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnresolvedQualifiedMethod,
                method_source,
                format!(
                    "type '{}' has no inherent method '{}'",
                    self_ty, method_name
                ),
            ));
            return None;
        };
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, method) = instantiate_method(
            env,
            subst,
            impl_block,
            &bindings,
            method,
            generics,
            method_source,
            types,
            d,
        )?;
        (fn_ty, ResolvedMethodTarget::Inherent { self_ty, method })
    };
    types.qualified_calls.insert(selector_source, target);
    Some(fn_ty)
}

pub(crate) fn resolve_path_call(
    env: &TypeEnv,
    subst: &mut Subst,
    target_ty: &Type,
    member_name: &str,
    generics: &GenericArgs,
    member_source: SourceInfo,
    selector_source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<Type> {
    let errors_before = d.error_count();
    let target_ty = subst.resolve(target_ty);

    // 1. Check for Enum variant constructor
    if let TypeKind::Custom(instance) = &target_ty.kind {
        if let Some(enum_decl) = env.enums.get(&instance.name).cloned() {
            if let Some(variant) = enum_decl.variants.iter().find(|v| v.name == member_name).cloned() {
                // Check if an inherent method with the same name collides on this enum
                let inherent_collision = env
                    .impls
                    .iter()
                    .filter(|impl_block| impl_block.trait_path.is_none())
                    .any(|impl_block| {
                        impl_bindings(impl_block, &target_ty, env).is_some()
                            && impl_block.methods.iter().any(|m| m.name == member_name)
                    });
                if inherent_collision {
                    d.push_error(source_diagnostic(
                        HllTypeCheckCode::AmbiguousReceiverCall,
                        member_source,
                        format!(
                            "scoped path '{}::{}' is ambiguous between enum variant and inherent method; use '<{}>::{}' to select the method",
                            target_ty, member_name, target_ty, member_name
                        ),
                    ));
                    return None;
                }

                let type_args: Vec<Type> = if instance.type_args.is_empty() {
                    enum_decl.type_params.iter().map(|_| subst.fresh_var()).collect()
                } else {
                    if instance.type_args.len() != enum_decl.type_params.len() {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::TypeArgArityMismatch,
                            selector_source,
                            format!(
                                "enum '{}' takes {} type arguments, found {}",
                                instance.name,
                                enum_decl.type_params.len(),
                                instance.type_args.len()
                            ),
                        ));
                        return None;
                    }
                    instance.type_args.clone()
                };
                let lifetime_args: Vec<Lifetime> = if instance.lifetime_args.is_empty() {
                    enum_decl
                        .lifetime_params
                        .iter()
                        .map(|_| {
                            types
                                .fresh_inferred_lifetime(env, subst, selector_source)
                                .expect("constructor expression outside a function body")
                        })
                        .collect()
                } else {
                    instance.lifetime_args.clone()
                };

                let mapping: HashMap<String, Type> = enum_decl
                    .type_params
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .zip(type_args.iter().cloned())
                    .collect();
                let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = enum_decl
                    .lifetime_params
                    .iter()
                    .map(|parameter| parameter.lifetime.clone())
                    .zip(lifetime_args.iter().cloned())
                    .collect();
                let payload_ty = substitute_all(&variant.ty, &mapping, &lifetime_mapping);
                let enum_instance = Instance::new(
                    instance.name.clone(),
                    lifetime_args.clone(),
                    type_args.clone(),
                );
                let ret_ty = Type::synthesized(TypeKind::Custom(enum_instance.clone()));
                let params = vec![payload_ty];
                let fn_ty = fn_ty(Abi::Silica, params, ret_ty);
                types.qualified_calls.insert(
                    selector_source,
                    ResolvedMethodTarget::EnumConstructor {
                        enum_instance,
                        variant_name: member_name.to_string(),
                    },
                );
                return Some(fn_ty);
            } else {
                let has_inherent_method = env
                    .impls
                    .iter()
                    .filter(|impl_block| impl_block.trait_path.is_none())
                    .any(|impl_block| {
                        impl_bindings(impl_block, &target_ty, env).is_some()
                            && impl_block.methods.iter().any(|m| m.name == member_name)
                    });
                if !has_inherent_method {
                    let mut diag = source_diagnostic(
                        HllTypeCheckCode::NoSuchVariant,
                        member_source,
                        format!("enum '{}' has no variant '{}'", instance.name, member_name),
                    );
                    if let Some(suggestion) = crate::diagnostics::find_best_match(
                        member_name,
                        enum_decl.variants.iter().map(|v| &v.name),
                    ) {
                        diag = diag.with_hint(format!(
                            "a variant with a similar name exists: '{}'",
                            suggestion
                        ));
                    }
                    d.push_error(diag);
                    return None;
                }
            }
        }
    }

    // 2. Expand unspecialized nominal type args if target_ty is a struct
    let resolved_target = if let TypeKind::Custom(instance) = &target_ty.kind {
        if let Some(struct_decl) = env.structs.get(&instance.name) {
            let type_args: Vec<Type> = if instance.type_args.is_empty() {
                struct_decl.type_params.iter().map(|_| subst.fresh_var()).collect()
            } else {
                instance.type_args.clone()
            };
            let lifetime_args: Vec<Lifetime> = if instance.lifetime_args.is_empty() {
                struct_decl
                    .lifetime_params
                    .iter()
                    .map(|_| {
                        types
                            .fresh_inferred_lifetime(env, subst, selector_source)
                            .expect("static method call outside a function body")
                    })
                    .collect()
            } else {
                instance.lifetime_args.clone()
            };
            Type::new(
                TypeKind::Custom(Instance::new(instance.name.clone(), lifetime_args, type_args)),
                target_ty.source,
            )
        } else {
            target_ty.clone()
        }
    } else {
        target_ty.clone()
    };

    // 3. Try Inherent / Trait Static Method via resolve_qualified_call
    if let Some(fn_ty) = resolve_qualified_call(
        env,
        subst,
        &resolved_target,
        None,
        member_name,
        generics,
        member_source,
        selector_source,
        types,
        d,
    ) {
        return Some(fn_ty);
    }

    if d.error_count() != errors_before {
        return None;
    }

    // 4. Report error
    if let TypeKind::Custom(instance) = &target_ty.kind {
        if let Some(e_decl) = env.enums.get(&instance.name) {
            let mut diag = source_diagnostic(
                HllTypeCheckCode::NoSuchVariant,
                member_source,
                format!("enum '{}' has no variant '{}'", instance.name, member_name),
            );
            if let Some(suggestion) =
                crate::diagnostics::find_best_match(member_name, e_decl.variants.iter().map(|v| &v.name))
            {
                diag = diag.with_hint(format!("a variant with a similar name exists: '{}'", suggestion));
            }
            d.push_error(diag);
        } else if let Some(s_decl) = env.structs.get(&instance.name) {
            let mut diag = source_diagnostic(
                HllTypeCheckCode::UnresolvedQualifiedMethod,
                member_source,
                format!("type '{}' has no inherent method '{}'", instance.name, member_name),
            );
            let inherent_methods: Vec<&String> = env
                .impls
                .iter()
                .filter(|ib| {
                    ib.trait_path.is_none()
                        && matches!(&ib.target.kind, TypeKind::Custom(i) if i.name == s_decl.name)
                })
                .flat_map(|ib| ib.methods.iter().map(|m| &m.name))
                .collect();
            if let Some(suggestion) =
                crate::diagnostics::find_best_match(member_name, inherent_methods)
            {
                diag = diag.with_hint(format!("a method with a similar name exists: '{}'", suggestion));
            }
            d.push_error(diag);
        } else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredType,
                selector_source,
                format!("undeclared type '{}'", instance.name),
            ));
        }
    } else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::UnresolvedQualifiedMethod,
            member_source,
            format!("type '{}' has no inherent method '{}'", target_ty, member_name),
        ));
    }
    None
}

pub(crate) fn resolve_receiver_call(
    env: &mut TypeEnv,
    subst: &mut Subst,
    receiver_ty: &Type,
    method_name: &str,
    generics: &GenericArgs,
    method_source: SourceInfo,
    selector_source: SourceInfo,
    call_source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Option<Type>)> {
    let resolved_receiver_ty = subst.resolve(receiver_ty);
    if resolved_receiver_ty.kind == TypeKind::Error {
        return None;
    }

    let inherent = env
        .impls
        .iter()
        .filter(|impl_block| impl_block.trait_path.is_none())
        .filter_map(|impl_block| {
            let method = impl_block
                .methods
                .iter()
                .find(|candidate| candidate.name == method_name)?;
            let (self_ty, bindings, adjustment) =
                match_impl_method_receiver(impl_block, method, &resolved_receiver_ty, env)?;
            Some((impl_block, method, self_ty, bindings, adjustment))
        })
        .collect::<Vec<_>>();
    let has_exact_inherent = inherent
        .iter()
        .any(|(_, _, _, _, adjustment)| *adjustment == ReceiverAdjustment::None);
    let inherent = inherent
        .into_iter()
        .filter(|(_, _, _, _, adjustment)| {
            !has_exact_inherent || *adjustment == ReceiverAdjustment::None
        })
        .collect::<Vec<_>>();
    if inherent.len() > 1 {
        let candidates = inherent
            .iter()
            .map(|(impl_block, method, _, _, _)| {
                impl_method_context(&impl_block.target, None, &method.name)
            })
            .collect::<Vec<_>>()
            .join(", ");
        d.push_error(source_diagnostic(
            HllTypeCheckCode::AmbiguousReceiverCall,
            method_source,
            format!(
                "receiver call '{}.{}' is ambiguous; inherent candidates: {}",
                resolved_receiver_ty, method_name, candidates
            ),
        ));
        return None;
    }
    if let Some((impl_block, method, self_ty, bindings, adjustment)) = inherent.into_iter().next() {
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, method_instance) = instantiate_method(
            env,
            subst,
            &impl_block,
            &bindings,
            &method,
            generics,
            method_source,
            types,
            d,
        )?;
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Method(ResolvedMethodTarget::Inherent {
                    self_ty,
                    method: method_instance,
                }),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    let bound_self_ty = match &resolved_receiver_ty.kind {
        TypeKind::Param(name) if env.current_type_params.contains_key(name) => {
            Some(resolved_receiver_ty.clone())
        }
        TypeKind::Ref(_, _, pointee) => {
            let pointee = subst.resolve(pointee);
            matches!(&pointee.kind, TypeKind::Param(name) if env.current_type_params.contains_key(name))
                .then_some(pointee)
        }
        _ => None,
    };
    let mut trait_methods = Vec::new();
    let mut seen_bound_methods = Vec::new();
    if let Some(self_ty) = bound_self_ty {
        if let TypeKind::Param(parameter_name) = &self_ty.kind {
            if let Some(bounds) = env.current_type_params.get(parameter_name) {
                for bound in &bounds.traits {
                    for trait_path in implied_trait_paths(env, &bound.trait_path, &self_ty) {
                        let Some(trait_decl) = env.traits.get(&trait_path.name) else {
                            continue;
                        };
                        let Some(method) = trait_decl
                            .methods
                            .iter()
                            .find(|candidate| candidate.name == method_name)
                        else {
                            continue;
                        };
                        if seen_bound_methods.contains(&(trait_path.clone(), self_ty.clone())) {
                            continue;
                        }
                        let mut mapping = trait_decl
                            .type_params
                            .iter()
                            .map(|parameter| parameter.name.clone())
                            .zip(trait_path.type_args.iter().cloned())
                            .collect::<HashMap<_, _>>();
                        mapping.insert("Self".to_string(), self_ty.clone());
                        let lifetime_mapping = trait_decl
                            .lifetime_params
                            .iter()
                            .map(|parameter| parameter.lifetime.clone())
                            .zip(trait_path.lifetime_args.iter().cloned())
                            .collect::<BTreeMap<_, _>>();
                        let Some(receiver_param) = method.params.first() else {
                            continue;
                        };
                        let expected_receiver =
                            substitute_all(&receiver_param.ty, &mapping, &lifetime_mapping);
                        let Some(adjustment) = receiver_adjustment_for_expected(
                            subst,
                            &expected_receiver,
                            &resolved_receiver_ty,
                        ) else {
                            continue;
                        };
                        seen_bound_methods.push((trait_path.clone(), self_ty.clone()));
                        trait_methods.push(TraitReceiverCandidate::Bound {
                            trait_path,
                            self_ty: self_ty.clone(),
                            method,
                            mapping,
                            lifetime_mapping,
                            adjustment,
                        });
                    }
                }
            }
        }
    }
    let bound_method_count = trait_methods.len();
    let impl_methods = env.impls.iter().filter_map(|impl_block| {
        let trait_path = impl_block.trait_path.as_ref()?;
        let trait_method = env
            .traits
            .get(&trait_path.name)?
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)?;
        let method = impl_block
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)?;
        let (self_ty, bindings, adjustment) =
            match_impl_method_receiver(impl_block, method, &resolved_receiver_ty, env)?;
        let trait_path = substitute_impl_instance(trait_path, &bindings);
        Some(TraitReceiverCandidate::Impl {
            impl_block,
            method,
            trait_path,
            self_ty,
            bindings,
            adjustment,
            is_unsafe: trait_method.is_unsafe,
        })
    });
    for candidate in impl_methods {
        let (candidate_trait, candidate_self, candidate_method) = candidate.identity();
        let duplicates_bound = trait_methods[..bound_method_count].iter().any(|bound| {
            let (bound_trait, bound_self, bound_method) = bound.identity();
            bound_trait == candidate_trait
                && bound_self == candidate_self
                && bound_method == candidate_method
        });
        if !duplicates_bound {
            trait_methods.push(candidate);
        }
    }
    let has_exact_trait = trait_methods
        .iter()
        .any(|candidate| candidate.adjustment() == ReceiverAdjustment::None);
    let trait_methods = trait_methods
        .into_iter()
        .filter(|candidate| !has_exact_trait || candidate.adjustment() == ReceiverAdjustment::None)
        .collect::<Vec<_>>();
    if trait_methods.len() > 1 {
        let only_direct_bounds = trait_methods
            .iter()
            .all(|candidate| matches!(candidate, TraitReceiverCandidate::Bound { .. }));
        let ambiguity_receiver = if only_direct_bounds {
            trait_methods[0].identity().1
        } else {
            &resolved_receiver_ty
        };
        let candidates = trait_methods
            .iter()
            .map(TraitReceiverCandidate::context)
            .collect::<Vec<_>>()
            .join(", ");
        d.push_error(source_diagnostic(
            HllTypeCheckCode::AmbiguousReceiverCall,
            method_source,
            format!(
                "receiver call '{}.{}' is ambiguous; trait candidates: {}",
                ambiguity_receiver, method_name, candidates
            ),
        ));
        return None;
    }
    if let Some(candidate) = trait_methods.into_iter().next() {
        let is_unsafe = match &candidate {
            TraitReceiverCandidate::Bound { method, .. } => method.is_unsafe,
            TraitReceiverCandidate::Impl { is_unsafe, .. } => *is_unsafe,
        };
        if is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe trait method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (trait_path, self_ty, adjustment, fn_ty, method_instance) = match candidate {
            TraitReceiverCandidate::Bound {
                trait_path,
                self_ty,
                method,
                mapping,
                lifetime_mapping,
                adjustment,
            } => {
                let (fn_ty, method_instance) = instantiate_method_signature(
                    env,
                    subst,
                    method,
                    mapping,
                    lifetime_mapping,
                    generics,
                    method_source,
                    types,
                    d,
                )?;
                (trait_path, self_ty, adjustment, fn_ty, method_instance)
            }
            TraitReceiverCandidate::Impl {
                impl_block,
                method,
                trait_path,
                self_ty,
                bindings,
                adjustment,
                ..
            } => {
                let (fn_ty, method_instance) = instantiate_method(
                    env,
                    subst,
                    impl_block,
                    &bindings,
                    method,
                    generics,
                    method_source,
                    types,
                    d,
                )?;
                (trait_path, self_ty, adjustment, fn_ty, method_instance)
            }
        };
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Method(ResolvedMethodTarget::Trait {
                    trait_path,
                    self_ty,
                    method: method_instance,
                }),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    let field_ty = receiver_field_type(env, subst, receiver_ty, method_name);
    let callable_field = matches!(
        field_ty.as_ref().map(|ty| &ty.kind),
        Some(TypeKind::Fn { .. })
    );
    if callable_field && generics.is_empty() {
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Field,
                adjustment: ReceiverAdjustment::None,
            },
        );
        return field_ty.map(|field_ty| (field_ty, None));
    }

    if env.functions.contains_key(method_name) {
        if env
            .functions
            .get(method_name)
            .is_some_and(|function| function.is_unsafe)
            && !env.in_unsafe
        {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe function '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, instance) =
            instantiate_function(env, subst, method_name, generics, method_source, types, d)?;
        let adjustment = receiver_adjustment_for_fn(subst, &fn_ty, receiver_ty);
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::FreeFunction(instance),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    if callable_field {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::GenericArgsOnFunctionValue,
            method_source,
            "explicit generic arguments require a named function",
        ));
    } else if let Some(field_ty) = field_ty {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ExpectedFunction,
            call_source,
            format!("expected function type, found {}", field_ty),
        ));
    } else {
        let mut diag = source_diagnostic(
            HllTypeCheckCode::UnresolvedReceiverCall,
            method_source,
            format!(
                "no method, callable field, or free function '{}' applies to receiver type {}",
                method_name, resolved_receiver_ty
            ),
        );
        let mut trait_candidates = Vec::new();
        for trait_decl in env.traits.values() {
            if trait_decl.methods.iter().any(|m| m.name == method_name) {
                trait_candidates.push(trait_decl.name.clone());
            }
        }
        if !trait_candidates.is_empty() {
            diag = diag.with_hint(format!(
                "the method '{}' exists on trait '{}', but '{}' does not implement it",
                method_name,
                trait_candidates.join(", "),
                resolved_receiver_ty
            ));
        } else {
            let all_methods: Vec<&String> =
                env.impls.iter().flat_map(|ib| ib.methods.iter().map(|m| &m.name)).collect();
            if let Some(suggestion) = crate::diagnostics::find_best_match(method_name, all_methods) {
                diag = diag.with_hint(format!("a method with a similar name exists: '{}'", suggestion));
            }
        }
        d.push_error(diag);
    }
    None
}
