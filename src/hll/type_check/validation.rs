use std::collections::{BTreeMap, HashMap, HashSet};

use crate::common::{Abi, Linkage, Marker, SourceInfo};
use crate::diagnostics::Diagnostics;
use crate::hll::ast::{
    impl_method_context, Bounds, Declaration, FnDecl, Instance, Program, Type, TypeKind, TypeParam,
};
use crate::hll::type_check::env::{substitute_bound, type_params_scope, TypeCheckResults, TypeEnv};
use crate::hll::type_check::mod_types::{source_diagnostic, HllTypeCheckCode};
use crate::hll::type_check::subst::Subst;
use crate::hll::type_check::traits;

/// Explain why a type argument failed to satisfy a marker bound.
pub(crate) fn explain_marker_failure(
    env: &TypeEnv,
    arg: &Type,
    marker: Marker,
    scope: &HashMap<String, Bounds>,
) -> Option<String> {
    match &arg.kind {
        TypeKind::Param(name) => {
            Some(format!("consider restricting type parameter '{}: {:?}'", name, marker))
        }
        TypeKind::Custom(instance) => {
            if let Some(s_decl) = env.structs.get(&instance.name) {
                if !s_decl.markers.declared(marker) {
                    for field in &s_decl.fields {
                        if !traits::class_of(env, &field.ty, scope).implies(marker) {
                            return Some(format!(
                                "struct '{}' cannot satisfy bound '{:?}' because field '{}' of type '{}' does not satisfy '{:?}'",
                                instance.name, marker, field.name, field.ty, marker
                            ));
                        }
                    }
                }
            } else if let Some(e_decl) = env.enums.get(&instance.name) {
                if !e_decl.markers.declared(marker) {
                    for variant in &e_decl.variants {
                        if !traits::class_of(env, &variant.ty, scope).implies(marker) {
                            return Some(format!(
                                "enum '{}' cannot satisfy bound '{:?}' because variant '{}' with payload '{}' does not satisfy '{:?}'",
                                instance.name, marker, variant.name, variant.ty, marker
                            ));
                        }
                    }
                }
            }
            None
        }
        TypeKind::Tuple(elems) => {
            for (idx, elem) in elems.iter().enumerate() {
                if !traits::class_of(env, elem, scope).implies(marker) {
                    return Some(format!(
                        "tuple element {} of type '{}' does not satisfy bound '{:?}'",
                        idx, elem, marker
                    ));
                }
            }
            None
        }
        _ => None,
    }
}

/// Explain why a type argument failed to satisfy a trait bound.
pub(crate) fn explain_trait_failure(
    env: &TypeEnv,
    arg: &Type,
    bound: &Instance,
    scope: &HashMap<String, Bounds>,
) -> Option<String> {
    let trait_name = &bound.name;
    match &arg.kind {
        TypeKind::Param(name) => {
            Some(format!("consider restricting type parameter '{}: {}'", name, bound))
        }
        TypeKind::Custom(instance) => {
            if trait_name == "AutoClone" || trait_name == "AutoDestroy" {
                if let Some(s_decl) = env.structs.get(&instance.name) {
                    for field in &s_decl.fields {
                        if !traits::type_satisfies_trait_with_scope(env, &field.ty, bound, scope) {
                            return Some(format!(
                                "struct '{}' cannot satisfy trait bound '{}' because field '{}' of type '{}' does not implement '{}'",
                                instance.name, bound, field.name, field.ty, trait_name
                            ));
                        }
                    }
                } else if let Some(e_decl) = env.enums.get(&instance.name) {
                    for variant in &e_decl.variants {
                        if !traits::type_satisfies_trait_with_scope(env, &variant.ty, bound, scope) {
                            return Some(format!(
                                "enum '{}' cannot satisfy trait bound '{}' because variant '{}' payload '{}' does not implement '{}'",
                                instance.name, bound, variant.name, variant.ty, trait_name
                            ));
                        }
                    }
                }
            }
            None
        }
        TypeKind::Tuple(elems) => {
            if trait_name == "AutoClone" || trait_name == "AutoDestroy" {
                for (idx, elem) in elems.iter().enumerate() {
                    if !traits::type_satisfies_trait_with_scope(env, elem, bound, scope) {
                        return Some(format!(
                            "tuple element {} of type '{}' does not implement '{}'",
                            idx, elem, trait_name
                        ));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Walk `ty` and push a diagnostic per problem: an undeclared
/// `Custom` name, a `Param` not in scope, wrong type-arg arity,
/// or an arg that fails the declared bound.
pub(crate) fn validate_type(
    env: &TypeEnv,
    ty: &Type,
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    match &ty.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Var(_)
        | TypeKind::IntVar(_)
        | TypeKind::FloatVar(_)
        | TypeKind::Error => {}
        TypeKind::Tuple(types) => {
            if types.len() > 12 {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::TupleArityExceeded,
                    ty.source,
                    format!("tuple arity {} exceeds maximum of 12", types.len()),
                ));
            }
            for t in types {
                validate_type(env, t, scope, d);
            }
        }
        TypeKind::Param(name) => {
            if !scope.contains_key(name) {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UndeclaredType,
                    ty.source,
                    format!("undeclared type parameter '{}'", name),
                ));
            }
        }
        TypeKind::Ref(_, _, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            validate_type(env, inner, scope, d);
        }
        TypeKind::Fn { params, ret, .. } => {
            for p in params {
                validate_type(env, p, scope, d);
            }
            validate_type(env, ret, scope, d);
        }
        TypeKind::Custom(instance) => {
            let (name, args, lifetime_args) = (
                &instance.name,
                &instance.type_args,
                &instance.lifetime_args,
            );
            for arg in args {
                validate_type(env, arg, scope, d);
            }
            let (type_params, lifetime_params) = if let Some(s) = env.structs.get(name) {
                (&s.type_params, &s.lifetime_params)
            } else if let Some(e) = env.enums.get(name) {
                (&e.type_params, &e.lifetime_params)
            } else {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UndeclaredType,
                    ty.source,
                    format!("undeclared type '{}'", name),
                ));
                return;
            };

            if args.len() != type_params.len() {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::TypeArgArityMismatch,
                    ty.source,
                    format!(
                        "'{}' takes {} type argument(s), found {}",
                        name,
                        type_params.len(),
                        args.len()
                    ),
                ));
                return;
            }
            if !lifetime_args.is_empty() && lifetime_args.len() != lifetime_params.len() {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::LifetimeArgArityMismatch,
                    ty.source,
                    format!(
                        "'{}' takes {} lifetime argument(s), found {}",
                        name,
                        lifetime_params.len(),
                        lifetime_args.len()
                    ),
                ));
                return;
            }

            let mapping = type_params
                .iter()
                .map(|parameter| parameter.name.clone())
                .zip(args.iter().cloned())
                .collect::<HashMap<_, _>>();
            let lifetime_mapping = lifetime_params
                .iter()
                .map(|parameter| parameter.lifetime.clone())
                .zip(lifetime_args.iter().cloned())
                .collect::<BTreeMap<_, _>>();
            for (tp, arg) in type_params.iter().zip(args.iter()) {
                let arg_class = traits::class_of(env, arg, scope);
                for m in [Marker::Copy, Marker::Drop, Marker::Move] {
                    if tp.bounds.markers.declared(m) && !arg_class.implies(m) {
                        let mut diag = source_diagnostic(
                            HllTypeCheckCode::BoundNotSatisfied,
                            arg.source,
                            format!(
                                "type argument '{}' for '{}::{}' does not satisfy bound '{:?}'",
                                arg, name, tp.name, m
                            ),
                        );
                        if let Some(hint) = explain_marker_failure(env, arg, m, scope) {
                            diag = diag.with_hint(hint);
                        }
                        d.push_error(diag);
                    }
                }
                for bound in &tp.bounds.traits {
                    let bound = substitute_bound(bound, &mapping, &lifetime_mapping);
                    if !traits::type_satisfies_trait_with_scope(env, arg, &bound, scope) {
                        let mut diag = source_diagnostic(
                            HllTypeCheckCode::BoundNotSatisfied,
                            arg.source,
                            format!(
                                "type argument '{}' for '{}::{}' does not satisfy trait bound '{}'",
                                arg, name, tp.name, bound
                            ),
                        );
                        if let Some(hint) = explain_trait_failure(env, arg, &bound, scope) {
                            diag = diag.with_hint(hint);
                        }
                        d.push_error(diag);
                    }
                }
            }
        }
    }
}

pub(crate) fn validate_trait_bound_cycles(program: &Program, env: &TypeEnv, d: &mut Diagnostics) {
    fn visit(
        env: &TypeEnv,
        name: &str,
        stack: &mut Vec<String>,
        complete: &mut HashSet<String>,
        d: &mut Diagnostics,
    ) {
        if complete.contains(name) {
            return;
        }
        let Some(trait_decl) = env.traits.get(name) else {
            return;
        };
        stack.push(name.to_string());
        for bound in &trait_decl.self_bounds.traits {
            if let Some(start) = stack
                .iter()
                .position(|ancestor| ancestor == &bound.trait_path.name)
            {
                let mut cycle = stack[start..].to_vec();
                cycle.push(bound.trait_path.name.clone());
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::TraitBoundCycle,
                    bound.source,
                    format!("trait-bound cycle: {}", cycle.join(" -> ")),
                ));
                continue;
            }
            visit(env, &bound.trait_path.name, stack, complete, d);
        }
        stack.pop();
        complete.insert(name.to_string());
    }

    let mut complete = HashSet::new();
    for declaration in &program.declarations {
        let Declaration::Trait(trait_decl) = declaration else {
            continue;
        };
        visit(env, &trait_decl.name, &mut Vec::new(), &mut complete, d);
    }
}

pub(crate) fn validate_impl_method_safety(env: &TypeEnv, d: &mut Diagnostics) {
    for (impl_block, trait_path) in env.impls.iter().filter_map(|impl_block| {
        impl_block
            .trait_path
            .as_ref()
            .map(|path| (impl_block, path))
    }) {
        let Some(trait_decl) = env.traits.get(&trait_path.name) else {
            continue;
        };
        for method in &impl_block.methods {
            let Some(trait_method) = trait_decl
                .methods
                .iter()
                .find(|trait_method| trait_method.name == method.name)
            else {
                continue;
            };
            if method.is_unsafe != trait_method.is_unsafe {
                let expected = if trait_method.is_unsafe {
                    "unsafe"
                } else {
                    "safe"
                };
                let found = if method.is_unsafe { "unsafe" } else { "safe" };
                d.push_error(
                    source_diagnostic(
                        HllTypeCheckCode::ImplMethodSafetyMismatch,
                        method.source,
                        format!(
                            "impl method '{}' is {}, but trait declaration is {}",
                            method.name, found, expected
                        ),
                    )
                    .in_function(impl_method_context(
                        &impl_block.target,
                        Some(trait_path),
                        &method.name,
                    )),
                );
            }
        }
    }
}

pub(crate) fn validate_fn_signature(
    env: &TypeEnv,
    function: &FnDecl,
    effective_params: &[TypeParam],
    context: &str,
    d: &mut Diagnostics,
) {
    let scope = type_params_scope(effective_params);
    let errors_before = d.error_count();
    for param in &function.params {
        validate_type(env, &param.ty, &scope, d);
    }
    validate_type(env, &function.ret_ty, &scope, d);
    d.annotate_errors_in_function(errors_before, context);
}

pub(crate) fn validate_type_param_bounds(
    env: &TypeEnv,
    params: &[TypeParam],
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for parameter in params {
        validate_bounds(
            env,
            &format!("type parameter '{}'", parameter.name),
            &parameter.bounds,
            scope,
            d,
        );
    }
}

pub(crate) fn validate_bounds(
    env: &TypeEnv,
    owner: &str,
    bounds: &Bounds,
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for bound in &bounds.traits {
        validate_trait_instance(
            env,
            owner,
            "trait bound",
            &bound.trait_path,
            bound.source,
            scope,
            d,
        );
    }
}

pub(crate) fn validate_trait_instance(
    env: &TypeEnv,
    owner: &str,
    reference_kind: &str,
    trait_path: &Instance,
    source: SourceInfo,
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for argument in &trait_path.type_args {
        validate_type(env, argument, scope, d);
    }
    let Some(trait_decl) = env.traits.get(&trait_path.name) else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::UndeclaredTrait,
            source,
            format!(
                "{} has undeclared {} '{}'",
                owner, reference_kind, trait_path.name
            ),
        ));
        return;
    };
    if trait_path.lifetime_args.len() != trait_decl.lifetime_params.len()
        || trait_path.type_args.len() != trait_decl.type_params.len()
    {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::TraitArgArityMismatch,
            source,
            format!(
                "{} '{}' expects {} lifetime and {} type argument(s), found {} lifetime and {} type argument(s)",
                reference_kind,
                trait_path.name,
                trait_decl.lifetime_params.len(),
                trait_decl.type_params.len(),
                trait_path.lifetime_args.len(),
                trait_path.type_args.len()
            ),
        ));
        return;
    }
    let mapping = trait_decl
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(trait_path.type_args.iter().cloned())
        .collect::<HashMap<_, _>>();
    let lifetime_mapping = trait_decl
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(trait_path.lifetime_args.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    for (trait_parameter, argument) in trait_decl.type_params.iter().zip(&trait_path.type_args) {
        let markers_satisfied = trait_parameter
            .bounds
            .markers
            .iter_declared()
            .all(|marker| env.class_of(argument, scope).implies(marker));
        let traits_satisfied = trait_parameter.bounds.traits.iter().all(|required| {
            let required = substitute_bound(required, &mapping, &lifetime_mapping);
            env.type_satisfies_trait_with_scope(argument, &required, scope)
        });
        if !markers_satisfied || !traits_satisfied {
            let mut diag = source_diagnostic(
                HllTypeCheckCode::BoundNotSatisfied,
                source,
                format!(
                    "type argument '{}' for {} '{}::{}' does not satisfy its declared bounds",
                    argument, reference_kind, trait_path.name, trait_parameter.name
                ),
            );
            if let Some(missing_marker) = trait_parameter
                .bounds
                .markers
                .iter_declared()
                .find(|m| !env.class_of(argument, scope).implies(*m))
            {
                if let Some(hint) = explain_marker_failure(env, argument, missing_marker, scope) {
                    diag = diag.with_hint(hint);
                }
            } else if let Some(missing_trait) = trait_parameter.bounds.traits.iter().find(|t| {
                let required = substitute_bound(t, &mapping, &lifetime_mapping);
                !env.type_satisfies_trait_with_scope(argument, &required, scope)
            }) {
                let required = substitute_bound(missing_trait, &mapping, &lifetime_mapping);
                if let Some(hint) = explain_trait_failure(env, argument, &required, scope) {
                    diag = diag.with_hint(hint);
                }
            }
            d.push_error(diag);
        }
    }
}

pub(crate) fn check_instantiation_bounds(
    env: &TypeEnv,
    subst: &Subst,
    types: &TypeCheckResults,
    first_pending: usize,
    d: &mut Diagnostics,
) {
    for pending in &types.pending_instantiations[first_pending..] {
        let mapping = pending
            .type_mapping
            .iter()
            .map(|(name, argument)| (name.clone(), subst.resolve(argument)))
            .collect::<HashMap<_, _>>();
        let lifetime_mapping = pending
            .lifetime_mapping
            .iter()
            .map(|(parameter, argument)| (parameter.clone(), subst.resolve_lifetime(argument)))
            .collect::<BTreeMap<_, _>>();
        for (parameter, argument) in pending.type_params.iter().zip(&pending.type_args) {
            let argument = subst.resolve(argument);
            for marker in parameter.bounds.markers.iter_declared() {
                if !env
                    .class_of(&argument, &pending.caller_type_params)
                    .implies(marker)
                {
                    let mut diag = source_diagnostic(
                        HllTypeCheckCode::BoundNotSatisfied,
                        pending.source,
                        format!(
                            "type argument '{}' for '{}::{}' does not satisfy bound '{:?}'",
                            argument, pending.function_name, parameter.name, marker
                        ),
                    );
                    if let Some(hint) = explain_marker_failure(
                        env,
                        &argument,
                        marker,
                        &pending.caller_type_params,
                    ) {
                        diag = diag.with_hint(hint);
                    }
                    d.push_error(diag);
                }
            }
            for bound in &parameter.bounds.traits {
                let bound = substitute_bound(bound, &mapping, &lifetime_mapping);
                if !env.type_satisfies_trait_with_scope(
                    &argument,
                    &bound,
                    &pending.caller_type_params,
                ) {
                    let mut diag = source_diagnostic(
                        HllTypeCheckCode::BoundNotSatisfied,
                        pending.source,
                        format!(
                            "type argument '{}' for '{}::{}' does not satisfy trait bound '{}'",
                            argument, pending.function_name, parameter.name, bound
                        ),
                    );
                    if let Some(hint) = explain_trait_failure(
                        env,
                        &argument,
                        &bound,
                        &pending.caller_type_params,
                    ) {
                        diag = diag.with_hint(hint);
                    }
                    d.push_error(diag);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum FnDeclSite {
    Free,
    TraitMethod,
    ImplMethod,
}

pub(crate) fn validate_fn_modifiers(
    f: &FnDecl,
    site: FnDeclSite,
    context: &str,
    d: &mut Diagnostics,
) {
    if f.abi == Abi::C && !f.is_unsafe {
        d.push_error(
            source_diagnostic(
                HllTypeCheckCode::InvalidFnModifiers,
                f.source,
                format!("extern \"C\" function '{}' must be unsafe", f.name),
            )
            .in_function(context),
        );
    }
    if f.linkage == Linkage::Foreign && f.abi == Abi::Silica && f.is_unsafe {
        d.push_error(
            source_diagnostic(
                HllTypeCheckCode::InvalidFnModifiers,
                f.source,
                format!(
                    "extern Silica function '{}' cannot be unsafe; safe by import contract",
                    f.name
                ),
            )
            .in_function(context),
        );
    }
    match site {
        FnDeclSite::Free => match (f.linkage, f.body.is_some()) {
            (Linkage::Foreign, true) => d.push_error(
                source_diagnostic(
                    HllTypeCheckCode::InvalidFnModifiers,
                    f.source,
                    format!("extern function '{}' must not have a body", f.name),
                )
                .in_function(context),
            ),
            (Linkage::Local, false) => d.push_error(
                source_diagnostic(
                    HllTypeCheckCode::InvalidFnModifiers,
                    f.source,
                    format!(
                        "function '{}' has no body; add one or mark it 'extern'",
                        f.name
                    ),
                )
                .in_function(context),
            ),
            _ => {}
        },
        FnDeclSite::TraitMethod => {
            if f.body.is_some() {
                d.push_error(
                    source_diagnostic(
                        HllTypeCheckCode::InvalidFnModifiers,
                        f.source,
                        format!("trait method '{}' must not have a body", f.name),
                    )
                    .in_function(context),
                );
            }
        }
        FnDeclSite::ImplMethod => {
            if f.body.is_none() {
                d.push_error(
                    source_diagnostic(
                        HllTypeCheckCode::InvalidFnModifiers,
                        f.source,
                        format!("impl method '{}' requires a body", f.name),
                    )
                    .in_function(context),
                );
            }
        }
    }
}
