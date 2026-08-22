use std::collections::{BTreeMap, HashMap, HashSet};

use crate::common::{Lifetime, Marker, Markers, RefKind};
use crate::hll::ast::{Bounds, FnDecl, ImplBlock, Instance, TraitBound, TraitDecl, Type, TypeKind};
use crate::hll::type_check::env::{
    substitute, substitute_all, substitute_bound, ReceiverAdjustment, TypeEnv,
};

#[derive(Clone, Default, Debug)]
pub(crate) struct ImplBindings {
    pub(crate) lifetimes: BTreeMap<Lifetime, Lifetime>,
    pub(crate) types: BTreeMap<String, Type>,
}

pub(crate) fn match_impl_lifetime(
    pattern: &Option<Lifetime>,
    actual: &Option<Lifetime>,
    parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    match (pattern, actual) {
        (Some(pattern), Some(actual)) if parameters.contains(pattern) => {
            match bindings.lifetimes.get(pattern) {
                Some(bound) => bound == actual,
                None => {
                    bindings.lifetimes.insert(pattern.clone(), actual.clone());
                    true
                }
            }
        }
        (Some(pattern), Some(actual)) => pattern == actual,
        (Some(pattern), None) if parameters.contains(pattern) => true,
        (None, _) => true,
        _ => false,
    }
}

pub(crate) fn match_impl_instance(
    pattern: &Instance,
    actual: &Instance,
    type_parameters: &HashSet<String>,
    lifetime_parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    pattern.name == actual.name
        && pattern.lifetime_args.len() == actual.lifetime_args.len()
        && pattern.type_args.len() == actual.type_args.len()
        && pattern
            .lifetime_args
            .iter()
            .zip(&actual.lifetime_args)
            .all(|(pattern, actual)| {
                match_impl_lifetime(
                    &Some(pattern.clone()),
                    &Some(actual.clone()),
                    lifetime_parameters,
                    bindings,
                )
            })
        && pattern
            .type_args
            .iter()
            .zip(&actual.type_args)
            .all(|(pattern, actual)| {
                match_impl_type(
                    pattern,
                    actual,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
            })
}

pub(crate) fn match_impl_type(
    pattern: &Type,
    actual: &Type,
    type_parameters: &HashSet<String>,
    lifetime_parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    if let TypeKind::Param(name) = &pattern.kind {
        if type_parameters.contains(name) {
            return match bindings.types.get(name) {
                Some(bound) => bound == actual,
                None => {
                    bindings.types.insert(name.clone(), actual.clone());
                    true
                }
            };
        }
    }

    match (&pattern.kind, &actual.kind) {
        (_, TypeKind::Var(_)) => true,
        (TypeKind::Int(_), TypeKind::IntVar(_)) => true,
        (TypeKind::Float(_), TypeKind::FloatVar(_)) => true,
        (TypeKind::Int(pattern), TypeKind::Int(actual)) => pattern == actual,
        (TypeKind::Float(pattern), TypeKind::Float(actual)) => pattern == actual,
        (TypeKind::Bool, TypeKind::Bool) | (TypeKind::Never, TypeKind::Never) => true,
        (TypeKind::Tuple(pattern_types), TypeKind::Tuple(actual_types)) => {
            pattern_types.len() == actual_types.len()
                && pattern_types
                    .iter()
                    .zip(actual_types)
                    .all(|(p, a)| match_impl_type(p, a, type_parameters, lifetime_parameters, bindings))
        }
        (TypeKind::Param(pattern), TypeKind::Param(actual)) => pattern == actual,
        (TypeKind::Custom(pattern), TypeKind::Custom(actual)) => match_impl_instance(
            pattern,
            actual,
            type_parameters,
            lifetime_parameters,
            bindings,
        ),
        (
            TypeKind::Fn {
                abi: pattern_abi,
                params: pattern_params,
                ret: pattern_ret,
            },
            TypeKind::Fn {
                abi: actual_abi,
                params: actual_params,
                ret: actual_ret,
            },
        ) => {
            pattern_abi == actual_abi
                && pattern_params.len() == actual_params.len()
                && pattern_params
                    .iter()
                    .zip(actual_params)
                    .all(|(pattern, actual)| {
                        match_impl_type(
                            pattern,
                            actual,
                            type_parameters,
                            lifetime_parameters,
                            bindings,
                        )
                    })
                && match_impl_type(
                    pattern_ret,
                    actual_ret,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        (
            TypeKind::Ref(pattern_kind, pattern_lifetime, pattern_inner),
            TypeKind::Ref(actual_kind, actual_lifetime, actual_inner),
        ) => {
            pattern_kind == actual_kind
                && match_impl_lifetime(
                    pattern_lifetime,
                    actual_lifetime,
                    lifetime_parameters,
                    bindings,
                )
                && match_impl_type(
                    pattern_inner,
                    actual_inner,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        (TypeKind::RawPtr(pattern), TypeKind::RawPtr(actual)) => match_impl_type(
            pattern,
            actual,
            type_parameters,
            lifetime_parameters,
            bindings,
        ),
        (TypeKind::Array(pattern, pattern_len), TypeKind::Array(actual, actual_len)) => {
            pattern_len == actual_len
                && match_impl_type(
                    pattern,
                    actual,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        _ => false,
    }
}

pub(crate) fn substitute_impl_instance(
    instance: &Instance,
    bindings: &ImplBindings,
) -> Instance {
    let type_mapping = bindings
        .types
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect::<HashMap<_, _>>();
    Instance::new(
        instance.name.clone(),
        instance
            .lifetime_args
            .iter()
            .map(|lifetime| {
                bindings
                    .lifetimes
                    .get(lifetime)
                    .cloned()
                    .unwrap_or_else(|| lifetime.clone())
            })
            .collect(),
        instance
            .type_args
            .iter()
            .map(|ty| substitute_all(ty, &type_mapping, &bindings.lifetimes))
            .collect(),
    )
}

pub(crate) fn impl_bindings(
    impl_block: &ImplBlock,
    self_ty: &Type,
    env: &TypeEnv,
) -> Option<ImplBindings> {
    impl_bindings_inner(
        impl_block,
        self_ty,
        None,
        env,
        &env.current_type_params,
        &mut Vec::new(),
    )
}

pub(crate) fn impl_bindings_inner(
    impl_block: &ImplBlock,
    self_ty: &Type,
    required_trait: Option<&Instance>,
    env: &TypeEnv,
    scope: &HashMap<String, Bounds>,
    obligations: &mut Vec<(Type, Instance)>,
) -> Option<ImplBindings> {
    let type_parameters = impl_block
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect::<HashSet<_>>();
    let lifetime_parameters = impl_block
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .collect::<HashSet<_>>();
    let mut bindings = ImplBindings::default();
    if !match_impl_type(
        &impl_block.target,
        self_ty,
        &type_parameters,
        &lifetime_parameters,
        &mut bindings,
    ) {
        return None;
    }
    if let Some(required_trait) = required_trait {
        let impl_trait = impl_block.trait_path.as_ref()?;
        if !match_impl_instance(
            impl_trait,
            required_trait,
            &type_parameters,
            &lifetime_parameters,
            &mut bindings,
        ) {
            return None;
        }
    }
    if impl_block.type_params.iter().any(|parameter| {
        let Some(argument) = bindings.types.get(&parameter.name) else {
            return true;
        };
        parameter
            .bounds
            .markers
            .iter_declared()
            .any(|bound| !class_of(env, argument, scope).implies(bound))
            || parameter.bounds.traits.iter().any(|bound| {
                let bound = substitute_impl_instance(&bound.trait_path, &bindings);
                !type_satisfies_trait_inner(env, argument, &bound, scope, obligations)
            })
    }) {
        return None;
    }
    Some(bindings)
}

pub(crate) fn instantiate_trait_self_bound(
    trait_decl: &TraitDecl,
    trait_path: &Instance,
    self_ty: &Type,
    bound: &TraitBound,
) -> Instance {
    let mut type_mapping = trait_decl
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(trait_path.type_args.iter().cloned())
        .collect::<HashMap<_, _>>();
    type_mapping.insert("Self".to_string(), self_ty.clone());
    let lifetime_mapping = trait_decl
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(trait_path.lifetime_args.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    substitute_bound(bound, &type_mapping, &lifetime_mapping)
}

pub(crate) fn trait_bound_implies(
    env: &TypeEnv,
    available: &Instance,
    self_ty: &Type,
    required: &Instance,
    visiting: &mut HashSet<String>,
) -> bool {
    if available == required {
        return true;
    }
    if !visiting.insert(available.name.clone()) {
        return false;
    }
    let Some(trait_decl) = env.traits.get(&available.name) else {
        visiting.remove(&available.name);
        return false;
    };
    let implied = trait_decl.self_bounds.traits.iter().any(|bound| {
        let bound = instantiate_trait_self_bound(trait_decl, available, self_ty, bound);
        trait_bound_implies(env, &bound, self_ty, required, visiting)
    });
    visiting.remove(&available.name);
    implied
}

pub(crate) fn implied_trait_paths(
    env: &TypeEnv,
    direct: &Instance,
    self_ty: &Type,
) -> Vec<Instance> {
    fn collect(
        env: &TypeEnv,
        path: Instance,
        self_ty: &Type,
        result: &mut Vec<Instance>,
        visiting: &mut HashSet<String>,
    ) {
        if result.contains(&path) {
            return;
        }
        let path_name = path.name.clone();
        if !visiting.insert(path_name.clone()) {
            return;
        }
        let Some(trait_decl) = env.traits.get(&path_name) else {
            result.push(path);
            visiting.remove(&path_name);
            return;
        };
        let implied = trait_decl
            .self_bounds
            .traits
            .iter()
            .map(|bound| instantiate_trait_self_bound(trait_decl, &path, self_ty, bound))
            .collect::<Vec<_>>();
        result.push(path);
        for bound in implied {
            collect(env, bound, self_ty, result, visiting);
        }
        visiting.remove(&path_name);
    }

    let mut result = Vec::new();
    collect(
        env,
        direct.clone(),
        self_ty,
        &mut result,
        &mut HashSet::new(),
    );
    result
}

pub(crate) fn find_fn_trait_bound(
    env: &TypeEnv,
    ty: &Type,
) -> Option<(&'static str, &'static str, ReceiverAdjustment, Instance)> {
    let TypeKind::Param(name) = &ty.kind else {
        return None;
    };
    let bounds = env.current_type_params.get(name)?;

    for bound in &bounds.traits {
        if bound.trait_path.name == "Fn" && bound.trait_path.type_args.len() == 2 {
            return Some((
                "Fn",
                "call",
                ReceiverAdjustment::Borrow(RefKind::Shared),
                bound.trait_path.clone(),
            ));
        }
    }

    for bound in &bounds.traits {
        if bound.trait_path.name == "FnMut" && bound.trait_path.type_args.len() == 2 {
            return Some((
                "FnMut",
                "call_mut",
                ReceiverAdjustment::Borrow(RefKind::Mut),
                bound.trait_path.clone(),
            ));
        }
    }

    for bound in &bounds.traits {
        if bound.trait_path.name == "FnOnce" && bound.trait_path.type_args.len() == 2 {
            return Some((
                "FnOnce",
                "call_once",
                ReceiverAdjustment::None,
                bound.trait_path.clone(),
            ));
        }
    }

    for direct_bound in &bounds.traits {
        for implied in implied_trait_paths(env, &direct_bound.trait_path, ty) {
            if implied.name == "Fn" && implied.type_args.len() == 2 {
                return Some((
                    "Fn",
                    "call",
                    ReceiverAdjustment::Borrow(RefKind::Shared),
                    implied,
                ));
            }
            if implied.name == "FnMut" && implied.type_args.len() == 2 {
                return Some((
                    "FnMut",
                    "call_mut",
                    ReceiverAdjustment::Borrow(RefKind::Mut),
                    implied,
                ));
            }
            if implied.name == "FnOnce" && implied.type_args.len() == 2 {
                return Some((
                    "FnOnce",
                    "call_once",
                    ReceiverAdjustment::None,
                    implied,
                ));
            }
        }
    }

    None
}

pub(crate) fn types_compatible_for_closure_trait(actual: &Type, required: &Type) -> bool {
    match (&actual.kind, &required.kind) {
        (TypeKind::IntVar(_), TypeKind::Int(_)) | (TypeKind::Int(_), TypeKind::IntVar(_)) => true,
        (TypeKind::FloatVar(_), TypeKind::Float(_))
        | (TypeKind::Float(_), TypeKind::FloatVar(_)) => true,
        (TypeKind::Var(_), _) | (_, TypeKind::Var(_)) => true,
        (TypeKind::Tuple(a), TypeKind::Tuple(b)) => {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|(x, y)| types_compatible_for_closure_trait(x, y))
        }
        (TypeKind::Ref(k1, _, in1), TypeKind::Ref(k2, _, in2)) => {
            k1 == k2 && types_compatible_for_closure_trait(in1, in2)
        }
        (TypeKind::Custom(i1), TypeKind::Custom(i2)) => {
            i1.name == i2.name
                && i1.type_args.len() == i2.type_args.len()
                && i1
                    .type_args
                    .iter()
                    .zip(i2.type_args.iter())
                    .all(|(x, y)| types_compatible_for_closure_trait(x, y))
        }
        (a, b) => a == b,
    }
}

pub fn type_satisfies_trait(env: &TypeEnv, ty: &Type, trait_path: &Instance) -> bool {
    type_satisfies_trait_inner(env, ty, trait_path, &HashMap::new(), &mut Vec::new())
}

pub fn type_satisfies_trait_with_scope(
    env: &TypeEnv,
    ty: &Type,
    trait_path: &Instance,
    scope: &HashMap<String, Bounds>,
) -> bool {
    type_satisfies_trait_inner(env, ty, trait_path, scope, &mut Vec::new())
}

pub(crate) fn type_satisfies_trait_inner(
    env: &TypeEnv,
    ty: &Type,
    trait_path: &Instance,
    scope: &HashMap<String, Bounds>,
    obligations: &mut Vec<(Type, Instance)>,
) -> bool {
    if let TypeKind::Param(name) = &ty.kind {
        return scope.get(name).is_some_and(|bounds| {
            bounds.traits.iter().any(|bound| {
                trait_bound_implies(env, &bound.trait_path, ty, trait_path, &mut HashSet::new())
            })
        });
    }
    if let TypeKind::Custom(Instance { name, .. }) = &ty.kind {
        if let Some(closure) = env.closures.get(name) {
            let is_fn_trait = match trait_path.name.as_str() {
                "FnOnce" => true,
                "FnMut" => matches!(
                    closure.fn_kind,
                    crate::hll::derive::FnKind::Fn | crate::hll::derive::FnKind::FnMut
                ),
                "Fn" => closure.fn_kind == crate::hll::derive::FnKind::Fn,
                _ => false,
            };
            if is_fn_trait && trait_path.type_args.len() == 2 {
                let actual_args = Type::synthesized(TypeKind::Tuple(
                    closure.params.iter().map(|p| p.ty.clone()).collect(),
                ));
                if types_compatible_for_closure_trait(&actual_args, &trait_path.type_args[0])
                    && types_compatible_for_closure_trait(&closure.ret_ty, &trait_path.type_args[1])
                {
                    return true;
                }
            }
        }
    }
    let obligation = (ty.clone(), trait_path.clone());
    if obligations.contains(&obligation) {
        return false;
    }
    obligations.push(obligation);
    let satisfied = env.impls.iter().any(|impl_block| {
        impl_bindings_inner(impl_block, ty, Some(trait_path), env, scope, obligations).is_some()
    });
    obligations.pop();
    satisfied
}

pub(crate) fn match_impl_method_receiver(
    impl_block: &ImplBlock,
    method: &FnDecl,
    receiver_ty: &Type,
    env: &TypeEnv,
) -> Option<(Type, ImplBindings, ReceiverAdjustment)> {
    let receiver_param = method.params.first()?;
    let mut possible_self_types = vec![receiver_ty.clone()];
    if let (TypeKind::Ref(expected_kind, _, _), TypeKind::Ref(actual_kind, _, actual_inner)) =
        (&receiver_param.ty.kind, &receiver_ty.kind)
    {
        if expected_kind == actual_kind {
            possible_self_types.push(*actual_inner.clone());
        }
    }

    let mut type_parameters = impl_block
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect::<HashSet<_>>();
    type_parameters.extend(method.type_params.iter().map(|p| p.name.clone()));
    let mut lifetime_parameters = impl_block
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .collect::<HashSet<_>>();
    lifetime_parameters.extend(method.lifetime_params.iter().map(|p| p.lifetime.clone()));
    let matches = possible_self_types
        .into_iter()
        .filter_map(|self_ty| {
            let mut bindings = impl_bindings(impl_block, &self_ty, env)?;
            let mut mapping = bindings
                .types
                .iter()
                .map(|(name, ty)| (name.clone(), ty.clone()))
                .collect::<HashMap<_, _>>();
            mapping.insert("Self".to_string(), self_ty.clone());
            let expected_receiver = substitute(&receiver_param.ty, &mapping);
            let mut exact_bindings = bindings.clone();
            if match_impl_type(
                &expected_receiver,
                receiver_ty,
                &type_parameters,
                &lifetime_parameters,
                &mut exact_bindings,
            ) {
                return Some((self_ty, exact_bindings, ReceiverAdjustment::None));
            }
            let TypeKind::Ref(kind, _, pointee) = &expected_receiver.kind else {
                return None;
            };
            match_impl_type(
                pointee,
                receiver_ty,
                &type_parameters,
                &lifetime_parameters,
                &mut bindings,
            )
            .then_some((self_ty, bindings, ReceiverAdjustment::Borrow(*kind)))
        })
        .collect::<Vec<_>>();
    matches
        .iter()
        .find(|(_, _, adjustment)| *adjustment == ReceiverAdjustment::None)
        .cloned()
        .or_else(|| matches.into_iter().next())
}

/// Substructural class of a type in this environment.
pub fn class_of(env: &TypeEnv, ty: &Type, scope: &HashMap<String, Bounds>) -> Markers {
    let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
    match &ty.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never => all(),
        TypeKind::Tuple(types) => {
            if types.is_empty() {
                all()
            } else {
                types
                    .iter()
                    .map(|elem| class_of(env, elem, scope))
                    .fold(all(), |acc, m| acc.intersection(m))
            }
        }
        TypeKind::Fn { .. } | TypeKind::RawPtr(_) => all(),
        TypeKind::Ref(kind, _, _) => kind.value_markers(),
        TypeKind::Custom(Instance { name, .. }) => {
            let declared = if let Some(s) = env.structs.get(name) {
                s.markers
            } else if let Some(e) = env.enums.get(name) {
                e.markers
            } else {
                Markers::empty()
            };
            let mut markers = declared.iter_declared().collect::<Vec<_>>();
            for m in [Marker::Copy, Marker::Drop, Marker::Move] {
                if !declared.declared(m)
                    && type_satisfies_trait_with_scope(env, ty, &Instance::bare(m.name()), scope)
                {
                    markers.push(m);
                }
            }
            Markers::from_iter(markers)
        }
        TypeKind::Param(name) => scope
            .get(name)
            .map(|bounds| markers_from_bounds(env, bounds, &mut HashSet::new()))
            .unwrap_or_else(Markers::empty),
        TypeKind::Array(elem, _) => class_of(env, elem, scope),
        TypeKind::Var(_) | TypeKind::IntVar(_) | TypeKind::FloatVar(_) | TypeKind::Error => all(),
    }
}

pub(crate) fn markers_from_bounds(
    env: &TypeEnv,
    bounds: &Bounds,
    visiting: &mut HashSet<String>,
) -> Markers {
    let mut markers = bounds.markers.iter_declared().collect::<Vec<_>>();
    for bound in &bounds.traits {
        let name = &bound.trait_path.name;
        if !visiting.insert(name.clone()) {
            continue;
        }
        if let Some(trait_decl) = env.traits.get(name) {
            markers.extend(
                markers_from_bounds(env, &trait_decl.self_bounds, visiting)
                    .iter_declared(),
            );
        }
        visiting.remove(name);
    }
    Markers::from_iter(markers)
}
