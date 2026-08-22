use std::collections::{BTreeMap, HashMap, HashSet};

use indexmap::{IndexMap, IndexSet};

use crate::common::{IntTy, Lifetime, LifetimeParam, Marker, Markers, RefKind, SourceInfo};
use crate::diagnostics::Diagnostics;
use crate::hll::ast::{
    BinOp, CallTarget, Expr, ExprKind, FnDecl, GenericArgs, Instance, LambdaParam, Literal, Param,
    Pattern, Stmt, Type, TypeKind, TypeParam, UnOp,
};
use crate::hll::helpers::*;
use crate::hll::type_check::casts::is_cast_supported;
use crate::hll::type_check::closures;
use crate::hll::type_check::dispatch::{
    instantiate_function, resolve_field_access, resolve_path_call, resolve_qualified_call,
    resolve_receiver_call,
};
use crate::hll::type_check::env::{
    array_len, build_lifetime_mapping, build_subst_map, substitute_all, type_params_scope,
    ClosureCapture, ClosureInfo, GenericClosureCall, PendingInstantiation, ResolvedMethodTarget,
    ResolvedReceiverTarget, TypeCheckResults, TypeEnv,
};
use crate::hll::type_check::mod_types::{source_diagnostic, HllTypeCheckCode};
use crate::hll::type_check::subst::{collect_unresolved_vars, Subst};
use crate::hll::type_check::traits::find_fn_trait_bound;
use crate::hll::type_check::validation::{check_instantiation_bounds, validate_type};

pub(crate) fn record_expression_type(
    env: &TypeEnv,
    types: &mut TypeCheckResults,
    source: SourceInfo,
    ty: Type,
) {
    types.expression_types.insert(source, ty);
    if let Some(context) = &env.current_function {
        types.expression_contexts.insert(source, context.clone());
    }
}

pub(crate) fn check_fn_body(
    env: &mut TypeEnv,
    types: &mut TypeCheckResults,
    function: &FnDecl,
    enclosing_lifetime_params: &[LifetimeParam],
    enclosing_params: &[TypeParam],
    context: &str,
    d: &mut Diagnostics,
) {
    let Some(body) = &function.body else { return };

    let mut effective_params = enclosing_params.to_vec();
    effective_params.extend(function.type_params.clone());
    env.current_type_params = type_params_scope(&effective_params);
    env.current_generic_params = effective_params;
    env.current_lifetimes = enclosing_lifetime_params
        .iter()
        .chain(&function.lifetime_params)
        .map(|parameter| parameter.lifetime.clone())
        .chain(std::iter::once(Lifetime("static".to_string())))
        .collect();
    env.current_function = Some(context.to_string());
    env.push_scope();
    env.current_ret_ty = Some(function.ret_ty.clone());
    env.in_unsafe = function.is_unsafe;
    for param in &function.params {
        env.insert_var(param.name.clone(), param.ty.clone());
    }
    let errors_before = d.error_count();
    let expr_types_before = types.expression_types.len();
    let pending_before = types.pending_instantiations.len();
    let fn_inst_before = types.function_instantiations.len();
    let recv_calls_before = types.receiver_calls.len();
    let qual_calls_before = types.qualified_calls.len();
    let closures_before = types.closures.len();

    let mut subst = Subst::new();
    check_inner(env, &mut subst, body, &function.ret_ty, types, d);
    check_instantiation_bounds(env, &subst, types, pending_before, d);

    // Check for unresolved type variables in expressions for this function
    let mut reported_vars = HashSet::new();
    for (source, ty) in types.expression_types.iter().skip(expr_types_before) {
        let resolved = subst.resolve(ty);
        let mut unresolved = HashSet::new();
        collect_unresolved_vars(&resolved, &subst, &mut unresolved);
        if !unresolved.is_empty() {
            let has_unreported = unresolved.iter().any(|id| !reported_vars.contains(id));
            if has_unreported {
                reported_vars.extend(unresolved);
                let diagnostic = source_diagnostic(
                    HllTypeCheckCode::AmbiguousType,
                    *source,
                    format!("type annotations needed: type of expression is ambiguous (could not resolve type variable in {})", resolved),
                );
                d.push_error(diagnostic.in_function(context));
            }
        }
    }
    for pending in &types.pending_instantiations[pending_before..] {
        for argument in &pending.type_args {
            let resolved = subst.resolve(argument);
            let mut unresolved = HashSet::new();
            collect_unresolved_vars(&resolved, &subst, &mut unresolved);
            if unresolved.iter().any(|id| !reported_vars.contains(id)) {
                reported_vars.extend(unresolved);
                let diagnostic = source_diagnostic(
                    HllTypeCheckCode::AmbiguousType,
                    pending.source,
                    format!(
                        "type annotations needed: cannot infer all type arguments for function '{}'",
                        pending.function_name
                    ),
                );
                d.push_error(diagnostic.in_function(context));
            }
        }
    }

    // Resolve this function's captured expression types
    for (_, ty) in types.expression_types.iter_mut().skip(expr_types_before) {
        *ty = subst.resolve_default(ty);
    }
    let resolve_instance = |instantiation: &mut Instance, subst: &Subst| {
        for lifetime in &mut instantiation.lifetime_args {
            *lifetime = subst.resolve_lifetime(lifetime);
        }
        for ty in &mut instantiation.type_args {
            *ty = subst.resolve_default(ty);
        }
    };
    for instantiation in types.function_instantiations.values_mut().skip(fn_inst_before) {
        resolve_instance(instantiation, &subst);
    }
    let resolve_method_target = |target: &mut ResolvedMethodTarget, subst: &Subst| match target {
        ResolvedMethodTarget::Inherent { self_ty, method } => {
            *self_ty = subst.resolve_default(self_ty);
            resolve_instance(method, subst);
        }
        ResolvedMethodTarget::Trait {
            trait_path,
            self_ty,
            method,
        } => {
            *self_ty = subst.resolve_default(self_ty);
            resolve_instance(trait_path, subst);
            resolve_instance(method, subst);
        }
        ResolvedMethodTarget::EnumConstructor { enum_instance, .. } => {
            resolve_instance(enum_instance, subst);
        }
    };
    for call in types.receiver_calls.values_mut().skip(recv_calls_before) {
        match &mut call.target {
            ResolvedReceiverTarget::Method(target) => resolve_method_target(target, &subst),
            ResolvedReceiverTarget::FreeFunction(instance) => resolve_instance(instance, &subst),
            ResolvedReceiverTarget::Field => {}
        }
    }
    for target in types.qualified_calls.values_mut().skip(qual_calls_before) {
        resolve_method_target(target, &subst);
    }
    for closure in types.closures.values_mut().skip(closures_before) {
        for p in &mut closure.params {
            p.ty = subst.resolve_default(&p.ty);
        }
        closure.ret_ty = subst.resolve_default(&closure.ret_ty);
        for c in &mut closure.captures {
            c.ty = subst.resolve_default(&c.ty);
        }
    }

    if let Some(params) = types.synthesized_lifetime_params.get_mut(context) {
        params.retain(|param| subst.resolve_lifetime(&param.lifetime) == param.lifetime);
    }

    d.annotate_errors_in_function(errors_before, context);
    env.pop_scope();
    env.in_unsafe = false;
    env.current_type_params.clear();
    env.current_generic_params.clear();
    env.current_lifetimes.clear();
    env.current_function = None;
}

pub(crate) fn infer_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let ty = match &expr.kind {
        ExprKind::Literal(lit) => infer_literal(lit, subst),
        ExprKind::Binary(lhs, op, rhs) => infer_binary(env, subst, expr, lhs, *op, rhs, types, d),
        ExprKind::Unary(op, operand) => infer_unary(env, subst, *op, operand, types, d),
        ExprKind::Variable(name) => infer_variable(env, subst, expr, name, types, d),
        ExprKind::FieldAccess(target, field) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            resolve_field_access(env, subst, &target_ty, target.source, field, expr.source, d)
        }
        ExprKind::Cast(target, to_ty) => infer_cast(env, subst, expr, target, to_ty, types, d),
        ExprKind::Deref(target) => infer_deref(env, subst, expr, target, types, d),
        ExprKind::Borrow(kind, target) => infer_borrow(env, subst, *kind, target, types, d),
        ExprKind::RawBorrow(target) => infer_raw_borrow(env, subst, target, types, d),
        ExprKind::Call(target, generics, args) => {
            infer_call(env, subst, expr, target, generics, args, types, d)
        }
        ExprKind::Lambda { params, ret_ty, body } => {
            infer_lambda(env, subst, expr, params, ret_ty.as_ref(), body, types, d)
        }
        ExprKind::Block(stmts, last_expr, is_unsafe) => {
            infer_block(env, subst, stmts, last_expr.as_deref(), *is_unsafe, types, d)
        }
        ExprKind::If(cond, true_block, false_block) => {
            infer_if(env, subst, expr, cond, true_block, false_block, types, d)
        }
        ExprKind::Loop(body) => infer_loop(env, subst, body, types, d),
        ExprKind::Break(val_expr) => infer_break(env, subst, val_expr.as_deref(), types, d),
        ExprKind::Continue => never_ty(),
        ExprKind::Return(val_expr) => infer_return(env, subst, expr, val_expr.as_deref(), types, d),
        ExprKind::Assign(lhs, rhs) => infer_assign(env, subst, lhs, rhs, types, d),
        ExprKind::Match(target, arms) => infer_match(env, subst, expr, target, arms, types, d),
        ExprKind::StructConstr(name, fields) => {
            infer_struct_constr(env, subst, expr, name, fields, types, d)
        }
        ExprKind::EnumConstr(enum_name, variant_name, payload) => {
            infer_enum_constr(env, subst, expr, enum_name, variant_name, payload, types, d)
        }
        ExprKind::Path(target_ty, member) => {
            infer_path(env, subst, expr, target_ty, member, types, d)
        }
        ExprKind::Array(elements) => infer_array(env, subst, elements, types, d),
        ExprKind::Tuple(elements) => infer_tuple(env, subst, expr, elements, types, d),
        ExprKind::ArrayIndex(arr, idx) => infer_array_index(env, subst, expr, arr, idx, types, d),
    };

    record_expression_type(env, types, expr.source, ty.clone());
    ty
}

fn infer_literal(lit: &Literal, subst: &mut Subst) -> Type {
    match lit {
        Literal::Int(_, Some(ty)) => int_ty(*ty),
        Literal::Int(_, None) => subst.fresh_int_var(),
        Literal::Float(_, Some(ty)) => float_ty(*ty),
        Literal::Float(_, None) => subst.fresh_float_var(),
        Literal::Bool(_) => bool_ty(),
        Literal::Tuple => unit_ty(),
        Literal::ByteStr(bytes) => array_ty(int_ty(IntTy::U8), array_len(bytes.len())),
    }
}

fn infer_binary(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    lhs: &Expr,
    op: BinOp,
    rhs: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let lhs_ty = infer_inner(env, subst, lhs, types, d);
    let rhs_ty = infer_inner(env, subst, rhs, types, d);
    if let Err(e) = subst.unify(&lhs_ty, &rhs_ty) {
        d.push_error(e.to_diag(expr.source));
    }

    let resolved = subst.resolve(&lhs_ty);
    match &resolved.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Var(_)
        | TypeKind::IntVar(_)
        | TypeKind::FloatVar(_)
        | TypeKind::Never
        | TypeKind::Error => {}
        _ => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::BinaryOpNonNumeric,
                lhs.source,
                format!(
                    "binary operations only supported on numeric types, found {}",
                    resolved
                ),
            ));
            return error_ty();
        }
    }

    let is_cmp = matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    );
    if is_cmp {
        bool_ty()
    } else {
        lhs_ty
    }
}

fn infer_unary(
    env: &mut TypeEnv,
    subst: &mut Subst,
    op: UnOp,
    operand: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let operand_ty = infer_inner(env, subst, operand, types, d);
    let resolved = subst.resolve(&operand_ty);
    match op {
        UnOp::Neg => match &resolved.kind {
            TypeKind::Int(int_ty) if int_ty.is_signed() => {}
            TypeKind::Float(_) => {}
            TypeKind::IntVar(_)
            | TypeKind::FloatVar(_)
            | TypeKind::Var(_)
            | TypeKind::Never
            | TypeKind::Error => {}
            _ => {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UnaryOpInvalidOperand,
                    operand.source,
                    format!(
                        "unary '-' requires a signed integer or float operand, found {}",
                        resolved
                    ),
                ));
                return error_ty();
            }
        },
    }
    operand_ty
}

fn infer_variable(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    name: &str,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    if let Some(ty) = env.lookup_var(name) {
        ty
    } else if env.functions.contains_key(name) {
        let Some((fn_ty, instance)) = instantiate_function(
            env,
            subst,
            name,
            &GenericArgs::empty(),
            expr.source,
            types,
            d,
        ) else {
            return error_ty();
        };
        types.function_instantiations.insert(expr.source, instance);
        fn_ty
    } else {
        let mut diag = source_diagnostic(
            HllTypeCheckCode::UndeclaredVariable,
            expr.source,
            format!("undeclared variable '{}'", name),
        );
        let in_scope_vars: Vec<&String> =
            env.variables.iter().flat_map(|scope| scope.keys()).collect();
        if let Some(suggestion) = crate::diagnostics::find_best_match(name, in_scope_vars) {
            diag = diag.with_hint(format!("a variable with a similar name exists: '{}'", suggestion));
        } else if let Some(func_name) =
            crate::diagnostics::find_best_match(name, env.functions.keys())
        {
            diag = diag.with_hint(format!("a function with a similar name exists: '{}'", func_name));
        }
        d.push_error(diag);
        error_ty()
    }
}

fn infer_cast(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    target: &Expr,
    to_ty: &Type,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let from_ty = infer_inner(env, subst, target, types, d);
    let from_resolved = subst.resolve(&from_ty);
    if from_resolved.kind == TypeKind::Error {
        return error_ty();
    }
    let scope = env.current_type_params.clone();
    validate_type(env, to_ty, &scope, d);
    if !is_cast_supported(&from_resolved, to_ty) {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::InvalidCast,
            expr.source,
            format!("cast from {} to {} is not supported", from_resolved, to_ty),
        ));
        return error_ty();
    }
    if matches!(&to_ty.kind, TypeKind::Ref(_, _, _)) && !env.in_unsafe {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::UnsafeRequired,
            expr.source,
            "cast to reference type requires unsafe block".to_string(),
        ));
    }
    to_ty.clone()
}

fn infer_deref(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    target: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let target_ty = infer_inner(env, subst, target, types, d);
    let resolved = subst.resolve(&target_ty);
    if resolved.kind == TypeKind::Error {
        return error_ty();
    }
    match resolved.kind {
        TypeKind::Ref(_, _, inner) => *inner,
        TypeKind::RawPtr(inner) => {
            if !env.in_unsafe {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UnsafeRequired,
                    expr.source,
                    "dereference of raw pointer requires unsafe block".to_string(),
                ));
            }
            *inner
        }
        other => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ExpectedPointer,
                target.source,
                format!("cannot dereference non-pointer type {}", other),
            ));
            error_ty()
        }
    }
}

fn infer_borrow(
    env: &mut TypeEnv,
    subst: &mut Subst,
    kind: RefKind,
    target: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let inner_ty = infer_inner(env, subst, target, types, d);
    ref_ty(kind, inner_ty)
}

fn infer_raw_borrow(
    env: &mut TypeEnv,
    subst: &mut Subst,
    target: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let inner_ty = infer_inner(env, subst, target, types, d);
    raw_ptr_ty(inner_ty)
}

fn infer_call(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    target: &CallTarget,
    generics: &GenericArgs,
    args: &[Expr],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let (fn_ty, receiver_ty) = match target {
        CallTarget::Expr(fn_expr) => {
            let direct_name = match &fn_expr.kind {
                ExprKind::Variable(name)
                    if env.lookup_var(name).is_none() && env.functions.contains_key(name) =>
                {
                    Some(name)
                }
                _ => None,
            };
            if let Some(name) = direct_name {
                if let Some(signature) = env.functions.get(name) {
                    if signature.is_unsafe && !env.in_unsafe {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::UnsafeRequired,
                            fn_expr.source,
                            format!("call to unsafe function '{}' requires unsafe block", name),
                        ));
                    }
                }
                let Some((fn_ty, instance)) = instantiate_function(
                    env,
                    subst,
                    name,
                    generics,
                    fn_expr.source,
                    types,
                    d,
                ) else {
                    return error_ty();
                };
                types.function_instantiations.insert(fn_expr.source, instance);
                record_expression_type(env, types, fn_expr.source, fn_ty.clone());
                (fn_ty, None)
            } else {
                if !generics.is_empty() {
                    d.push_error(source_diagnostic(
                        HllTypeCheckCode::GenericArgsOnFunctionValue,
                        fn_expr.source,
                        "explicit generic arguments require a named function",
                    ));
                    return error_ty();
                }
                (infer_inner(env, subst, fn_expr, types, d), None)
            }
        }
        CallTarget::Receiver {
            receiver,
            method,
            method_source,
            selector_source,
        } => {
            let receiver_ty = infer_inner(env, subst, receiver, types, d);
            let Some((fn_ty, receiver_ty)) = resolve_receiver_call(
                env,
                subst,
                &receiver_ty,
                method,
                generics,
                *method_source,
                *selector_source,
                expr.source,
                types,
                d,
            ) else {
                return error_ty();
            };
            (fn_ty, receiver_ty)
        }
        CallTarget::Qualified {
            self_ty,
            trait_path,
            method,
            method_source,
            selector_source,
        } => {
            let Some(fn_ty) = resolve_qualified_call(
                env,
                subst,
                self_ty,
                trait_path.as_ref(),
                method,
                generics,
                *method_source,
                *selector_source,
                types,
                d,
            ) else {
                return error_ty();
            };
            (fn_ty, None)
        }
        CallTarget::Path {
            target: target_ty,
            member,
            member_source,
            selector_source,
        } => {
            let Some(fn_ty) = resolve_path_call(
                env,
                subst,
                target_ty,
                member,
                generics,
                *member_source,
                *selector_source,
                types,
                d,
            ) else {
                return error_ty();
            };
            (fn_ty, None)
        }
    };
    let resolved = subst.resolve(&fn_ty);
    if resolved.kind == TypeKind::Error {
        return error_ty();
    }
    if let TypeKind::Fn {
        params: param_tys,
        ret: ret_ty,
        ..
    } = resolved.kind
    {
        let implicit_count = usize::from(receiver_ty.is_some());
        if param_tys.len() != args.len() + implicit_count {
            let (expected, found) = if param_tys.len() < implicit_count {
                (param_tys.len(), args.len() + implicit_count)
            } else {
                (param_tys.len() - implicit_count, args.len())
            };
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ArityMismatch,
                expr.source,
                format!("function expected {} arguments, found {}", expected, found),
            ));
            return error_ty();
        }
        let explicit_params = if let Some(receiver_ty) = receiver_ty {
            if let Err(error) = subst.unify(&param_tys[0], &receiver_ty) {
                d.push_error(error.to_diag(match target {
                    CallTarget::Receiver { receiver, .. } => receiver.source,
                    CallTarget::Expr(_) | CallTarget::Qualified { .. } | CallTarget::Path { .. } => {
                        expr.source
                    }
                }));
            }
            &param_tys[1..]
        } else {
            &param_tys[..]
        };
        for (arg, param_ty) in args.iter().zip(explicit_params) {
            check_inner(env, subst, arg, param_ty, types, d);
        }
        if let Some(pending) = types.pending_instantiations.last() {
            for (tp, arg_ty_slot) in pending.type_params.iter().zip(&pending.type_args) {
                let arg_resolved = subst.resolve(arg_ty_slot);
                if let TypeKind::Custom(Instance { name, .. }) = &arg_resolved.kind {
                    if let Some(closure) = env.closures.get(name) {
                        for bound in &tp.bounds.traits {
                            if (bound.trait_path.name == "FnOnce"
                                || bound.trait_path.name == "FnMut"
                                || bound.trait_path.name == "Fn")
                                && bound.trait_path.type_args.len() == 2
                            {
                                let bound_args = substitute_all(
                                    &bound.trait_path.type_args[0],
                                    &pending.type_mapping,
                                    &pending.lifetime_mapping,
                                );
                                let bound_ret = substitute_all(
                                    &bound.trait_path.type_args[1],
                                    &pending.type_mapping,
                                    &pending.lifetime_mapping,
                                );
                                let closure_args = Type::synthesized(TypeKind::Tuple(
                                    closure.params.iter().map(|p| p.ty.clone()).collect(),
                                ));
                                let _ = subst.unify(&bound_args, &closure_args);
                                let _ = subst.unify(&bound_ret, &closure.ret_ty);
                            }
                        }
                    }
                }
            }
        }
        *ret_ty
    } else if let TypeKind::Custom(Instance { name, .. }) = &resolved.kind {
        if let Some(closure) = types.closures_by_struct.get(name).cloned() {
            if closure.params.len() != args.len() {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ArityMismatch,
                    expr.source,
                    format!(
                        "closure expected {} arguments, found {}",
                        closure.params.len(),
                        args.len()
                    ),
                ));
                return error_ty();
            }
            for (arg, param) in args.iter().zip(&closure.params) {
                check_inner(env, subst, arg, &param.ty, types, d);
            }
            closure.ret_ty
        } else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ExpectedFunction,
                expr.source,
                format!("expected function type, found {}", resolved),
            ));
            error_ty()
        }
    } else if let Some((_trait_name, method_name, adjustment, bound_trait)) =
        find_fn_trait_bound(env, &resolved)
    {
        let args_tuple_ty = subst.resolve(&bound_trait.type_args[0]);
        let ret_ty = subst.resolve(&bound_trait.type_args[1]);

        let param_tys = match &args_tuple_ty.kind {
            TypeKind::Tuple(elems) => elems.clone(),
            TypeKind::Var(_) => {
                let elem_tys: Vec<Type> = (0..args.len()).map(|_| subst.fresh_var()).collect();
                let tuple_ty = Type::synthesized(TypeKind::Tuple(elem_tys.clone()));
                let _ = subst.unify(&args_tuple_ty, &tuple_ty);
                elem_tys
            }
            _ => Vec::new(),
        };

        if param_tys.len() != args.len() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ArityMismatch,
                expr.source,
                format!(
                    "function expected {} arguments, found {}",
                    param_tys.len(),
                    args.len()
                ),
            ));
            return error_ty();
        }

        for (arg, param_ty) in args.iter().zip(&param_tys) {
            check_inner(env, subst, arg, param_ty, types, d);
        }

        types.generic_closure_calls.insert(
            expr.source,
            GenericClosureCall {
                trait_path: bound_trait,
                self_ty: resolved.clone(),
                method: Instance::bare(method_name),
                adjustment,
                args_tuple_ty: Type::synthesized(TypeKind::Tuple(param_tys)),
            },
        );

        ret_ty
    } else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ExpectedFunction,
            expr.source,
            format!("expected function type, found {}", resolved),
        ));
        error_ty()
    }
}

fn infer_block(
    env: &mut TypeEnv,
    subst: &mut Subst,
    stmts: &[Stmt],
    last_expr: Option<&Expr>,
    is_unsafe: bool,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let old_unsafe = env.in_unsafe;
    if is_unsafe {
        env.in_unsafe = true;
    }
    env.push_scope();
    check_block_statements(env, subst, stmts, types, d);
    let res = if let Some(last) = last_expr {
        infer_inner(env, subst, last, types, d)
    } else {
        unit_ty()
    };
    env.pop_scope();
    env.in_unsafe = old_unsafe;
    res
}

fn infer_if(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    cond: &Expr,
    true_block: &Expr,
    false_block: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    check_inner(env, subst, cond, &bool_ty(), types, d);
    let t1 = infer_inner(env, subst, true_block, types, d);
    let t2 = infer_inner(env, subst, false_block, types, d);
    if let Err(e) = subst.unify(&t1, &t2) {
        let diag = e
            .to_diag(expr.source)
            .with_secondary(true_block.source, "expected because of this 'then' branch");
        d.push_error(diag);
    }
    subst.resolve(&t1)
}

fn infer_loop(
    env: &mut TypeEnv,
    subst: &mut Subst,
    body: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    check_inner(env, subst, body, &unit_ty(), types, d);
    never_ty()
}

fn infer_break(
    env: &mut TypeEnv,
    subst: &mut Subst,
    val_expr: Option<&Expr>,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    if let Some(val) = val_expr {
        infer_inner(env, subst, val, types, d);
    }
    never_ty()
}

fn infer_return(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    val_expr: Option<&Expr>,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let ret_ty = env.current_ret_ty.clone().unwrap_or_else(unit_ty);
    if let Some(val) = val_expr {
        check_inner(env, subst, val, &ret_ty, types, d);
    } else if let Err(e) = subst.unify(&ret_ty, &unit_ty()) {
        d.push_error(e.to_diag(expr.source));
    }
    never_ty()
}

fn infer_assign(
    env: &mut TypeEnv,
    subst: &mut Subst,
    lhs: &Expr,
    rhs: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let lhs_ty = infer_inner(env, subst, lhs, types, d);
    check_inner(env, subst, rhs, &lhs_ty, types, d);
    unit_ty()
}

fn infer_match(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    target: &Expr,
    arms: &[(Pattern, Expr)],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let target_ty = infer_inner(env, subst, target, types, d);
    let resolved = subst.resolve(&target_ty);
    if resolved.kind == TypeKind::Error {
        return error_ty();
    }
    if let TypeKind::Custom(Instance {
        name: enum_name,
        lifetime_args,
        type_args: args,
    }) = resolved.kind
    {
        let e_decl = match env.enums.get(&enum_name).cloned() {
            Some(decl) => decl,
            None => {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UndeclaredEnum,
                    expr.source,
                    format!("undeclared enum '{}'", enum_name),
                ));
                return error_ty();
            }
        };
        let mapping = match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.source, d) {
            Some(m) => m,
            None => return error_ty(),
        };
        let Some(lifetime_mapping) =
            build_lifetime_mapping(&e_decl.lifetime_params, &lifetime_args)
        else {
            return error_ty();
        };
        let mut arm_tys = Vec::new();
        for (pattern, body) in arms {
            let Pattern::Variant(variant, bound_var) = pattern;
            if let Some(v) = e_decl.variants.iter().find(|var_decl| var_decl.name == *variant) {
                env.push_scope();
                if let Some(var_name) = bound_var {
                    env.insert_var(
                        var_name.clone(),
                        substitute_all(&v.ty, &mapping, &lifetime_mapping),
                    );
                }
                let body_ty = infer_inner(env, subst, body, types, d);
                env.pop_scope();
                arm_tys.push(body_ty);
            } else {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::NoSuchVariant,
                    expr.source,
                    format!("enum '{}' has no variant '{}'", enum_name, variant),
                ));
                arm_tys.push(error_ty());
            }
        }
        if arm_tys.is_empty() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::EmptySwitch,
                expr.source,
                "empty switch expression",
            ));
            return error_ty();
        }
        let first_ty = arm_tys[0].clone();
        for ty in &arm_tys[1..] {
            if let Err(e) = subst.unify(&first_ty, ty) {
                d.push_error(e.to_diag(expr.source));
            }
        }
        subst.resolve(&first_ty)
    } else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ExpectedEnum,
            expr.source,
            format!("expected enum type for switch target, found {}", resolved),
        ));
        error_ty()
    }
}

fn infer_struct_constr(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    name: &str,
    fields: &[(String, Expr)],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let s_decl = match env.structs.get(name).cloned() {
        Some(decl) => decl,
        None => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredStruct,
                expr.source,
                format!("undeclared struct '{}'", name),
            ));
            return error_ty();
        }
    };

    if fields.len() != s_decl.fields.len() {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::StructFieldCountMismatch,
            expr.source,
            format!(
                "struct '{}' has {} fields, but {} were initialized",
                name,
                s_decl.fields.len(),
                fields.len()
            ),
        ));
        return error_ty();
    }

    let type_args: Vec<Type> = s_decl
        .type_params
        .iter()
        .map(|_| subst.fresh_var())
        .collect();
    let lifetime_args = s_decl
        .lifetime_params
        .iter()
        .map(|_| {
            types
                .fresh_inferred_lifetime(env, subst, expr.source)
                .expect("constructor expression outside a function body")
        })
        .collect::<Vec<_>>();
    let mapping: HashMap<String, Type> = s_decl
        .type_params
        .iter()
        .map(|tp| tp.name.clone())
        .zip(type_args.iter().cloned())
        .collect();
    let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = s_decl
        .lifetime_params
        .iter()
        .map(|lp| lp.lifetime.clone())
        .zip(lifetime_args.iter().cloned())
        .collect();

    for f_decl in &s_decl.fields {
        let mut matches = fields.iter().filter(|(fname, _)| fname == &f_decl.name);
        let Some((_, val_expr)) = matches.next() else {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::MissingField,
                expr.source,
                format!(
                    "missing field '{}' in constructor for '{}'",
                    f_decl.name, name
                ),
            ));
            return error_ty();
        };
        if matches.next().is_some() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::DuplicateField,
                expr.source,
                format!(
                    "duplicate field '{}' in constructor for '{}'",
                    f_decl.name, name
                ),
            ));
            return error_ty();
        }
        let expected = substitute_all(&f_decl.ty, &mapping, &lifetime_mapping);
        check_inner(env, subst, val_expr, &expected, types, d);
    }

    if !s_decl.type_params.is_empty() {
        types.pending_instantiations.push(PendingInstantiation {
            source: expr.source,
            function_name: name.to_string(),
            caller_type_params: env.current_type_params.clone(),
            type_params: s_decl.type_params.clone(),
            type_args: type_args.clone(),
            type_mapping: mapping,
            lifetime_mapping,
        });
    }

    Type::synthesized(TypeKind::Custom(Instance::new(
        name.to_string(),
        lifetime_args,
        type_args,
    )))
}

fn infer_enum_constr(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    enum_name: &str,
    variant_name: &str,
    payload: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let e_decl = match env.enums.get(enum_name).cloned() {
        Some(decl) => decl,
        None => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::UndeclaredEnum,
                expr.source,
                format!("undeclared enum '{}'", enum_name),
            ));
            return error_ty();
        }
    };

    let variant_decl = match e_decl.variants.iter().find(|v| v.name == variant_name) {
        Some(v) => v.clone(),
        None => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::NoSuchVariant,
                expr.source,
                format!("enum '{}' has no variant '{}'", enum_name, variant_name),
            ));
            return error_ty();
        }
    };

    let type_args: Vec<Type> = e_decl
        .type_params
        .iter()
        .map(|_| subst.fresh_var())
        .collect();
    let lifetime_args = e_decl
        .lifetime_params
        .iter()
        .map(|_| {
            types
                .fresh_inferred_lifetime(env, subst, expr.source)
                .expect("constructor expression outside a function body")
        })
        .collect::<Vec<_>>();
    let mapping: HashMap<String, Type> = e_decl
        .type_params
        .iter()
        .map(|tp| tp.name.clone())
        .zip(type_args.iter().cloned())
        .collect();
    let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = e_decl
        .lifetime_params
        .iter()
        .map(|lp| lp.lifetime.clone())
        .zip(lifetime_args.iter().cloned())
        .collect();
    let expected_payload = substitute_all(&variant_decl.ty, &mapping, &lifetime_mapping);
    check_inner(env, subst, payload, &expected_payload, types, d);

    if !e_decl.type_params.is_empty() {
        types.pending_instantiations.push(PendingInstantiation {
            source: expr.source,
            function_name: format!("{}::{}", enum_name, variant_name),
            caller_type_params: env.current_type_params.clone(),
            type_params: e_decl.type_params.clone(),
            type_args: type_args.clone(),
            type_mapping: mapping,
            lifetime_mapping,
        });
    }

    Type::synthesized(TypeKind::Custom(Instance::new(
        enum_name.to_string(),
        lifetime_args,
        type_args,
    )))
}

fn infer_path(
    env: &TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    target_ty: &Type,
    member: &str,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let Some(fn_ty) = resolve_path_call(
        env,
        subst,
        target_ty,
        member,
        &GenericArgs::empty(),
        expr.source,
        expr.source,
        types,
        d,
    ) else {
        return error_ty();
    };
    if let TypeKind::Fn { params, ret: ret_ty, .. } = subst.resolve(&fn_ty).kind {
        if !params.is_empty() {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ArityMismatch,
                expr.source,
                format!("constructor '{}::{}' requires payload argument", target_ty, member),
            ));
            return error_ty();
        }
        *ret_ty
    } else {
        error_ty()
    }
}

fn infer_array(
    env: &mut TypeEnv,
    subst: &mut Subst,
    elements: &[Expr],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    if elements.is_empty() {
        let elem_ty = subst.fresh_var();
        array_ty(elem_ty, 0)
    } else {
        let first_ty = infer_inner(env, subst, &elements[0], types, d);
        for el in &elements[1..] {
            check_inner(env, subst, el, &first_ty, types, d);
        }
        array_ty(first_ty, array_len(elements.len()))
    }
}

fn infer_tuple(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    elements: &[Expr],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    if elements.len() > 12 {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::TupleArityExceeded,
            expr.source,
            format!("tuple arity {} exceeds maximum of 12", elements.len()),
        ));
    }
    let elem_types = elements
        .iter()
        .map(|el| infer_inner(env, subst, el, types, d))
        .collect::<Vec<_>>();
    Type::synthesized(TypeKind::Tuple(elem_types))
}

fn infer_array_index(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    arr: &Expr,
    idx: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let arr_ty = infer_inner(env, subst, arr, types, d);
    let resolved = subst.resolve(&arr_ty);
    if resolved.kind == TypeKind::Error {
        return error_ty();
    }
    if let TypeKind::Array(inner, _) = resolved.kind {
        let idx_ty = infer_inner(env, subst, idx, types, d);
        let idx_resolved = subst.resolve(&idx_ty);
        match &idx_resolved.kind {
            TypeKind::Int(_) => {}
            TypeKind::Var(_) | TypeKind::IntVar(_) => {
                if let Err(e) = subst.unify(&int_ty(crate::mir::ast::IntTy::I64), &idx_resolved) {
                    d.push_error(e.to_diag(expr.source));
                }
            }
            TypeKind::Error => {}
            other => {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ArrayIndexNotInt,
                    idx.source,
                    format!("array index must be an integer, found {}", other),
                ));
                return error_ty();
            }
        }
        *inner
    } else {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ExpectedArray,
            arr.source,
            format!("expected array type, found {}", resolved),
        ));
        error_ty()
    }
}

pub(crate) fn check_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    expected: &Type,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) {
    let resolved_expected = subst.resolve(expected);
    match (&expr.kind, &resolved_expected.kind) {
        (ExprKind::Block(stmts, last_expr, is_unsafe), _) => {
            let old_unsafe = env.in_unsafe;
            if *is_unsafe {
                env.in_unsafe = true;
            }
            env.push_scope();
            check_block_statements(env, subst, stmts, types, d);
            let errors_before = d.error_count();
            if let Some(last) = last_expr {
                check_inner(env, subst, last, &resolved_expected, types, d);
            } else if let Err(e) = subst.unify(&resolved_expected, &unit_ty()) {
                d.push_error(e.to_diag(expr.source));
            }
            env.pop_scope();
            env.in_unsafe = old_unsafe;
            if d.error_count() == errors_before {
                record_expression_type(env, types, expr.source, resolved_expected.clone());
            }
        }
        (ExprKind::If(cond, true_block, false_block), _) => {
            check_inner(env, subst, cond, &bool_ty(), types, d);
            check_inner(env, subst, true_block, &resolved_expected, types, d);
            check_inner(env, subst, false_block, &resolved_expected, types, d);
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Match(target, arms), _) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved.kind == TypeKind::Error {
                return;
            }
            if arms.is_empty() {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::EmptySwitch,
                    expr.source,
                    "empty switch expression",
                ));
                return;
            }
            if let TypeKind::Custom(Instance {
                name: enum_name,
                lifetime_args,
                type_args: args,
            }) = resolved.kind
            {
                let e_decl = match env.enums.get(&enum_name).cloned() {
                    Some(decl) => decl,
                    None => {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::UndeclaredEnum,
                            expr.source,
                            format!("undeclared enum '{}'", enum_name),
                        ));
                        return;
                    }
                };
                let mapping = match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.source, d) {
                    Some(m) => m,
                    None => return,
                };
                let Some(lifetime_mapping) =
                    build_lifetime_mapping(&e_decl.lifetime_params, &lifetime_args)
                else {
                    return;
                };
                for (pattern, body) in arms {
                    let Pattern::Variant(variant, bound_var) = pattern;
                    if let Some(v) = e_decl.variants.iter().find(|var_decl| var_decl.name == *variant) {
                        env.push_scope();
                        if let Some(var_name) = bound_var {
                            env.insert_var(
                                var_name.clone(),
                                substitute_all(&v.ty, &mapping, &lifetime_mapping),
                            );
                        }
                        check_inner(env, subst, body, &resolved_expected, types, d);
                        env.pop_scope();
                    } else {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::NoSuchVariant,
                            expr.source,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        ));
                    }
                }
                record_expression_type(env, types, expr.source, resolved_expected.clone());
            } else {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ExpectedEnum,
                    expr.source,
                    format!("expected enum type for switch target, found {}", resolved),
                ));
            }
        }
        (ExprKind::Literal(Literal::Int(_val, None)), TypeKind::Int(_ty)) => {
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Literal(Literal::Float(_val, None)), TypeKind::Float(_ty)) => {
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Array(elements), TypeKind::Array(expected_elem, expected_size)) => {
            let actual_size = array_len(elements.len());
            if actual_size != *expected_size {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ArrayLengthMismatch,
                    expr.source,
                    format!(
                        "expected array of length {}, found length {}",
                        expected_size,
                        elements.len()
                    ),
                ));
                return;
            }
            for el in elements {
                check_inner(env, subst, el, expected_elem, types, d);
            }
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        _ => {
            let inferred = infer_inner(env, subst, expr, types, d);
            if let Err(e) = subst.unify(&resolved_expected, &inferred) {
                let mut diag = e.to_diag(expr.source);
                if matches!(resolved_expected.source, SourceInfo::Written(_))
                    && resolved_expected.source != expr.source
                {
                    diag = diag.with_secondary(
                        resolved_expected.source,
                        "expected due to this type constraint",
                    );
                }
                d.push_error(diag);
            }
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
    }
}

pub(crate) fn check_block_statements(
    env: &mut TypeEnv,
    subst: &mut Subst,
    statements: &[Stmt],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) {
    for statement in statements {
        match statement {
            Stmt::Let {
                name,
                ty,
                init,
                source,
                ..
            } => {
                if let Some(annotation) = ty {
                    validate_type(env, annotation, &env.current_type_params, d);
                }
                let binding_type = match (ty, init) {
                    (Some(annotation), Some(initializer)) => {
                        check_inner(env, subst, initializer, annotation, types, d);
                        annotation.clone()
                    }
                    (Some(annotation), None) => annotation.clone(),
                    (None, Some(initializer)) => infer_inner(env, subst, initializer, types, d),
                    (None, None) => {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::AmbiguousType,
                            *source,
                            "let binding without initializer requires an explicit type annotation",
                        ));
                        error_ty()
                    }
                };
                env.insert_var(name.clone(), binding_type);
            }
            Stmt::Defer { body, .. } => {
                check_no_control_flow(body, 0, d);
                let body_type = infer_inner(env, subst, body, types, d);
                if let Err(error) = subst.unify(&unit_ty(), &body_type) {
                    d.push_error(error.to_diag(body.source));
                }
            }
            Stmt::Expr(expression) => {
                infer_inner(env, subst, expression, types, d);
            }
        }
    }
}

pub(crate) fn check_no_control_flow(expr: &Expr, loop_depth: usize, d: &mut Diagnostics) {
    match &expr.kind {
        ExprKind::Break(_) => {
            if loop_depth == 0 {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.source,
                    "break is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Continue => {
            if loop_depth == 0 {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.source,
                    "continue is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Return(_) => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ControlFlowInDefer,
                expr.source,
                "return is not allowed inside defer".to_string(),
            ));
        }
        ExprKind::Block(stmts, last, _) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let {
                        init: Some(init), ..
                    } => check_no_control_flow(init, loop_depth, d),
                    Stmt::Let { init: None, .. } => {}
                    Stmt::Defer { body, .. } => check_no_control_flow(body, loop_depth, d),
                    Stmt::Expr(e) => check_no_control_flow(e, loop_depth, d),
                }
            }
            if let Some(e) = last {
                check_no_control_flow(e, loop_depth, d);
            }
        }
        ExprKind::If(cond, thn, els) => {
            check_no_control_flow(cond, loop_depth, d);
            check_no_control_flow(thn, loop_depth, d);
            check_no_control_flow(els, loop_depth, d);
        }
        ExprKind::Loop(body) => {
            check_no_control_flow(body, loop_depth + 1, d);
        }
        ExprKind::Assign(lhs, rhs) => {
            check_no_control_flow(lhs, loop_depth, d);
            check_no_control_flow(rhs, loop_depth, d);
        }
        ExprKind::Binary(lhs, _, rhs) => {
            check_no_control_flow(lhs, loop_depth, d);
            check_no_control_flow(rhs, loop_depth, d);
        }
        ExprKind::Unary(_, operand) => {
            check_no_control_flow(operand, loop_depth, d);
        }
        ExprKind::FieldAccess(base, _) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Cast(base, _) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::ArrayIndex(base, index) => {
            check_no_control_flow(base, loop_depth, d);
            check_no_control_flow(index, loop_depth, d);
        }
        ExprKind::Deref(base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Borrow(_, base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::RawBorrow(base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Call(target, _generics, args) => {
            match target {
                CallTarget::Expr(callee) => check_no_control_flow(callee, loop_depth, d),
                CallTarget::Receiver { receiver, .. } => {
                    check_no_control_flow(receiver, loop_depth, d)
                }
                CallTarget::Qualified { .. } | CallTarget::Path { .. } => {}
            }
            for arg in args {
                check_no_control_flow(arg, loop_depth, d);
            }
        }
        ExprKind::Path(_, _) => {}
        ExprKind::StructConstr(_, fields) => {
            for (_, f_init) in fields {
                check_no_control_flow(f_init, loop_depth, d);
            }
        }
        ExprKind::EnumConstr(_, _, payload) => {
            check_no_control_flow(payload, loop_depth, d);
        }
        ExprKind::Array(elems) | ExprKind::Tuple(elems) => {
            for elem in elems {
                check_no_control_flow(elem, loop_depth, d);
            }
        }
        ExprKind::Match(target, arms) => {
            check_no_control_flow(target, loop_depth, d);
            for (_, arm_expr) in arms {
                check_no_control_flow(arm_expr, loop_depth, d);
            }
        }
        ExprKind::Literal(_) | ExprKind::Variable(_) => {}
        ExprKind::Lambda { body, .. } => {
            check_no_control_flow(body, loop_depth, d);
        }
    }
}

pub(crate) fn infer_lambda(
    env: &mut TypeEnv,
    subst: &mut Subst,
    lambda_expr: &Expr,
    params: &[LambdaParam],
    ret_ty: Option<&Type>,
    body: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let closure_id = types.next_closure_id;
    types.next_closure_id += 1;
    let struct_name = format!("$closure_{}", closure_id);
    let fn_name = format!("$closure_{}_call", closure_id);

    let mut bound = HashSet::new();
    for p in params {
        bound.insert(p.name.clone());
    }
    let mut free_vars = IndexMap::new();
    closures::collect_free_vars(body, &mut bound, &mut free_vars);

    let mut captures = Vec::new();
    for (name, source) in free_vars {
        if let Some(ty) = env.lookup_var(&name) {
            let field_markers = env.class_of(&ty, &HashMap::new());
            captures.push(ClosureCapture {
                name,
                is_copy: field_markers.declared(Marker::Copy),
                is_drop: field_markers.declared(Marker::Drop),
                ty,
                source,
            });
        }
    }

    let mut typed_params = Vec::new();
    for p in params {
        let ty = if let Some(annotated_ty) = &p.ty {
            let scope = env.current_type_params.clone();
            validate_type(env, annotated_ty, &scope, d);
            annotated_ty.clone()
        } else {
            subst.fresh_var()
        };
        typed_params.push(Param {
            name: p.name.clone(),
            ty,
            source: p.source,
        });
    }

    let expected_ret_ty = if let Some(annotated_ret) = ret_ty {
        let scope = env.current_type_params.clone();
        validate_type(env, annotated_ret, &scope, d);
        annotated_ret.clone()
    } else {
        subst.fresh_var()
    };

    env.push_scope();
    let old_ret_ty = env.current_ret_ty.replace(expected_ret_ty.clone());
    for p in &typed_params {
        env.insert_var(p.name.clone(), p.ty.clone());
    }
    check_inner(env, subst, body, &expected_ret_ty, types, d);
    env.pop_scope();
    env.current_ret_ty = old_ret_ty;

    let mut lts = IndexSet::new();
    let mut counter = 0;
    for c in &mut captures {
        closures::assign_closure_capture_lifetimes(&mut c.ty, &mut lts, &mut counter);
    }
    let lifetime_args: Vec<Lifetime> = lts.into_iter().collect();
    let lifetime_params: Vec<LifetimeParam> = lifetime_args
        .iter()
        .map(|lt| {
            LifetimeParam::generated(
                lt.clone(),
                crate::common::GeneratedKind::HllDesugaring,
                lambda_expr.source.span(),
            )
        })
        .collect();

    let mut is_copy = true;
    let mut is_drop = true;
    let mut is_move = true;
    for c in &captures {
        let field_markers = env.class_of(&c.ty, &env.current_type_params);
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
    let markers = Markers::from_iter(derived);

    let type_params = env.current_generic_params.clone();
    let type_args: Vec<Type> = type_params
        .iter()
        .map(|p| Type::synthesized(TypeKind::Param(p.name.clone())))
        .collect();

    let fn_kind = crate::hll::derive::infer_closure_fn_kind(&captures, body, env);
    let resolved_params: Vec<Param> = typed_params
        .iter()
        .map(|p| Param {
            name: p.name.clone(),
            ty: subst.resolve(&p.ty),
            source: p.source,
        })
        .collect();
    let resolved_ret = subst.resolve(&expected_ret_ty);

    let closure_info = ClosureInfo {
        struct_name: struct_name.clone(),
        fn_name,
        params: resolved_params,
        ret_ty: resolved_ret,
        captures,
        source: lambda_expr.source,
        body: body.clone(),
        lifetime_params,
        lifetime_args: lifetime_args.clone(),
        type_params,
        type_args: type_args.clone(),
        markers,
        is_auto_clone: false,
        is_auto_destroy: false,
        fn_kind,
    };

    let struct_decl = closure_info.to_struct_decl();
    env.structs.insert(struct_decl.name.clone(), struct_decl);
    env.closures.insert(closure_info.struct_name.clone(), closure_info.clone());

    types.closures.insert(lambda_expr.source, closure_info.clone());
    types.closures_by_struct.insert(struct_name.clone(), closure_info.clone());

    closures::register_closure_impls(env, &closure_info, lambda_expr.source);

    Type::synthesized(TypeKind::Custom(Instance::new(
        struct_name,
        lifetime_args,
        type_args,
    )))
}

