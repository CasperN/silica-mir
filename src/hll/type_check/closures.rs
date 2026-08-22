use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::common::{Abi, Lifetime, Linkage, RefKind, SourceInfo};
use crate::hll::ast::{
    Expr, ExprKind, FnDecl, ImplBlock, Instance, Param, Pattern, Stmt, Type, TypeKind,
};
use crate::hll::type_check::env::{ClosureInfo, TypeEnv};

pub(crate) fn collect_free_vars(
    expr: &Expr,
    bound: &mut HashSet<String>,
    free: &mut IndexMap<String, SourceInfo>,
) {
    match &expr.kind {
        ExprKind::Literal(_) => {}
        ExprKind::Variable(name) => {
            if !bound.contains(name) {
                free.entry(name.clone()).or_insert(expr.source);
            }
        }
        ExprKind::FieldAccess(target, _)
        | ExprKind::Cast(target, _)
        | ExprKind::Deref(target)
        | ExprKind::Borrow(_, target)
        | ExprKind::RawBorrow(target) => {
            collect_free_vars(target, bound, free);
        }
        ExprKind::Call(target, _, args) => {
            match target {
                crate::hll::ast::CallTarget::Expr(e) => collect_free_vars(e, bound, free),
                crate::hll::ast::CallTarget::Receiver { receiver, .. } => {
                    collect_free_vars(receiver, bound, free)
                }
                crate::hll::ast::CallTarget::Qualified { .. }
                | crate::hll::ast::CallTarget::Path { .. } => {}
            }
            for arg in args {
                collect_free_vars(arg, bound, free);
            }
        }
        ExprKind::Path(_, _) => {}
        ExprKind::Block(stmts, last_expr, _) => {
            let initial_bound = bound.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { name, init, .. } => {
                        if let Some(init) = init {
                            collect_free_vars(init, bound, free);
                        }
                        bound.insert(name.clone());
                    }
                    Stmt::Defer { body, .. } => {
                        collect_free_vars(body, bound, free);
                    }
                    Stmt::Expr(e) => {
                        collect_free_vars(e, bound, free);
                    }
                }
            }
            if let Some(last) = last_expr {
                collect_free_vars(last, bound, free);
            }
            *bound = initial_bound;
        }
        ExprKind::If(cond, thn, els) => {
            collect_free_vars(cond, bound, free);
            collect_free_vars(thn, bound, free);
            collect_free_vars(els, bound, free);
        }
        ExprKind::Loop(body) => {
            collect_free_vars(body, bound, free);
        }
        ExprKind::Break(val) | ExprKind::Return(val) => {
            if let Some(val) = val {
                collect_free_vars(val, bound, free);
            }
        }
        ExprKind::Continue => {}
        ExprKind::Assign(lhs, rhs) => {
            collect_free_vars(lhs, bound, free);
            collect_free_vars(rhs, bound, free);
        }
        ExprKind::Match(target, arms) => {
            collect_free_vars(target, bound, free);
            for (pat, arm_expr) in arms {
                let initial_bound = bound.clone();
                if let Pattern::Variant(_, Some(var_name)) = pat {
                    bound.insert(var_name.clone());
                }
                collect_free_vars(arm_expr, bound, free);
                *bound = initial_bound;
            }
        }
        ExprKind::StructConstr(_, fields) => {
            for (_, field_expr) in fields {
                collect_free_vars(field_expr, bound, free);
            }
        }
        ExprKind::EnumConstr(_, _, payload) => {
            collect_free_vars(payload, bound, free);
        }
        ExprKind::Array(elems) | ExprKind::Tuple(elems) => {
            for elem in elems {
                collect_free_vars(elem, bound, free);
            }
        }
        ExprKind::ArrayIndex(target, idx) => {
            collect_free_vars(target, bound, free);
            collect_free_vars(idx, bound, free);
        }
        ExprKind::Binary(lhs, _, rhs) => {
            collect_free_vars(lhs, bound, free);
            collect_free_vars(rhs, bound, free);
        }
        ExprKind::Unary(_, operand) => {
            collect_free_vars(operand, bound, free);
        }
        ExprKind::Lambda { params, body, .. } => {
            let initial_bound = bound.clone();
            for p in params {
                bound.insert(p.name.clone());
            }
            collect_free_vars(body, bound, free);
            *bound = initial_bound;
        }
    }
}

pub(crate) fn assign_closure_capture_lifetimes(
    ty: &mut Type,
    lts: &mut IndexSet<Lifetime>,
    counter: &mut usize,
) {
    match &mut ty.kind {
        TypeKind::Ref(_, slot, inner) => {
            if slot.is_none() {
                let lt = Lifetime(format!("s{}", *counter));
                *counter += 1;
                *slot = Some(lt.clone());
                lts.insert(lt);
            } else if let Some(lt) = slot {
                lts.insert(lt.clone());
            }
            assign_closure_capture_lifetimes(inner, lts, counter);
        }
        TypeKind::Custom(Instance {
            lifetime_args,
            type_args,
            ..
        }) => {
            for lt in lifetime_args {
                lts.insert(lt.clone());
            }
            for t in type_args {
                assign_closure_capture_lifetimes(t, lts, counter);
            }
        }
        TypeKind::Array(elem, _) | TypeKind::RawPtr(elem) => {
            assign_closure_capture_lifetimes(elem, lts, counter);
        }
        TypeKind::Tuple(types) => {
            for t in types {
                assign_closure_capture_lifetimes(t, lts, counter);
            }
        }
        TypeKind::Fn { params, ret, .. } => {
            for p in params {
                assign_closure_capture_lifetimes(p, lts, counter);
            }
            assign_closure_capture_lifetimes(ret, lts, counter);
        }
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Var(_)
        | TypeKind::IntVar(_)
        | TypeKind::FloatVar(_)
        | TypeKind::Param(_)
        | TypeKind::Error => {}
    }
}

pub(crate) fn register_closure_impls(
    env: &mut TypeEnv,
    closure_info: &ClosureInfo,
    source: SourceInfo,
) {
    let target_ty = Type::synthesized(TypeKind::Custom(Instance::new(
        closure_info.struct_name.clone(),
        closure_info.lifetime_args.clone(),
        closure_info.type_args.clone(),
    )));
    let args_ty = Type::synthesized(TypeKind::Tuple(
        closure_info.params.iter().map(|p| p.ty.clone()).collect(),
    ));

    let call_once_decl = FnDecl {
        linkage: Linkage::Local,
        abi: Abi::Silica,
        is_unsafe: false,
        name: "call_once".to_string(),
        lifetime_params: Vec::new(),
        outlives: Vec::new(),
        type_params: Vec::new(),
        params: vec![
            Param {
                name: "recv".to_string(),
                ty: target_ty.clone(),
                source,
            },
            Param {
                name: "args".to_string(),
                ty: args_ty.clone(),
                source,
            },
        ],
        ret_ty: closure_info.ret_ty.clone(),
        body: None,
        source,
    };

    env.impls.push(ImplBlock {
        lifetime_params: closure_info.lifetime_params.clone(),
        outlives: Vec::new(),
        type_params: closure_info.type_params.clone(),
        trait_path: Some(Instance::new(
            "FnOnce".to_string(),
            Vec::new(),
            vec![args_ty.clone(), closure_info.ret_ty.clone()],
        )),
        target: target_ty.clone(),
        methods: vec![call_once_decl],
        source,
    });
    if matches!(
        closure_info.fn_kind,
        crate::hll::derive::FnKind::Fn | crate::hll::derive::FnKind::FnMut
    ) {
        let call_mut_decl = FnDecl {
            linkage: Linkage::Local,
            abi: Abi::Silica,
            is_unsafe: false,
            name: "call_mut".to_string(),
            lifetime_params: Vec::new(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            params: vec![
                Param {
                    name: "recv".to_string(),
                    ty: Type::synthesized(TypeKind::Ref(
                        RefKind::Mut,
                        None,
                        Box::new(target_ty.clone()),
                    )),
                    source,
                },
                Param {
                    name: "args".to_string(),
                    ty: args_ty.clone(),
                    source,
                },
            ],
            ret_ty: closure_info.ret_ty.clone(),
            body: None,
            source,
        };
        env.impls.push(ImplBlock {
            lifetime_params: closure_info.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: closure_info.type_params.clone(),
            trait_path: Some(Instance::new(
                "FnMut".to_string(),
                Vec::new(),
                vec![args_ty.clone(), closure_info.ret_ty.clone()],
            )),
            target: target_ty.clone(),
            methods: vec![call_mut_decl],
            source,
        });
    }
    if closure_info.fn_kind == crate::hll::derive::FnKind::Fn {
        let call_decl = FnDecl {
            linkage: Linkage::Local,
            abi: Abi::Silica,
            is_unsafe: false,
            name: "call".to_string(),
            lifetime_params: Vec::new(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            params: vec![
                Param {
                    name: "recv".to_string(),
                    ty: Type::synthesized(TypeKind::Ref(
                        RefKind::Shared,
                        None,
                        Box::new(target_ty.clone()),
                    )),
                    source,
                },
                Param {
                    name: "args".to_string(),
                    ty: args_ty.clone(),
                    source,
                },
            ],
            ret_ty: closure_info.ret_ty.clone(),
            body: None,
            source,
        };
        env.impls.push(ImplBlock {
            lifetime_params: closure_info.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: closure_info.type_params.clone(),
            trait_path: Some(Instance::new(
                "Fn".to_string(),
                Vec::new(),
                vec![args_ty, closure_info.ret_ty.clone()],
            )),
            target: target_ty,
            methods: vec![call_decl],
            source,
        });
    }
}
