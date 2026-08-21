//! Trait derivation machinery for HLL structs, enums, and closures.
//!
//! Provides capability queries (`can_derive_*`) and MIR synthesizers (`derive_*_mir`)
//! for Silica's compiler-supported auto-traits (`AutoClone`, `AutoDestroy`, etc.).

use crate::common::{Abi, Linkage, Marker, Markers, RefKind, SourceInfo};
use crate::hll::ast::{EnumDecl, StructDecl, StructField, TypeKind};
use crate::hll::lowering::lower_type;
use crate::hll::type_check::TypeEnv;
use crate::mir::ast::{self as mir, BasicBlock, DeclMeta, GenericParams, Place};
use crate::mir::helpers::*;

// ---------------- Capability Queries ----------------

/// Check if any field holds an unfulfilled linear/directional obligation (`&out` or `&drop`).
pub fn has_linear_reference_obligation(fields: &[StructField]) -> bool {
    fields.iter().any(|f| {
        matches!(f.ty.kind, TypeKind::Ref(RefKind::Out | RefKind::Drop, _, _))
    })
}

pub fn can_derive_auto_clone(s: &StructDecl, env: &TypeEnv) -> bool {
    s.fields
        .iter()
        .all(|f| env.type_satisfies_trait(&f.ty, &crate::hll::ast::Instance::bare("AutoClone")))
}

pub fn can_derive_auto_clone_enum(e: &EnumDecl, env: &TypeEnv) -> bool {
    e.variants
        .iter()
        .all(|v| env.type_satisfies_trait(&v.ty, &crate::hll::ast::Instance::bare("AutoClone")))
}

pub fn can_derive_auto_destroy(s: &StructDecl, env: &TypeEnv) -> bool {
    !has_linear_reference_obligation(&s.fields)
        && s.fields.iter().all(|f| {
            env.type_satisfies_trait(&f.ty, &crate::hll::ast::Instance::bare("AutoDestroy"))
        })
}

pub fn can_derive_auto_destroy_enum(e: &EnumDecl, env: &TypeEnv) -> bool {
    e.variants
        .iter()
        .all(|v| env.type_satisfies_trait(&v.ty, &crate::hll::ast::Instance::bare("AutoDestroy")))
}

// ---------------- Closure Calling Capability (Fn / FnMut / FnOnce) ----------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FnKind {
    /// Read-only access to captures: callable via `&self`.
    Fn,
    /// Mutable access to captures without consuming: callable via `&mut self`.
    FnMut,
    /// Consumes non-AutoClone / linear captures: callable only via `self`.
    FnOnce,
}

/// Infer whether a closure qualifies as `Fn`, `FnMut`, or `FnOnce`.
pub fn infer_closure_fn_kind(
    captures: &[crate::hll::type_check::ClosureCapture],
    body: &crate::hll::ast::Expr,
    env: &TypeEnv,
) -> FnKind {
    let has_linear_ref = captures.iter().any(|c| {
        matches!(c.ty.kind, TypeKind::Ref(RefKind::Out | RefKind::Drop, _, _))
    });
    if has_linear_ref {
        return FnKind::FnOnce;
    }

    let has_mut_ref = captures.iter().any(|c| {
        matches!(c.ty.kind, TypeKind::Ref(RefKind::Mut, _, _))
    });

    let mut tracker = ClosureUsageTracker {
        capture_names: captures.iter().map(|c| c.name.clone()).collect(),
        captures_by_name: captures.iter().map(|c| (c.name.clone(), c.clone())).collect(),
        local_scopes: Vec::new(),
        has_mutations: has_mut_ref,
        has_linear_moves: false,
    };
    tracker.walk_expr(body, env);
    if tracker.has_linear_moves {
        FnKind::FnOnce
    } else if tracker.has_mutations {
        FnKind::FnMut
    } else {
        FnKind::Fn
    }
}

struct ClosureUsageTracker {
    capture_names: std::collections::HashSet<String>,
    captures_by_name: std::collections::HashMap<String, crate::hll::type_check::ClosureCapture>,
    local_scopes: Vec<std::collections::HashSet<String>>,
    has_mutations: bool,
    has_linear_moves: bool,
}

impl ClosureUsageTracker {
    fn is_capture(&self, name: &str) -> bool {
        if !self.capture_names.contains(name) {
            return false;
        }
        for scope in self.local_scopes.iter().rev() {
            if scope.contains(name) {
                return false;
            }
        }
        true
    }

    fn push_scope(&mut self) {
        self.local_scopes.push(std::collections::HashSet::new());
    }

    fn pop_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn declare_local(&mut self, name: &str) {
        if let Some(scope) = self.local_scopes.last_mut() {
            scope.insert(name.to_string());
        }
    }

    fn check_place_root_mutation(&mut self, place: &crate::hll::ast::Expr) {
        match &place.kind {
            crate::hll::ast::ExprKind::Variable(name) => {
                if self.is_capture(name) {
                    self.has_mutations = true;
                }
            }
            crate::hll::ast::ExprKind::FieldAccess(inner, _)
            | crate::hll::ast::ExprKind::ArrayIndex(inner, _) => {
                self.check_place_root_mutation(inner);
            }
            crate::hll::ast::ExprKind::Deref(inner) => {
                if let crate::hll::ast::ExprKind::Variable(name) = &inner.kind {
                    if self.is_capture(name) {
                        self.has_mutations = true;
                    }
                }
            }
            _ => {}
        }
    }

    fn walk_expr(&mut self, expr: &crate::hll::ast::Expr, env: &TypeEnv) {
        use crate::hll::ast::{CallTarget, ExprKind, Pattern, Stmt};
        match &expr.kind {
            ExprKind::Literal(_) | ExprKind::Path(_, _) | ExprKind::Continue => {}
            ExprKind::Variable(name) => {
                if self.is_capture(name) {
                    if let Some(cap) = self.captures_by_name.get(name) {
                        let is_copy = env
                            .class_of(&cap.ty, &std::collections::HashMap::new())
                            .implies(Marker::Copy);
                        let is_auto_clone = env.type_satisfies_trait(
                            &cap.ty,
                            &crate::hll::ast::Instance::bare("AutoClone"),
                        );
                        if !is_copy && !is_auto_clone {
                            self.has_linear_moves = true;
                        }
                    }
                }
            }
            ExprKind::FieldAccess(inner, field) => {
                match &inner.kind {
                    ExprKind::Variable(name) => {
                        if self.is_capture(name) {
                            if let Some(cap) = self.captures_by_name.get(name) {
                                if let Some(field_ty) = env.field_type(&cap.ty, field) {
                                    let is_copy = env
                                        .class_of(&field_ty, &std::collections::HashMap::new())
                                        .implies(Marker::Copy);
                                    let is_auto_clone = env.type_satisfies_trait(
                                        &field_ty,
                                        &crate::hll::ast::Instance::bare("AutoClone"),
                                    );
                                    if !is_copy && !is_auto_clone {
                                        self.has_linear_moves = true;
                                    }
                                }
                            }
                        } else {
                            self.walk_expr(inner, env);
                        }
                    }
                    _ => self.walk_expr(inner, env),
                }
            }
            ExprKind::ArrayIndex(arr, idx) => {
                self.walk_expr(idx, env);
                match &arr.kind {
                    ExprKind::Variable(name) => {
                        if self.is_capture(name) {
                            if let Some(cap) = self.captures_by_name.get(name) {
                                if let TypeKind::Array(elem, _) = &cap.ty.kind {
                                    let is_copy = env
                                        .class_of(elem, &std::collections::HashMap::new())
                                        .implies(Marker::Copy);
                                    let is_auto_clone = env.type_satisfies_trait(
                                        elem,
                                        &crate::hll::ast::Instance::bare("AutoClone"),
                                    );
                                    if !is_copy && !is_auto_clone {
                                        self.has_linear_moves = true;
                                    }
                                }
                            }
                        } else {
                            self.walk_expr(arr, env);
                        }
                    }
                    _ => self.walk_expr(arr, env),
                }
            }
            ExprKind::Cast(inner, _)
            | ExprKind::Unary(_, inner) => {
                self.walk_expr(inner, env);
            }
            ExprKind::Deref(inner) => {
                match &inner.kind {
                    ExprKind::Variable(name) => {
                        if !self.is_capture(name) {
                            self.walk_expr(inner, env);
                        }
                    }
                    _ => self.walk_expr(inner, env),
                }
            }
            ExprKind::Borrow(kind, inner) => {
                if matches!(
                    kind,
                    RefKind::Mut | RefKind::Out | RefKind::Drop | RefKind::Uninit
                ) {
                    self.check_place_root_mutation(inner);
                }
                match &inner.kind {
                    ExprKind::Variable(name) => {
                        if !self.is_capture(name) {
                            self.walk_expr(inner, env);
                        }
                    }
                    _ => self.walk_expr(inner, env),
                }
            }
            ExprKind::RawBorrow(inner) => {
                match &inner.kind {
                    ExprKind::Variable(name) => {
                        if !self.is_capture(name) {
                            self.walk_expr(inner, env);
                        }
                    }
                    _ => self.walk_expr(inner, env),
                }
            }
            ExprKind::Assign(lhs, rhs) => {
                self.check_place_root_mutation(lhs);
                self.walk_expr(rhs, env);
            }
            ExprKind::Call(target, _, args) => {
                match target {
                    CallTarget::Expr(callee) => self.walk_expr(callee, env),
                    CallTarget::Receiver { receiver, .. } => self.walk_expr(receiver, env),
                    CallTarget::Qualified { .. } | CallTarget::Path { .. } => {}
                }
                for a in args {
                    self.walk_expr(a, env);
                }
            }
            ExprKind::Block(stmts, last_expr, _) => {
                self.push_scope();
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { name, init, .. } => {
                            if let Some(init) = init {
                                self.walk_expr(init, env);
                            }
                            self.declare_local(name);
                        }
                        Stmt::Expr(e) => {
                            self.walk_expr(e, env);
                        }
                        Stmt::Defer { body, .. } => {
                            self.walk_expr(body, env);
                        }
                    }
                }
                if let Some(last) = last_expr {
                    self.walk_expr(last, env);
                }
                self.pop_scope();
            }
            ExprKind::If(cond, true_b, false_b) => {
                self.walk_expr(cond, env);
                self.walk_expr(true_b, env);
                self.walk_expr(false_b, env);
            }
            ExprKind::Loop(body) => {
                self.walk_expr(body, env);
            }
            ExprKind::Break(opt) | ExprKind::Return(opt) => {
                if let Some(e) = opt {
                    self.walk_expr(e, env);
                }
            }
            ExprKind::Match(target, arms) => {
                self.walk_expr(target, env);
                for (pat, arm_expr) in arms {
                    self.push_scope();
                    match pat {
                        Pattern::Variant(_, Some(var_name)) => {
                            self.declare_local(var_name);
                        }
                        _ => {}
                    }
                    self.walk_expr(arm_expr, env);
                    self.pop_scope();
                }
            }
            ExprKind::StructConstr(_, fields) => {
                for (_, f_expr) in fields {
                    self.walk_expr(f_expr, env);
                }
            }
            ExprKind::EnumConstr(_, _, payload) => {
                self.walk_expr(payload, env);
            }
            ExprKind::Array(elements) | ExprKind::Tuple(elements) => {
                for el in elements {
                    self.walk_expr(el, env);
                }
            }
            ExprKind::Binary(lhs, _, rhs) => {
                self.walk_expr(lhs, env);
                self.walk_expr(rhs, env);
            }
            ExprKind::Lambda { params, body, .. } => {
                self.push_scope();
                for p in params {
                    self.declare_local(&p.name);
                }
                self.walk_expr(body, env);
                self.pop_scope();
            }
        }
    }
}

// ---------------- MIR Derivation Synthesizers ----------------

/// Synthesize `impl<'s0, ...> AutoClone for $closure_N<'s0, ...> { fn clone(recv: &Self, $return: &out Self) { ... } }`.
pub fn derive_auto_clone_mir(closure: &crate::hll::type_check::ClosureInfo) -> mir::Declaration {
    let source = SourceInfo::generated(mir::GeneratedKind::HllDesugaring, closure.source.span());
    let target_ty = mir::Type::new(
        mir::TypeKind::Custom(mir::Instance::new(
            closure.struct_name.clone(),
            closure.lifetime_args.clone(),
            Vec::new(),
        )),
        source,
    );

    let recv_param = mir::Param {
        name: "recv".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Shared, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };
    let return_param = mir::Param {
        name: "$return".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Out, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };

    let mut stmts = Vec::new();
    let mut locals = Vec::new();

    let recv_place = Place::Var("recv".to_string());
    let return_place = Place::Var("$return".to_string());

    // 1. $call field is always Copy:
    let call_dest = field_place(deref_place(return_place.clone()), "$call".to_string());
    let call_src = field_place(deref_place(recv_place.clone()), "$call".to_string());
    stmts.push(assign_stmt(call_dest, use_rv(copy_op(call_src)), source));

    // 2. Capture fields:
    for c in &closure.captures {
        let field_name = format!("$cap_{}", c.name);
        let field_dest = field_place(deref_place(return_place.clone()), field_name.clone());
        let field_src = field_place(deref_place(recv_place.clone()), field_name.clone());
        let mir_field_ty = lower_type(&c.ty);

        if c.is_copy {
            stmts.push(assign_stmt(field_dest, use_rv(copy_op(field_src)), source));
        } else {
            let tmp_recv_name = format!("$tmp_recv_{}", c.name);
            let tmp_recv_place = Place::Var(tmp_recv_name.clone());
            let tmp_recv_ty = shared_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_recv_name,
                ty: tmp_recv_ty,
                source,
            });

            let tmp_out_name = format!("$tmp_out_{}", c.name);
            let tmp_out_place = Place::Var(tmp_out_name.clone());
            let tmp_out_ty = out_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_out_name,
                ty: tmp_out_ty,
                source,
            });

            stmts.push(assign_stmt(
                tmp_recv_place.clone(),
                ref_rv(RefKind::Shared, field_src),
                source,
            ));
            stmts.push(assign_stmt(
                tmp_out_place.clone(),
                ref_rv(RefKind::Out, field_dest),
                source,
            ));
            let callee = trait_fn_op(
                mir::Instance::bare("AutoClone"),
                mir_field_ty,
                mir::Instance::bare("clone"),
            );
            stmts.push(call_stmt(
                callee,
                vec![move_op(tmp_recv_place), move_op(tmp_out_place)],
                source,
            ));
        }
    }

    stmts.push(unborrow_stmt(return_place.clone(), source));
    stmts.push(drop_stmt(recv_place.clone(), source));
    stmts.push(require_uninit_stmt(recv_place, source));

    let entry_block = BasicBlock {
        label: "entry".to_string(),
        label_source: source,
        statements: stmts,
        terminator: return_term(source),
    };

    let clone_fn = mir::Function {
        meta: DeclMeta {
            name: "clone".to_string(),
            name_source: source,
            params: GenericParams {
                lifetime_params: Vec::new(),
                outlives: Vec::new(),
                type_params: Vec::new(),
                source,
            },
            markers: Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]),
        },
        linkage: Linkage::Local,
        abi: Abi::Silica,
        params: vec![recv_param, return_param],
        body: Some(mir::FunctionBody {
            locals,
            blocks: vec![entry_block],
        }),
    };

    mir::Declaration::Impl(mir::ImplBlock {
        params: GenericParams {
            lifetime_params: closure.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            source,
        },
        trait_path: Some(mir::Instance::bare("AutoClone")),
        target: target_ty,
        methods: vec![clone_fn],
    })
}

/// Synthesize `impl<'s0, ...> AutoDestroy for $closure_N<'s0, ...> { fn destroy(recv: &drop Self) { ... } }`.
pub fn derive_auto_destroy_mir(closure: &crate::hll::type_check::ClosureInfo) -> mir::Declaration {
    let source = SourceInfo::generated(mir::GeneratedKind::HllDesugaring, closure.source.span());
    let target_ty = mir::Type::new(
        mir::TypeKind::Custom(mir::Instance::new(
            closure.struct_name.clone(),
            closure.lifetime_args.clone(),
            Vec::new(),
        )),
        source,
    );

    let recv_param = mir::Param {
        name: "recv".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Drop, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };

    let mut stmts = Vec::new();
    let mut locals = Vec::new();

    let recv_place = Place::Var("recv".to_string());

    // 1. $call field is always Drop:
    let call_src = field_place(deref_place(recv_place.clone()), "$call".to_string());
    stmts.push(drop_stmt(call_src, source));

    // 2. Capture fields:
    for c in &closure.captures {
        let field_name = format!("$cap_{}", c.name);
        let field_src = field_place(deref_place(recv_place.clone()), field_name.clone());
        let mir_field_ty = lower_type(&c.ty);

        if c.is_drop {
            stmts.push(drop_stmt(field_src, source));
        } else {
            let tmp_recv_name = format!("$tmp_drop_{}", c.name);
            let tmp_recv_place = Place::Var(tmp_recv_name.clone());
            let tmp_recv_ty = drop_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_recv_name,
                ty: tmp_recv_ty,
                source,
            });

            stmts.push(assign_stmt(
                tmp_recv_place.clone(),
                ref_rv(RefKind::Drop, field_src),
                source,
            ));
            let callee = trait_fn_op(
                mir::Instance::bare("AutoDestroy"),
                mir_field_ty,
                mir::Instance::bare("destroy"),
            );
            stmts.push(call_stmt(callee, vec![move_op(tmp_recv_place)], source));
        }
    }

    let entry_block = BasicBlock {
        label: "entry".to_string(),
        label_source: source,
        statements: stmts,
        terminator: return_term(source),
    };

    let destroy_fn = mir::Function {
        meta: DeclMeta {
            name: "destroy".to_string(),
            name_source: source,
            params: GenericParams {
                lifetime_params: Vec::new(),
                outlives: Vec::new(),
                type_params: Vec::new(),
                source,
            },
            markers: Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]),
        },
        linkage: Linkage::Local,
        abi: Abi::Silica,
        params: vec![recv_param],
        body: Some(mir::FunctionBody {
            locals,
            blocks: vec![entry_block],
        }),
    };

    mir::Declaration::Impl(mir::ImplBlock {
        params: GenericParams {
            lifetime_params: closure.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            source,
        },
        trait_path: Some(mir::Instance::bare("AutoDestroy")),
        target: target_ty,
        methods: vec![destroy_fn],
    })
}
