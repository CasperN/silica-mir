use std::collections::HashMap;
use crate::hll::ast::*;
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::Span;

use HllTypeCheckCode::*;

/// Structured error returned by inner type-check functions. Converted
/// to a `Diagnostic` at the public boundary.
type TcErr = Diagnostic;

fn err_at<T>(code: HllTypeCheckCode, span: Span, msg: impl Into<String>) -> Result<T, TcErr> {
    Err(Diagnostic::new(code, span, msg))
}

/// Distinguish unification failure modes returned by [`Subst::unify`] so
/// call sites can attach the right span and diagnostic code.
#[derive(Debug)]
pub enum UnifyError {
    Mismatch(String),
    Infinite,
    ArityMismatch,
}

impl UnifyError {
    fn to_diag(self, span: Span) -> Diagnostic {
        match self {
            UnifyError::Mismatch(msg) => Diagnostic::new(TypeMismatch, span, msg),
            UnifyError::Infinite => Diagnostic::new(
                InfiniteType,
                span,
                "infinite type detected during unification",
            ),
            UnifyError::ArityMismatch => {
                Diagnostic::new(ArityMismatch, span, "function arity mismatch")
            }
        }
    }
}

/// Machine-readable code for each HLL type-check error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HllTypeCheckCode {
    /// Unification failed — two types couldn't be reconciled.
    TypeMismatch,
    /// Occurs-check failed during unification.
    InfiniteType,
    /// Function call with the wrong number of arguments.
    ArityMismatch,
    /// Reference to a variable/function not in scope.
    UndeclaredVariable,
    /// Reference to a struct type that isn't declared.
    UndeclaredStruct,
    /// Reference to an enum type that isn't declared.
    UndeclaredEnum,
    /// Field access on a struct that has no such field.
    NoSuchField,
    /// Downcast or match arm names an enum variant that doesn't exist.
    NoSuchVariant,
    /// Field access on a value whose type isn't a struct.
    ExpectedStruct,
    /// Match target / downcast target isn't an enum type.
    ExpectedEnum,
    /// Call target isn't a function type.
    ExpectedFunction,
    /// Array indexing on a non-array type.
    ExpectedArray,
    /// Deref applied to a value that isn't a reference or raw pointer.
    ExpectedPointer,
    /// Match expression with zero arms.
    EmptySwitch,
    /// Binary operator applied to non-numeric operand types.
    BinaryOpNonNumeric,
    /// Struct constructor initializes wrong number of fields.
    StructFieldCountMismatch,
    /// Struct constructor is missing a field.
    MissingField,
    /// Struct constructor initializes a field twice.
    DuplicateField,
    /// Array index expression isn't an integer.
    ArrayIndexNotInt,
    /// Array literal doesn't match the expected length.
    ArrayLengthMismatch,
}

impl From<HllTypeCheckCode> for DiagCode {
    fn from(code: HllTypeCheckCode) -> DiagCode {
        DiagCode::HllTypeCheck(code)
    }
}

pub struct Subst {
    map: HashMap<usize, Type>,
    next_id: usize,
}

impl Subst {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            next_id: 0,
        }
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        Type::Var(id)
    }

    pub fn resolve(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve(resolved)
                } else {
                    Type::Var(*id)
                }
            }
            Type::Ref(kind, inner) => Type::Ref(*kind, Box::new(self.resolve(inner))),
            Type::RawPtr(inner) => Type::RawPtr(Box::new(self.resolve(inner))),
            Type::Fn(params, ret) => {
                let resolved_params = params.iter().map(|p| self.resolve(p)).collect();
                Type::Fn(resolved_params, Box::new(self.resolve(ret)))
            }
            Type::Array(inner, size) => Type::Array(Box::new(self.resolve(inner)), *size),
            other => other.clone(),
        }
    }
    pub fn resolve_default(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve_default(resolved)
                } else {
                    // Default unresolved type variables to i64
                    Type::Int(crate::mir::ast::IntTy::I64)
                }
            }
            Type::Ref(kind, inner) => Type::Ref(*kind, Box::new(self.resolve_default(inner))),
            Type::RawPtr(inner) => Type::RawPtr(Box::new(self.resolve_default(inner))),
            Type::Array(inner, size) => Type::Array(Box::new(self.resolve_default(inner)), *size),
            Type::Fn(params, ret) => {
                let resolved_params = params.iter().map(|p| self.resolve_default(p)).collect();
                Type::Fn(resolved_params, Box::new(self.resolve_default(ret)))
            }
            other => other.clone(),
        }
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnifyError> {
        let r1 = self.resolve(t1);
        let r2 = self.resolve(t2);
        match (&r1, &r2) {
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), other) | (other, Type::Var(id)) => {
                if self.occurs_in(*id, other) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, other.clone());
                Ok(())
            }
            (Type::Int(i1), Type::Int(i2)) if i1 == i2 => Ok(()),
            (Type::Float(f1), Type::Float(f2)) if f1 == f2 => Ok(()),
            (Type::Bool, Type::Bool) => Ok(()),
            (Type::Unit, Type::Unit) => Ok(()),
            (Type::Never, _) | (_, Type::Never) => Ok(()),
            (Type::Custom(n1), Type::Custom(n2)) if n1 == n2 => Ok(()),
            (Type::Ref(k1, inner1), Type::Ref(k2, inner2)) if k1 == k2 => self.unify(inner1, inner2),
            (Type::RawPtr(inner1), Type::RawPtr(inner2)) => self.unify(inner1, inner2),
            (Type::Array(inner1, size1), Type::Array(inner2, size2)) if size1 == size2 => self.unify(inner1, inner2),
            (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
                if p1.len() != p2.len() {
                    return Err(UnifyError::ArityMismatch);
                }
                for (a1, a2) in p1.iter().zip(p2.iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(r1, r2)
            }
            (a, b) => Err(UnifyError::Mismatch(format!(
                "type mismatch: expected {}, found {}",
                a, b
            ))),
        }
    }

    fn occurs_in(&self, id: usize, ty: &Type) -> bool {
        match ty {
            Type::Var(v) => {
                if *v == id {
                    true
                } else if let Some(resolved) = self.map.get(v) {
                    self.occurs_in(id, resolved)
                } else {
                    false
                }
            }
            Type::Ref(_, inner) => self.occurs_in(id, inner),
            Type::RawPtr(inner) => self.occurs_in(id, inner),
            Type::Array(inner, _) => self.occurs_in(id, inner),
            Type::Fn(params, ret) => {
                params.iter().any(|p| self.occurs_in(id, p)) || self.occurs_in(id, ret)
            }
            _ => false,
        }
    }
}

pub struct TypeEnv {
    variables: Vec<HashMap<String, Type>>,
    structs: HashMap<String, StructDecl>,
    enums: HashMap<String, EnumDecl>,
    functions: HashMap<String, (Vec<Type>, Type)>,
    current_ret_ty: Option<Type>,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            variables: vec![HashMap::new()],
            structs: HashMap::new(),
            enums: HashMap::new(),
            functions: HashMap::new(),
            current_ret_ty: None,
        }
    }

    pub fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.variables.pop();
    }

    pub fn insert_var(&mut self, name: String, ty: Type) {
        if let Some(scope) = self.variables.last_mut() {
            scope.insert(name, ty);
        }
    }

    pub fn lookup_var(&self, name: &str) -> Option<Type> {
        for scope in self.variables.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return Some(ty.clone());
            }
        }
        None
    }
}

/// Run HLL type-checking, pushing errors into `d`. Returns the
/// per-expression type map on success; `None` if any error was reported.
pub fn run_type_check(program: &Program, d: &mut Diagnostics) -> Option<HashMap<*const Expr, Type>> {
    match typecheck_program_collect(program) {
        Ok(types) => Some(types),
        Err(diag) => {
            d.push_error(diag);
            None
        }
    }
}

/// Test-facing wrapper — sibling modules under `hll::*` use this to
/// stage a typecheck without needing a `Diagnostics` container.
/// Production callers should use `run_type_check`.
pub(super) fn typecheck_program(program: &Program) -> Result<(), Diagnostic> {
    typecheck_program_collect(program).map(|_| ())
}

/// Test-facing wrapper that returns the per-expression type map on
/// success. Sibling modules use this to stage lowering-time work
/// without needing a `Diagnostics` container. Production callers
/// should use `run_type_check`.
pub(super) fn typecheck_program_collect(program: &Program) -> Result<HashMap<*const Expr, Type>, Diagnostic> {
    let mut env = TypeEnv::new();
    let mut subst = Subst::new();
    let mut types = HashMap::new();

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
                let params_tys: Vec<Type> = f.params.iter().map(|p| p.ty.clone()).collect();
                env.functions.insert(f.name.clone(), (params_tys, f.ret_ty.clone()));
            }
        }
    }

    // Typecheck function bodies
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            env.push_scope();
            env.current_ret_ty = Some(f.ret_ty.clone());
            for param in &f.params {
                env.insert_var(param.name.clone(), param.ty.clone());
            }
            check_inner(&mut env, &mut subst, &f.body, &f.ret_ty, &mut types)
                .map_err(|d| d.in_function(&f.name))?;
            env.pop_scope();
        }
    }

    // Resolve all captured expression types in the final map
    let mut resolved_types = HashMap::new();
    for (expr_ptr, ty) in types {
        resolved_types.insert(expr_ptr, subst.resolve_default(&ty));
    }

    Ok(resolved_types)
}

fn infer_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    types: &mut HashMap<*const Expr, Type>,
) -> Result<Type, Diagnostic> {
    let ty = match &expr.kind {
        ExprKind::Literal(lit) => match lit {
            Literal::Int(_, Some(ty)) => Ok(Type::Int(*ty)),
            Literal::Int(_, None) => Ok(subst.fresh_var()),
            Literal::Float(_, Some(ty)) => Ok(Type::Float(*ty)),
            Literal::Float(_, None) => Ok(subst.fresh_var()),
            Literal::Bool(_) => Ok(Type::Bool),
            Literal::Unit => Ok(Type::Unit),
        },
        ExprKind::Binary(lhs, op, rhs) => {
            let lhs_ty = infer_inner(env, subst, lhs, types)?;
            let rhs_ty = infer_inner(env, subst, rhs, types)?;
            subst.unify(&lhs_ty, &rhs_ty).map_err(|e| e.to_diag(expr.span))?;

            let resolved = subst.resolve(&lhs_ty);
            match &resolved {
                Type::Int(_) | Type::Float(_) | Type::Var(_) | Type::Never => {}
                _ => return err_at(
                    BinaryOpNonNumeric,
                    expr.span,
                    format!("binary operations only supported on numeric types, found {}", resolved),
                ),
            }

            let is_cmp = matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            );
            let res_ty = if is_cmp {
                Type::Bool
            } else {
                lhs_ty.clone()
            };
            Ok(res_ty)
        }
        ExprKind::Variable(name) => {
            if let Some(ty) = env.lookup_var(name) {
                Ok(ty)
            } else if let Some((params, ret)) = env.functions.get(name) {
                Ok(Type::Fn(params.clone(), Box::new(ret.clone())))
            } else {
                err_at(
                    UndeclaredVariable,
                    expr.span,
                    format!("undeclared variable '{}'", name),
                )
            }
        }
        ExprKind::FieldAccess(target, field) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            let struct_ty = match &resolved {
                Type::Ref(_, inner) => subst.resolve(inner),
                other => other.clone(),
            };
            if let Type::Custom(struct_name) = struct_ty {
                if let Some(s_decl) = env.structs.get(&struct_name) {
                    if let Some(f) = s_decl.fields.iter().find(|field_decl| field_decl.name == *field) {
                        Ok(f.ty.clone())
                    } else {
                        err_at(
                            NoSuchField,
                            expr.span,
                            format!("struct '{}' has no field '{}'", struct_name, field),
                        )
                    }
                } else {
                    err_at(
                        UndeclaredStruct,
                        expr.span,
                        format!("undeclared struct '{}'", struct_name),
                    )
                }
            } else {
                err_at(
                    ExpectedStruct,
                    expr.span,
                    format!("expected struct type, found {}", resolved),
                )
            }
        }
        ExprKind::Downcast(target, variant) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            if let Type::Custom(enum_name) = resolved {
                if let Some(e_decl) = env.enums.get(&enum_name) {
                    if let Some(v) = e_decl.variants.iter().find(|var_decl| var_decl.name == *variant) {
                        Ok(v.ty.clone())
                    } else {
                        err_at(
                            NoSuchVariant,
                            expr.span,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        )
                    }
                } else {
                    err_at(
                        UndeclaredEnum,
                        expr.span,
                        format!("undeclared enum '{}'", enum_name),
                    )
                }
            } else {
                err_at(
                    ExpectedEnum,
                    expr.span,
                    format!("expected enum type, found {}", resolved),
                )
            }
        }
        ExprKind::Deref(target) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            match resolved {
                Type::Ref(_, inner) | Type::RawPtr(inner) => Ok(*inner),
                other => err_at(
                    ExpectedPointer,
                    expr.span,
                    format!("cannot dereference non-pointer type {}", other),
                ),
            }
        }
        ExprKind::Borrow(kind, target) => {
            let inner_ty = infer_inner(env, subst, target, types)?;
            Ok(Type::Ref(*kind, Box::new(inner_ty)))
        }
        ExprKind::RawBorrow(target) => {
            let inner_ty = infer_inner(env, subst, target, types)?;
            Ok(Type::RawPtr(Box::new(inner_ty)))
        }
        ExprKind::Call(fn_expr, args) => {
            let fn_ty = infer_inner(env, subst, fn_expr, types)?;
            let resolved = subst.resolve(&fn_ty);
            if let Type::Fn(param_tys, ret_ty) = resolved {
                if param_tys.len() != args.len() {
                    return err_at(
                        ArityMismatch,
                        expr.span,
                        format!(
                            "function expected {} arguments, found {}",
                            param_tys.len(),
                            args.len()
                        ),
                    );
                }
                for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                    check_inner(env, subst, arg, param_ty, types)?;
                }
                Ok(*ret_ty)
            } else {
                err_at(
                    ExpectedFunction,
                    expr.span,
                    format!("expected function type, found {}", resolved),
                )
            }
        }
        ExprKind::Block(stmts, last_expr) => {
            env.push_scope();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { is_mut: _, name, ty, init, span: _ } => {
                        let var_ty = if let Some(annotated_ty) = ty {
                            check_inner(env, subst, init, annotated_ty, types)?;
                            annotated_ty.clone()
                        } else {
                            infer_inner(env, subst, init, types)?
                        };
                        env.insert_var(name.clone(), var_ty);
                    }
                    Stmt::Expr(e) => {
                        infer_inner(env, subst, e, types)?;
                    }
                }
            }
            let res = if let Some(last) = last_expr {
                infer_inner(env, subst, last, types)
            } else {
                Ok(Type::Unit)
            };
            env.pop_scope();
            res
        }
        ExprKind::If(cond, true_block, false_block) => {
            check_inner(env, subst, cond, &Type::Bool, types)?;
            let t1 = infer_inner(env, subst, true_block, types)?;
            let t2 = infer_inner(env, subst, false_block, types)?;
            subst.unify(&t1, &t2).map_err(|e| e.to_diag(expr.span))?;
            Ok(subst.resolve(&t1))
        }
        ExprKind::Loop(body) => {
            check_inner(env, subst, body, &Type::Unit, types)?;
            Ok(Type::Never)
        }
        ExprKind::Break(val_expr) => {
            if let Some(val) = val_expr {
                infer_inner(env, subst, val, types)?;
            }
            Ok(Type::Never)
        }
        ExprKind::Continue => Ok(Type::Never),
        ExprKind::Return(val_expr) => {
            let ret_ty = env.current_ret_ty.clone().unwrap_or(Type::Unit);
            if let Some(val) = val_expr {
                check_inner(env, subst, val, &ret_ty, types)?;
            } else {
                subst.unify(&ret_ty, &Type::Unit).map_err(|e| e.to_diag(expr.span))?;
            }
            Ok(Type::Never)
        }
        ExprKind::Assign(lhs, rhs) => {
            let lhs_ty = infer_inner(env, subst, lhs, types)?;
            check_inner(env, subst, rhs, &lhs_ty, types)?;
            Ok(Type::Unit)
        }
        ExprKind::Match(target, arms) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            if let Type::Custom(enum_name) = resolved {
                let e_decl = env.enums.get(&enum_name).cloned().ok_or_else(|| {
                    Diagnostic::new(
                        UndeclaredEnum,
                        expr.span,
                        format!("undeclared enum '{}'", enum_name),
                    )
                })?;
                let mut arm_tys = Vec::new();
                for (pattern, body) in arms {
                    let Pattern::Variant(variant, bound_var) = pattern;
                    if let Some(v) = e_decl.variants.iter().find(|var_decl| var_decl.name == *variant) {
                        env.push_scope();
                        if let Some(var_name) = bound_var {
                            env.insert_var(var_name.clone(), v.ty.clone());
                        }
                        let body_ty = infer_inner(env, subst, body, types)?;
                        env.pop_scope();
                        arm_tys.push(body_ty);
                    } else {
                        return err_at(
                            NoSuchVariant,
                            expr.span,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        );
                    }
                }
                if arm_tys.is_empty() {
                    return err_at(EmptySwitch, expr.span, "empty switch expression");
                }
                let first_ty = arm_tys[0].clone();
                for ty in &arm_tys[1..] {
                    subst.unify(&first_ty, ty).map_err(|e| e.to_diag(expr.span))?;
                }
                Ok(subst.resolve(&first_ty))
            } else {
                err_at(
                    ExpectedEnum,
                    expr.span,
                    format!("expected enum type for switch target, found {}", resolved),
                )
            }
        }
        ExprKind::StructConstr(name, fields) => {
            let s_decl = env.structs.get(name).cloned().ok_or_else(|| {
                Diagnostic::new(
                    UndeclaredStruct,
                    expr.span,
                    format!("undeclared struct '{}'", name),
                )
            })?;

            if fields.len() != s_decl.fields.len() {
                return err_at(
                    StructFieldCountMismatch,
                    expr.span,
                    format!(
                        "struct '{}' has {} fields, but {} were initialized",
                        name,
                        s_decl.fields.len(),
                        fields.len()
                    ),
                );
            }

            for f_decl in &s_decl.fields {
                let mut matches = fields.iter().filter(|(fname, _)| fname == &f_decl.name);
                let Some((_, val_expr)) = matches.next() else {
                    return err_at(
                        MissingField,
                        expr.span,
                        format!(
                            "missing field '{}' in constructor for '{}'",
                            f_decl.name, name
                        ),
                    );
                };
                if matches.next().is_some() {
                    return err_at(
                        DuplicateField,
                        expr.span,
                        format!(
                            "duplicate field '{}' in constructor for '{}'",
                            f_decl.name, name
                        ),
                    );
                }
                check_inner(env, subst, val_expr, &f_decl.ty, types)?;
            }

            Ok(Type::Custom(name.clone()))
        }
        ExprKind::EnumConstr(enum_name, variant_name, payload) => {
            let e_decl = env.enums.get(enum_name).cloned().ok_or_else(|| {
                Diagnostic::new(
                    UndeclaredEnum,
                    expr.span,
                    format!("undeclared enum '{}'", enum_name),
                )
            })?;

            let variant_decl = e_decl.variants.iter().find(|v| v.name == *variant_name).ok_or_else(|| {
                Diagnostic::new(
                    NoSuchVariant,
                    expr.span,
                    format!("enum '{}' has no variant '{}'", enum_name, variant_name),
                )
            })?;

            check_inner(env, subst, payload, &variant_decl.ty, types)?;
            Ok(Type::Custom(enum_name.clone()))
        }
        ExprKind::Array(elements) => {
            if elements.is_empty() {
                let elem_ty = subst.fresh_var();
                Ok(Type::Array(Box::new(elem_ty), 0))
            } else {
                let first_ty = infer_inner(env, subst, &elements[0], types)?;
                for el in &elements[1..] {
                    check_inner(env, subst, el, &first_ty, types)?;
                }
                Ok(Type::Array(Box::new(first_ty), elements.len()))
            }
        }
        ExprKind::ArrayIndex(arr, idx) => {
            let arr_ty = infer_inner(env, subst, arr, types)?;
            let resolved = subst.resolve(&arr_ty);
            if let Type::Array(inner, _) = resolved {
                let idx_ty = infer_inner(env, subst, idx, types)?;
                let idx_resolved = subst.resolve(&idx_ty);
                match idx_resolved {
                    Type::Int(_) => {}
                    Type::Var(_) => {
                        subst.unify(&idx_resolved, &Type::Int(crate::mir::ast::IntTy::I64))
                            .map_err(|e| e.to_diag(expr.span))?;
                    }
                    other => return err_at(
                        ArrayIndexNotInt,
                        expr.span,
                        format!("array index must be an integer, found {}", other),
                    ),
                }
                Ok(*inner)
            } else {
                err_at(
                    ExpectedArray,
                    expr.span,
                    format!("expected array type, found {}", resolved),
                )
            }
        }
    }?;

    types.insert(expr as *const Expr, ty.clone());
    Ok(ty)
}

fn check_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    expected: &Type,
    types: &mut HashMap<*const Expr, Type>,
) -> Result<(), Diagnostic> {
    let resolved_expected = subst.resolve(expected);
    match (&expr.kind, &resolved_expected) {
        (ExprKind::Block(stmts, last_expr), expected_ty) => {
            env.push_scope();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { is_mut: _, name, ty, init, span: _ } => {
                        let var_ty = if let Some(annotated_ty) = ty {
                            check_inner(env, subst, init, annotated_ty, types)?;
                            annotated_ty.clone()
                        } else {
                            infer_inner(env, subst, init, types)?
                        };
                        env.insert_var(name.clone(), var_ty);
                    }
                    Stmt::Expr(e) => {
                        infer_inner(env, subst, e, types)?;
                    }
                }
            }
            let res = if let Some(last) = last_expr {
                check_inner(env, subst, last, expected_ty, types)
            } else {
                subst.unify(expected_ty, &Type::Unit).map_err(|e| e.to_diag(expr.span))
            };
            env.pop_scope();
            if res.is_ok() {
                types.insert(expr as *const Expr, resolved_expected.clone());
            }
            res
        }
        (ExprKind::If(cond, true_block, false_block), expected_ty) => {
            check_inner(env, subst, cond, &Type::Bool, types)?;
            check_inner(env, subst, true_block, expected_ty, types)?;
            check_inner(env, subst, false_block, expected_ty, types)?;
            types.insert(expr as *const Expr, resolved_expected.clone());
            Ok(())
        }
        (ExprKind::Match(target, arms), expected_ty) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            if let Type::Custom(enum_name) = resolved {
                let e_decl = env.enums.get(&enum_name).cloned().ok_or_else(|| {
                    Diagnostic::new(
                        UndeclaredEnum,
                        expr.span,
                        format!("undeclared enum '{}'", enum_name),
                    )
                })?;
                for (pattern, body) in arms {
                    let Pattern::Variant(variant, bound_var) = pattern;
                    if let Some(v) = e_decl.variants.iter().find(|var_decl| var_decl.name == *variant) {
                        env.push_scope();
                        if let Some(var_name) = bound_var {
                            env.insert_var(var_name.clone(), v.ty.clone());
                        }
                        check_inner(env, subst, body, expected_ty, types)?;
                        env.pop_scope();
                    } else {
                        return err_at(
                            NoSuchVariant,
                            expr.span,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        );
                    }
                }
                types.insert(expr as *const Expr, resolved_expected.clone());
                Ok(())
            } else {
                err_at(
                    ExpectedEnum,
                    expr.span,
                    format!("expected enum type for switch target, found {}", resolved),
                )
            }
        }
        (ExprKind::Literal(Literal::Int(_val, None)), Type::Int(_ty)) => {
            types.insert(expr as *const Expr, resolved_expected.clone());
            Ok(())
        }
        (ExprKind::Literal(Literal::Float(_val, None)), Type::Float(_ty)) => {
            types.insert(expr as *const Expr, resolved_expected.clone());
            Ok(())
        }
        (ExprKind::Array(elements), Type::Array(expected_elem, expected_size)) => {
            if elements.len() != *expected_size {
                return err_at(
                    ArrayLengthMismatch,
                    expr.span,
                    format!(
                        "expected array of length {}, found length {}",
                        expected_size, elements.len()
                    ),
                );
            }
            for el in elements {
                check_inner(env, subst, el, expected_elem, types)?;
            }
            types.insert(expr as *const Expr, resolved_expected.clone());
            Ok(())
        }
        _ => {
            let inferred = infer_inner(env, subst, expr, types)?;
            subst.unify(&inferred, &resolved_expected).map_err(|e| e.to_diag(expr.span))?;
            types.insert(expr as *const Expr, resolved_expected.clone());
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::parser::Parser;

    fn check_program(source: &str) -> Result<(), String> {
        let program = Parser::new(source)
            .parse()
            .map_err(|d| d.errors_str().join("\n"))?;
        // Render Diagnostic errors as strings for the existing
        // `.contains(...)` substring assertions.
        typecheck_program(&program).map_err(|d| {
            let mut ds = crate::diagnostics::Diagnostics::default()
                .with_source(program.source.clone());
            ds.push_error(d);
            ds.errors_str().join("\n")
        })
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
            enum Option { None: unit, Some: i64 }
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
        // Calling through a fn-typed parameter: the return type
        // flows correctly to the assignment binding. Exercises the
        // return-arrow surface syntax through both parser and
        // type checker.
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
        // If the declared return type of the fn-typed param is `i64`
        // but the binding demands `bool`, the type checker catches
        // it. Confirms the arrow's return type is actually consulted
        // (not silently dropped and defaulted to unit).
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
        // Wrong number of arguments is caught. Verifies the parser
        // filled the param list correctly (previous walker bug
        // would have accidentally included the return type as an
        // extra param, breaking arity).
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
}

