use std::collections::HashMap;
use crate::hll::ast::*;

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
            Type::Fn(params, ret) => {
                let resolved_params = params.iter().map(|p| self.resolve_default(p)).collect();
                Type::Fn(resolved_params, Box::new(self.resolve_default(ret)))
            }
            other => other.clone(),
        }
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), String> {
        let r1 = self.resolve(t1);
        let r2 = self.resolve(t2);
        match (&r1, &r2) {
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), other) | (other, Type::Var(id)) => {
                if self.occurs_in(*id, other) {
                    return Err(format!("infinite type detected during unification"));
                }
                self.map.insert(*id, other.clone());
                Ok(())
            }
            (Type::Int(i1), Type::Int(i2)) if i1 == i2 => Ok(()),
            (Type::Float(f1), Type::Float(f2)) if f1 == f2 => Ok(()),
            (Type::Boolean, Type::Boolean) => Ok(()),
            (Type::Unit, Type::Unit) => Ok(()),
            (Type::Never, _) | (_, Type::Never) => Ok(()),
            (Type::Custom(n1), Type::Custom(n2)) if n1 == n2 => Ok(()),
            (Type::Ref(k1, inner1), Type::Ref(k2, inner2)) if k1 == k2 => self.unify(inner1, inner2),
            (Type::RawPtr(inner1), Type::RawPtr(inner2)) => self.unify(inner1, inner2),
            (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
                if p1.len() != p2.len() {
                    return Err(format!("function arity mismatch"));
                }
                for (a1, a2) in p1.iter().zip(p2.iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(r1, r2)
            }
            (a, b) => Err(format!("type mismatch: expected {:?}, found {:?}", a, b)),
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

pub fn typecheck_program(program: &Program) -> Result<(), String> {
    typecheck_program_collect(program).map(|_| ())
}

pub fn typecheck_program_collect(program: &Program) -> Result<HashMap<*const Expr, Type>, String> {
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
                .map_err(|e| format!("in function '{}': {}", f.name, e))?;
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

pub fn infer(env: &mut TypeEnv, subst: &mut Subst, expr: &Expr) -> Result<Type, String> {
    let mut types = HashMap::new();
    infer_inner(env, subst, expr, &mut types)
}

pub fn check(env: &mut TypeEnv, subst: &mut Subst, expr: &Expr, expected: &Type) -> Result<(), String> {
    let mut types = HashMap::new();
    check_inner(env, subst, expr, expected, &mut types)
}

fn infer_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    types: &mut HashMap<*const Expr, Type>,
) -> Result<Type, String> {
    let ty = match &expr.kind {
        ExprKind::Literal(lit) => match lit {
            Literal::Int(_, Some(ty)) => Ok(Type::Int(*ty)),
            Literal::Int(_, None) => Ok(subst.fresh_var()),
            Literal::Float(_, Some(ty)) => Ok(Type::Float(*ty)),
            Literal::Float(_, None) => Ok(subst.fresh_var()),
            Literal::Boolean(_) => Ok(Type::Boolean),
            Literal::Unit => Ok(Type::Unit),
        },
        ExprKind::Variable(name) => {
            if let Some(ty) = env.lookup_var(name) {
                Ok(ty)
            } else if let Some((params, ret)) = env.functions.get(name) {
                Ok(Type::Fn(params.clone(), Box::new(ret.clone())))
            } else {
                Err(format!("at {}: undeclared variable '{}'", expr.span, name))
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
                        Err(format!("at {}: struct '{}' has no field '{}'", expr.span, struct_name, field))
                    }
                } else {
                    Err(format!("at {}: undeclared struct '{}'", expr.span, struct_name))
                }
            } else {
                Err(format!("at {}: expected struct type, found {:?}", expr.span, resolved))
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
                        Err(format!("at {}: enum '{}' has no variant '{}'", expr.span, enum_name, variant))
                    }
                } else {
                    Err(format!("at {}: undeclared enum '{}'", expr.span, enum_name))
                }
            } else {
                Err(format!("at {}: expected enum type, found {:?}", expr.span, resolved))
            }
        }
        ExprKind::Deref(target) => {
            let target_ty = infer_inner(env, subst, target, types)?;
            let resolved = subst.resolve(&target_ty);
            match resolved {
                Type::Ref(_, inner) | Type::RawPtr(inner) => Ok(*inner),
                other => Err(format!("at {}: cannot dereference non-pointer type {:?}", expr.span, other)),
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
                    return Err(format!(
                        "at {}: function expected {} arguments, found {}",
                        expr.span,
                        param_tys.len(),
                        args.len()
                    ));
                }
                for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                    check_inner(env, subst, arg, param_ty, types)?;
                }
                Ok(*ret_ty)
            } else {
                Err(format!("at {}: expected function type, found {:?}", expr.span, resolved))
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
            check_inner(env, subst, cond, &Type::Boolean, types)?;
            let t1 = infer_inner(env, subst, true_block, types)?;
            let t2 = infer_inner(env, subst, false_block, types)?;
            subst.unify(&t1, &t2)?;
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
                subst.unify(&ret_ty, &Type::Unit)?;
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
                    format!("at {}: undeclared enum '{}'", expr.span, enum_name)
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
                        return Err(format!("at {}: enum '{}' has no variant '{}'", expr.span, enum_name, variant));
                    }
                }
                if arm_tys.is_empty() {
                    return Err(format!("at {}: empty switch expression", expr.span));
                }
                let first_ty = arm_tys[0].clone();
                for ty in &arm_tys[1..] {
                    subst.unify(&first_ty, ty)?;
                }
                Ok(subst.resolve(&first_ty))
            } else {
                Err(format!("at {}: expected enum type for switch target, found {:?}", expr.span, resolved))
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
) -> Result<(), String> {
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
                subst.unify(expected_ty, &Type::Unit)
            };
            env.pop_scope();
            if res.is_ok() {
                types.insert(expr as *const Expr, resolved_expected.clone());
            }
            res
        }
        (ExprKind::If(cond, true_block, false_block), expected_ty) => {
            check_inner(env, subst, cond, &Type::Boolean, types)?;
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
                    format!("at {}: undeclared enum '{}'", expr.span, enum_name)
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
                        return Err(format!("at {}: enum '{}' has no variant '{}'", expr.span, enum_name, variant));
                    }
                }
                types.insert(expr as *const Expr, resolved_expected.clone());
                Ok(())
            } else {
                Err(format!("at {}: expected enum type for switch target, found {:?}", expr.span, resolved))
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
        _ => {
            let inferred = infer_inner(env, subst, expr, types)?;
            subst.unify(&inferred, &resolved_expected)?;
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
        let mut p = Parser::new(source)?;
        let program = p.parse_program()?;
        typecheck_program(&program)
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
}
