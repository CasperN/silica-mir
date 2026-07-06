use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::{fmt_error, push_error};
use indexmap::IndexMap;
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum TypeDecl {
    Struct(StructDecl),
    Enum(EnumDecl),
}

#[derive(Debug, Clone)]
pub struct Env {
    /// Struct and enum declarations, keyed by name. Uses `IndexMap` so
    /// iteration order matches declaration order — analyses that iterate
    /// (e.g. field validation) produce diagnostics deterministically.
    pub types: IndexMap<String, TypeDecl>,
    /// Function declarations, keyed by name. Same rationale as `types`.
    pub functions: IndexMap<String, Function>,
}

impl Env {
    pub fn build(program: &Program, d: &mut Diagnostics) -> Self {
        let mut types = IndexMap::new();
        let mut functions = IndexMap::new();

        for decl in &program.declarations {
            match decl {
                Declaration::Struct(s) => {
                    if types.contains_key(&s.name) {
                        d.errors.push(format!(
                            "at {}: Duplicate declaration of type '{}'",
                            s.name_span, s.name
                        ));
                    } else {
                        types.insert(s.name.clone(), TypeDecl::Struct(s.clone()));
                    }
                }
                Declaration::Enum(e) => {
                    if types.contains_key(&e.name) {
                        d.errors.push(format!(
                            "at {}: Duplicate declaration of type '{}'",
                            e.name_span, e.name
                        ));
                    } else {
                        types.insert(e.name.clone(), TypeDecl::Enum(e.clone()));
                    }
                }
                Declaration::Fn(f) => {
                    if functions.contains_key(&f.name) {
                        d.errors.push(format!(
                            "at {}: Duplicate declaration of function '{}'",
                            f.name_span, f.name
                        ));
                    } else {
                        functions.insert(f.name.clone(), f.clone());
                    }
                }
            }
        }

        Env { types, functions }
    }

    pub fn validate_type(&self, ty: &Type) -> Result<(), String> {
        match ty {
            Type::Number | Type::Boolean | Type::Unit => Ok(()),
            Type::Custom(name) => {
                if self.types.contains_key(name) {
                    Ok(())
                } else {
                    Err(format!("Use of undeclared type '{}'", name))
                }
            }
            Type::Fn(params) => {
                for p in params {
                    self.validate_type(p)?;
                }
                Ok(())
            }
            Type::Ref(_, inner) => {
                self.validate_type(inner)
            }
        }
    }

    /// Type of `field` in the struct type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared struct or the field doesn't exist.
    pub fn field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        let Type::Custom(name) = ty else { return None; };
        match self.types.get(name) {
            Some(TypeDecl::Struct(s)) => s.fields.iter()
                .find(|f| f.name == field)
                .map(|f| f.ty.clone()),
            _ => None,
        }
    }

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Number, Type::Number) => true,
            (Type::Boolean, Type::Boolean) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Custom(a), Type::Custom(b)) => a == b,
            (Type::Fn(a), Type::Fn(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter().zip(b.iter()).all(|(x, y)| self.types_match(x, y))
            }
            (Type::Ref(k1, i1), Type::Ref(k2, i2)) => {
                k1 == k2 && self.types_match(i1, i2)
            }
            _ => false,
        }
    }

    pub fn infer_place_type(&self, place: &Place, locals: &IndexMap<String, Type>) -> Result<Type, String> {
        match place {
            Place::Var(name) => {
                locals.get(name).cloned().ok_or_else(|| format!("Use of undeclared variable '{}'", name))
            }
            Place::Deref(inner) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                if let Type::Ref(_, pointee) = inner_ty {
                    Ok(*pointee)
                } else {
                    Err(format!("Cannot dereference non-reference type {:?}", inner_ty))
                }
            }
            Place::Field(inner, field_name) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                let name = match &inner_ty {
                    Type::Custom(n) => n,
                    _ => return Err(format!("Cannot project field '{}' of non-struct type {:?}", field_name, inner_ty)),
                };
                match self.types.get(name) {
                    Some(TypeDecl::Struct(s)) => s.fields.iter()
                        .find(|f| f.name == *field_name)
                        .map(|f| f.ty.clone())
                        .ok_or_else(|| format!("Struct '{}' has no field '{}'", name, field_name)),
                    Some(TypeDecl::Enum(_)) => Err(format!(
                        "Cannot project field '{}' of enum type '{}'", field_name, name
                    )),
                    None => Err(format!("Use of undeclared type '{}'", name)),
                }
            }
            Place::Downcast(inner, variant_name) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                let name = match &inner_ty {
                    Type::Custom(n) => n,
                    _ => return Err(format!("Cannot downcast non-enum type {:?}", inner_ty)),
                };
                match self.types.get(name) {
                    Some(TypeDecl::Enum(e)) => e.variants.iter()
                        .find(|v| v.name == *variant_name)
                        .map(|v| v.ty.clone())
                        .ok_or_else(|| format!("Enum '{}' has no variant '{}'", name, variant_name)),
                    Some(TypeDecl::Struct(_)) => Err(format!(
                        "Cannot downcast struct type '{}'", name
                    )),
                    None => Err(format!("Use of undeclared type '{}'", name)),
                }
            }
        }
    }

    pub fn infer_operand_type(&self, op: &Operand, locals: &IndexMap<String, Type>) -> Result<Type, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.infer_place_type(place, locals),
            Operand::Const(c) => match c {
                ConstVal::Number(_) => Ok(Type::Number),
                ConstVal::Boolean(_) => Ok(Type::Boolean),
                ConstVal::Unit => Ok(Type::Unit),
                ConstVal::FnName(name) => {
                    let f = self.functions.get(name).ok_or_else(|| format!("Undeclared function name '{}'", name))?;
                    let param_tys = f.params.iter().map(|p| p.ty.clone()).collect();
                    Ok(Type::Fn(param_tys))
                }
            }
        }
    }

    pub fn infer_rvalue_type(&self, rvalue: &RValue, locals: &IndexMap<String, Type>) -> Result<Type, String> {
        match rvalue {
            RValue::Use(op) => self.infer_operand_type(op, locals),
            RValue::Ref(kind, place) => {
                let pointee_ty = self.infer_place_type(place, locals)?;
                Ok(Type::Ref(kind.clone(), Box::new(pointee_ty)))
            }
            RValue::EnumConstr(enum_name, variant_name, op) => {
                let e_decl = match self.types.get(enum_name) {
                    Some(TypeDecl::Enum(e)) => e,
                    Some(TypeDecl::Struct(_)) => {
                        return Err(format!("'{}' is a struct, not an enum", enum_name));
                    }
                    None => return Err(format!("Undeclared enum '{}'", enum_name)),
                };
                let variant = e_decl.variants.iter()
                    .find(|v| v.name == *variant_name)
                    .ok_or_else(|| format!("Enum '{}' has no variant '{}'", enum_name, variant_name))?;

                let op_ty = self.infer_operand_type(op, locals)?;
                if !self.types_match(&variant.ty, &op_ty) {
                    return Err(format!("Variant '{}' of enum '{}' expects type {:?}, found {:?}", variant_name, enum_name, variant.ty, op_ty));
                }

                Ok(Type::Custom(enum_name.clone()))
            }
        }
    }

    pub fn typecheck(&self, d: &mut Diagnostics) {
        // Validate struct fields and enum variants
        for type_decl in self.types.values() {
            match type_decl {
                TypeDecl::Struct(s) => {
                    let mut seen: HashSet<&str> = HashSet::new();
                    for f in &s.fields {
                        if !seen.insert(f.name.as_str()) {
                            d.errors.push(format!(
                                "at {}: In struct '{}', field '{}' is declared more than once",
                                f.span, s.name, f.name
                            ));
                        }
                        if let Err(e) = self.validate_type(&f.ty) {
                            d.errors.push(format!(
                                "at {}: In struct '{}', field '{}': {}",
                                f.span, s.name, f.name, e
                            ));
                        }
                    }
                }
                TypeDecl::Enum(e) => {
                    let mut seen: HashSet<&str> = HashSet::new();
                    for v in &e.variants {
                        if !seen.insert(v.name.as_str()) {
                            d.errors.push(format!(
                                "at {}: In enum '{}', variant '{}' is declared more than once",
                                v.span, e.name, v.name
                            ));
                        }
                        if let Err(err) = self.validate_type(&v.ty) {
                            d.errors.push(format!(
                                "at {}: In enum '{}', variant '{}': {}",
                                v.span, e.name, v.name, err
                            ));
                        }
                    }
                }
            }
        }

        // Validate all functions
        for f in self.functions.values() {
            self.typecheck_function(f, d);
        }
    }

    fn typecheck_function(&self, f: &Function, d: &mut Diagnostics) {
        for p in &f.params {
            if let Err(e) = self.validate_type(&p.ty) {
                d.errors.push(format!(
                    "at {}: In function '{}', parameter '{}': {}",
                    p.span, f.name, p.name, e
                ));
            }
        }

        let Some(body) = &f.body else { return; };

        if body.blocks.is_empty() {
            d.errors.push(format!(
                "at {}: Function '{}' has no entry block: body must contain at least one basic block",
                f.name_span, f.name
            ));
            return;
        }

        // Build the locals map. On name conflict, keep the first binding and
        // record an error — later checks still see a consistent scope.
        let mut locals_map: IndexMap<String, Type> = IndexMap::new();
        for p in &f.params {
            if locals_map.contains_key(&p.name) {
                d.errors.push(format!(
                    "at {}: Duplicate variable name '{}' in parameters of function '{}'",
                    p.span, p.name, f.name
                ));
            } else {
                locals_map.insert(p.name.clone(), p.ty.clone());
            }
        }
        for l in &body.locals {
            if let Err(e) = self.validate_type(&l.ty) {
                d.errors.push(format!(
                    "at {}: In function '{}', local '{}': {}",
                    l.span, f.name, l.name, e
                ));
            }
            if locals_map.contains_key(&l.name) {
                d.errors.push(format!(
                    "at {}: Duplicate variable name '{}' in locals/parameters of function '{}'",
                    l.span, l.name, f.name
                ));
            } else {
                locals_map.insert(l.name.clone(), l.ty.clone());
            }
        }

        let block_labels: HashSet<String> = body.blocks.iter().map(|b| b.label.clone()).collect();

        for block in &body.blocks {
            self.typecheck_block(f, block, &locals_map, &block_labels, d);
        }
    }

    fn typecheck_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        locals: &IndexMap<String, Type>,
        block_labels: &HashSet<String>,
        d: &mut Diagnostics,
    ) {
        for (stmt, span) in &block.statements {
            if let Err(e) = self.typecheck_statement(func, block, stmt, *span, locals) {
                d.errors.push(e);
            }
        }
        self.typecheck_terminator(func, block, locals, block_labels, d);
    }

    fn typecheck_statement(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        stmt_span: Span,
        locals: &IndexMap<String, Type>,
    ) -> Result<(), String> {
        match stmt {
            Statement::Assign(place, rvalue) => {
                let lhs_ty = self.infer_place_type(place, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "assignment LHS: {}", e))?;
                let rhs_ty = self.infer_rvalue_type(rvalue, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "assignment RHS: {}", e))?;
                if !self.types_match(&lhs_ty, &rhs_ty) {
                    return Err(fmt_error!(
                        stmt_span, func, block,
                        "Type mismatch in assignment. LHS is {:?}, RHS is {:?}", lhs_ty, rhs_ty
                    ));
                }
                Ok(())
            }
            Statement::Call(target, args) => {
                let target_ty = self.infer_operand_type(target, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "call target: {}", e))?;

                let Type::Fn(param_tys) = target_ty else {
                    return Err(fmt_error!(
                        stmt_span, func, block,
                        "Call target is not a function type: {:?}", target_ty
                    ));
                };

                if args.len() != param_tys.len() {
                    return Err(fmt_error!(
                        stmt_span, func, block,
                        "Wrong number of arguments for call. Expected {}, found {}",
                        param_tys.len(), args.len()
                    ));
                }
                for (i, (arg, param_ty)) in args.iter().zip(param_tys.iter()).enumerate() {
                    let arg_ty = self.infer_operand_type(arg, locals)
                        .map_err(|e| fmt_error!(stmt_span, func, block, "call arg {}: {}", i, e))?;
                    if !self.types_match(param_ty, &arg_ty) {
                        return Err(fmt_error!(
                            stmt_span, func, block,
                            "Call argument {} type mismatch. Expected {:?}, found {:?}",
                            i, param_ty, arg_ty
                        ));
                    }
                }
                Ok(())
            }
            Statement::Drop(place) => {
                // Just resolve the place — any legality (Drop,
                // currently init) is enforced by the substructural checker.
                self.infer_place_type(place, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "drop: {}", e))?;
                Ok(())
            }
        }
    }

    fn typecheck_terminator(
        &self,
        func: &Function,
        block: &BasicBlock,
        locals: &IndexMap<String, Type>,
        block_labels: &HashSet<String>,
        d: &mut Diagnostics,
    ) {
        let ts = block.terminator_span;
        match &block.terminator {
            Terminator::Goto(label) => {
                if !block_labels.contains(label) {
                    push_error!(d, ts, func, block, "goto targets undefined block '{}'", label);
                }
            }
            Terminator::Return => {}
            Terminator::Branch { cond, true_label, false_label } => {
                match self.infer_operand_type(cond, locals) {
                    Ok(cond_ty) if cond_ty != Type::Boolean => push_error!(
                        d, ts, func, block,
                        "branch condition must be boolean, found {:?}", cond_ty
                    ),
                    Ok(_) => {}
                    Err(e) => push_error!(d, ts, func, block, "branch condition: {}", e),
                }
                if !block_labels.contains(true_label) {
                    push_error!(d, ts, func, block, "branch true target undefined block '{}'", true_label);
                }
                if !block_labels.contains(false_label) {
                    push_error!(d, ts, func, block, "branch false target undefined block '{}'", false_label);
                }
            }
            Terminator::SwitchEnum { place, cases } => {
                // Resolve the place to (enum_name, decl) or record an error.
                // Variant-membership checks are skipped if this fails, but
                // label-existence checks still run on every case.
                let enum_decl: Option<&EnumDecl> = match self.infer_place_type(place, locals) {
                    Ok(Type::Custom(name)) => match self.types.get(&name) {
                        Some(TypeDecl::Enum(e)) => Some(e),
                        Some(TypeDecl::Struct(_)) => {
                            push_error!(
                                d, ts, func, block,
                                "switchEnum place must be an enum type, found struct '{}'", name
                            );
                            None
                        }
                        None => {
                            push_error!(
                                d, ts, func, block,
                                "Undeclared enum '{}' in switchEnum", name
                            );
                            None
                        }
                    },
                    Ok(other) => {
                        push_error!(
                            d, ts, func, block,
                            "switchEnum place must be an enum type, found {:?}", other
                        );
                        None
                    }
                    Err(e) => {
                        push_error!(d, ts, func, block, "switchEnum place: {}", e);
                        None
                    }
                };

                for (variant, label) in cases {
                    if let Some(e_decl) = enum_decl {
                        if !e_decl.variants.iter().any(|v| v.name == *variant) {
                            push_error!(
                                d, ts, func, block,
                                "variant '{}' is not part of enum '{}'", variant, e_decl.name
                            );
                        }
                    }
                    if !block_labels.contains(label) {
                        push_error!(
                            d, ts, func, block,
                            "switchEnum variant '{}' targets undefined block '{}'",
                            variant, label
                        );
                    }
                }
            }
            Terminator::Abort => {}
            Terminator::Unreachable => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::*;

    // ---------- Env::build ----------

    #[test]
    fn env_build_ok_mixed_decls() {
        assert_ok(
            "
            struct Point { x: number y: number }
            enum Copy Drop Option { None: Option Some: number }
            fn f() { entry: return }
            extern fn g();
            ",
        );
    }

    #[test]
    fn struct_duplicate_field_name_error() {
        assert_err(
            "
            struct S {
              x: number
              x: boolean
            }
            ",
            "field 'x' is declared more than once",
        );
    }

    #[test]
    fn enum_duplicate_variant_name_error() {
        assert_err(
            "
            enum E {
              A: unit
              A: number
            }
            ",
            "variant 'A' is declared more than once",
        );
    }

    #[test]
    fn env_build_duplicate_struct() {
        assert_err(
            "
            struct P { x: number }
            struct P { y: number }
            ",
            "Duplicate declaration of type 'P'",
        );
    }

    #[test]
    fn env_build_duplicate_enum() {
        assert_err(
            "
            enum E { A: number }
            enum E { B: number }
            ",
            "Duplicate declaration of type 'E'",
        );
    }

    #[test]
    fn env_build_struct_enum_name_clash() {
        assert_err(
            "
            struct N { x: number }
            enum N { A: number }
            ",
            "Duplicate declaration of type 'N'",
        );
    }

    #[test]
    fn env_build_duplicate_function() {
        assert_err(
            "
            fn f() { entry: return }
            fn f() { entry: return }
            ",
            "Duplicate declaration of function 'f'",
        );
    }

    #[test]
    fn env_build_struct_and_fn_same_name_currently_ok() {
        // Documents current behavior: struct/enum and fn share different namespaces.
        // If we ever unify, this test tightens into an assert_err.
        assert_ok(
            "
            struct N { x: number }
            fn N() { entry: return }
            ",
        );
    }

    // ---------- validate_type ----------

    #[test]
    fn validate_undeclared_field_type() {
        assert_err(
            "struct S { x: Nope }",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn validate_undeclared_enum_payload_type() {
        assert_err(
            "enum E { A: Nope }",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn validate_undeclared_param_type() {
        assert_err(
            "fn f(x: Nope) { entry: return }",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn validate_undeclared_local_type() {
        assert_err(
            "fn f() { x: Nope; entry: return }",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn validate_undeclared_type_inside_ref() {
        assert_err(
            "fn f(x: &mut Nope) { entry: return }",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn validate_undeclared_type_inside_fn_type() {
        assert_err(
            "fn f(g: fn(Nope)) { entry: return }",
            "Use of undeclared type 'Nope'",
        );
    }

    // ---------- Place typing ----------

    #[test]
    fn place_unknown_var_error() {
        assert_err(
            "
            fn f() {
              entry:
                x = 42;
                return
            }
            ",
            "Use of undeclared variable 'x'",
        );
    }

    #[test]
    fn place_struct_field_ok() {
        assert_ok(
            "
            struct Copy Drop P { x: number y: number }
            fn f(p: P) {
              a: number;
              entry:
                a = copy p.x;
                return
            }
            ",
        );
    }

    #[test]
    fn place_unknown_field_error() {
        assert_err(
            "
            struct P { x: number }
            fn f(p: P) {
              a: number;
              entry:
                a = copy p.z;
                return
            }
            ",
            "Struct 'P' has no field 'z'",
        );
    }

    #[test]
    fn place_field_on_non_struct_error() {
        assert_err(
            "
            fn f(n: number) {
              a: number;
              entry:
                a = copy n.x;
                return
            }
            ",
            "Cannot project field",
        );
    }

    #[test]
    fn place_field_on_enum_error() {
        assert_err(
            "
            enum E { A: number }
            fn f(e: E) {
              a: number;
              entry:
                a = copy e.x;
                return
            }
            ",
            "Cannot project field 'x' of enum type 'E'",
        );
    }

    #[test]
    fn place_downcast_ok() {
        // Downcast reads are only legal in a block refined by a preceding
        // switchEnum arm — enforced by `enum_variants`.
        assert_ok(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                switchEnum(o) [None: n, Some: s]
              s:
                x = copy o as Some;
                return
              n: return
            }
            ",
        );
    }

    #[test]
    fn place_downcast_unknown_variant_error() {
        assert_err(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                x = copy o as Wat;
                return
            }
            ",
            "Enum 'Option' has no variant 'Wat'",
        );
    }

    #[test]
    fn place_downcast_on_non_enum_type() {
        // Downcasting a non-Custom (e.g. reference) hits the dedicated
        // 'Cannot downcast non-enum type' branch.
        assert_err(
            "
            fn f(r: &number) {
              x: number;
              entry:
                x = copy r as Some;
                return
            }
            ",
            "Cannot downcast non-enum type",
        );
    }

    #[test]
    fn place_downcast_on_struct_error() {
        assert_err(
            "
            struct S { x: number }
            fn f(s: S) {
              x: number;
              entry:
                x = copy s as Some;
                return
            }
            ",
            "Cannot downcast struct type 'S'",
        );
    }

    #[test]
    fn place_deref_ok() {
        assert_ok(
            "
            fn f(r: &number) {
              x: number;
              entry:
                x = copy *r;
                return
            }
            ",
        );
    }

    #[test]
    fn nested_reference_type_ok() {
        // `&mut &mut T` — parser and tc handle both the type and the double
        // deref on the read side.
        assert_ok(
            "
            fn f(r: &mut &mut number) {
              a: number;
              entry:
                a = copy **r;
                return
            }
            ",
        );
    }

    #[test]
    fn zero_arity_fn_type_ok() {
        // `fn()` as a local type — the operand chain and Type::Fn(vec![])
        // round-trip through the checker cleanly.
        assert_ok(
            "
            fn noop() { entry: return }
            fn f() {
              g: fn();
              entry:
                g = noop;
                call copy g();
                return
            }
            ",
        );
    }

    #[test]
    fn place_deref_of_non_ref_error() {
        assert_err(
            "
            fn f(y: number) {
              x: number;
              entry:
                x = copy *y;
                return
            }
            ",
            "Cannot dereference non-reference type",
        );
    }

    #[test]
    fn place_deref_through_field_ok() {
        // Exercises Deref(Field(Var, "r")) — a reference held in a struct field.
        assert_ok(
            "
            struct Copy Drop Ptr { r: &number }
            fn f(p: Ptr) {
              a: number;
              entry:
                a = copy *p.r;
                return
            }
            ",
        );
    }

    // ---------- Operand typing ----------

    #[test]
    fn operand_number_const_ok() {
        assert_ok(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                return
            }
            ",
        );
    }

    #[test]
    fn operand_unit_const_ok() {
        assert_ok(
            "
            fn f() {
              u: unit;
              entry:
                u = unit;
                return
            }
            ",
        );
    }

    #[test]
    fn unit_as_enum_payload_ok() {
        assert_ok(
            "
            enum Copy Drop Tag { A: unit B: number }
            fn f() {
              t: Tag;
              entry:
                t = Tag::A(unit);
                return
            }
            ",
        );
    }

    #[test]
    fn unit_type_mismatch_error() {
        assert_err(
            "
            fn f() {
              n: number;
              entry:
                n = unit;
                return
            }
            ",
            "Type mismatch in assignment",
        );
    }

    #[test]
    fn operand_boolean_const_ok() {
        assert_ok(
            "
            fn f() {
              b: boolean;
              entry:
                b = true;
                return
            }
            ",
        );
    }

    #[test]
    fn operand_fnname_defined_ok() {
        assert_ok(
            "
            fn callee(x: number) { entry: return }
            fn f() {
              g: fn(number);
              entry:
                g = callee;
                return
            }
            ",
        );
    }

    #[test]
    fn operand_fnname_extern_ok() {
        assert_ok(
            "
            extern fn callee(x: number);
            fn f() {
              g: fn(number);
              entry:
                g = callee;
                return
            }
            ",
        );
    }

    #[test]
    fn operand_fnname_undeclared_error() {
        // A bare identifier in operand position is parsed as ConstVal::FnName —
        // if it isn't a declared function, this is where the error surfaces.
        assert_err(
            "
            fn f() {
              g: fn(number);
              entry:
                g = missing;
                return
            }
            ",
            "Undeclared function name 'missing'",
        );
    }

    // ---------- RValue typing ----------

    #[test]
    fn rvalue_ref_shared_ok() {
        assert_ok(
            "
            fn f(y: number) {
              r: &number;
              entry:
                r = &y;
                return
            }
            ",
        );
    }

    #[test]
    fn rvalue_ref_mut_ok() {
        assert_ok(
            "
            fn f(y: number) {
              r: &mut number;
              entry:
                r = &mut y;
                return
            }
            ",
        );
    }

    #[test]
    fn rvalue_enum_constr_ok() {
        assert_ok(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::Some(42);
                return
            }
            ",
        );
    }

    #[test]
    fn rvalue_enum_constr_unknown_enum_error() {
        assert_err(
            "
            fn f() {
              entry:
                return
            }
            enum Copy Drop Option { None: Option Some: number }
            struct S { x: number }
            fn g() {
              o: Option;
              entry:
                o = Nope::Some(42);
                return
            }
            ",
            "Undeclared enum 'Nope'",
        );
    }

    #[test]
    fn rvalue_enum_constr_unknown_variant_error() {
        assert_err(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::Wat(42);
                return
            }
            ",
            "Enum 'Option' has no variant 'Wat'",
        );
    }

    #[test]
    fn rvalue_enum_constr_wrong_payload_type_error() {
        assert_err(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f() {
              o: Option;
              entry:
                o = Option::Some(true);
                return
            }
            ",
            "expects type",
        );
    }

    #[test]
    fn rvalue_enum_constr_self_recursive_payload_ok() {
        // Option::None has payload type Option (matches whole enum).
        assert_ok(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              r: Option;
              entry:
                r = Option::None(move o);
                return
            }
            ",
        );
    }

    // ---------- Statement: Assign ----------

    #[test]
    fn assign_type_match_ok() {
        assert_ok(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                return
            }
            ",
        );
    }

    #[test]
    fn assign_type_mismatch_error() {
        assert_err(
            "
            fn f() {
              x: number;
              entry:
                x = true;
                return
            }
            ",
            "Type mismatch in assignment",
        );
    }

    #[test]
    fn assign_through_mut_ref_ok() {
        assert_ok(
            "
            fn f(r: &mut number) {
              entry:
                *r = 42;
                return
            }
            ",
        );
    }

    #[test]
    fn assign_field_type_mismatch_error() {
        assert_err(
            "
            struct S { f: number }
            fn f(s: S) {
              entry:
                s.f = true;
                return
            }
            ",
            "Type mismatch in assignment",
        );
    }

    #[test]
    fn assign_via_downcast_ok() {
        // Downcast writes need the same refinement as reads.
        assert_ok(
            "
            enum Copy Drop Option { None: unit Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: n, Some: s]
              s:
                o as Some = 7;
                return
              n: return
            }
            ",
        );
    }

    #[test]
    fn assign_ref_kind_mismatch_error() {
        assert_err(
            "
            fn f(y: number) {
              r: &mut number;
              entry:
                r = &y;
                return
            }
            ",
            "Type mismatch in assignment",
        );
    }

    #[test]
    fn assign_fn_arity_mismatch_error() {
        assert_err(
            "
            fn callee(x: number) { entry: return }
            fn f() {
              g: fn(number, number);
              entry:
                g = callee;
                return
            }
            ",
            "Type mismatch in assignment",
        );
    }

    // ---------- Statement: Call ----------

    #[test]
    fn call_direct_by_fn_name_ok() {
        assert_ok(
            "
            extern fn add(a: number, b: number);
            fn f() {
              entry:
                call add(1, 2);
                return
            }
            ",
        );
    }

    #[test]
    fn call_through_local_ok() {
        assert_ok(
            "
            extern fn add(a: number, b: number);
            fn f() {
              g: fn(number, number);
              entry:
                g = add;
                call copy g(1, 2);
                return
            }
            ",
        );
    }

    #[test]
    fn call_wrong_arity_error() {
        assert_err(
            "
            extern fn add(a: number, b: number);
            fn f() {
              entry:
                call add(1);
                return
            }
            ",
            "Wrong number of arguments",
        );
    }

    #[test]
    fn call_wrong_arg_type_error() {
        assert_err(
            "
            extern fn takes_num(a: number);
            fn f() {
              entry:
                call takes_num(true);
                return
            }
            ",
            "Call argument 0 type mismatch",
        );
    }

    #[test]
    fn call_non_function_target_error() {
        assert_err(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                call copy x();
                return
            }
            ",
            "Call target is not a function type",
        );
    }

    #[test]
    fn call_ref_kind_mismatch_error() {
        assert_err(
            "
            extern fn takes_drop(r: &drop number);
            fn f(y: number) {
              r: &mut number;
              entry:
                r = &mut y;
                call takes_drop(move r);
                return
            }
            ",
            "Call argument 0 type mismatch",
        );
    }

    // ---------- Terminators ----------

    #[test]
    fn goto_defined_label_ok() {
        assert_ok(
            "
            fn f() {
              entry:
                goto end
              end:
                return
            }
            ",
        );
    }

    // ---------- Sanity ----------

    #[test]
    fn empty_program_ok() {
        // Zero declarations — every pass should silently succeed.
        assert_no_diagnostics("");
    }

    #[test]
    fn infinite_loop_function_ok() {
        // No return; every analysis must terminate on the CFG cycle.
        assert_no_diagnostics(
            "
            fn f() {
              entry:
                goto entry
            }
            ",
        );
    }

    #[test]
    fn cross_function_local_names_are_independent() {
        // Two functions each define a local `x` and a block labeled `entry`.
        // Nothing should cross-pollinate — same-named things in one function
        // don't affect the other.
        assert_no_diagnostics(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                return
            }
            fn g() {
              x: number;
              entry:
                x = 7;
                return
            }
            ",
        );
    }

    #[test]
    fn goto_label_defined_in_another_function_is_undefined() {
        // Labels are function-scoped; a label defined in one function is
        // invisible to gotos in another.
        assert_err(
            "
            fn f() {
              entry:
                goto other
            }
            fn g() {
              other:
                return
            }
            ",
            "goto targets undefined block 'other'",
        );
    }

    #[test]
    fn goto_undefined_label_error() {
        assert_err(
            "
            fn f() {
              entry:
                goto nowhere
            }
            ",
            "goto targets undefined block 'nowhere'",
        );
    }

    #[test]
    fn branch_ok() {
        assert_ok(
            "
            fn f(b: boolean) {
              entry:
                branch(copy b) [true: yes, false: no]
              yes:
                return
              no:
                return
            }
            ",
        );
    }

    #[test]
    fn branch_non_boolean_error() {
        assert_err(
            "
            fn f(n: number) {
              entry:
                branch(copy n) [true: yes, false: no]
              yes:
                return
              no:
                return
            }
            ",
            "branch condition must be boolean",
        );
    }

    #[test]
    fn branch_true_label_undefined_error() {
        assert_err(
            "
            fn f(b: boolean) {
              entry:
                branch(copy b) [true: nowhere, false: no]
              no:
                return
            }
            ",
            "branch true target undefined block 'nowhere'",
        );
    }

    #[test]
    fn branch_false_label_undefined_error() {
        assert_err(
            "
            fn f(b: boolean) {
              entry:
                branch(copy b) [true: yes, false: nowhere]
              yes:
                return
            }
            ",
            "branch false target undefined block 'nowhere'",
        );
    }

    #[test]
    fn switch_enum_ok() {
        assert_ok(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: end, Some: end]
              end:
                return
            }
            ",
        );
    }

    #[test]
    fn switch_enum_non_enum_place_error() {
        assert_err(
            "
            fn f(n: number) {
              entry:
                switchEnum(n) [A: end]
              end:
                return
            }
            ",
            "switchEnum place must be an enum type",
        );
    }

    #[test]
    fn switch_enum_unknown_variant_error() {
        assert_err(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [Wat: end]
              end:
                return
            }
            ",
            "variant 'Wat' is not part of enum 'Option'",
        );
    }

    #[test]
    fn switch_enum_undefined_target_error() {
        assert_err(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: nowhere]
            }
            ",
            "targets undefined block 'nowhere'",
        );
    }

    // ---------- drop statement ----------

    #[test]
    fn drop_statement_ok() {
        // Syntactically well-formed drop on a param of Drop type.
        assert_ok(
            "
            fn f(x: number) {
              entry:
                drop x;
                return
            }
            ",
        )
    }
     #[test]
    fn double_drop_error() {
        // Syntactically well-formed drop on a param of Drop type.
        assert_err(
            "
            fn f(x: number) {
              entry:
                drop x;
                drop x;
                return
            }
            ",
            "In function 'f', block 'entry': variable 'x' is used after move",
        );
    }

    #[test]
    fn drop_of_undeclared_var_error() {
        assert_err(
            "
            fn f() {
              entry:
                drop x;
                return
            }
            ",
            "Use of undeclared variable 'x'",
        );
    }

    #[test]
    fn trivial_terminators_ok() {
        // return / abort / unreachable in well-formed blocks all pass.
        assert_ok(
            "
            fn a() { entry: return }
            fn b() { entry: abort }
            fn c() { entry: unreachable }
            ",
        );
    }

    // ---------- Function-level ----------

    #[test]
    fn duplicate_param_name_error() {
        assert_err(
            "fn f(x: number, x: number) { entry: return }",
            "Duplicate variable name 'x' in parameters",
        );
    }

    #[test]
    fn local_shadows_param_error() {
        assert_err(
            "
            fn f(x: number) {
              x: number;
              entry:
                return
            }
            ",
            "Duplicate variable name 'x'",
        );
    }

    #[test]
    fn duplicate_local_name_error() {
        assert_err(
            "
            fn f() {
              x: number;
              x: number;
              entry:
                return
            }
            ",
            "Duplicate variable name 'x'",
        );
    }

    #[test]
    fn extern_fn_declared_and_callable_ok() {
        assert_ok(
            "
            extern fn takes_num(a: number);
            fn f() {
              entry:
                call takes_num(1);
                return
            }
            ",
        );
    }

    #[test]
    fn extern_fn_with_bad_param_type_error() {
        assert_err(
            "extern fn foo(x: Nope);",
            "Use of undeclared type 'Nope'",
        );
    }

    #[test]
    fn unreachable_with_statements_ok() {
        // Intentionally allowed: an `unreachable` block can host debug/printf
        // statements for when the compiler mispredicts unreachability.
        assert_ok(
            "
            fn f() {
              x: number;
              entry:
                x = 42;
                unreachable
            }
            ",
        );
    }

    #[test]
    fn empty_function_body_error() {
        assert_err("fn f() { }", "Function 'f' has no entry block");
    }

    // ---------- Source spans ----------

    #[test]
    fn error_includes_line_and_col() {
        // A bad assignment on a specific line — verify the exact `at L:C:`
        // shows up (not just some span). Line 4, col 17 for `x = true`.
        let src = "fn f() {\n  x: number;\n  entry:\n                x = true;\n                return\n}";
        let errs = errors_of(src);
        assert_errors_contain(&errs, &["at 4:17:", "Type mismatch in assignment"]);
    }

    #[test]
    fn distinct_errors_carry_distinct_spans() {
        let src = "fn f() {\n  x: number;\n  y: number;\n  entry:\n    x = true;\n    y = true;\n    return\n}";
        let errs = errors_of(src);
        assert_errors_contain(&errs, &["at 5:5:", "at 6:5:"]);
    }

    #[test]
    fn accumulate_env_build_duplicates() {
        let errs = errors_of(
            "
            struct S { x: number }
            struct S { y: number }
            fn f() { entry: return }
            fn f() { entry: return }
            ",
        );
        assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
        assert_errors_contain(&errs, &["type 'S'", "function 'f'"]);
    }

    #[test]
    fn accumulate_statement_errors_in_one_block() {
        let errs = errors_of(
            "
            fn f() {
              x: number;
              y: number;
              entry:
                x = true;
                y = true;
                return
            }
            ",
        );
        // Two independent bad assigns in one block should both be reported.
        assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
        assert!(errs.iter().all(|e| e.contains("Type mismatch in assignment")));
    }

    #[test]
    fn accumulate_across_functions() {
        let errs = errors_of(
            "
            fn f() {
              x: number;
              entry:
                x = true;
                return
            }
            fn g() {
              y: number;
              entry:
                y = true;
                return
            }
            ",
        );
        assert_eq!(errs.len(), 2, "expected 2 errors, got: {:?}", errs);
        assert_errors_contain(&errs, &["'f'", "'g'"]);
    }

    #[test]
    fn accumulate_branch_multi_error() {
        // A single `branch` terminator can produce three independent errors:
        // non-boolean cond and both labels undefined.
        let errs = errors_of(
            "
            fn f(n: number) {
              entry:
                branch(copy n) [true: nowhere1, false: nowhere2]
            }
            fn g(n: number) {
              entry:
                branch(copy n) [true: nowhere1, false: nowhere2]
              nowhere1:
                return
              nowhere2:
                return
            }
            ",
        );
        assert_errors_contain(&errs, &["branch condition must be boolean"]);
        assert_one_error_contains_all(
            &errs,
            &["4:17", "branch true target undefined block 'nowhere1'"],
        );
        assert_one_error_contains_all(
            &errs,
            &["4:17", "branch false target undefined block 'nowhere2'"],
        );
    }

    #[test]
    fn accumulate_switch_enum_multi_error() {
        // switchEnum with an unknown variant AND an undefined target should
        // report both, and continue past the failed variant check.
        let errs = errors_of(
            "
            enum Copy Drop Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [Wat: nowhere, None: end]
              end:
                return
            }
            ",
        );
        assert_errors_contain(
            &errs,
            &[
                "variant 'Wat' is not part of enum 'Option'",
                "targets undefined block 'nowhere'",
            ],
        );
    }
}

