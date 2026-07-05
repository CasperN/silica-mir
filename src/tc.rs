use crate::ast::*;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub enum TypeDecl {
    Struct(StructDecl),
    Enum(EnumDecl),
}

#[derive(Debug, Clone)]
pub struct Env {
    pub types: HashMap<String, TypeDecl>,
    pub functions: HashMap<String, Function>,
}

impl Env {
    pub fn build(program: &Program) -> Result<Self, String> {
        let mut types = HashMap::new();
        let mut functions = HashMap::new();

        for decl in &program.declarations {
            match decl {
                Declaration::Struct(s) => {
                    if types.contains_key(&s.name) {
                        return Err(format!("Duplicate declaration of type '{}'", s.name));
                    }
                    types.insert(s.name.clone(), TypeDecl::Struct(s.clone()));
                }
                Declaration::Enum(e) => {
                    if types.contains_key(&e.name) {
                        return Err(format!("Duplicate declaration of type '{}'", e.name));
                    }
                    types.insert(e.name.clone(), TypeDecl::Enum(e.clone()));
                }
                Declaration::Fn(f) => {
                    if functions.contains_key(&f.name) {
                        return Err(format!("Duplicate declaration of function '{}'", f.name));
                    }
                    functions.insert(f.name.clone(), f.clone());
                }
            }
        }

        Ok(Env { types, functions })
    }

    pub fn validate_type(&self, ty: &Type) -> Result<(), String> {
        match ty {
            Type::Number | Type::Boolean => Ok(()),
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

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Number, Type::Number) => true,
            (Type::Boolean, Type::Boolean) => true,
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

    pub fn infer_place_type(&self, place: &Place, locals: &HashMap<String, Type>) -> Result<Type, String> {
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
                        .find(|(f_name, _)| f_name == field_name)
                        .map(|(_, f_ty)| f_ty.clone())
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
                        .find(|(v_name, _)| v_name == variant_name)
                        .map(|(_, v_ty)| v_ty.clone())
                        .ok_or_else(|| format!("Enum '{}' has no variant '{}'", name, variant_name)),
                    Some(TypeDecl::Struct(_)) => Err(format!(
                        "Cannot downcast struct type '{}'", name
                    )),
                    None => Err(format!("Use of undeclared type '{}'", name)),
                }
            }
        }
    }

    pub fn infer_operand_type(&self, op: &Operand, locals: &HashMap<String, Type>) -> Result<Type, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.infer_place_type(place, locals),
            Operand::Const(c) => match c {
                ConstVal::Number(_) => Ok(Type::Number),
                ConstVal::Boolean(_) => Ok(Type::Boolean),
                ConstVal::FnName(name) => {
                    let f = self.functions.get(name).ok_or_else(|| format!("Undeclared function name '{}'", name))?;
                    let param_tys = f.params.iter().map(|(_, t)| t.clone()).collect();
                    Ok(Type::Fn(param_tys))
                }
            }
        }
    }

    pub fn infer_rvalue_type(&self, rvalue: &RValue, locals: &HashMap<String, Type>) -> Result<Type, String> {
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
                let (_, variant_ty) = e_decl.variants.iter()
                    .find(|(v, _)| v == variant_name)
                    .ok_or_else(|| format!("Enum '{}' has no variant '{}'", enum_name, variant_name))?;

                let op_ty = self.infer_operand_type(op, locals)?;
                if !self.types_match(variant_ty, &op_ty) {
                    return Err(format!("Variant '{}' of enum '{}' expects type {:?}, found {:?}", variant_name, enum_name, variant_ty, op_ty));
                }

                Ok(Type::Custom(enum_name.clone()))
            }
        }
    }

    pub fn typecheck(&self) -> Result<(), String> {
        // Validate struct fields and enum variants
        for type_decl in self.types.values() {
            match type_decl {
                TypeDecl::Struct(s) => {
                    for (f_name, f_ty) in &s.fields {
                        self.validate_type(f_ty).map_err(|err| format!("In struct '{}', field '{}': {}", s.name, f_name, err))?;
                    }
                }
                TypeDecl::Enum(e) => {
                    for (v_name, v_ty) in &e.variants {
                        self.validate_type(v_ty).map_err(|err| format!("In enum '{}', variant '{}': {}", e.name, v_name, err))?;
                    }
                }
            }
        }

        // Validate all functions
        for f in self.functions.values() {
            for (p_name, p_ty) in &f.params {
                self.validate_type(p_ty).map_err(|err| format!("In function '{}', parameter '{}': {}", f.name, p_name, err))?;
            }

            if let Some(body) = &f.body {
                if body.blocks.is_empty() {
                    return Err(format!(
                        "Function '{}' has no entry block: body must contain at least one basic block",
                        f.name
                    ));
                }
                let mut locals_map = HashMap::new();
                for (p_name, p_ty) in &f.params {
                    if locals_map.insert(p_name.clone(), p_ty.clone()).is_some() {
                        return Err(format!("Duplicate variable name '{}' in parameters of function '{}'", p_name, f.name));
                    }
                }
                for (l_name, l_ty) in &body.locals {
                    self.validate_type(l_ty).map_err(|err| format!("In function '{}', local '{}': {}", f.name, l_name, err))?;
                    if locals_map.insert(l_name.clone(), l_ty.clone()).is_some() {
                        return Err(format!("Duplicate variable name '{}' in locals/parameters of function '{}'", l_name, f.name));
                    }
                }

                let block_labels: HashSet<String> = body.blocks.iter().map(|b| b.label.clone()).collect();

                for block in &body.blocks {
                    self.typecheck_block(f, block, &locals_map, &block_labels)?;
                }
            }
        }

        Ok(())
    }

    fn typecheck_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        locals: &HashMap<String, Type>,
        block_labels: &HashSet<String>,
    ) -> Result<(), String> {
        for stmt in &block.statements {
            match stmt {
                Statement::Assign(place, rvalue) => {
                    let lhs_ty = self.infer_place_type(place, locals)
                        .map_err(|e| format!("In function '{}', block '{}', assignment LHS: {}", func.name, block.label, e))?;
                    let rhs_ty = self.infer_rvalue_type(rvalue, locals)
                        .map_err(|e| format!("In function '{}', block '{}', assignment RHS: {}", func.name, block.label, e))?;
                    if !self.types_match(&lhs_ty, &rhs_ty) {
                        return Err(format!(
                            "In function '{}', block '{}': Type mismatch in assignment. LHS is {:?}, RHS is {:?}",
                            func.name, block.label, lhs_ty, rhs_ty
                        ));
                    }
                }
                Statement::Call(target, args) => {
                    let target_ty = self.infer_operand_type(target, locals)
                        .map_err(|e| format!("In function '{}', block '{}', call target: {}", func.name, block.label, e))?;
                    
                    if let Type::Fn(param_tys) = target_ty {
                        if args.len() != param_tys.len() {
                            return Err(format!(
                                "In function '{}', block '{}': Wrong number of arguments for call. Expected {}, found {}",
                                func.name, block.label, param_tys.len(), args.len()
                            ));
                        }
                        for (i, (arg, param_ty)) in args.iter().zip(param_tys.iter()).enumerate() {
                            let arg_ty = self.infer_operand_type(arg, locals)
                                .map_err(|e| format!("In function '{}', block '{}', call arg {}: {}", func.name, block.label, i, e))?;
                            if !self.types_match(param_ty, &arg_ty) {
                                return Err(format!(
                                    "In function '{}', block '{}': Call argument {} type mismatch. Expected {:?}, found {:?}",
                                    func.name, block.label, i, param_ty, arg_ty
                                ));
                            }
                        }
                    } else {
                        return Err(format!(
                            "In function '{}', block '{}': Call target is not a function type: {:?}",
                            func.name, block.label, target_ty
                        ));
                    }
                }
            }
        }

        // Typecheck terminator
        match &block.terminator {
            Terminator::Goto(label) => {
                if !block_labels.contains(label) {
                    return Err(format!(
                        "In function '{}', block '{}': goto targets undefined block '{}'",
                        func.name, block.label, label
                    ));
                }
            }
            Terminator::Return => {}
            Terminator::Branch { cond, true_label, false_label } => {
                let cond_ty = self.infer_operand_type(cond, locals)
                    .map_err(|e| format!("In function '{}', block '{}', branch condition: {}", func.name, block.label, e))?;
                if cond_ty != Type::Boolean {
                    return Err(format!(
                        "In function '{}', block '{}': branch condition must be boolean, found {:?}",
                        func.name, block.label, cond_ty
                    ));
                }
                if !block_labels.contains(true_label) {
                    return Err(format!(
                        "In function '{}', block '{}': branch true target undefined block '{}'",
                        func.name, block.label, true_label
                    ));
                }
                if !block_labels.contains(false_label) {
                    return Err(format!(
                        "In function '{}', block '{}': branch false target undefined block '{}'",
                        func.name, block.label, false_label
                    ));
                }
            }
            Terminator::SwitchEnum { place, cases } => {
                let place_ty = self.infer_place_type(place, locals)
                    .map_err(|e| format!("In function '{}', block '{}', switchEnum place: {}", func.name, block.label, e))?;

                let enum_name = match &place_ty {
                    Type::Custom(name) => name,
                    _ => return Err(format!(
                        "In function '{}', block '{}': switchEnum place must be an enum type, found {:?}",
                        func.name, block.label, place_ty
                    ))
                };

                let e_decl = match self.types.get(enum_name) {
                    Some(TypeDecl::Enum(e)) => e,
                    Some(TypeDecl::Struct(_)) => return Err(format!(
                        "In function '{}', block '{}': switchEnum place must be an enum type, found struct '{}'",
                        func.name, block.label, enum_name
                    )),
                    None => return Err(format!(
                        "In function '{}', block '{}': Undeclared enum '{}' in switchEnum",
                        func.name, block.label, enum_name
                    )),
                };

                for (variant, label) in cases {
                    if !e_decl.variants.iter().any(|(v, _)| v == variant) {
                        return Err(format!(
                            "In function '{}', block '{}': variant '{}' is not part of enum '{}'",
                            func.name, block.label, variant, enum_name
                        ));
                    }
                    if !block_labels.contains(label) {
                        return Err(format!(
                            "In function '{}', block '{}': switchEnum variant '{}' targets undefined block '{}'",
                            func.name, block.label, variant, label
                        ));
                    }
                }
            }
            Terminator::Abort => {}
            Terminator::Unreachable => {}
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn check(src: &str) -> Result<(), String> {
        let program = Parser::new(src.to_string())
            .parse()
            .map_err(|e| format!("parse error: {}", e))?;
        Env::build(&program)?.typecheck()
    }

    #[track_caller]
    fn assert_ok(src: &str) {
        if let Err(e) = check(src) {
            panic!("expected success, got error: {}\n--- source ---\n{}", e, src);
        }
    }

    #[track_caller]
    fn assert_err(src: &str, needle: &str) {
        match check(src) {
            Ok(()) => panic!(
                "expected error containing {:?}, got Ok\n--- source ---\n{}",
                needle, src
            ),
            Err(e) => assert!(
                e.contains(needle),
                "expected error containing {:?}, got: {}\n--- source ---\n{}",
                needle,
                e,
                src
            ),
        }
    }

    // ---------- Env::build ----------

    #[test]
    fn env_build_ok_mixed_decls() {
        assert_ok(
            "
            struct Point { x: number y: number }
            enum Option { None: Option Some: number }
            fn f() { entry: return }
            extern fn g();
            ",
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
            struct P { x: number y: number }
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
        assert_ok(
            "
            enum Option { None: Option Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                x = copy (o as Some).payload;
                return
            }
            ",
        );
    }

    #[test]
    fn place_downcast_unknown_variant_error() {
        assert_err(
            "
            enum Option { None: Option Some: number }
            fn f(o: Option) {
              x: number;
              entry:
                x = copy (o as Wat).payload;
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
                x = copy (r as Some).payload;
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
                x = copy (s as Some).payload;
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
            struct Ptr { r: &number }
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
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
        assert_ok(
            "
            enum Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                (o as Some).payload = 7;
                return
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
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
            enum Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: nowhere]
            }
            ",
            "targets undefined block 'nowhere'",
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
    fn switch_enum_non_exhaustive_ok() {
        // Syntactic switchEnum does not require exhaustiveness; whether
        // omitted variants are actually reachable is a flow-check concern.
        assert_ok(
            "
            enum Option { None: Option Some: number }
            fn f(o: Option) {
              entry:
                switchEnum(o) [None: end]
              end:
                return
            }
            ",
        );
    }

    #[test]
    fn empty_function_body_error() {
        assert_err("fn f() { }", "Function 'f' has no entry block");
    }
}

