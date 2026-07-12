use crate::ast::*;
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::{fmt_error, push_error, push_error_at};
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
    /// Build the checker's projection over `program`. Returns the env
    /// plus any duplicate-declaration errors — callers that care (i.e.
    /// the main pipeline) plumb them into their `Diagnostics`; callers
    /// that don't (i.e. tests and codegen) can drop them. Duplicate
    /// declarations are the only failure mode.
    pub fn build(program: &Program) -> (Self, Vec<Diagnostic>) {
        let mut types = IndexMap::new();
        let mut functions = IndexMap::new();
        let mut errors: Vec<Diagnostic> = Vec::new();

        // Preload intrinsic signatures. Reserved-namespace names (`$*`)
        // can never conflict with user declarations at the lexical
        // level, but if we ever add non-`$` prelude items, redeclarations
        // will hit the duplicate-declaration path below.
        for f in crate::intrinsics::prelude_fns() {
            functions.insert(f.name.clone(), f);
        }

        use crate::diagnostics::DiagCode;
        for decl in &program.declarations {
            match decl {
                Declaration::Struct(s) => {
                    if types.contains_key(&s.name) {
                        errors.push(
                            Diagnostic::new(
                                DiagCode::Unspecified,
                                format!("Duplicate declaration of type '{}'", s.name),
                            )
                            .at(s.name_span),
                        );
                    } else {
                        types.insert(s.name.clone(), TypeDecl::Struct(s.clone()));
                    }
                }
                Declaration::Enum(e) => {
                    if types.contains_key(&e.name) {
                        errors.push(
                            Diagnostic::new(
                                DiagCode::Unspecified,
                                format!("Duplicate declaration of type '{}'", e.name),
                            )
                            .at(e.name_span),
                        );
                    } else {
                        types.insert(e.name.clone(), TypeDecl::Enum(e.clone()));
                    }
                }
                Declaration::Fn(f) => {
                    if functions.contains_key(&f.name) {
                        errors.push(
                            Diagnostic::new(
                                DiagCode::Unspecified,
                                format!("Duplicate declaration of function '{}'", f.name),
                            )
                            .at(f.name_span),
                        );
                    } else {
                        functions.insert(f.name.clone(), f.clone());
                    }
                }
            }
        }

        (Env { types, functions }, errors)
    }

    /// Refresh cached function definitions from `program` in place.
    /// Elaboration passes mutate function bodies; after that the cloned
    /// `functions` map in `Env` is stale. This resyncs the map without
    /// touching `types` (declarations aren't mutated by elaboration).
    /// Intrinsic signatures are re-preloaded so they survive the sync.
    pub fn sync_functions(&mut self, program: &Program) {
        self.functions.clear();
        for f in crate::intrinsics::prelude_fns() {
            self.functions.insert(f.name.clone(), f);
        }
        for decl in &program.declarations {
            if let Declaration::Fn(f) = decl {
                self.functions.insert(f.name.clone(), f.clone());
            }
        }
    }

    pub fn validate_type(&self, ty: &Type) -> Result<(), String> {
        match ty {
            Type::Int(_) | Type::Float(_) | Type::Boolean | Type::Unit | Type::Never => Ok(()),
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
            Type::Ref(_, inner) => self.validate_type(inner),
            Type::RawPtr(inner) => self.validate_type(inner),
            Type::Array(elem, _) => self.validate_type(elem),
        }
    }

    /// Type of `field` in the struct type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared struct or the field doesn't exist.
    pub fn field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        let Type::Custom(name) = ty else {
            return None;
        };
        match self.types.get(name) {
            Some(TypeDecl::Struct(s)) => s
                .fields
                .iter()
                .find(|f| f.name == field)
                .map(|f| f.ty.clone()),
            _ => None,
        }
    }

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Int(a), Type::Int(b)) => a == b,
            (Type::Float(a), Type::Float(b)) => a == b,
            (Type::Boolean, Type::Boolean) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Never, Type::Never) => true,
            (Type::Custom(a), Type::Custom(b)) => a == b,
            (Type::Fn(a), Type::Fn(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter().zip(b.iter()).all(|(x, y)| self.types_match(x, y))
            }
            (Type::Ref(k1, i1), Type::Ref(k2, i2)) => k1 == k2 && self.types_match(i1, i2),
            (Type::RawPtr(i1), Type::RawPtr(i2)) => self.types_match(i1, i2),
            (Type::Array(e1, n1), Type::Array(e2, n2)) => {
                n1 == n2 && self.types_match(e1, e2)
            }
            _ => false,
        }
    }

    pub fn infer_place_type(
        &self,
        place: &Place,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, String> {
        match place {
            Place::Var(name) => locals
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Use of undeclared variable '{}'", name)),
            Place::Deref(inner) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                match inner_ty {
                    Type::Ref(_, pointee) => Ok(*pointee),
                    Type::RawPtr(pointee) => Ok(*pointee),
                    other => Err(format!(
                        "Cannot dereference non-pointer type {:?}",
                        other
                    )),
                }
            }
            Place::Field(inner, field_name) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                let name = match &inner_ty {
                    Type::Custom(n) => n,
                    _ => {
                        return Err(format!(
                            "Cannot project field '{}' of non-struct type {:?}",
                            field_name, inner_ty
                        ))
                    }
                };
                match self.types.get(name) {
                    Some(TypeDecl::Struct(s)) => s
                        .fields
                        .iter()
                        .find(|f| f.name == *field_name)
                        .map(|f| f.ty.clone())
                        .ok_or_else(|| format!("Struct '{}' has no field '{}'", name, field_name)),
                    Some(TypeDecl::Enum(_)) => Err(format!(
                        "Cannot project field '{}' of enum type '{}'",
                        field_name, name
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
                    Some(TypeDecl::Enum(e)) => e
                        .variants
                        .iter()
                        .find(|v| v.name == *variant_name)
                        .map(|v| v.ty.clone())
                        .ok_or_else(|| {
                            format!("Enum '{}' has no variant '{}'", name, variant_name)
                        }),
                    Some(TypeDecl::Struct(_)) => {
                        Err(format!("Cannot downcast struct type '{}'", name))
                    }
                    None => Err(format!("Use of undeclared type '{}'", name)),
                }
            }
            Place::Index(inner, op) => {
                let inner_ty = self.infer_place_type(inner, locals)?;
                let Type::Array(elem, n) = inner_ty else {
                    return Err(format!(
                        "Cannot index non-array type {:?}",
                        inner_ty
                    ));
                };
                // Index operand must be an integer type.
                let op_ty = self.infer_operand_type(op, locals)?;
                if !matches!(op_ty, Type::Int(_)) {
                    return Err(format!(
                        "Array index must be an integer, got {:?}",
                        op_ty
                    ));
                }
                // Constant-index bounds check. Cheap defensive check
                // that catches known-bad accesses at check time.
                // Dynamic indices are left to the HLL / runtime.
                if let Some(k) = const_int_operand(op) {
                    if k >= n {
                        return Err(format!(
                            "Array index {} out of bounds for [_; {}]",
                            k, n
                        ));
                    }
                }
                Ok(*elem)
            }
        }
    }

    pub fn infer_operand_type(
        &self,
        op: &Operand,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.infer_place_type(place, locals),
            Operand::Const(c) => match c {
                ConstVal::Int { ty, .. } => Ok(Type::Int(*ty)),
                ConstVal::Float { ty, .. } => Ok(Type::Float(*ty)),
                ConstVal::Boolean(_) => Ok(Type::Boolean),
                ConstVal::Unit => Ok(Type::Unit),
                ConstVal::FnName(name) => {
                    let f = self
                        .functions
                        .get(name)
                        .ok_or_else(|| format!("Undeclared function name '{}'", name))?;
                    let param_tys = f.params.iter().map(|p| p.ty.clone()).collect();
                    Ok(Type::Fn(param_tys))
                }
                ConstVal::ByteStr(bytes) => Ok(Type::Array(
                    Box::new(Type::Int(IntTy::U8)),
                    bytes.len() as u64,
                )),
            },
        }
    }

    pub fn infer_rvalue_type(
        &self,
        rvalue: &RValue,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, String> {
        match rvalue {
            RValue::Use(op) => self.infer_operand_type(op, locals),
            RValue::Ref(kind, place) => {
                let pointee_ty = self.infer_place_type(place, locals)?;
                Ok(Type::Ref(kind.clone(), Box::new(pointee_ty)))
            }
            RValue::RawRef(place) => {
                let pointee_ty = self.infer_place_type(place, locals)?;
                Ok(Type::RawPtr(Box::new(pointee_ty)))
            }
            RValue::EnumConstr(enum_name, variant_name, op) => {
                let e_decl = match self.types.get(enum_name) {
                    Some(TypeDecl::Enum(e)) => e,
                    Some(TypeDecl::Struct(_)) => {
                        return Err(format!("'{}' is a struct, not an enum", enum_name));
                    }
                    None => return Err(format!("Undeclared enum '{}'", enum_name)),
                };
                let variant = e_decl
                    .variants
                    .iter()
                    .find(|v| v.name == *variant_name)
                    .ok_or_else(|| {
                        format!("Enum '{}' has no variant '{}'", enum_name, variant_name)
                    })?;

                let op_ty = self.infer_operand_type(op, locals)?;
                if !self.types_match(&variant.ty, &op_ty) {
                    return Err(format!(
                        "Variant '{}' of enum '{}' expects type {:?}, found {:?}",
                        variant_name, enum_name, variant.ty, op_ty
                    ));
                }

                Ok(Type::Custom(enum_name.clone()))
            }
            RValue::ArrayLit(ops) => {
                // Empty array literal: `[]` has type `[Unit; 0]` as a
                // placeholder — types_match will still reject any real
                // target type mismatch. Effectively unusable but not
                // an error at inference time.
                if ops.is_empty() {
                    return Ok(Type::Array(Box::new(Type::Unit), 0));
                }
                let first_ty = self.infer_operand_type(&ops[0], locals)?;
                for (i, op) in ops.iter().enumerate().skip(1) {
                    let ty = self.infer_operand_type(op, locals)?;
                    if !self.types_match(&first_ty, &ty) {
                        return Err(format!(
                            "Array literal element {} has type {:?}, expected {:?}",
                            i, ty, first_ty
                        ));
                    }
                }
                Ok(Type::Array(Box::new(first_ty), ops.len() as u64))
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
                            push_error_at!(
                                d,
                                f.span,
                                "In struct '{}', field '{}' is declared more than once",
                                s.name,
                                f.name
                            );
                        }
                        if let Err(e) = self.validate_type(&f.ty) {
                            push_error_at!(
                                d,
                                f.span,
                                "In struct '{}', field '{}': {}",
                                s.name,
                                f.name,
                                e
                            );
                        }
                    }
                }
                TypeDecl::Enum(e) => {
                    let mut seen: HashSet<&str> = HashSet::new();
                    for v in &e.variants {
                        if !seen.insert(v.name.as_str()) {
                            push_error_at!(
                                d,
                                v.span,
                                "In enum '{}', variant '{}' is declared more than once",
                                e.name,
                                v.name
                            );
                        }
                        if let Err(err) = self.validate_type(&v.ty) {
                            push_error_at!(
                                d,
                                v.span,
                                "In enum '{}', variant '{}': {}",
                                e.name,
                                v.name,
                                err
                            );
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
                push_error_at!(
                    d,
                    p.span,
                    "In function '{}', parameter '{}': {}",
                    f.name,
                    p.name,
                    e
                );
            }
        }

        // `main` has a fixed signature convention — codegen synthesizes
        // an `i32 @main()` wrapper that calls it. Reject any other
        // shape here so bad programs fail at check time instead of
        // producing invalid IR.
        if f.name == "main" {
            check_main_signature(f, d);
        }

        let Some(body) = &f.body else {
            return;
        };

        if body.blocks.is_empty() {
            push_error_at!(
                d,
                f.name_span,
                "Function '{}' has no entry block: body must contain at least one basic block",
                f.name
            );
            return;
        }

        // Build the locals map. On name conflict, keep the first binding and
        // record an error — later checks still see a consistent scope.
        let mut locals_map: IndexMap<String, Type> = IndexMap::new();
        for p in &f.params {
            if locals_map.contains_key(&p.name) {
                push_error_at!(
                    d,
                    p.span,
                    "Duplicate variable name '{}' in parameters of function '{}'",
                    p.name,
                    f.name
                );
            } else {
                locals_map.insert(p.name.clone(), p.ty.clone());
            }
        }
        for l in &body.locals {
            if let Err(e) = self.validate_type(&l.ty) {
                push_error_at!(
                    d,
                    l.span,
                    "In function '{}', local '{}': {}",
                    f.name,
                    l.name,
                    e
                );
            }
            if locals_map.contains_key(&l.name) {
                push_error_at!(
                    d,
                    l.span,
                    "Duplicate variable name '{}' in locals/parameters of function '{}'",
                    l.name,
                    f.name
                );
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
                d.push_error(e);
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
    ) -> Result<(), Diagnostic> {
        match stmt {
            Statement::Assign(place, rvalue) => {
                let lhs_ty = self
                    .infer_place_type(place, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "assignment LHS: {}", e))?;
                let rhs_ty = self
                    .infer_rvalue_type(rvalue, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "assignment RHS: {}", e))?;
                if !self.types_match(&lhs_ty, &rhs_ty) {
                    return Err(fmt_error!(
                        stmt_span,
                        func,
                        block,
                        "Type mismatch in assignment. LHS is {:?}, RHS is {:?}",
                        lhs_ty,
                        rhs_ty
                    ));
                }
                Ok(())
            }
            Statement::Call(target, args) => {
                let target_ty = self
                    .infer_operand_type(target, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "call target: {}", e))?;

                let Type::Fn(param_tys) = target_ty else {
                    return Err(fmt_error!(
                        stmt_span,
                        func,
                        block,
                        "Call target is not a function type: {:?}",
                        target_ty
                    ));
                };

                if args.len() != param_tys.len() {
                    return Err(fmt_error!(
                        stmt_span,
                        func,
                        block,
                        "Wrong i64 of arguments for call. Expected {}, found {}",
                        param_tys.len(),
                        args.len()
                    ));
                }
                for (i, (arg, param_ty)) in args.iter().zip(param_tys.iter()).enumerate() {
                    let arg_ty = self
                        .infer_operand_type(arg, locals)
                        .map_err(|e| fmt_error!(stmt_span, func, block, "call arg {}: {}", i, e))?;
                    if !self.types_match(param_ty, &arg_ty) {
                        return Err(fmt_error!(
                            stmt_span,
                            func,
                            block,
                            "Call argument {} type mismatch. Expected {:?}, found {:?}",
                            i,
                            param_ty,
                            arg_ty
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
            Statement::Unborrow(place) => {
                let ty = self
                    .infer_place_type(place, locals)
                    .map_err(|e| fmt_error!(stmt_span, func, block, "unborrow: {}", e))?;
                if !matches!(ty, Type::Ref(_, _)) {
                    return Err(fmt_error!(
                        stmt_span,
                        func,
                        block,
                        "unborrow requires a reference-typed place, found {:?}",
                        ty
                    ));
                }
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
                    push_error!(
                        d,
                        ts,
                        func,
                        block,
                        "goto targets undefined block '{}'",
                        label
                    );
                }
            }
            Terminator::Return => {}
            Terminator::Branch {
                cond,
                true_label,
                false_label,
            } => {
                match self.infer_operand_type(cond, locals) {
                    Ok(cond_ty) if cond_ty != Type::Boolean => push_error!(
                        d,
                        ts,
                        func,
                        block,
                        "branch condition must be boolean, found {:?}",
                        cond_ty
                    ),
                    Ok(_) => {}
                    Err(e) => push_error!(d, ts, func, block, "branch condition: {}", e),
                }
                if !block_labels.contains(true_label) {
                    push_error!(
                        d,
                        ts,
                        func,
                        block,
                        "branch true target undefined block '{}'",
                        true_label
                    );
                }
                if !block_labels.contains(false_label) {
                    push_error!(
                        d,
                        ts,
                        func,
                        block,
                        "branch false target undefined block '{}'",
                        false_label
                    );
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
                                d,
                                ts,
                                func,
                                block,
                                "switchEnum place must be an enum type, found struct '{}'",
                                name
                            );
                            None
                        }
                        None => {
                            push_error!(
                                d,
                                ts,
                                func,
                                block,
                                "Undeclared enum '{}' in switchEnum",
                                name
                            );
                            None
                        }
                    },
                    Ok(other) => {
                        push_error!(
                            d,
                            ts,
                            func,
                            block,
                            "switchEnum place must be an enum type, found {:?}",
                            other
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
                                d,
                                ts,
                                func,
                                block,
                                "variant '{}' is not part of enum '{}'",
                                variant,
                                e_decl.name
                            );
                        }
                    }
                    if !block_labels.contains(label) {
                        push_error!(
                            d,
                            ts,
                            func,
                            block,
                            "switchEnum variant '{}' targets undefined block '{}'",
                            variant,
                            label
                        );
                    }
                }
            }
            Terminator::Abort => {}
            Terminator::Unreachable => {}
        }
    }
}

/// Verify `fn main`'s signature is one of the two accepted shapes:
///
/// - `fn main()` — the wrapper always returns 0.
/// - `fn main(exit: &out i32)` — the wrapper returns the value
///   written through `exit`.
///
/// Anything else is a check error. Externs (no body) are ignored;
/// this only fires on definitions.
fn check_main_signature(f: &Function, d: &mut Diagnostics) {
    if f.is_extern {
        return;
    }
    let expected = Type::Ref(RefKind::Out, Box::new(Type::Int(IntTy::I32)));
    match f.params.as_slice() {
        [] => {}
        [p] if p.ty == expected => {}
        [p] => {
            push_error_at!(
                d,
                p.span,
                "In function 'main': single parameter must be '&out i32', found {:?}",
                p.ty
            );
        }
        _ => {
            push_error_at!(
                d,
                f.name_span,
                "In function 'main': takes at most one parameter (an optional '&out i32'), found {} parameters",
                f.params.len()
            );
        }
    }
}

#[cfg(test)]
mod build_tests;
#[cfg(test)]
mod control_flow_tests;
#[cfg(test)]
mod declaration_tests;
#[cfg(test)]
mod error_span_tests;
#[cfg(test)]
mod function_tests;
#[cfg(test)]
mod operand_typing_tests;
#[cfg(test)]
mod place_typing_tests;
#[cfg(test)]
mod rvalue_typing_tests;
#[cfg(test)]
mod statement_tests;
