//! The type environment.
//!
//! Owns the declaration table (struct/enum/function) and provides
//! type-of-expression queries used by all downstream passes.
//! Environment construction (`build`) collects duplicate-declaration
//! errors up front so later passes see a well-formed lookup table.
//!
//! MIR type checking is pure computation, not inference — every
//! expression's type is determined structurally from its operands
//! plus the environment. The `type_of_*` methods walk that structure
//! and return either the concrete type or a `Diagnostic` explaining
//! why it couldn't be resolved.

use super::TypeCheckCode::*;
use super::TypeDecl;
use crate::diagnostics::Diagnostic;
use crate::mir::ast::*;
use indexmap::IndexMap;

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
        for f in crate::mir::intrinsics::prelude_fns() {
            functions.insert(f.name.clone(), f);
        }

        for decl in &program.declarations {
            match decl {
                Declaration::Struct(s) => {
                    if types.contains_key(&s.name) {
                        errors.push(
                            Diagnostic::new(DuplicateDeclaration, s.name_span, format!("Duplicate declaration of type '{}'", s.name)),
                        );
                    } else {
                        types.insert(s.name.clone(), TypeDecl::Struct(s.clone()));
                    }
                }
                Declaration::Enum(e) => {
                    if types.contains_key(&e.name) {
                        errors.push(
                            Diagnostic::new(DuplicateDeclaration, e.name_span, format!("Duplicate declaration of type '{}'", e.name)),
                        );
                    } else {
                        types.insert(e.name.clone(), TypeDecl::Enum(e.clone()));
                    }
                }
                Declaration::Fn(f) => {
                    if functions.contains_key(&f.name) {
                        errors.push(
                            Diagnostic::new(DuplicateDeclaration, f.name_span, format!("Duplicate declaration of function '{}'", f.name)),
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
        for f in crate::mir::intrinsics::prelude_fns() {
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
            Type::Int(_) | Type::Float(_) | Type::Bool | Type::Unit | Type::Never => Ok(()),
            Type::Custom(name, args) => {
                if !self.types.contains_key(name) {
                    return Err(format!("Use of undeclared type '{}'", name));
                }
                for a in args {
                    self.validate_type(a)?;
                }
                Ok(())
            }
            // A TypeVar is validated by the parser (which only emits it
            // for names in the current type-param scope). Nothing more
            // to check here.
            Type::TypeVar(_) => Ok(()),
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
        let Type::Custom(name, _args) = ty else {
            return None;
        };
        // Returns the raw declared field type; args are NOT substituted
        // in. Concretization happens at monomorphization time, so
        // callers that need the specialized type after that pass runs
        // will see it there. Correct as-is for non-generic decls.
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
            (Type::Bool, Type::Bool) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Never, Type::Never) => true,
            (Type::Custom(a_name, a_args), Type::Custom(b_name, b_args)) => {
                a_name == b_name
                    && a_args.len() == b_args.len()
                    && a_args
                        .iter()
                        .zip(b_args.iter())
                        .all(|(x, y)| self.types_match(x, y))
            }
            (Type::TypeVar(a), Type::TypeVar(b)) => a == b,
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

    /// Compute the type of a place. On failure returns a `Diagnostic`
    /// with a code and `span` — the `span` here is the enclosing
    /// syntactic construct (usually the statement or terminator span)
    /// since `Place` itself doesn't carry a source position.
    /// Function/block context is *not* set; the caller layers those
    /// on via `.in_function()` / `.in_block()` if desired.
    pub fn type_of_place(
        &self,
        place: &Place,
        span: Span,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, Diagnostic> {
        let err = |code, msg: String| Diagnostic::new(code, span, msg);
        match place {
            Place::Var(name) => locals.get(name).cloned().ok_or_else(|| {
                err(
                    UndeclaredVariable,
                    format!("Use of undeclared variable '{}'", name),
                )
            }),
            Place::Deref(inner) => {
                let inner_ty = self.type_of_place(inner, span, locals)?;
                match inner_ty {
                    Type::Ref(_, pointee) => Ok(*pointee),
                    Type::RawPtr(pointee) => Ok(*pointee),
                    other => Err(err(
                        DerefOfNonPointer,
                        format!("Cannot dereference non-pointer type {}", other),
                    )),
                }
            }
            Place::Field(inner, field_name) => {
                let inner_ty = self.type_of_place(inner, span, locals)?;
                let name = match &inner_ty {
                    Type::Custom(n, _) => n,
                    _ => {
                        return Err(err(
                            FieldOfNonStruct,
                            format!(
                                "Cannot project field '{}' of non-struct type {}",
                                field_name, inner_ty
                            ),
                        ))
                    }
                };
                match self.types.get(name) {
                    Some(TypeDecl::Struct(s)) => s
                        .fields
                        .iter()
                        .find(|f| f.name == *field_name)
                        .map(|f| f.ty.clone())
                        .ok_or_else(|| {
                            err(
                                NoSuchField,
                                format!("Struct '{}' has no field '{}'", name, field_name),
                            )
                        }),
                    Some(TypeDecl::Enum(_)) => Err(err(
                        FieldOfNonStruct,
                        format!(
                            "Cannot project field '{}' of enum type '{}'",
                            field_name, name
                        ),
                    )),
                    None => Err(err(
                        UndeclaredType,
                        format!("Use of undeclared type '{}'", name),
                    )),
                }
            }
            Place::Downcast(inner, variant_name) => {
                let inner_ty = self.type_of_place(inner, span, locals)?;
                let name = match &inner_ty {
                    Type::Custom(n, _) => n,
                    _ => {
                        return Err(err(
                            DowncastOfNonEnum,
                            format!("Cannot downcast non-enum type {}", inner_ty),
                        ))
                    }
                };
                match self.types.get(name) {
                    Some(TypeDecl::Enum(e)) => e
                        .variants
                        .iter()
                        .find(|v| v.name == *variant_name)
                        .map(|v| v.ty.clone())
                        .ok_or_else(|| {
                            err(
                                NoSuchVariant,
                                format!("Enum '{}' has no variant '{}'", name, variant_name),
                            )
                        }),
                    Some(TypeDecl::Struct(_)) => Err(err(
                        DowncastOfNonEnum,
                        format!("Cannot downcast struct type '{}'", name),
                    )),
                    None => Err(err(
                        UndeclaredType,
                        format!("Use of undeclared type '{}'", name),
                    )),
                }
            }
            Place::Index(inner, op) => {
                let inner_ty = self.type_of_place(inner, span, locals)?;
                let Type::Array(elem, n) = inner_ty else {
                    return Err(err(
                        IndexOfNonArray,
                        format!("Cannot index non-array type {}", inner_ty),
                    ));
                };
                // Index operand must be an integer type.
                let op_ty = self.type_of_operand(op, span, locals)?;
                if !matches!(op_ty, Type::Int(_)) {
                    return Err(err(
                        ArrayIndexNotInteger,
                        format!("Array index must be an integer, got {}", op_ty),
                    ));
                }
                // Constant-index bounds check. Cheap defensive check
                // that catches known-bad accesses at check time.
                // Dynamic indices are left to the HLL / runtime.
                if let Some(k) = const_int_operand(op) {
                    if k >= n {
                        return Err(err(
                            ArrayIndexOutOfBounds,
                            format!("Array index {} out of bounds for [_; {}]", k, n),
                        ));
                    }
                }
                Ok(*elem)
            }
        }
    }

    /// See [`type_of_place`] for the `span` argument's role.
    pub fn type_of_operand(
        &self,
        op: &Operand,
        span: Span,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, Diagnostic> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                self.type_of_place(place, span, locals)
            }
            Operand::Const(c) => match c {
                ConstVal::Int { ty, .. } => Ok(Type::Int(*ty)),
                ConstVal::Float { ty, .. } => Ok(Type::Float(*ty)),
                ConstVal::Bool(_) => Ok(Type::Bool),
                ConstVal::Unit => Ok(Type::Unit),
                ConstVal::FnName(name, _type_args) => {
                    // Returns the raw declared fn signature; `_type_args`
                    // are NOT substituted into param types. Concretization
                    // happens at monomorphization time. Correct as-is for
                    // non-generic fns.
                    let f = self.functions.get(name).ok_or_else(|| {
                        Diagnostic::new(
                            UndeclaredFunction,
                            span,
                            format!("Undeclared function name '{}'", name),
                        )
                    })?;
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

    pub fn type_of_rvalue(
        &self,
        rvalue: &RValue,
        span: Span,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, Diagnostic> {
        let err = |code, msg: String| Diagnostic::new(code, span, msg);
        match rvalue {
            RValue::Use(op) => self.type_of_operand(op, span, locals),
            RValue::Ref(kind, place) => {
                let pointee_ty = self.type_of_place(place, span, locals)?;
                Ok(Type::Ref(kind.clone(), Box::new(pointee_ty)))
            }
            RValue::RawRef(place) => {
                let pointee_ty = self.type_of_place(place, span, locals)?;
                Ok(Type::RawPtr(Box::new(pointee_ty)))
            }
            RValue::EnumConstr(enum_name, variant_name, op) => {
                let e_decl = match self.types.get(enum_name) {
                    Some(TypeDecl::Enum(e)) => e,
                    Some(TypeDecl::Struct(_)) => {
                        return Err(err(
                            EnumConstrOnNonEnum,
                            format!("'{}' is a struct, not an enum", enum_name),
                        ));
                    }
                    None => {
                        return Err(err(
                            EnumConstrOnNonEnum,
                            format!("Undeclared enum '{}'", enum_name),
                        ))
                    }
                };
                let variant = e_decl
                    .variants
                    .iter()
                    .find(|v| v.name == *variant_name)
                    .ok_or_else(|| {
                        err(
                            NoSuchVariant,
                            format!("Enum '{}' has no variant '{}'", enum_name, variant_name),
                        )
                    })?;

                let op_ty = self.type_of_operand(op, span, locals)?;
                if !self.types_match(&variant.ty, &op_ty) {
                    return Err(err(
                        EnumConstrPayloadTypeMismatch,
                        format!(
                            "Variant '{}' of enum '{}' expects type {}, found {}",
                            variant_name, enum_name, variant.ty, op_ty
                        ),
                    ));
                }

                Ok(Type::Custom(enum_name.clone(), Vec::new()))
            }
            RValue::ArrayLit(ops) => {
                // Empty array literal: `[]` has type `[Unit; 0]` as a
                // placeholder — types_match will still reject any real
                // target type mismatch. Effectively unusable but not
                // an error at inference time.
                if ops.is_empty() {
                    return Ok(Type::Array(Box::new(Type::Unit), 0));
                }
                let first_ty = self.type_of_operand(&ops[0], span, locals)?;
                for (i, op) in ops.iter().enumerate().skip(1) {
                    let ty = self.type_of_operand(op, span, locals)?;
                    if !self.types_match(&first_ty, &ty) {
                        return Err(err(
                            ArrayLitElementTypeMismatch,
                            format!(
                                "Array literal element {} has type {}, expected {}",
                                i, ty, first_ty
                            ),
                        ));
                    }
                }
                Ok(Type::Array(Box::new(first_ty), ops.len() as u64))
            }
        }
    }
}
