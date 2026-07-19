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
use crate::mir::helpers::*;
use crate::mir::substructural::composition::{class_of, ParamScope};
use crate::mir::type_util::substitute_params;
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

    /// Validate `ty` against the current type-parameter scope.
    ///
    /// `Custom(name, args)` triggers a use-site check: arity must
    /// match the decl's `type_params` and each arg's substructural
    /// class must imply the corresponding param's declared bounds.
    /// This pairs with the decl-side marker check in
    /// [`composition`](crate::mir::substructural::composition) —
    /// together they license `class_of(Custom(_, args))` returning
    /// the decl's declared markers without substitution.
    pub fn validate_type(&self, ty: &Type, scope: ParamScope) -> Result<(), String> {
        match ty {
            Type::Int(_) | Type::Float(_) | Type::Bool | Type::Unit | Type::Never => Ok(()),
            Type::Custom(name, _, args) => {
                let decl_params: &[TypeParam] = match self.types.get(name) {
                    Some(TypeDecl::Struct(s)) => &s.type_params,
                    Some(TypeDecl::Enum(e)) => &e.type_params,
                    None => return Err(format!("Use of undeclared type '{}'", name)),
                };
                if args.len() != decl_params.len() {
                    return Err(format!(
                        "Type '{}' expects {} type argument(s), got {}",
                        name,
                        decl_params.len(),
                        args.len(),
                    ));
                }
                for (arg, param) in args.iter().zip(decl_params.iter()) {
                    self.validate_type(arg, scope)?;
                    let arg_class = class_of(arg, self, scope);
                    for bound in param.bounds.iter_declared() {
                        if !arg_class.implies(bound) {
                            return Err(format!(
                                "Type argument {} for '{}::{}' does not satisfy required bound '{}'",
                                arg, name, param.name, bound.name(),
                            ));
                        }
                    }
                }
                Ok(())
            }
            // A `Param` is validated by the parser (which only emits it
            // for names in the current type-param scope). Nothing more
            // to check here.
            Type::Param(_) => Ok(()),
            Type::Fn(params) => {
                for p in params {
                    self.validate_type(p, scope)?;
                }
                Ok(())
            }
            Type::Ref(_, _, inner) => self.validate_type(inner, scope),
            Type::RawPtr(inner) => self.validate_type(inner, scope),
            Type::Array(elem, _) => self.validate_type(elem, scope),
        }
    }

    /// Empty-scope convenience: for callers with no in-scope type
    /// parameters. A `Param(_)` reachable via this path is
    /// well-formed (Ok) but its markers can't be resolved to real
    /// bounds — use only outside of generic decl bodies.
    pub fn validate_type_empty_scope(&self, ty: &Type) -> Result<(), String> {
        self.validate_type(ty, &IndexMap::new())
    }

    /// Type of `field` in the struct type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared struct or the field doesn't exist.
    /// Substitutes the struct's type-parameter references (`Type::Param`)
    /// with the concrete args on `ty`, so `Box<i64>::inner` yields `i64`,
    /// not the raw declared `T`.
    pub fn field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        let Type::Custom(name, _, args) = ty else {
            return None;
        };
        let TypeDecl::Struct(s) = self.types.get(name)? else {
            return None;
        };
        let f_ty = &s.fields.iter().find(|f| f.name == field)?.ty;
        Some(substitute_params(f_ty, &s.type_params, args))
    }

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Int(a), Type::Int(b)) => a == b,
            (Type::Float(a), Type::Float(b)) => a == b,
            (Type::Bool, Type::Bool) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Never, Type::Never) => true,
            (Type::Custom(a_name, _, a_args), Type::Custom(b_name, _, b_args)) => {
                a_name == b_name
                    && a_args.len() == b_args.len()
                    && a_args
                        .iter()
                        .zip(b_args.iter())
                        .all(|(x, y)| self.types_match(x, y))
            }
            (Type::Param(a), Type::Param(b)) => a == b,
            (Type::Fn(a), Type::Fn(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter().zip(b.iter()).all(|(x, y)| self.types_match(x, y))
            }
            (Type::Ref(k1, _, i1), Type::Ref(k2, _, i2)) => k1 == k2 && self.types_match(i1, i2),
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
                    Type::Ref(_, _, pointee) => Ok(*pointee),
                    Type::RawPtr(pointee) => Ok(*pointee),
                    other => Err(err(
                        DerefOfNonPointer,
                        format!("Cannot dereference non-pointer type {}", other),
                    )),
                }
            }
            Place::Field(inner, field_name) => {
                let inner_ty = self.type_of_place(inner, span, locals)?;
                let (name, args) = match &inner_ty {
                    Type::Custom(n, _, a) => (n, a),
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
                        .map(|f| substitute_params(&f.ty, &s.type_params, args))
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
                let (name, args) = match &inner_ty {
                    Type::Custom(n, _, a) => (n, a),
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
                        .map(|v| substitute_params(&v.ty, &e.type_params, args))
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
                ConstVal::FnName(name, type_args) => {
                    // Substitute the fn's declared type-params with the
                    // args on this reference: e.g. `identity<i64>` gives
                    // `fn(i64) -> i64` after walking the declared
                    // `fn<T>(T) -> T`. Non-generic fns have empty args
                    // and substitution is a no-op.
                    let f = self.functions.get(name).ok_or_else(|| {
                        Diagnostic::new(
                            UndeclaredFunction,
                            span,
                            format!("Undeclared function name '{}'", name),
                        )
                    })?;
                    let param_tys = f
                        .params
                        .iter()
                        .map(|p| substitute_params(&p.ty, &f.type_params, type_args))
                        .collect();
                    Ok(fn_ty(param_tys))
                }
                ConstVal::ByteStr(bytes) => Ok(array_ty(u8_ty(), bytes.len() as u64)),
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
                Ok(ref_ty(kind.clone(), pointee_ty))
            }
            RValue::RawRef(place) => {
                let pointee_ty = self.type_of_place(place, span, locals)?;
                Ok(raw_ptr_ty(pointee_ty))
            }
            RValue::EnumConstr(enum_name, type_args, variant_name, op) => {
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
                if type_args.len() != e_decl.type_params.len() {
                    return Err(err(
                        EnumConstrOnNonEnum,
                        format!(
                            "Enum '{}' takes {} type argument(s), found {}",
                            enum_name,
                            e_decl.type_params.len(),
                            type_args.len()
                        ),
                    ));
                }
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

                let expected_payload = substitute_params(&variant.ty, &e_decl.type_params, type_args);
                let op_ty = self.type_of_operand(op, span, locals)?;
                if !self.types_match(&expected_payload, &op_ty) {
                    return Err(err(
                        EnumConstrPayloadTypeMismatch,
                        format!(
                            "Variant '{}' of enum '{}' expects type {}, found {}",
                            variant_name, enum_name, expected_payload, op_ty
                        ),
                    ));
                }

                Ok(Type::Custom(enum_name.clone(), Vec::new(), type_args.clone()))
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
