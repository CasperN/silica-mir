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
//! and return either the concrete type or a structured
//! [`TypeResolutionError`] explaining why it couldn't be resolved.

// TODO: Should this be moved to mir/ since its used widely?

use super::TypeCheckCode::*;
use super::TypeDecl;
use crate::diagnostics::Diagnostic;
use crate::mir::ast::*;
use crate::mir::diagnostic_format::{DiagnosticFormat, DiagnosticScope};
use crate::mir::helpers::*;
use crate::mir::substructural::composition::{class_of, ParamScope};
use indexmap::IndexMap;

#[derive(Debug, Clone)]
pub struct TypeResolutionError {
    kind: TypeResolutionErrorKind,
}

#[derive(Debug, Clone)]
pub struct TypeValidationError {
    kind: TypeValidationErrorKind,
}

#[derive(Debug, Clone)]
enum TypeValidationErrorKind {
    UndeclaredType(String),
    LifetimeArgArity {
        type_name: String,
        expected: usize,
        found: usize,
    },
    TypeArgArity {
        type_name: String,
        expected: usize,
        found: usize,
    },
    BoundNotSatisfied {
        argument: Type,
        type_name: String,
        parameter: String,
        bound: Marker,
    },
}

impl TypeValidationError {
    fn new(kind: TypeValidationErrorKind) -> Self {
        Self { kind }
    }

    pub fn message(&self, format: &mut DiagnosticFormat, scope: &DiagnosticScope) -> String {
        match &self.kind {
            TypeValidationErrorKind::UndeclaredType(name) => {
                format!("Use of undeclared type '{}'", name)
            }
            TypeValidationErrorKind::LifetimeArgArity {
                type_name,
                expected,
                found,
            } => format!(
                "Type '{}' expects {} lifetime argument(s), got {}",
                type_name, expected, found,
            ),
            TypeValidationErrorKind::TypeArgArity {
                type_name,
                expected,
                found,
            } => format!(
                "Type '{}' expects {} type argument(s), got {}",
                type_name, expected, found,
            ),
            TypeValidationErrorKind::BoundNotSatisfied {
                argument,
                type_name,
                parameter,
                bound,
            } => format!(
                "Type argument {} for '{}::{}' does not satisfy required bound '{}'",
                format.ty(scope, argument),
                type_name,
                parameter,
                bound.name(),
            ),
        }
    }
}

#[derive(Debug, Clone)]
enum TypeResolutionErrorKind {
    UndeclaredVariable(String),
    DerefOfNonPointer(Type),
    FieldOfNonStruct {
        field: String,
        ty: Type,
    },
    NoSuchField {
        type_name: String,
        field: String,
    },
    FieldOfEnum {
        field: String,
        enum_name: String,
    },
    UndeclaredType(String),
    DowncastOfNonEnum(Type),
    DowncastOfStruct(String),
    NoSuchVariant {
        enum_name: String,
        variant: String,
    },
    IndexOfNonArray(Type),
    ArrayIndexNotInteger(Type),
    ArrayIndexOutOfBounds {
        index: u64,
        len: u64,
    },
    UndeclaredFunction(String),
    EnumConstrOnStruct(String),
    UndeclaredEnum(String),
    EnumTypeArgArity {
        enum_name: String,
        expected: usize,
        found: usize,
    },
    EnumPayloadMismatch {
        variant: String,
        enum_name: String,
        expected: Type,
        found: Type,
    },
    ArrayElementMismatch {
        index: usize,
        found: Type,
        expected: Type,
    },
    PtrCastSourceNotPointer(Type),
    PtrCastTargetNotPointer(Type),
}

impl TypeResolutionError {
    fn new(kind: TypeResolutionErrorKind) -> Self {
        Self { kind }
    }

    pub fn code(&self) -> super::TypeCheckCode {
        match &self.kind {
            TypeResolutionErrorKind::UndeclaredVariable(_) => UndeclaredVariable,
            TypeResolutionErrorKind::DerefOfNonPointer(_) => DerefOfNonPointer,
            TypeResolutionErrorKind::FieldOfNonStruct { .. }
            | TypeResolutionErrorKind::FieldOfEnum { .. } => FieldOfNonStruct,
            TypeResolutionErrorKind::NoSuchField { .. } => NoSuchField,
            TypeResolutionErrorKind::UndeclaredType(_) => UndeclaredType,
            TypeResolutionErrorKind::DowncastOfNonEnum(_)
            | TypeResolutionErrorKind::DowncastOfStruct(_) => DowncastOfNonEnum,
            TypeResolutionErrorKind::NoSuchVariant { .. } => NoSuchVariant,
            TypeResolutionErrorKind::IndexOfNonArray(_) => IndexOfNonArray,
            TypeResolutionErrorKind::ArrayIndexNotInteger(_) => ArrayIndexNotInteger,
            TypeResolutionErrorKind::ArrayIndexOutOfBounds { .. } => ArrayIndexOutOfBounds,
            TypeResolutionErrorKind::UndeclaredFunction(_) => UndeclaredFunction,
            TypeResolutionErrorKind::EnumConstrOnStruct(_)
            | TypeResolutionErrorKind::UndeclaredEnum(_)
            | TypeResolutionErrorKind::EnumTypeArgArity { .. } => EnumConstrOnNonEnum,
            TypeResolutionErrorKind::EnumPayloadMismatch { .. } => EnumConstrPayloadTypeMismatch,
            TypeResolutionErrorKind::ArrayElementMismatch { .. } => ArrayLitElementTypeMismatch,
            TypeResolutionErrorKind::PtrCastSourceNotPointer(_) => PtrCastSourceNotPointer,
            TypeResolutionErrorKind::PtrCastTargetNotPointer(_) => PtrCastTargetNotPointer,
        }
    }

    pub fn message(
        &self,
        format: &mut DiagnosticFormat,
        caller_scope: &DiagnosticScope,
        env: &Env,
    ) -> String {
        match &self.kind {
            TypeResolutionErrorKind::UndeclaredVariable(name) => {
                format!("Use of undeclared variable '{}'", name)
            }
            TypeResolutionErrorKind::DerefOfNonPointer(ty) => {
                format!(
                    "Cannot dereference non-pointer type {}",
                    format.ty(caller_scope, ty)
                )
            }
            TypeResolutionErrorKind::FieldOfNonStruct { field, ty } => format!(
                "Cannot project field '{}' of non-struct type {}",
                field,
                format.ty(caller_scope, ty),
            ),
            TypeResolutionErrorKind::NoSuchField { type_name, field } => {
                format!("Struct '{}' has no field '{}'", type_name, field)
            }
            TypeResolutionErrorKind::FieldOfEnum { field, enum_name } => format!(
                "Cannot project field '{}' of enum type '{}'",
                field, enum_name,
            ),
            TypeResolutionErrorKind::UndeclaredType(name) => {
                format!("Use of undeclared type '{}'", name)
            }
            TypeResolutionErrorKind::DowncastOfNonEnum(ty) => {
                format!(
                    "Cannot downcast non-enum type {}",
                    format.ty(caller_scope, ty)
                )
            }
            TypeResolutionErrorKind::DowncastOfStruct(name) => {
                format!("Cannot downcast struct type '{}'", name)
            }
            TypeResolutionErrorKind::NoSuchVariant { enum_name, variant } => {
                format!("Enum '{}' has no variant '{}'", enum_name, variant)
            }
            TypeResolutionErrorKind::IndexOfNonArray(ty) => {
                format!(
                    "Cannot index non-array type {}",
                    format.ty(caller_scope, ty)
                )
            }
            TypeResolutionErrorKind::ArrayIndexNotInteger(ty) => {
                format!(
                    "Array index must be an integer, got {}",
                    format.ty(caller_scope, ty)
                )
            }
            TypeResolutionErrorKind::ArrayIndexOutOfBounds { index, len } => {
                format!("Array index {} out of bounds for [_; {}]", index, len)
            }
            TypeResolutionErrorKind::UndeclaredFunction(name) => {
                format!("Undeclared function name '{}'", name)
            }
            TypeResolutionErrorKind::EnumConstrOnStruct(name) => {
                format!("'{}' is a struct, not an enum", name)
            }
            TypeResolutionErrorKind::UndeclaredEnum(name) => {
                format!("Undeclared enum '{}'", name)
            }
            TypeResolutionErrorKind::EnumTypeArgArity {
                enum_name,
                expected,
                found,
            } => format!(
                "Enum '{}' takes {} type argument(s), found {}",
                enum_name, expected, found,
            ),
            TypeResolutionErrorKind::EnumPayloadMismatch {
                variant,
                enum_name,
                expected,
                found,
            } => {
                let expected_scope = env
                    .types
                    .get(enum_name)
                    .map(|declaration| format.scope(declaration.meta()));
                let expected = match expected_scope {
                    Some(scope) => format.ty(&scope, expected),
                    None => format.ty(caller_scope, expected),
                };
                let found = format.ty(caller_scope, found);
                format!(
                    "Variant '{}' of enum '{}' expects type {}, found {}",
                    variant, enum_name, expected, found,
                )
            }
            TypeResolutionErrorKind::ArrayElementMismatch {
                index,
                found,
                expected,
            } => format!(
                "Array literal element {} has type {}, expected {}",
                index,
                format.ty(caller_scope, found),
                format.ty(caller_scope, expected),
            ),
            TypeResolutionErrorKind::PtrCastSourceNotPointer(ty) => format!(
                "Pointer cast source must be a raw pointer or reference type, found {}",
                format.ty(caller_scope, ty),
            ),
            TypeResolutionErrorKind::PtrCastTargetNotPointer(ty) => format!(
                "Pointer cast target must be a raw pointer or reference type, found {}",
                format.ty(caller_scope, ty),
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Env {
    /// Struct and enum declarations, keyed by name. Uses `IndexMap` so
    /// iteration order matches declaration order — analyses that iterate
    /// (e.g. field validation) produce diagnostics deterministically.
    pub types: IndexMap<String, TypeDecl>,
    /// Function signatures, keyed by name. Bodies live in
    /// [`Program`](crate::mir::ast::Program) — callers that need to
    /// walk statements iterate `Program::functions()` and use `Env` for
    /// name resolution (`env.functions[callee_name].params`, etc.).
    /// Keeping only signatures in `Env` means elaboration can mutate
    /// bodies in-place on `Program` without an `Env` resync step.
    pub functions: IndexMap<String, FunctionSignature>,
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
            functions.insert(f.meta.name.clone(), FunctionSignature::from_function(&f));
        }

        for decl in &program.declarations {
            let m = decl.meta();
            let (existing, kind_word) = match decl {
                Declaration::Struct(_) | Declaration::Enum(_) => {
                    (types.contains_key(&m.name), "type")
                }
                Declaration::Fn(_) => (functions.contains_key(&m.name), "function"),
            };
            if existing {
                errors.push(Diagnostic::new(
                    DuplicateDeclaration,
                    m.name_source,
                    format!("Duplicate declaration of {} '{}'", kind_word, m.name),
                ));
                continue;
            }
            match decl {
                Declaration::Struct(s) => {
                    types.insert(m.name.clone(), TypeDecl::Struct(s.clone()));
                }
                Declaration::Enum(e) => {
                    types.insert(m.name.clone(), TypeDecl::Enum(e.clone()));
                }
                Declaration::Fn(f) => {
                    functions.insert(m.name.clone(), FunctionSignature::from_function(f));
                }
            }
        }

        (Env { types, functions }, errors)
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
    pub fn validate_type(&self, ty: &Type, scope: ParamScope) -> Result<(), TypeValidationError> {
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never => Ok(()),
            TypeKind::Custom(Instance { name, lifetime_args, type_args: args }) => {
                let Some(decl) = self.types.get(name) else {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::UndeclaredType(name.clone()),
                    ));
                };
                let decl_meta = decl.meta();
                // Reject explicit-but-wrong-count lifetime args. Zero is
                // still tolerated to preserve compatibility with bare
                // mentions that rely on elision defaults — closing that
                // loophole needs the elision-backfill work tracked in
                // the punchlist.
                if !lifetime_args.is_empty()
                    && lifetime_args.len() != decl_meta.lifetime_params.len()
                {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::LifetimeArgArity {
                            type_name: name.clone(),
                            expected: decl_meta.lifetime_params.len(),
                            found: lifetime_args.len(),
                        },
                    ));
                }
                let decl_params: &[TypeParam] = &decl_meta.type_params;
                if args.len() != decl_params.len() {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::TypeArgArity {
                            type_name: name.clone(),
                            expected: decl_params.len(),
                            found: args.len(),
                        },
                    ));
                }
                for (arg, param) in args.iter().zip(decl_params.iter()) {
                    self.validate_type(arg, scope)?;
                    let arg_class = class_of(arg, self, scope);
                    for bound in param.bounds.markers.iter_declared() {
                        if !arg_class.implies(bound) {
                            return Err(TypeValidationError::new(
                                TypeValidationErrorKind::BoundNotSatisfied {
                                    argument: arg.clone(),
                                    type_name: name.clone(),
                                    parameter: param.name.clone(),
                                    bound,
                                },
                            ));
                        }
                    }
                }
                Ok(())
            }
            // A `Param` is validated by the parser (which only emits it
            // for names in the current type-param scope). Nothing more
            // to check here.
            TypeKind::Param(_) => Ok(()),
            TypeKind::Fn(params) => {
                for p in params {
                    self.validate_type(p, scope)?;
                }
                Ok(())
            }
            TypeKind::Ref(_, _, inner) => self.validate_type(inner, scope),
            TypeKind::RawPtr(inner) => self.validate_type(inner, scope),
            TypeKind::Array(elem, _) => self.validate_type(elem, scope),
        }
    }

    /// Empty-scope convenience: for callers with no in-scope type
    /// parameters. A `Param(_)` reachable via this path is
    /// well-formed (Ok) but its markers can't be resolved to real
    /// bounds — use only outside of generic decl bodies.
    pub fn validate_type_empty_scope(&self, ty: &Type) -> Result<(), TypeValidationError> {
        self.validate_type(ty, &IndexMap::new())
    }

    /// Type of `field` in the struct type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared struct or the field doesn't exist.
    /// Substitutes the struct's type-parameter references (`TypeKind::Param`)
    /// with the concrete args on `ty`, so `Box<i64>::inner` yields `i64`,
    /// not the raw declared `T`.
    pub fn field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        let TypeKind::Custom(Instance { name, type_args: args, .. }) = &ty.kind else {
            return None;
        };
        let TypeDecl::Struct(s) = self.types.get(name)? else {
            return None;
        };
        let f_ty = &s.fields.iter().find(|f| f.name == field)?.ty;
        Some(s.meta.substitute_types(f_ty, args))
    }

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (&t1.kind, &t2.kind) {
            (TypeKind::Int(a), TypeKind::Int(b)) => a == b,
            (TypeKind::Float(a), TypeKind::Float(b)) => a == b,
            (TypeKind::Bool, TypeKind::Bool) => true,
            (TypeKind::Unit, TypeKind::Unit) => true,
            (TypeKind::Never, TypeKind::Never) => true,
            (TypeKind::Custom(Instance { name: a_name, type_args: a_args, .. }), TypeKind::Custom(Instance { name: b_name, type_args: b_args, .. })) => {
                a_name == b_name
                    && a_args.len() == b_args.len()
                    && a_args
                        .iter()
                        .zip(b_args.iter())
                        .all(|(x, y)| self.types_match(x, y))
            }
            (TypeKind::Param(a), TypeKind::Param(b)) => a == b,
            (TypeKind::Fn(a), TypeKind::Fn(b)) => {
                if a.len() != b.len() {
                    return false;
                }
                a.iter().zip(b.iter()).all(|(x, y)| self.types_match(x, y))
            }
            (TypeKind::Ref(k1, _, i1), TypeKind::Ref(k2, _, i2)) => {
                k1 == k2 && self.types_match(i1, i2)
            }
            (TypeKind::RawPtr(i1), TypeKind::RawPtr(i2)) => self.types_match(i1, i2),
            (TypeKind::Array(e1, n1), TypeKind::Array(e2, n2)) => {
                n1 == n2 && self.types_match(e1, e2)
            }
            _ => false,
        }
    }

    /// Compute the type of a place. Failures remain structured; the checker
    /// that owns the enclosing statement or terminator supplies source and
    /// declaration context when turning them into diagnostics.
    pub fn type_of_place(
        &self,
        place: &Place,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, TypeResolutionError> {
        let err = TypeResolutionError::new;
        match place {
            Place::Var(name) => locals
                .get(name)
                .cloned()
                .ok_or_else(|| err(TypeResolutionErrorKind::UndeclaredVariable(name.clone()))),
            Place::Deref(inner) => {
                let inner_ty = self.type_of_place(inner, locals)?;
                match &inner_ty.kind {
                    TypeKind::Ref(_, _, pointee) => Ok(*pointee.clone()),
                    TypeKind::RawPtr(pointee) => Ok(*pointee.clone()),
                    _ => Err(err(TypeResolutionErrorKind::DerefOfNonPointer(inner_ty))),
                }
            }
            Place::Field(inner, field_name) => {
                let inner_ty = self.type_of_place(inner, locals)?;
                let (name, args) = match &inner_ty.kind {
                    TypeKind::Custom(Instance { name: n, type_args: a, .. }) => (n, a),
                    _ => {
                        return Err(err(TypeResolutionErrorKind::FieldOfNonStruct {
                            field: field_name.clone(),
                            ty: inner_ty,
                        }))
                    }
                };
                match self.types.get(name) {
                    Some(TypeDecl::Struct(s)) => s
                        .fields
                        .iter()
                        .find(|f| f.name == *field_name)
                        .map(|f| s.meta.substitute_types(&f.ty, args))
                        .ok_or_else(|| {
                            err(TypeResolutionErrorKind::NoSuchField {
                                type_name: name.clone(),
                                field: field_name.clone(),
                            })
                        }),
                    Some(TypeDecl::Enum(_)) => Err(err(TypeResolutionErrorKind::FieldOfEnum {
                        field: field_name.clone(),
                        enum_name: name.clone(),
                    })),
                    None => Err(err(TypeResolutionErrorKind::UndeclaredType(name.clone()))),
                }
            }
            Place::Downcast(inner, variant_name) => {
                let inner_ty = self.type_of_place(inner, locals)?;
                let (name, args) = match &inner_ty.kind {
                    TypeKind::Custom(Instance { name: n, type_args: a, .. }) => (n, a),
                    _ => return Err(err(TypeResolutionErrorKind::DowncastOfNonEnum(inner_ty))),
                };
                match self.types.get(name) {
                    Some(TypeDecl::Enum(e)) => e
                        .variants
                        .iter()
                        .find(|v| v.name == *variant_name)
                        .map(|v| e.meta.substitute_types(&v.ty, args))
                        .ok_or_else(|| {
                            err(TypeResolutionErrorKind::NoSuchVariant {
                                enum_name: name.clone(),
                                variant: variant_name.clone(),
                            })
                        }),
                    Some(TypeDecl::Struct(_)) => {
                        Err(err(TypeResolutionErrorKind::DowncastOfStruct(name.clone())))
                    }
                    None => Err(err(TypeResolutionErrorKind::UndeclaredType(name.clone()))),
                }
            }
            Place::Index(inner, op) => {
                let inner_ty = self.type_of_place(inner, locals)?;
                let TypeKind::Array(elem, n) = inner_ty.kind else {
                    return Err(err(TypeResolutionErrorKind::IndexOfNonArray(inner_ty)));
                };
                // Index operand must be an integer type.
                let op_ty = self.type_of_operand(op, locals)?;
                if !matches!(&op_ty.kind, TypeKind::Int(_)) {
                    return Err(err(TypeResolutionErrorKind::ArrayIndexNotInteger(op_ty)));
                }
                // Constant-index bounds check. Cheap defensive check
                // that catches known-bad accesses at check time.
                // Dynamic indices are left to the HLL / runtime.
                if let Some(k) = const_int_operand(op) {
                    if k >= n {
                        return Err(err(TypeResolutionErrorKind::ArrayIndexOutOfBounds {
                            index: k,
                            len: n,
                        }));
                    }
                }
                Ok(*elem)
            }
        }
    }

    pub fn type_of_operand(
        &self,
        op: &Operand,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, TypeResolutionError> {
        match op {
            Operand::Copy(place) | Operand::Move(place) | Operand::Take(place) => {
                self.type_of_place(place, locals)
            }
            Operand::Const(c) => match c {
                ConstVal::Int { ty, .. } => Ok(int_ty(*ty)),
                ConstVal::Float { ty, .. } => Ok(float_ty(*ty)),
                ConstVal::Bool(_) => Ok(bool_ty()),
                ConstVal::Unit => Ok(unit_ty()),
                ConstVal::FnName(name, type_args) => {
                    // Substitute the fn's declared type-params with the
                    // args on this reference: e.g. `identity<i64>` gives
                    // `fn(i64) -> i64` after walking the declared
                    // `fn<T>(T) -> T`. Non-generic fns have empty args
                    // and substitution is a no-op.
                    let f = self.functions.get(name).ok_or_else(|| {
                        TypeResolutionError::new(TypeResolutionErrorKind::UndeclaredFunction(
                            name.clone(),
                        ))
                    })?;
                    let param_tys = f
                        .params
                        .iter()
                        .map(|p| f.meta.substitute_types(&p.ty, type_args))
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
        source: SourceInfo,
        locals: &IndexMap<String, Type>,
    ) -> Result<Type, TypeResolutionError> {
        let err = TypeResolutionError::new;
        match rvalue {
            RValue::Use(op) => self.type_of_operand(op, locals),
            RValue::Ref(kind, place) => {
                let pointee_ty = self.type_of_place(place, locals)?;
                Ok(ref_ty(kind.clone(), pointee_ty))
            }
            RValue::RawRef(place) => {
                let pointee_ty = self.type_of_place(place, locals)?;
                Ok(raw_ptr_ty(pointee_ty))
            }
            RValue::EnumConstr(enum_name, type_args, variant_name, op) => {
                let e_decl = match self.types.get(enum_name) {
                    Some(TypeDecl::Enum(e)) => e,
                    Some(TypeDecl::Struct(_)) => {
                        return Err(err(TypeResolutionErrorKind::EnumConstrOnStruct(
                            enum_name.clone(),
                        )));
                    }
                    None => {
                        return Err(err(TypeResolutionErrorKind::UndeclaredEnum(
                            enum_name.clone(),
                        )))
                    }
                };
                if type_args.len() != e_decl.meta.type_params.len() {
                    return Err(err(TypeResolutionErrorKind::EnumTypeArgArity {
                        enum_name: enum_name.clone(),
                        expected: e_decl.meta.type_params.len(),
                        found: type_args.len(),
                    }));
                }
                let variant = e_decl
                    .variants
                    .iter()
                    .find(|v| v.name == *variant_name)
                    .ok_or_else(|| {
                        err(TypeResolutionErrorKind::NoSuchVariant {
                            enum_name: enum_name.clone(),
                            variant: variant_name.clone(),
                        })
                    })?;

                let expected_payload = e_decl.meta.substitute_types(&variant.ty, type_args);
                let op_ty = self.type_of_operand(op, locals)?;
                if !self.types_match(&expected_payload, &op_ty) {
                    return Err(err(TypeResolutionErrorKind::EnumPayloadMismatch {
                        variant: variant_name.clone(),
                        enum_name: enum_name.clone(),
                        expected: expected_payload,
                        found: op_ty,
                    }));
                }

                Ok(Type::new(
                    TypeKind::Custom(Instance::new(enum_name.clone(), Vec::new(), type_args.clone())),
                    SourceInfo::generated(GeneratedKind::TypeSynthesis, source.span()),
                ))
            }
            RValue::ArrayLit(ops) => {
                // Empty array literal: `[]` has type `[Unit; 0]` as a
                // placeholder — types_match will still reject any real
                // target type mismatch. Effectively unusable but not
                // an error at inference time.
                if ops.is_empty() {
                    return Ok(array_ty(unit_ty(), 0));
                }
                let first_ty = self.type_of_operand(&ops[0], locals)?;
                for (i, op) in ops.iter().enumerate().skip(1) {
                    let ty = self.type_of_operand(op, locals)?;
                    if !self.types_match(&first_ty, &ty) {
                        return Err(err(TypeResolutionErrorKind::ArrayElementMismatch {
                            index: i,
                            found: ty,
                            expected: first_ty,
                        }));
                    }
                }
                Ok(array_ty(first_ty, ops.len() as u64))
            }
            RValue::PtrCast(op, to_ty) => {
                let op_ty = self.type_of_operand(op, locals)?;
                if !matches!(op_ty.kind, TypeKind::RawPtr(_) | TypeKind::Ref(_, _, _)) {
                    return Err(err(TypeResolutionErrorKind::PtrCastSourceNotPointer(op_ty)));
                }
                if !matches!(to_ty.kind, TypeKind::RawPtr(_) | TypeKind::Ref(_, _, _)) {
                    return Err(err(TypeResolutionErrorKind::PtrCastTargetNotPointer(
                        to_ty.clone(),
                    )));
                }
                Ok(to_ty.clone())
            }
        }
    }
}
