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

use crate::common::{GeneratedKind, Lifetime, Marker, SourceInfo};
use crate::diagnostics::Diagnostic;
use crate::mir::ast::*;
use crate::mir::diagnostic_format::{DiagnosticFormat, DiagnosticScope};
use crate::mir::helpers::*;
use crate::mir::type_check::{TypeCheckCode, TypeCheckCode::*};
use indexmap::IndexMap;
use std::collections::BTreeMap;

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
    /// `TraitFn` callee names a trait not in the env.
    TraitFnUnknownTrait(String),
    /// `TraitFn` receiver is a generic type parameter; resolution
    /// through the parameter's trait bounds needs the trait-bound
    /// vocabulary populated on `TypeParam.bounds.traits`, which
    /// requires trait-bound syntax at the binding site.
    TraitFnParamReceiver(String),
    /// No impl of `trait_path` matches the given self_ty.
    TraitFnNoImpl {
        trait_path: Instance,
        self_ty: Type,
    },
    /// Multiple impl patterns match the call.
    TraitFnAmbiguousImpl {
        trait_path: Instance,
        self_ty: Type,
    },
    /// Impl of `trait_path` for self_ty exists but doesn't declare the
    /// method the callee names.
    TraitFnNoMethod {
        trait_path: Instance,
        self_ty: Type,
        method: String,
    },
}

impl TypeResolutionError {
    fn new(kind: TypeResolutionErrorKind) -> Self {
        Self { kind }
    }

    // TODO(diagnostics): Derive TypeCheckCode from the eventual typed failure
    // payload instead of translating TypeResolutionError separately.
    pub fn code(&self) -> TypeCheckCode {
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
            TypeResolutionErrorKind::TraitFnUnknownTrait(_) => TraitFnUnknownTrait,
            TypeResolutionErrorKind::TraitFnParamReceiver(_) => TraitFnParamReceiver,
            TypeResolutionErrorKind::TraitFnNoImpl { .. } => TraitFnNoImpl,
            TypeResolutionErrorKind::TraitFnAmbiguousImpl { .. } => TraitFnAmbiguousImpl,
            TypeResolutionErrorKind::TraitFnNoMethod { .. } => TraitFnNoMethod,
        }
    }

    pub fn message(
        &self,
        format: &mut DiagnosticFormat,
        caller_scope: &DiagnosticScope,
        prog: &IndexedProgram,
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
                let expected_scope = prog
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
            TypeResolutionErrorKind::TraitFnUnknownTrait(name) => {
                format!("Trait-method call references undeclared trait '{}'", name)
            }
            TypeResolutionErrorKind::TraitFnParamReceiver(name) => format!(
                "Trait-method call on generic parameter '{}' requires a trait bound (deferred pending trait-bound syntax)",
                name,
            ),
            TypeResolutionErrorKind::TraitFnNoImpl {
                trait_path,
                self_ty,
            } => format!(
                "No impl of '{}' for {} in scope",
                trait_path,
                format.ty(caller_scope, self_ty),
            ),
            TypeResolutionErrorKind::TraitFnAmbiguousImpl {
                trait_path,
                self_ty,
            } => format!(
                "Multiple impls of '{}' match {}",
                trait_path,
                format.ty(caller_scope, self_ty),
            ),
            TypeResolutionErrorKind::TraitFnNoMethod {
                trait_path,
                self_ty,
                method,
            } => format!(
                "Impl of '{}' for {} has no method '{}'",
                trait_path,
                format.ty(caller_scope, self_ty),
                method,
            ),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DeclarationRef<'a> {
    Struct(&'a StructDecl),
    Enum(&'a EnumDecl),
    Function(&'a Function),
    Trait(&'a TraitDecl),
    Impl(&'a ImplBlock),
}

impl<'a> DeclarationRef<'a> {
    pub fn meta(self) -> Option<&'a DeclMeta> {
        match self {
            DeclarationRef::Struct(s) => Some(&s.meta),
            DeclarationRef::Enum(e) => Some(&e.meta),
            DeclarationRef::Function(f) => Some(&f.meta),
            DeclarationRef::Trait(t) => Some(&t.meta),
            DeclarationRef::Impl(_) => None,
        }
    }

    pub fn source(self) -> SourceInfo {
        match self {
            DeclarationRef::Struct(s) => s.meta.name_source,
            DeclarationRef::Enum(e) => e.meta.name_source,
            DeclarationRef::Function(f) => f.meta.name_source,
            DeclarationRef::Trait(t) => t.meta.name_source,
            DeclarationRef::Impl(i) => i.params.source,
        }
    }
}

/// Global declarations plus the generic parameters visible in one declaration
/// body. Impl methods see both the impl header and their own parameters.
#[derive(Debug, Clone, Copy)]
pub struct LocalEnv<'a> {
    program: &'a IndexedProgram,
    impl_generics: Option<&'a GenericParams>,
    decl_generics: &'a GenericParams,
    self_ty: Option<&'a Type>,
}

impl<'a> LocalEnv<'a> {
    pub fn for_decl(program: &'a IndexedProgram, decl_generics: &'a GenericParams) -> Self {
        Self {
            program,
            impl_generics: None,
            decl_generics,
            self_ty: None,
        }
    }

    pub fn for_impl_method(
        program: &'a IndexedProgram,
        impl_block: &'a ImplBlock,
        method: &'a Function,
    ) -> Self {
        Self {
            program,
            impl_generics: Some(&impl_block.params),
            decl_generics: &method.meta.params,
            self_ty: Some(&impl_block.target),
        }
    }

    pub fn program(&self) -> &'a IndexedProgram {
        self.program
    }

    pub fn impl_generics(&self) -> Option<&'a GenericParams> {
        self.impl_generics
    }

    pub fn decl_generics(&self) -> &'a GenericParams {
        self.decl_generics
    }

    pub fn self_ty(&self) -> Option<&'a Type> {
        self.self_ty
    }

    /// Whether an impl whose header and marker bounds match is available.
    /// Overlap is an invalid program awaiting declaration-time coherence
    /// checking, so it remains an internal failure rather than a lookup state.
    pub(crate) fn has_applicable_trait_impl(&self, trait_path: &Instance, self_ty: &Type) -> bool {
        if matches!(self_ty.kind, TypeKind::Param(_)) {
            return false;
        }
        let mut matches = self.matching_impls(trait_path, self_ty).into_iter();
        let found = matches.next().is_some();
        assert!(
            matches.next().is_none(),
            "overlapping impls while resolving {} for {}; coherence checking should have rejected them",
            trait_path,
            self_ty,
        );
        found
    }

    pub fn type_param(&self, name: &str) -> Option<&'a TypeParam> {
        self.decl_generics
            .type_params
            .iter()
            .find(|param| param.name == name)
            .or_else(|| {
                self.impl_generics?
                    .type_params
                    .iter()
                    .find(|param| param.name == name)
            })
    }

    pub fn lifetime_params(&self) -> impl Iterator<Item = &'a LifetimeParam> {
        self.impl_generics
            .into_iter()
            .flat_map(|params| &params.lifetime_params)
            .chain(&self.decl_generics.lifetime_params)
    }

    pub fn outlives_bounds(&self) -> impl Iterator<Item = &'a OutlivesBound> {
        self.impl_generics
            .into_iter()
            .flat_map(|params| &params.outlives)
            .chain(&self.decl_generics.outlives)
    }

    /// Return the substructural class of `ty` under this declaration's
    /// visible generic parameters.
    pub fn class_of(&self, ty: &Type) -> Markers {
        let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Fn(_) => all(),
            TypeKind::Never | TypeKind::RawPtr(_) => all(),
            TypeKind::Ref(kind, _, _) => match kind {
                RefKind::Shared => all(),
                RefKind::Mut | RefKind::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
                RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
            },
            TypeKind::Custom(Instance { name, .. }) => match self.program.types.get(name) {
                Some(TypeDecl::Struct(s)) => s.meta.markers,
                Some(TypeDecl::Enum(e)) => e.meta.markers,
                None => Markers::empty(),
            },
            TypeKind::Param(name) => self
                .type_param(name)
                .map(|param| param.bounds.markers)
                .unwrap_or_else(Markers::empty),
            TypeKind::Array(elem, _) => self.class_of(elem),
        }
    }

    /// Validate `ty` under this declaration's visible generic parameters.
    ///
    /// A custom type use must have the declared argument arity and each type
    /// argument must satisfy the corresponding parameter bounds.
    pub fn validate_type(&self, ty: &Type) -> Result<(), TypeValidationError> {
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never => Ok(()),
            TypeKind::Custom(Instance {
                name,
                lifetime_args,
                type_args: args,
            }) => {
                let Some(decl) = self.program.types.get(name) else {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::UndeclaredType(name.clone()),
                    ));
                };
                let decl_meta = decl.meta();
                if !lifetime_args.is_empty()
                    && lifetime_args.len() != decl_meta.params.lifetime_params.len()
                {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::LifetimeArgArity {
                            type_name: name.clone(),
                            expected: decl_meta.params.lifetime_params.len(),
                            found: lifetime_args.len(),
                        },
                    ));
                }
                let decl_params = &decl_meta.params.type_params;
                if args.len() != decl_params.len() {
                    return Err(TypeValidationError::new(
                        TypeValidationErrorKind::TypeArgArity {
                            type_name: name.clone(),
                            expected: decl_params.len(),
                            found: args.len(),
                        },
                    ));
                }
                for (arg, param) in args.iter().zip(decl_params) {
                    self.validate_type(arg)?;
                    let arg_class = self.class_of(arg);
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
            TypeKind::Param(_) => Ok(()),
            TypeKind::Fn(fn_params) => {
                for param in fn_params {
                    self.validate_type(param)?;
                }
                Ok(())
            }
            TypeKind::Ref(_, _, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
                self.validate_type(inner)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct IndexedProgram {
    /// Struct and enum declarations, keyed by name. Uses `IndexMap` so
    /// iteration order matches declaration order — analyses that iterate
    /// (e.g. field validation) produce diagnostics deterministically.
    pub types: IndexMap<String, TypeDecl>,
    /// Trait declarations, keyed by name. Kept out of `types` because
    /// a trait is not a first-class type: `x: MyTrait` and
    /// `Vec<MyTrait>` are illegal at the type-name resolver, so putting
    /// traits in `types` would make them accidentally satisfy those
    /// positions. Name-uniqueness between `types` and `traits` is
    /// enforced together (see `IndexedProgram::build`) — Rust's type-namespace
    /// rule.
    pub traits: IndexMap<String, TraitDecl>,
    /// Functions, including bodies, keyed by name. Compiler-provided
    /// intrinsics also occupy this lookup namespace but do not participate in
    /// ordered declaration traversal.
    pub functions: IndexMap<String, Function>,
    /// Impl blocks, keyed by `(trait_path, target_type)`. The full
    /// trait path (name + lifetime + type args) is the key so multiple
    /// impls of a generic trait for the same target coexist —
    /// `impl Iter<i64> for X` and `impl Iter<u8> for X` are distinct
    /// impls, not a collision. Exact duplicate keys are rejected at build
    /// time; call resolution structurally matches generic impl headers and
    /// diagnoses overlapping matches.
    pub impls: IndexMap<(Instance, Type), ImplBlock>,
    /// Inherent impl blocks. Multiple blocks for the same target are legal;
    /// method-name overlap is checked across applicable blocks.
    pub inherent_impls: Vec<ImplBlock>,
}

pub(crate) struct ImplBindings {
    pub type_args: Vec<Type>,
}

pub(crate) fn impl_marker_bounds_satisfied(
    impl_block: &ImplBlock,
    bindings: &ImplBindings,
    mut class_of: impl FnMut(&Type) -> Markers,
) -> bool {
    impl_block
        .params
        .type_params
        .iter()
        .zip(&bindings.type_args)
        .all(|(param, arg)| {
            // TODO(trait bounds): Check `bounds.traits` here once
            // binding-site trait-bound syntax populates it.
            param
                .bounds
                .markers
                .iter_declared()
                .all(|bound| class_of(arg).implies(bound))
        })
}

pub(crate) fn match_impl_header(
    impl_block: &ImplBlock,
    trait_path: &Instance,
    self_ty: &Type,
) -> Option<ImplBindings> {
    let impl_trait_path = impl_block.trait_path.as_ref()?;
    let mut type_bindings = BTreeMap::new();
    let mut lifetime_bindings = BTreeMap::new();
    if !match_instance(
        impl_trait_path,
        trait_path,
        &impl_block.params,
        &mut type_bindings,
        &mut lifetime_bindings,
    ) || !match_type(
        &impl_block.target,
        self_ty,
        &impl_block.params,
        &mut type_bindings,
        &mut lifetime_bindings,
    ) {
        return None;
    }
    let type_args = impl_block
        .params
        .type_params
        .iter()
        .map(|param| type_bindings.get(&param.name).cloned())
        .collect::<Option<Vec<_>>>()?;
    let lifetimes_bound = impl_block
        .params
        .lifetime_params
        .iter()
        .all(|param| lifetime_bindings.contains_key(&param.lifetime));
    lifetimes_bound.then_some(ImplBindings { type_args })
}

fn match_instance(
    pattern: &Instance,
    actual: &Instance,
    params: &GenericParams,
    type_bindings: &mut BTreeMap<String, Type>,
    lifetime_bindings: &mut BTreeMap<Lifetime, Lifetime>,
) -> bool {
    pattern.name == actual.name
        && pattern.lifetime_args.len() == actual.lifetime_args.len()
        && pattern.type_args.len() == actual.type_args.len()
        && pattern
            .lifetime_args
            .iter()
            .zip(&actual.lifetime_args)
            .all(|(pattern, actual)| match_lifetime(pattern, actual, params, lifetime_bindings))
        && pattern
            .type_args
            .iter()
            .zip(&actual.type_args)
            .all(|(pattern, actual)| {
                match_type(pattern, actual, params, type_bindings, lifetime_bindings)
            })
}

fn match_lifetime(
    pattern: &Lifetime,
    actual: &Lifetime,
    params: &GenericParams,
    bindings: &mut BTreeMap<Lifetime, Lifetime>,
) -> bool {
    if params
        .lifetime_params
        .iter()
        .any(|param| param.lifetime == *pattern)
    {
        match bindings.get(pattern) {
            Some(bound) => bound == actual,
            None => {
                bindings.insert(pattern.clone(), actual.clone());
                true
            }
        }
    } else {
        pattern == actual
    }
}

fn match_optional_lifetime(
    pattern: &Option<Lifetime>,
    actual: &Option<Lifetime>,
    params: &GenericParams,
    bindings: &mut BTreeMap<Lifetime, Lifetime>,
) -> bool {
    match (pattern, actual) {
        (Some(pattern), Some(actual)) => match_lifetime(pattern, actual, params, bindings),
        (None, None) => true,
        _ => false,
    }
}

fn match_type(
    pattern: &Type,
    actual: &Type,
    params: &GenericParams,
    type_bindings: &mut BTreeMap<String, Type>,
    lifetime_bindings: &mut BTreeMap<Lifetime, Lifetime>,
) -> bool {
    if let TypeKind::Param(name) = &pattern.kind {
        if params.type_params.iter().any(|param| param.name == *name) {
            return match type_bindings.get(name) {
                Some(bound) => bound == actual,
                None => {
                    type_bindings.insert(name.clone(), actual.clone());
                    true
                }
            };
        }
    }

    match (&pattern.kind, &actual.kind) {
        (TypeKind::Int(pattern), TypeKind::Int(actual)) => pattern == actual,
        (TypeKind::Float(pattern), TypeKind::Float(actual)) => pattern == actual,
        (TypeKind::Bool, TypeKind::Bool)
        | (TypeKind::Unit, TypeKind::Unit)
        | (TypeKind::Never, TypeKind::Never) => true,
        (TypeKind::Param(pattern), TypeKind::Param(actual)) => pattern == actual,
        (TypeKind::Custom(pattern), TypeKind::Custom(actual)) => {
            match_instance(pattern, actual, params, type_bindings, lifetime_bindings)
        }
        (TypeKind::Fn(pattern), TypeKind::Fn(actual)) => {
            pattern.len() == actual.len()
                && pattern.iter().zip(actual).all(|(pattern, actual)| {
                    match_type(pattern, actual, params, type_bindings, lifetime_bindings)
                })
        }
        (
            TypeKind::Ref(pattern_kind, pattern_lifetime, pattern_inner),
            TypeKind::Ref(actual_kind, actual_lifetime, actual_inner),
        ) => {
            pattern_kind == actual_kind
                && match_optional_lifetime(
                    pattern_lifetime,
                    actual_lifetime,
                    params,
                    lifetime_bindings,
                )
                && match_type(
                    pattern_inner,
                    actual_inner,
                    params,
                    type_bindings,
                    lifetime_bindings,
                )
        }
        (TypeKind::RawPtr(pattern), TypeKind::RawPtr(actual)) => {
            match_type(pattern, actual, params, type_bindings, lifetime_bindings)
        }
        (TypeKind::Array(pattern, pattern_len), TypeKind::Array(actual, actual_len)) => {
            pattern_len == actual_len
                && match_type(pattern, actual, params, type_bindings, lifetime_bindings)
        }
        _ => false,
    }
}

#[derive(Debug, Clone)]
enum FunctionBodyId {
    Function(String),
    TraitImplMethod {
        impl_key: (Instance, Type),
        method_index: usize,
    },
    InherentImplMethod {
        impl_index: usize,
        method_index: usize,
    },
}

impl IndexedProgram {
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
            functions.insert(f.meta.name.clone(), f.clone());
        }

        let mut traits: IndexMap<String, TraitDecl> = IndexMap::new();
        let mut impls: IndexMap<(Instance, Type), ImplBlock> = IndexMap::new();
        let mut inherent_impls = Vec::new();
        for decl in &program.declarations {
            if let Some(m) = decl.meta() {
                // Types and traits share the type namespace: `struct Foo`
                // and `trait Foo` collide (Rust's rule). Functions have
                // their own namespace, so `struct Foo` and `fn Foo`
                // coexist. Impls are anonymous — keyed by (trait, target),
                // duplicates are a coherence error.
                let existing = match decl {
                    Declaration::Struct(_) | Declaration::Enum(_) | Declaration::Trait(_) => {
                        if types.contains_key(&m.name) {
                            Some("type")
                        } else if traits.contains_key(&m.name) {
                            Some("trait")
                        } else {
                            None
                        }
                    }
                    Declaration::Fn(_) => {
                        if functions.contains_key(&m.name) {
                            Some("function")
                        } else {
                            None
                        }
                    }
                    Declaration::Impl(_) => None,
                };
                if let Some(kind_word) = existing {
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
                        functions.insert(m.name.clone(), f.clone());
                    }
                    Declaration::Trait(t) => {
                        traits.insert(m.name.clone(), t.clone());
                    }
                    Declaration::Impl(_) => {}
                }
            } else if let Declaration::Impl(imp) = decl {
                if let Some(trait_path) = &imp.trait_path {
                    let key = (trait_path.clone(), imp.target.clone());
                    if impls.contains_key(&key) {
                        errors.push(Diagnostic::new(
                            DuplicateDeclaration,
                            imp.params.source,
                            format!(
                                "Duplicate impl of trait '{}' for target type {}",
                                trait_path, imp.target,
                            ),
                        ));
                        continue;
                    }
                    impls.insert(key, imp.clone());
                } else {
                    inherent_impls.push(imp.clone());
                }
            }
        }

        (
            IndexedProgram {
                types,
                traits,
                functions,
                impls,
                inherent_impls,
            },
            errors,
        )
    }

    /// Return accepted declarations in source order.
    /// Compiler-provided intrinsic signatures are lookup entries only and are
    /// excluded from declaration traversal.
    pub fn declarations(&self) -> Vec<DeclarationRef<'_>> {
        let types = self.types.values().map(|decl| match decl {
            TypeDecl::Struct(s) => DeclarationRef::Struct(s),
            TypeDecl::Enum(e) => DeclarationRef::Enum(e),
        });
        let traits = self.traits.values().map(DeclarationRef::Trait);
        let functions = self
            .functions
            .values()
            .filter(|function| {
                function.meta.name_source.generated_kind() != Some(GeneratedKind::Intrinsic)
            })
            .map(DeclarationRef::Function);
        let impls = self
            .impls
            .values()
            .chain(&self.inherent_impls)
            .map(DeclarationRef::Impl);

        let mut declarations: Vec<_> = types.chain(traits).chain(functions).chain(impls).collect();
        declarations.sort_by_key(|declaration| {
            let span = declaration.source().span();
            (span.line, span.col, span.end_line, span.end_col)
        });
        declarations
    }

    /// Visit free functions and impl methods in source declaration order,
    /// with their generic context and optional body. Compiler-provided
    /// intrinsic lookup entries are excluded.
    pub fn functions(
        &self,
        mut visitor: impl FnMut(LocalEnv<'_>, &Function, Option<&FunctionBody>),
    ) {
        for declaration in self.declarations() {
            match declaration {
                DeclarationRef::Function(function) => {
                    visitor(
                        LocalEnv::for_decl(self, &function.meta.params),
                        function,
                        function.body.as_ref(),
                    );
                }
                DeclarationRef::Impl(impl_block) => {
                    for method in &impl_block.methods {
                        visitor(
                            LocalEnv::for_impl_method(self, impl_block, method),
                            method,
                            method.body.as_ref(),
                        );
                    }
                }
                DeclarationRef::Struct(_) | DeclarationRef::Enum(_) | DeclarationRef::Trait(_) => {}
            }
        }
    }

    /// Visit free-function and impl-method bodies with their generic context.
    pub fn function_bodies(&self, mut visitor: impl FnMut(LocalEnv<'_>, &Function, &FunctionBody)) {
        self.functions(|env, function, body| {
            if let Some(body) = body {
                visitor(env, function, body);
            }
        });
    }

    /// Mutable body visitor for free functions and impl methods.
    /// Each body is detached while the visitor runs so the accompanying
    /// [`LocalEnv`] can borrow the complete indexed program immutably.
    pub fn visit_function_bodies_mut(
        &mut self,
        mut visitor: impl FnMut(LocalEnv<'_>, &Function, &mut FunctionBody),
    ) {
        let body_ids = self.function_body_ids();
        for body_id in body_ids {
            match body_id {
                FunctionBodyId::Function(name) => {
                    let mut body = self
                        .functions
                        .get_mut(&name)
                        .and_then(|function| function.body.take())
                        .expect("body identity collected from this indexed program");
                    let function = self
                        .functions
                        .get(&name)
                        .expect("body visitation does not remove functions");
                    visitor(
                        LocalEnv::for_decl(self, &function.meta.params),
                        function,
                        &mut body,
                    );
                    self.functions
                        .get_mut(&name)
                        .expect("body visitation does not remove functions")
                        .body = Some(body);
                }
                FunctionBodyId::TraitImplMethod {
                    impl_key,
                    method_index,
                } => {
                    let mut body = self
                        .impls
                        .get_mut(&impl_key)
                        .and_then(|impl_block| impl_block.methods.get_mut(method_index))
                        .and_then(|method| method.body.take())
                        .expect("method body identity collected from this indexed program");
                    let impl_block = self
                        .impls
                        .get(&impl_key)
                        .expect("body visitation does not remove impls");
                    let method = impl_block
                        .methods
                        .get(method_index)
                        .expect("body visitation does not remove methods");
                    visitor(
                        LocalEnv::for_impl_method(self, impl_block, method),
                        method,
                        &mut body,
                    );
                    self.impls
                        .get_mut(&impl_key)
                        .and_then(|impl_block| impl_block.methods.get_mut(method_index))
                        .expect("body visitation does not remove methods")
                        .body = Some(body);
                }
                FunctionBodyId::InherentImplMethod {
                    impl_index,
                    method_index,
                } => {
                    let mut body = self.inherent_impls[impl_index].methods[method_index]
                        .body
                        .take()
                        .expect("method body identity collected from this indexed program");
                    let impl_block = &self.inherent_impls[impl_index];
                    let method = &impl_block.methods[method_index];
                    visitor(
                        LocalEnv::for_impl_method(self, impl_block, method),
                        method,
                        &mut body,
                    );
                    self.inherent_impls[impl_index].methods[method_index].body = Some(body);
                }
            }
        }
    }

    fn function_body_ids(&self) -> Vec<FunctionBodyId> {
        let mut body_ids = Vec::new();
        for function in self.functions.values() {
            if function.body.is_some()
                && function.meta.name_source.generated_kind() != Some(GeneratedKind::Intrinsic)
            {
                body_ids.push((
                    function.meta.name_source,
                    FunctionBodyId::Function(function.meta.name.clone()),
                ));
            }
        }
        for ((trait_path, target), impl_block) in &self.impls {
            for (method_index, method) in impl_block.methods.iter().enumerate() {
                if method.body.is_some() {
                    body_ids.push((
                        impl_block.params.source,
                        FunctionBodyId::TraitImplMethod {
                            impl_key: (trait_path.clone(), target.clone()),
                            method_index,
                        },
                    ));
                }
            }
        }
        for (impl_index, impl_block) in self.inherent_impls.iter().enumerate() {
            for (method_index, method) in impl_block.methods.iter().enumerate() {
                if method.body.is_some() {
                    body_ids.push((
                        impl_block.params.source,
                        FunctionBodyId::InherentImplMethod {
                            impl_index,
                            method_index,
                        },
                    ));
                }
            }
        }
        body_ids.sort_by_key(|(source, _)| {
            let span = source.span();
            (span.line, span.col, span.end_line, span.end_col)
        });
        body_ids.into_iter().map(|(_, body_id)| body_id).collect()
    }

    /// Return all instantiated fields of the struct type `ty`, if `ty` is a declared struct.
    /// Substitutes the struct's type-parameter references (`TypeKind::Param`)
    /// with the concrete args on `ty`.
    pub fn struct_fields(&self, ty: &Type) -> Option<Vec<StructField>> {
        let TypeKind::Custom(Instance {
            name,
            type_args: args,
            ..
        }) = &ty.kind
        else {
            return None;
        };
        let TypeDecl::Struct(s) = self.types.get(name)? else {
            return None;
        };
        s.fields
            .iter()
            .map(|f| {
                s.meta
                    .try_substitute_types(&f.ty, args)
                    .map(|substituted_ty| StructField {
                        name: f.name.clone(),
                        ty: substituted_ty,
                        source: f.source,
                    })
            })
            .collect()
    }

    /// Type of `field` in the struct type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared struct or the field doesn't exist.
    /// Substitutes the struct's type-parameter references (`TypeKind::Param`)
    /// with the concrete args on `ty`, so `Box<i64>::inner` yields `i64`,
    /// not the raw declared `T`.
    pub fn field_type(&self, ty: &Type, field: &str) -> Option<Type> {
        let TypeKind::Custom(Instance {
            name,
            type_args: args,
            ..
        }) = &ty.kind
        else {
            return None;
        };
        let TypeDecl::Struct(s) = self.types.get(name)? else {
            return None;
        };
        let f_ty = &s.fields.iter().find(|f| f.name == field)?.ty;
        // Arity mismatch on the instance is already reported by
        // validate_type; fall back to the raw field type so callers
        // don't misinterpret arity errors as "no such field".
        Some(
            s.meta
                .try_substitute_types(f_ty, args)
                .unwrap_or_else(|| f_ty.clone()),
        )
    }

    /// Payload type of `variant` in the enum type `ty`, if any. Returns `None` if
    /// `ty` isn't a declared enum or the variant doesn't exist.
    /// Substitutes the enum's type-parameter references (`TypeKind::Param`)
    /// with the concrete args on `ty`, so `Option<i64>::Some` yields `i64`,
    /// not the raw declared `T`.
    pub fn variant_payload_type(&self, ty: &Type, variant: &str) -> Option<Type> {
        let TypeKind::Custom(Instance {
            name,
            type_args: args,
            ..
        }) = &ty.kind
        else {
            return None;
        };
        let TypeDecl::Enum(e) = self.types.get(name)? else {
            return None;
        };
        let v_ty = &e.variants.iter().find(|v| v.name == variant)?.ty;
        Some(
            e.meta
                .try_substitute_types(v_ty, args)
                .unwrap_or_else(|| v_ty.clone()),
        )
    }

    pub fn types_match(&self, t1: &Type, t2: &Type) -> bool {
        match (&t1.kind, &t2.kind) {
            (TypeKind::Int(a), TypeKind::Int(b)) => a == b,
            (TypeKind::Float(a), TypeKind::Float(b)) => a == b,
            (TypeKind::Bool, TypeKind::Bool) => true,
            (TypeKind::Unit, TypeKind::Unit) => true,
            (TypeKind::Never, TypeKind::Never) => true,
            (
                TypeKind::Custom(Instance {
                    name: a_name,
                    type_args: a_args,
                    ..
                }),
                TypeKind::Custom(Instance {
                    name: b_name,
                    type_args: b_args,
                    ..
                }),
            ) => {
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
}

impl LocalEnv<'_> {
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
                if let Some(f_ty) = self.program.field_type(&inner_ty, field_name) {
                    return Ok(f_ty);
                }
                let name = match &inner_ty.kind {
                    TypeKind::Custom(Instance { name: n, .. }) => n,
                    _ => {
                        return Err(err(TypeResolutionErrorKind::FieldOfNonStruct {
                            field: field_name.clone(),
                            ty: inner_ty,
                        }))
                    }
                };
                match self.program.types.get(name) {
                    Some(TypeDecl::Struct(_)) => Err(err(TypeResolutionErrorKind::NoSuchField {
                        type_name: name.clone(),
                        field: field_name.clone(),
                    })),
                    Some(TypeDecl::Enum(_)) => Err(err(TypeResolutionErrorKind::FieldOfEnum {
                        field: field_name.clone(),
                        enum_name: name.clone(),
                    })),
                    None => Err(err(TypeResolutionErrorKind::UndeclaredType(name.clone()))),
                }
            }
            Place::Downcast(inner, variant_name) => {
                let inner_ty = self.type_of_place(inner, locals)?;
                if let Some(payload_ty) = self.program.variant_payload_type(&inner_ty, variant_name)
                {
                    return Ok(payload_ty);
                }
                let name = match &inner_ty.kind {
                    TypeKind::Custom(Instance { name: n, .. }) => n,
                    _ => return Err(err(TypeResolutionErrorKind::DowncastOfNonEnum(inner_ty))),
                };
                match self.program.types.get(name) {
                    Some(TypeDecl::Enum(_)) => Err(err(TypeResolutionErrorKind::NoSuchVariant {
                        enum_name: name.clone(),
                        variant: variant_name.clone(),
                    })),
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

    /// Look up free function `name` and instantiate its signature for `type_args`.
    pub fn fn_type(&self, name: &str, type_args: &[Type]) -> Result<Type, TypeResolutionError> {
        let f = self.program.functions.get(name).ok_or_else(|| {
            TypeResolutionError::new(TypeResolutionErrorKind::UndeclaredFunction(
                name.to_string(),
            ))
        })?;
        Ok(fn_ty(f.instantiate_params(type_args)))
    }

    /// Resolve a `TraitFn` callee to the concrete `fn(...)` type of its
    /// method after impl-table lookup and substitution. Errors trickle
    /// out as `TypeResolutionError`s so the caller renders them
    /// alongside other operand-typing errors.
    ///
    /// Impl lookup structurally matches the trait path and target together,
    /// binding impl-header parameters consistently across both patterns.
    fn resolve_trait_fn(
        &self,
        trait_path: &Instance,
        self_ty: &Type,
        method: &Instance,
    ) -> Result<Type, TypeResolutionError> {
        if !self.program.traits.contains_key(&trait_path.name) {
            return Err(TypeResolutionError::new(
                TypeResolutionErrorKind::TraitFnUnknownTrait(trait_path.name.clone()),
            ));
        }
        if let TypeKind::Param(name) = &self_ty.kind {
            return Err(TypeResolutionError::new(
                TypeResolutionErrorKind::TraitFnParamReceiver(name.clone()),
            ));
        }
        let matches = self.matching_impls(trait_path, self_ty);
        let (imp, bindings) = match matches.as_slice() {
            [] => {
                return Err(TypeResolutionError::new(
                    TypeResolutionErrorKind::TraitFnNoImpl {
                        trait_path: trait_path.clone(),
                        self_ty: self_ty.clone(),
                    },
                ));
            }
            [matched] => matched,
            _ => {
                return Err(TypeResolutionError::new(
                    TypeResolutionErrorKind::TraitFnAmbiguousImpl {
                        trait_path: trait_path.clone(),
                        self_ty: self_ty.clone(),
                    },
                ));
            }
        };
        let impl_method = imp
            .methods
            .iter()
            .find(|m| m.meta.name == method.name)
            .ok_or_else(|| {
                TypeResolutionError::new(TypeResolutionErrorKind::TraitFnNoMethod {
                    trait_path: trait_path.clone(),
                    self_ty: self_ty.clone(),
                    method: method.name.clone(),
                })
            })?;
        let mut params = imp.params.clone();
        params
            .lifetime_params
            .extend(impl_method.meta.params.lifetime_params.clone());
        params
            .outlives
            .extend(impl_method.meta.params.outlives.clone());
        params
            .type_params
            .extend(impl_method.meta.params.type_params.clone());
        let type_args = bindings
            .type_args
            .iter()
            .cloned()
            .chain(method.type_args.iter().cloned())
            .collect::<Vec<_>>();
        let param_tys = impl_method
            .params
            .iter()
            .map(|p| {
                params
                    .try_substitute_types(&p.ty, &type_args)
                    .unwrap_or_else(|| p.ty.clone())
            })
            .collect();
        Ok(fn_ty(param_tys))
    }

    fn matching_impls(
        &self,
        trait_path: &Instance,
        self_ty: &Type,
    ) -> Vec<(&ImplBlock, ImplBindings)> {
        self.program
            .impls
            .values()
            .filter_map(|imp| {
                let bindings = match_impl_header(imp, trait_path, self_ty)?;
                impl_marker_bounds_satisfied(imp, &bindings, |arg| self.class_of(arg))
                    .then_some((imp, bindings))
            })
            .collect()
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
                ConstVal::FnName(name, type_args) => self.fn_type(name, type_args),
                ConstVal::TraitFn {
                    trait_path,
                    self_ty,
                    method,
                } => self.resolve_trait_fn(trait_path, self_ty, method),
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
                let e_decl = match self.program.types.get(enum_name) {
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
                if type_args.len() != e_decl.meta.params.type_params.len() {
                    return Err(err(TypeResolutionErrorKind::EnumTypeArgArity {
                        enum_name: enum_name.clone(),
                        expected: e_decl.meta.params.type_params.len(),
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
                if !self.program.types_match(&expected_payload, &op_ty) {
                    return Err(err(TypeResolutionErrorKind::EnumPayloadMismatch {
                        variant: variant_name.clone(),
                        enum_name: enum_name.clone(),
                        expected: expected_payload,
                        found: op_ty,
                    }));
                }

                Ok(Type::new(
                    TypeKind::Custom(Instance::new(
                        enum_name.clone(),
                        Vec::new(),
                        type_args.clone(),
                    )),
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
                    if !self.program.types_match(&first_ty, &ty) {
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

#[cfg(test)]
mod declaration_iteration_tests {
    use super::*;
    use crate::mir::parser::Parser;

    #[test]
    fn declarations_cover_indexed_namespaces_and_exclude_intrinsics() {
        let program = Parser::parse_or_panic(
            "
            trait T { fn use_(value: & Self); }
            struct S: Copy + Drop { value: i64 }
            impl T for S {
              fn use_(value: & S) { entry: return }
            }
            fn f() { entry: return }
            enum E: Copy + Drop { V: unit }
            ",
        );
        let (program, errors) = IndexedProgram::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");

        let declarations: Vec<String> = program
            .declarations()
            .into_iter()
            .map(|declaration| match declaration {
                DeclarationRef::Struct(s) => format!("struct {}", s.meta.name),
                DeclarationRef::Enum(e) => format!("enum {}", e.meta.name),
                DeclarationRef::Function(f) => format!("fn {}", f.meta.name),
                DeclarationRef::Trait(t) => format!("trait {}", t.meta.name),
                DeclarationRef::Impl(_) => "impl".to_string(),
            })
            .collect();

        assert_eq!(
            declarations,
            ["trait T", "struct S", "impl", "fn f", "enum E"]
        );
        let mut functions = Vec::new();
        program.functions(|_env, function, body| {
            functions.push((function.meta.name.clone(), body.is_some()));
        });
        assert_eq!(
            functions,
            [("use_".to_string(), true), ("f".to_string(), true)]
        );
    }

    #[test]
    fn function_visitors_provide_generic_context_and_reattach_mutated_bodies() {
        let program = Parser::parse_or_panic(
            "
            trait<T> Tr { fn<U> method(value: & Self, other: U); }
            struct<T> S { value: T }
            impl<X> Tr<X> for S<X> {
              fn<Y> method(value: & S<X>, other: Y) { entry: return }
            }
            fn<Z> free(value: Z) { entry: return }
            extern fn<Z> external(value: Z);
            ",
        );
        let (mut program, errors) = IndexedProgram::build(&program);
        assert!(errors.is_empty(), "environment errors: {errors:?}");

        let mut contexts = Vec::new();
        program.functions(|env, function, body| {
            if function.meta.name == "method" {
                assert!(env.type_param("X").is_some());
                assert!(env.type_param("Y").is_some());
            } else {
                assert!(env.type_param("Z").is_some());
                assert!(env.type_param("X").is_none());
            }
            contexts.push((
                function.meta.name.clone(),
                env.impl_generics()
                    .and_then(|params| params.type_params.first())
                    .map(|param| param.name.clone()),
                env.decl_generics()
                    .type_params
                    .first()
                    .map(|param| param.name.clone()),
                env.self_ty().map(ToString::to_string),
                body.is_some(),
            ));
        });
        assert_eq!(
            contexts,
            [
                (
                    "method".to_string(),
                    Some("X".to_string()),
                    Some("Y".to_string()),
                    Some("S<X>".to_string()),
                    true,
                ),
                ("free".to_string(), None, Some("Z".to_string()), None, true),
                (
                    "external".to_string(),
                    None,
                    Some("Z".to_string()),
                    None,
                    false,
                ),
            ]
        );

        program.visit_function_bodies_mut(|env, function, body| {
            if function.meta.name == "free" {
                assert!(env.program().functions["free"].body.is_none());
            } else {
                assert!(env
                    .program()
                    .impls
                    .values()
                    .flat_map(|impl_block| &impl_block.methods)
                    .find(|method| method.meta.name == function.meta.name)
                    .is_some_and(|method| method.body.is_none()));
            }
            body.blocks[0].label.push_str("_visited");
        });

        let mut labels = Vec::new();
        program.function_bodies(|_env, function, body| {
            labels.push((function.meta.name.clone(), body.blocks[0].label.clone()));
        });
        assert_eq!(
            labels,
            [
                ("method".to_string(), "entry_visited".to_string()),
                ("free".to_string(), "entry_visited".to_string()),
            ]
        );
    }
}
