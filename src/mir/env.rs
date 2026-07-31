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

use crate::common::Marker;
use crate::diagnostics::Diagnostic;
use crate::mir::ast::*;
use crate::mir::diagnostic_format::{DiagnosticFormat, DiagnosticScope};
use crate::mir::helpers::*;
use crate::mir::type_check::{TypeCheckCode, TypeCheckCode::*};
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
    /// `TraitFn` callee names a trait not in the env.
    TraitFnUnknownTrait(String),
    /// `TraitFn` receiver is a generic type parameter; resolution
    /// through the parameter's trait bounds needs the trait-bound
    /// vocabulary populated on `TypeParam.bounds.traits`, which
    /// requires trait-bound syntax at the binding site.
    TraitFnParamReceiver(String),
    /// No impl of `trait_path` matches the given self_ty.
    TraitFnNoImpl { trait_path: Instance, self_ty: Type },
    /// Impl of `trait_path` for self_ty exists but doesn't declare the
    /// method the callee names.
    TraitFnNoMethod { trait_path: Instance, self_ty: Type, method: String },
}

impl TypeResolutionError {
    fn new(kind: TypeResolutionErrorKind) -> Self {
        Self { kind }
    }

    // TODO: Why is there this translation happening, can this be inlined or simplified?
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
            TypeResolutionErrorKind::TraitFnNoMethod { .. } => TraitFnNoMethod,
        }
    }

    pub fn message(
        &self,
        format: &mut DiagnosticFormat,
        caller_scope: &DiagnosticScope,
        env: &GlobalEnv,
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

#[derive(Debug, Clone)]
pub struct GlobalEnv {
    /// Struct and enum declarations, keyed by name. Uses `IndexMap` so
    /// iteration order matches declaration order — analyses that iterate
    /// (e.g. field validation) produce diagnostics deterministically.
    pub types: IndexMap<String, TypeDecl>,
    /// Trait declarations, keyed by name. Kept out of `types` because
    /// a trait is not a first-class type: `x: MyTrait` and
    /// `Vec<MyTrait>` are illegal at the type-name resolver, so putting
    /// traits in `types` would make them accidentally satisfy those
    /// positions. Name-uniqueness between `types` and `traits` is
    /// enforced together (see `GlobalEnv::build`) — Rust's type-namespace
    /// rule.
    pub traits: IndexMap<String, TraitDecl>,
    /// Function signatures, keyed by name. Bodies live in
    /// [`Program`](crate::mir::ast::Program) — callers that need to
    /// walk statements iterate `Program::functions()` and use `GlobalEnv` for
    /// name resolution (`env.functions[callee_name].params`, etc.).
    /// Keeping only signatures in `GlobalEnv` means elaboration can mutate
    /// bodies in-place on `Program` without an `GlobalEnv` resync step.
    pub functions: IndexMap<String, Function>,
    /// Impl blocks, keyed by `(trait_path, target_type)`. The full
    /// trait path (name + lifetime + type args) is the key so multiple
    /// impls of a generic trait for the same target coexist —
    /// `impl Iter<i64> for X` and `impl Iter<u8> for X` are distinct
    /// impls, not a collision. Lookup uses structural equality;
    /// unification for generic impl targets like `impl<T> Iter<T> for
    /// Bag<T>` is a follow-up under the mono trait-resolution work.
    /// Duplicate keys are a coherence error caught at build time.
    pub impls: IndexMap<(Instance, Type), ImplBlock>,
}

impl GlobalEnv {
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
                let key = (imp.trait_path.clone(), imp.target.clone());
                if impls.contains_key(&key) {
                    errors.push(Diagnostic::new(
                        DuplicateDeclaration,
                        imp.params.source,
                        format!(
                            "Duplicate impl of trait '{}' for target type {}",
                            imp.trait_path, imp.target,
                        ),
                    ));
                    continue;
                }
                impls.insert(key, imp.clone());
            }
        }

        (
            GlobalEnv {
                types,
                traits,
                functions,
                impls,
            },
            errors,
        )
    }

    /// Return the substructural class of `ty` as a `Markers` value under
    /// the given type-parameter scope.
    pub fn class_of(&self, ty: &Type, params: &ParamsIntro) -> Markers {
        let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Fn(_) => all(),
            TypeKind::Never => all(),
            TypeKind::RawPtr(_) => all(),
            TypeKind::Ref(kind, _, _) => match kind {
                RefKind::Shared => all(),
                RefKind::Mut | RefKind::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
                RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
            },
            TypeKind::Custom(Instance { name, .. }) => match self.types.get(name) {
                Some(TypeDecl::Struct(s)) => s.meta.markers,
                Some(TypeDecl::Enum(e)) => e.meta.markers,
                None => Markers::empty(),
            },
            TypeKind::Param(name) => params
                .type_params
                .iter()
                .find(|p| p.name == *name)
                .map(|p| p.bounds.markers)
                .unwrap_or_else(Markers::empty),
            TypeKind::Array(elem, _) => self.class_of(elem, params),
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
    pub fn validate_type(&self, ty: &Type, params: &ParamsIntro) -> Result<(), TypeValidationError> {
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
                let decl_params: &[TypeParam] = &decl_meta.params.type_params;
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
                    self.validate_type(arg, params)?;
                    let arg_class = self.class_of(arg, params);
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
            TypeKind::Fn(fn_params) => {
                for p in fn_params {
                    self.validate_type(p, params)?;
                }
                Ok(())
            }
            TypeKind::Ref(_, _, inner) => self.validate_type(inner, params),
            TypeKind::RawPtr(inner) => self.validate_type(inner, params),
            TypeKind::Array(elem, _) => self.validate_type(elem, params),
        }
    }

    /// Empty-scope convenience: for callers with no in-scope type
    /// parameters. A `Param(_)` reachable via this path is
    /// well-formed (Ok) but its markers can't be resolved to real
    /// bounds — use only outside of generic decl bodies.
    pub fn validate_type_empty_scope(&self, ty: &Type) -> Result<(), TypeValidationError> {
        let empty = ParamsIntro::empty(crate::common::SourceInfo::generated(
            crate::common::GeneratedKind::TestHelper,
            crate::common::Span::default(),
        ));
        self.validate_type(ty, &empty)
    }

    /// Return all instantiated fields of the struct type `ty`, if `ty` is a declared struct.
    /// Substitutes the struct's type-parameter references (`TypeKind::Param`)
    /// with the concrete args on `ty`.
    pub fn struct_fields(&self, ty: &Type) -> Option<Vec<StructField>> {
        let TypeKind::Custom(Instance { name, type_args: args, .. }) = &ty.kind else {
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
        let TypeKind::Custom(Instance { name, type_args: args, .. }) = &ty.kind else {
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
        let TypeKind::Custom(Instance { name, type_args: args, .. }) = &ty.kind else {
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
                if let Some(f_ty) = self.field_type(&inner_ty, field_name) {
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
                match self.types.get(name) {
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
                if let Some(payload_ty) = self.variant_payload_type(&inner_ty, variant_name) {
                    return Ok(payload_ty);
                }
                let name = match &inner_ty.kind {
                    TypeKind::Custom(Instance { name: n, .. }) => n,
                    _ => return Err(err(TypeResolutionErrorKind::DowncastOfNonEnum(inner_ty))),
                };
                match self.types.get(name) {
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
        let f = self.functions.get(name).ok_or_else(|| {
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
    /// Impl lookup uses structural target equality: `self_ty` must
    /// exactly equal an impl's declared target. Generic-impl-target
    /// unification (matching `Bag<i64>` to `impl<T> Iter<T> for Bag<T>`)
    /// is a follow-up under monomorphization.
    fn resolve_trait_fn(
        &self,
        trait_path: &Instance,
        self_ty: &Type,
        method: &Instance,
    ) -> Result<Type, TypeResolutionError> {
        if !self.traits.contains_key(&trait_path.name) {
            return Err(TypeResolutionError::new(
                TypeResolutionErrorKind::TraitFnUnknownTrait(trait_path.name.clone()),
            ));
        }
        if let TypeKind::Param(name) = &self_ty.kind {
            return Err(TypeResolutionError::new(
                TypeResolutionErrorKind::TraitFnParamReceiver(name.clone()),
            ));
        }
        let imp = self
            .impls
            .get(&(trait_path.clone(), self_ty.clone()))
            .ok_or_else(|| {
                TypeResolutionError::new(TypeResolutionErrorKind::TraitFnNoImpl {
                    trait_path: trait_path.clone(),
                    self_ty: self_ty.clone(),
                })
            })?;
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
        // Impl-header substitution is a no-op: the impl was found via
        // structural equality on a concrete target, so its methods are
        // already instantiated. Only the method's own type_params
        // need substituting from the callee's method args.
        let param_tys = impl_method
            .params
            .iter()
            .map(|p| {
                impl_method
                    .meta
                    .try_substitute_types(&p.ty, &method.type_args)
                    .unwrap_or_else(|| p.ty.clone())
            })
            .collect();
        Ok(fn_ty(param_tys))
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
