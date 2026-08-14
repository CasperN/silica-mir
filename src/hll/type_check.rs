use crate::common::{IntTy, Lifetime, LifetimeParam, Marker, Markers, RefKind, SourceInfo};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::hll::ast::*;
use crate::hll::helpers::*;
use crate::hll::type_fold::TypeFolder;
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

/// Construct an HLL type-check diagnostic without discarding whether its
/// source node was written or generated.
fn source_diagnostic(
    code: HllTypeCheckCode,
    source: SourceInfo,
    message: impl Into<String>,
) -> Diagnostic {
    Diagnostic::new(code, source, message)
}

/// Build a `name → bounds` map from a decl's type parameters. Used
/// when computing a type's substructural class or validating uses
/// against bounds — both need per-name marker info.
fn type_params_scope(params: &[TypeParam]) -> HashMap<String, Markers> {
    params
        .iter()
        .map(|p| (p.name.clone(), p.bounds.markers))
        .collect()
}

/// Substitute type-parameter references in `ty` using `mapping`. Used
/// when reading a declared field/variant/param type on a generic decl:
/// e.g. `Box::inner` has declared type `T`, but on `Box<i64>` the
/// caller sees `i64`. `mapping` binds each declared type-parameter
/// name to the concrete argument at the use site.
fn substitute(ty: &Type, mapping: &HashMap<String, Type>) -> Type {
    SubstituteFolder { mapping }.fold_type(ty)
}

struct SubstituteFolder<'a> {
    mapping: &'a HashMap<String, Type>,
}

impl TypeFolder for SubstituteFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        match &ty.kind {
            TypeKind::Param(name) => self.mapping.get(name).cloned(),
            // Only named type parameters are substitution sites. Every other
            // variant uses the shared structural recursion.
            _ => None,
        }
    }
}

/// Build a `param_name -> arg_type` substitution map, checking that
/// the number of args matches the number of declared type parameters.
/// Pushes an error diagnostic on arity mismatch and returns `None`.
fn build_subst_map(
    decl_name: &str,
    type_params: &[TypeParam],
    args: &[Type],
    source: SourceInfo,
    d: &mut Diagnostics,
) -> Option<HashMap<String, Type>> {
    if args.len() != type_params.len() {
        d.push_error(source_diagnostic(
            ArityMismatch,
            source,
            format!(
                "'{}' takes {} type argument(s), found {}",
                decl_name,
                type_params.len(),
                args.len()
            ),
        ));
        return None;
    }
    let mut mapping = HashMap::new();
    for (tp, arg) in type_params.iter().zip(args.iter()) {
        mapping.insert(tp.name.clone(), arg.clone());
    }
    Some(mapping)
}

use HllTypeCheckCode::*;

fn array_len(len: usize) -> u64 {
    u64::try_from(len).expect("host collection length exceeds Silica's u64 array length")
}

/// Distinguish unification failure modes returned by [`Subst::unify`] while
/// retaining the types needed to render the final diagnostic.
#[derive(Debug)]
pub enum UnifyError {
    Mismatch { expected: Type, found: Type },
    ExpectedInteger { found: Type },
    ExpectedFloat { found: Type },
    Infinite,
    ArityMismatch,
}

impl UnifyError {
    fn to_diag(self, source: SourceInfo) -> Diagnostic {
        match self {
            UnifyError::Mismatch { expected, found } => source_diagnostic(
                TypeMismatch,
                source,
                format!("type mismatch: expected {}, found {}", expected, found),
            ),
            UnifyError::ExpectedInteger { found } => source_diagnostic(
                TypeMismatch,
                source,
                format!("type mismatch: expected integer type, found {}", found),
            ),
            UnifyError::ExpectedFloat { found } => source_diagnostic(
                TypeMismatch,
                source,
                format!("type mismatch: expected float type, found {}", found),
            ),
            UnifyError::Infinite => source_diagnostic(
                InfiniteType,
                source,
                "infinite type detected during unification",
            ),
            UnifyError::ArityMismatch => {
                source_diagnostic(ArityMismatch, source, "function arity mismatch")
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
    /// Unary operator applied to an incompatible operand type
    /// (e.g. unary `-` on an unsigned int or bool).
    UnaryOpInvalidOperand,
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
    /// Control flow statement (break, continue, return) inside a defer block.
    ControlFlowInDefer,
    /// Type annotation references a struct/enum name that isn't declared.
    UndeclaredType,
    /// Generic type instantiation has the wrong number of type arguments
    /// (e.g. `Box<i64, i64>` on a 1-parameter decl, or a bare `Box` on a
    /// generic decl).
    TypeArgArityMismatch,
    /// A type argument at a generic instantiation site doesn't satisfy
    /// the declared marker bound on the corresponding type parameter
    /// (e.g. `Box<Linear>` where the decl is `struct<T: Copy> Box`).
    BoundNotSatisfied,
    /// A function call supplies the wrong number of explicit lifetime
    /// arguments.
    LifetimeArgArityMismatch,
    /// An explicit lifetime argument is not visible at the call site.
    UndeclaredLifetime,
    /// Explicit generic arguments were applied to a function-valued
    /// expression rather than a named generic function.
    GenericArgsOnFunctionValue,
    /// Ambiguous type (type annotations needed).
    AmbiguousType,
    /// Dereferencing a raw pointer outside an unsafe block.
    UnsafeRequired,
    /// `extern "..."` names an ABI other than `"C"`.
    UnknownAbi,
    /// `expr as Type` where the pair isn't a supported cast.
    /// Today's supported cells: numeric widths & signedness, int↔float,
    /// bool→int. Casts *to* bool aren't supported (use `!= 0`); casts
    /// to/from pointer/ref types are not yet supported.
    InvalidCast,
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

#[derive(Clone, Copy)]
enum ResolveMode {
    PreserveUnresolved,
    DefaultUnresolved,
}

#[derive(Clone, Copy)]
enum SolverVariable {
    General(usize),
    Integer(usize),
    Float(usize),
}

impl SolverVariable {
    fn id(self) -> usize {
        match self {
            Self::General(id) | Self::Integer(id) | Self::Float(id) => id,
        }
    }
}

struct ResolveFolder<'a> {
    subst: &'a Subst,
    mode: ResolveMode,
}

impl TypeFolder for ResolveFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        let variable = match &ty.kind {
            TypeKind::Var(id) => SolverVariable::General(*id),
            TypeKind::IntVar(id) => SolverVariable::Integer(*id),
            TypeKind::FloatVar(id) => SolverVariable::Float(*id),
            // Only solver variables are resolution sites. Every structural
            // variant uses the shared recursion and metadata preservation.
            _ => return None,
        };

        if let Some(resolved) = self.subst.map.get(&variable.id()).cloned() {
            return Some(self.fold_type(&resolved));
        }

        match (self.mode, variable) {
            (
                ResolveMode::PreserveUnresolved,
                SolverVariable::General(_) | SolverVariable::Integer(_) | SolverVariable::Float(_),
            ) => None,
            (ResolveMode::DefaultUnresolved, SolverVariable::General(_)) => Some(error_ty()),
            (ResolveMode::DefaultUnresolved, SolverVariable::Integer(_)) => Some(i64_ty()),
            (ResolveMode::DefaultUnresolved, SolverVariable::Float(_)) => Some(f64_ty()),
        }
    }
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
        var_ty(id)
    }

    pub fn fresh_int_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        int_var_ty(id)
    }

    pub fn fresh_float_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        float_var_ty(id)
    }

    pub fn resolve(&self, ty: &Type) -> Type {
        ResolveFolder {
            subst: self,
            mode: ResolveMode::PreserveUnresolved,
        }
        .fold_type(ty)
    }

    pub fn resolve_default(&self, ty: &Type) -> Type {
        ResolveFolder {
            subst: self,
            mode: ResolveMode::DefaultUnresolved,
        }
        .fold_type(ty)
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnifyError> {
        let r1 = self.resolve(t1);
        let r2 = self.resolve(t2);
        match (&r1.kind, &r2.kind) {
            (TypeKind::Error, _) | (_, TypeKind::Error) => Ok(()),
            (TypeKind::Var(id1), TypeKind::Var(id2)) if id1 == id2 => Ok(()),
            (TypeKind::IntVar(id1), TypeKind::IntVar(id2)) if id1 == id2 => Ok(()),
            (TypeKind::FloatVar(id1), TypeKind::FloatVar(id2)) if id1 == id2 => Ok(()),
            (TypeKind::Var(id), _) => {
                if self.occurs_in(*id, &r2) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, r2);
                Ok(())
            }
            (_, TypeKind::Var(id)) => {
                if self.occurs_in(*id, &r1) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, r1);
                Ok(())
            }
            (TypeKind::Never, _) | (_, TypeKind::Never) => Ok(()),
            (TypeKind::IntVar(id), other) => match other {
                TypeKind::IntVar(_) | TypeKind::Int(_) => {
                    self.map.insert(*id, r2);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedInteger { found: r2.clone() }),
            },
            (other, TypeKind::IntVar(id)) => match other {
                TypeKind::IntVar(_) | TypeKind::Int(_) => {
                    self.map.insert(*id, r1);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedInteger { found: r1.clone() }),
            },
            (TypeKind::FloatVar(id), other) => match other {
                TypeKind::FloatVar(_) | TypeKind::Float(_) => {
                    self.map.insert(*id, r2);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedFloat { found: r2.clone() }),
            },
            (other, TypeKind::FloatVar(id)) => match other {
                TypeKind::FloatVar(_) | TypeKind::Float(_) => {
                    self.map.insert(*id, r1);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedFloat { found: r1.clone() }),
            },
            (TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => Ok(()),
            (TypeKind::Float(f1), TypeKind::Float(f2)) if f1 == f2 => Ok(()),
            (TypeKind::Bool, TypeKind::Bool) => Ok(()),
            (TypeKind::Unit, TypeKind::Unit) => Ok(()),
            (
                TypeKind::Custom(Instance {
                    name: n1,
                    type_args: a1,
                    ..
                }),
                TypeKind::Custom(Instance {
                    name: n2,
                    type_args: a2,
                    ..
                }),
            ) if n1 == n2 && a1.len() == a2.len() => {
                let a1 = a1.clone();
                let a2 = a2.clone();
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (TypeKind::Param(p1), TypeKind::Param(p2)) if p1 == p2 => Ok(()),
            (TypeKind::Ref(k1, _, inner1), TypeKind::Ref(k2, _, inner2)) if k1 == k2 => {
                self.unify(inner1, inner2)
            }
            (TypeKind::RawPtr(inner1), TypeKind::RawPtr(inner2)) => self.unify(inner1, inner2),
            (TypeKind::Array(inner1, size1), TypeKind::Array(inner2, size2)) if size1 == size2 => {
                self.unify(inner1, inner2)
            }
            (TypeKind::Fn(p1, r1), TypeKind::Fn(p2, r2)) => {
                if p1.len() != p2.len() {
                    return Err(UnifyError::ArityMismatch);
                }
                for (a1, a2) in p1.iter().zip(p2.iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(r1, r2)
            }
            (_, _) => Err(UnifyError::Mismatch {
                expected: r1,
                found: r2,
            }),
        }
    }

    fn occurs_in(&self, id: usize, ty: &Type) -> bool {
        match &ty.kind {
            TypeKind::Var(v) | TypeKind::IntVar(v) | TypeKind::FloatVar(v) => {
                if *v == id {
                    true
                } else if let Some(resolved) = self.map.get(v) {
                    self.occurs_in(id, resolved)
                } else {
                    false
                }
            }
            TypeKind::Ref(_, _, inner) => self.occurs_in(id, inner),
            TypeKind::RawPtr(inner) => self.occurs_in(id, inner),
            TypeKind::Array(inner, _) => self.occurs_in(id, inner),
            TypeKind::Fn(params, ret) => {
                params.iter().any(|p| self.occurs_in(id, p)) || self.occurs_in(id, ret)
            }
            TypeKind::Custom(Instance {
                type_args: args, ..
            }) => args.iter().any(|a| self.occurs_in(id, a)),
            _ => false,
        }
    }
}

pub struct TypeEnv {
    variables: Vec<HashMap<String, Type>>,
    structs: HashMap<String, StructDecl>,
    enums: HashMap<String, EnumDecl>,
    functions: HashMap<String, FnDecl>,
    current_ret_ty: Option<Type>,
    /// Type-parameter names → declared marker bounds for the fn being
    /// checked. Empty outside a fn body.
    current_type_params: HashMap<String, Markers>,
    current_lifetimes: HashSet<Lifetime>,
    current_function: Option<String>,
    in_unsafe: bool,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            variables: vec![HashMap::new()],
            structs: HashMap::new(),
            enums: HashMap::new(),
            functions: HashMap::new(),
            current_ret_ty: None,
            current_type_params: HashMap::new(),
            current_lifetimes: HashSet::new(),
            current_function: None,
            in_unsafe: false,
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

    /// Substructural class of a type in this environment. Scalars,
    /// references, raw pointers, fn-ptr types are all `Copy + Drop +
    /// Move`. A `Custom` name resolves to the decl's declared markers
    /// (or empty if the name is undeclared — validation catches that
    /// separately). A `Param` uses the bounds attached to it in
    /// `scope`. See MIR's `class_of` for the same rules.
    fn class_of(&self, ty: &Type, scope: &HashMap<String, Markers>) -> Markers {
        let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never => all(),
            TypeKind::Fn(_, _) | TypeKind::RawPtr(_) => all(),
            TypeKind::Ref(kind, _, _) => match kind {
                RefKind::Shared => all(),
                RefKind::Mut | RefKind::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
                RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
            },
            TypeKind::Custom(Instance { name, .. }) => {
                if let Some(s) = self.structs.get(name) {
                    s.markers
                } else if let Some(e) = self.enums.get(name) {
                    e.markers
                } else {
                    Markers::empty()
                }
            }
            TypeKind::Param(name) => scope.get(name).copied().unwrap_or_else(Markers::empty),
            TypeKind::Array(elem, _) => self.class_of(elem, scope),
            TypeKind::Var(_) | TypeKind::IntVar(_) | TypeKind::FloatVar(_) | TypeKind::Error => {
                all()
            }
        }
    }

    /// Walk `ty` and push a diagnostic per problem: an undeclared
    /// `Custom` name, a `Param` not in scope, wrong type-arg arity,
    /// or an arg that fails the declared bound. Each is reported at
    /// the source of the precise type node that is invalid. Continues past
    /// errors so a single top-level `Type` with multiple defects surfaces
    /// them all.
    pub fn validate_type(&self, ty: &Type, scope: &HashMap<String, Markers>, d: &mut Diagnostics) {
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never
            | TypeKind::Var(_)
            | TypeKind::IntVar(_)
            | TypeKind::FloatVar(_)
            | TypeKind::Error => {}
            TypeKind::Param(name) => {
                if !scope.contains_key(name) {
                    d.push_error(Diagnostic::new(
                        UndeclaredType,
                        ty.source,
                        format!("undeclared type '{}'", name),
                    ));
                }
            }
            TypeKind::Ref(_, _, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
                self.validate_type(inner, scope, d);
            }
            TypeKind::Fn(params, ret) => {
                for p in params {
                    self.validate_type(p, scope, d);
                }
                self.validate_type(ret, scope, d);
            }
            TypeKind::Custom(Instance {
                name,
                type_args: args,
                ..
            }) => {
                for a in args {
                    self.validate_type(a, scope, d);
                }
                let type_params: &[TypeParam] = if let Some(s) = self.structs.get(name) {
                    &s.type_params
                } else if let Some(e) = self.enums.get(name) {
                    &e.type_params
                } else {
                    d.push_error(Diagnostic::new(
                        UndeclaredType,
                        ty.source,
                        format!("undeclared type '{}'", name),
                    ));
                    return;
                };
                if args.len() != type_params.len() {
                    d.push_error(Diagnostic::new(
                        TypeArgArityMismatch,
                        ty.source,
                        format!(
                            "'{}' takes {} type argument(s), found {}",
                            name,
                            type_params.len(),
                            args.len()
                        ),
                    ));
                    return;
                }
                for (tp, arg) in type_params.iter().zip(args.iter()) {
                    let arg_class = self.class_of(arg, scope);
                    for m in [Marker::Copy, Marker::Drop, Marker::Move] {
                        if tp.bounds.markers.declared(m) && !arg_class.implies(m) {
                            d.push_error(Diagnostic::new(
                                BoundNotSatisfied,
                                arg.source,
                                format!(
                                    "type argument '{}' for '{}::{}' does not satisfy bound '{:?}'",
                                    arg, name, tp.name, m
                                ),
                            ));
                        }
                    }
                }
            }
        }
    }
}

/// Fully resolved types inferred for HLL expressions, keyed by their complete
/// source provenance so written and generated nodes attributed to the same
/// span do not alias.
pub type ExpressionTypes = IndexMap<SourceInfo, Type>;

struct PendingInstantiation {
    source: SourceInfo,
    function_name: String,
    caller_name: Option<String>,
    caller_type_params: HashMap<String, Markers>,
    type_params: Vec<TypeParam>,
    type_args: Vec<Type>,
}

#[derive(Default)]
pub struct TypeCheckResults {
    pub expression_types: ExpressionTypes,
    pub function_instantiations: IndexMap<SourceInfo, Instance>,
    expression_contexts: IndexMap<SourceInfo, String>,
    pending_instantiations: Vec<PendingInstantiation>,
}

impl std::ops::Deref for TypeCheckResults {
    type Target = ExpressionTypes;

    fn deref(&self) -> &Self::Target {
        &self.expression_types
    }
}

impl std::ops::DerefMut for TypeCheckResults {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.expression_types
    }
}

/// Run HLL type-checking, pushing errors into `d`. Returns resolved expression
/// types and function instantiations; errors accumulate in `d`.
pub fn run_type_check(program: &Program, d: &mut Diagnostics) -> Option<TypeCheckResults> {
    let types = typecheck_program_collect(program, d);
    if d.has_errors() {
        None
    } else {
        Some(types)
    }
}

/// Test-facing wrapper — sibling modules under `hll::*` use this to
/// stage a typecheck without needing a `Diagnostics` container.
/// Production callers should use `run_type_check`.
#[cfg(test)]
pub(super) fn typecheck_program(program: &Program) -> Diagnostics {
    let mut d = Diagnostics::default();
    typecheck_program_collect(program, &mut d);
    d
}

/// Run HLL type-checking, pushing all errors into `d` and returning its results
/// unconditionally. Production callers should use `run_type_check`.
pub(super) fn typecheck_program_collect(
    program: &Program,
    d: &mut Diagnostics,
) -> TypeCheckResults {
    let mut env = TypeEnv::new();
    let mut subst = Subst::new();
    let mut types = TypeCheckResults::default();

    // Preload prelude wrappers (`size_of<T>`, `ptr_offset<T>`) so user
    // code can spell them by name. Bodies live at the MIR level; here
    // we only need the surface signatures.
    for f in crate::hll::prelude::prelude_fn_decls() {
        env.functions.insert(f.name.clone(), f);
    }

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
                env.functions.insert(f.name.clone(), f.clone());
            }
            Declaration::Trait(_) | Declaration::Impl(_) => {}
        }
    }

    // Validate every decl-level type: fields, variant payloads, fn
    // params, fn returns. Every referenced `Custom` must be declared
    // with matching arity, every arg must satisfy the declared bound,
    // and every `Param` must be in scope for its enclosing decl.
    for decl in &program.declarations {
        match decl {
            Declaration::Struct(s) => {
                let scope = type_params_scope(&s.type_params);
                for f in &s.fields {
                    env.validate_type(&f.ty, &scope, d);
                }
            }
            Declaration::Enum(e) => {
                let scope = type_params_scope(&e.type_params);
                for v in &e.variants {
                    env.validate_type(&v.ty, &scope, d);
                }
            }
            Declaration::Fn(f) => {
                let scope = type_params_scope(&f.type_params);
                let errors_before = d.error_count();
                for p in &f.params {
                    env.validate_type(&p.ty, &scope, d);
                }
                env.validate_type(&f.ret_ty, &scope, d);
                d.annotate_errors_in_function(errors_before, &f.name);
            }
            Declaration::Trait(t) => {
                for method in &t.methods {
                    let mut params = t.type_params.clone();
                    params.push(TypeParam {
                        name: "Self".to_string(),
                        bounds: Bounds::default(),
                        source: t.source,
                    });
                    params.extend(method.type_params.clone());
                    let context = trait_method_context(&t.name, &method.name);
                    validate_fn_signature(&env, method, &params, &context, d);
                }
            }
            Declaration::Impl(i) => {
                let impl_scope = type_params_scope(&i.type_params);
                env.validate_type(&i.target, &impl_scope, d);
                if let Some(trait_path) = &i.trait_path {
                    for arg in &trait_path.type_args {
                        env.validate_type(arg, &impl_scope, d);
                    }
                }
                for method in &i.methods {
                    let mut params = i.type_params.clone();
                    params.extend(method.type_params.clone());
                    let context =
                        impl_method_context(&i.target, i.trait_path.as_ref(), &method.name);
                    validate_fn_signature(&env, method, &params, &context, d);
                }
            }
        }
    }

    // Typecheck function bodies
    for decl in &program.declarations {
        match decl {
            Declaration::Fn(f) => {
                validate_extern_abi(f, &f.name, d);
                check_fn_body(&mut env, &mut subst, &mut types, f, &[], &[], &f.name, d);
            }
            Declaration::Impl(i) => {
                for method in &i.methods {
                    let context =
                        impl_method_context(&i.target, i.trait_path.as_ref(), &method.name);
                    check_fn_body(
                        &mut env,
                        &mut subst,
                        &mut types,
                        method,
                        &i.lifetime_params,
                        &i.type_params,
                        &context,
                        d,
                    );
                }
            }
            Declaration::Struct(_) | Declaration::Enum(_) | Declaration::Trait(_) => {}
        }
    }

    // Check for unresolved type variables
    let mut reported_vars = HashSet::new();
    for (source, ty) in &types.expression_types {
        let resolved = subst.resolve(ty);
        let mut unresolved = HashSet::new();
        collect_unresolved_vars(&resolved, &subst, &mut unresolved);
        if !unresolved.is_empty() {
            let has_unreported = unresolved.iter().any(|id| !reported_vars.contains(id));
            if has_unreported {
                reported_vars.extend(unresolved);
                let diagnostic = source_diagnostic(
                    HllTypeCheckCode::AmbiguousType,
                    *source,
                    format!("type annotations needed: type of expression is ambiguous (could not resolve type variable in {})", resolved),
                );
                d.push_error(match types.expression_contexts.get(source) {
                    Some(context) => diagnostic.in_function(context),
                    None => diagnostic,
                });
            }
        }
    }
    for pending in &types.pending_instantiations {
        for argument in &pending.type_args {
            let resolved = subst.resolve(argument);
            let mut unresolved = HashSet::new();
            collect_unresolved_vars(&resolved, &subst, &mut unresolved);
            if unresolved.iter().any(|id| !reported_vars.contains(id)) {
                reported_vars.extend(unresolved);
                let diagnostic = source_diagnostic(
                    HllTypeCheckCode::AmbiguousType,
                    pending.source,
                    format!(
                        "type annotations needed: cannot infer all type arguments for function '{}'",
                        pending.function_name
                    ),
                );
                d.push_error(match &pending.caller_name {
                    Some(function) => diagnostic.in_function(function),
                    None => diagnostic,
                });
            }
        }
    }

    // Resolve all captured expression types in the final map
    let mut resolved_types = IndexMap::new();
    for (source, ty) in std::mem::take(&mut types.expression_types) {
        resolved_types.insert(source, subst.resolve_default(&ty));
    }
    types.expression_types = resolved_types;
    for instantiation in types.function_instantiations.values_mut() {
        for ty in &mut instantiation.type_args {
            *ty = subst.resolve_default(ty);
        }
    }
    types.pending_instantiations.clear();
    types
}

fn validate_fn_signature(
    env: &TypeEnv,
    function: &FnDecl,
    effective_params: &[TypeParam],
    context: &str,
    d: &mut Diagnostics,
) {
    let scope = type_params_scope(effective_params);
    let errors_before = d.error_count();
    for param in &function.params {
        env.validate_type(&param.ty, &scope, d);
    }
    env.validate_type(&function.ret_ty, &scope, d);
    d.annotate_errors_in_function(errors_before, context);
}

fn record_expression_type(
    env: &TypeEnv,
    types: &mut TypeCheckResults,
    source: SourceInfo,
    ty: Type,
) {
    types.expression_types.insert(source, ty);
    if let Some(context) = &env.current_function {
        types.expression_contexts.insert(source, context.clone());
    }
}

fn check_fn_body(
    env: &mut TypeEnv,
    subst: &mut Subst,
    types: &mut TypeCheckResults,
    function: &FnDecl,
    enclosing_lifetime_params: &[LifetimeParam],
    enclosing_params: &[TypeParam],
    context: &str,
    d: &mut Diagnostics,
) {
    let Some(body) = &function.body else { return };

    let mut effective_params = enclosing_params.to_vec();
    effective_params.extend(function.type_params.clone());
    env.current_type_params = type_params_scope(&effective_params);
    env.current_lifetimes = enclosing_lifetime_params
        .iter()
        .chain(&function.lifetime_params)
        .map(|parameter| parameter.lifetime.clone())
        .chain(std::iter::once(Lifetime("static".to_string())))
        .collect();
    env.current_function = Some(context.to_string());
    env.push_scope();
    env.current_ret_ty = Some(function.ret_ty.clone());
    env.in_unsafe = function.is_unsafe;
    for param in &function.params {
        env.insert_var(param.name.clone(), param.ty.clone());
    }
    let errors_before = d.error_count();
    let pending_before = types.pending_instantiations.len();
    check_inner(env, subst, body, &function.ret_ty, types, d);
    check_instantiation_bounds(env, subst, types, pending_before, d);
    d.annotate_errors_in_function(errors_before, context);
    env.pop_scope();
    env.in_unsafe = false;
    env.current_type_params.clear();
    env.current_lifetimes.clear();
    env.current_function = None;
}

fn check_instantiation_bounds(
    env: &TypeEnv,
    subst: &Subst,
    types: &TypeCheckResults,
    first_pending: usize,
    d: &mut Diagnostics,
) {
    for pending in &types.pending_instantiations[first_pending..] {
        for (parameter, argument) in pending.type_params.iter().zip(&pending.type_args) {
            let argument = subst.resolve(argument);
            for marker in parameter.bounds.markers.iter_declared() {
                if !env
                    .class_of(&argument, &pending.caller_type_params)
                    .implies(marker)
                {
                    d.push_error(source_diagnostic(
                        BoundNotSatisfied,
                        pending.source,
                        format!(
                            "type argument '{}' for '{}::{}' does not satisfy bound '{:?}'",
                            argument, pending.function_name, parameter.name, marker
                        ),
                    ));
                }
            }
        }
    }
}

fn validate_extern_abi(function: &FnDecl, context: &str, d: &mut Diagnostics) {
    if function.body.is_some() {
        return;
    }
    let Some(abi) = &function.abi else { return };
    if abi != "C" {
        let source = function.abi_source.unwrap_or(function.source);
        d.push_error(
            source_diagnostic(
                HllTypeCheckCode::UnknownAbi,
                source,
                format!("unknown extern ABI '{}' — expected 'C' or bare extern", abi),
            )
            .in_function(context),
        );
    }
}

fn collect_unresolved_vars(ty: &Type, subst: &Subst, vars: &mut HashSet<usize>) {
    match &ty.kind {
        TypeKind::Var(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            } else {
                vars.insert(*id);
            }
        }
        TypeKind::IntVar(id) | TypeKind::FloatVar(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            }
        }
        TypeKind::Ref(_, _, inner) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::RawPtr(inner) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::Array(inner, _) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::Fn(params, ret) => {
            for p in params {
                collect_unresolved_vars(p, subst, vars);
            }
            collect_unresolved_vars(ret, subst, vars);
        }
        TypeKind::Custom(Instance {
            type_args: args, ..
        }) => {
            for a in args {
                collect_unresolved_vars(a, subst, vars);
            }
        }
        _ => {}
    }
}

/// Return true iff `expr as to` is a supported numeric cast.
///
/// Supported: int↔int (any width, any signedness), float↔float, int↔float,
/// bool→int. `from == to` is trivially supported (lowering drops it).
///
/// Not supported (and rejected with `HTC-InvalidCast`):
/// - Casts to bool from any type. Rust also rejects `int as bool`; the
///   caller should write `!= 0` explicitly. Silica's `$iN_to_bool`
///   intrinsic exists at MIR level (as a truncation to the low bit),
///   but HLL doesn't expose it via `as`.
/// - Casts to or from pointer / ref types. `*T as *U`, `&T as *T`, etc.
///   are on the punchlist; they need a distinct MIR RValue and are
///   blocked on lifetime annotations for the ref-target cases.
/// - Casts involving unit, never, arrays, fn types, or custom types.
pub fn is_cast_supported(from: &Type, to: &Type) -> bool {
    if from == to {
        return true;
    }
    if matches!(&from.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
        && matches!(&to.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
    {
        return true;
    }
    matches!(
        (&from.kind, &to.kind),
        (TypeKind::Int(_), TypeKind::Int(_))
            | (TypeKind::Float(_), TypeKind::Float(_))
            | (TypeKind::Int(_), TypeKind::Float(_))
            | (TypeKind::Float(_), TypeKind::Int(_))
            | (TypeKind::Bool, TypeKind::Int(_))
    )
}

/// Return the intrinsic name that implements `expr as to`, or `None`
/// if `from == to` (no cast needed). Caller must have checked
/// `is_cast_supported` first — this helper panics on unsupported pairs.
pub fn cast_intrinsic_name(from: &Type, to: &Type) -> Option<String> {
    if from == to {
        return None;
    }
    if matches!(&from.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
        && matches!(&to.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
    {
        return None;
    }
    let ty_name = |ty: &Type| match &ty.kind {
        TypeKind::Int(k) => k.name().to_string(),
        TypeKind::Float(k) => k.name().to_string(),
        TypeKind::Bool => "bool".to_string(),
        _ => panic!("cast_intrinsic_name: unsupported type {:?}", ty),
    };
    Some(format!("${}_to_{}", ty_name(from), ty_name(to)))
}

fn instantiate_function(
    env: &TypeEnv,
    subst: &mut Subst,
    name: &str,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<Type> {
    let signature = env.functions.get(name)?.clone();

    if !generics.lifetimes.is_empty() && generics.lifetimes.len() != signature.lifetime_params.len()
    {
        d.push_error(source_diagnostic(
            LifetimeArgArityMismatch,
            source,
            format!(
                "function '{}' takes {} lifetime argument(s), found {}",
                name,
                signature.lifetime_params.len(),
                generics.lifetimes.len()
            ),
        ));
        return None;
    }
    for lifetime in &generics.lifetimes {
        if !env.current_lifetimes.contains(lifetime) {
            d.push_error(source_diagnostic(
                UndeclaredLifetime,
                source,
                format!("undeclared lifetime {}", lifetime),
            ));
        }
    }

    let type_args = if generics.types.is_empty() {
        signature
            .type_params
            .iter()
            .map(|_| subst.fresh_var())
            .collect::<Vec<_>>()
    } else {
        if generics.types.len() != signature.type_params.len() {
            d.push_error(source_diagnostic(
                TypeArgArityMismatch,
                source,
                format!(
                    "function '{}' takes {} type argument(s), found {}",
                    name,
                    signature.type_params.len(),
                    generics.types.len()
                ),
            ));
            return None;
        }
        for argument in &generics.types {
            env.validate_type(argument, &env.current_type_params, d);
        }
        generics.types.clone()
    };

    let mapping: HashMap<String, Type> = signature
        .type_params
        .iter()
        .map(|parameter| &parameter.name)
        .cloned()
        .zip(type_args.iter().cloned())
        .collect();
    let params = signature
        .params
        .iter()
        .map(|parameter| substitute(&parameter.ty, &mapping))
        .collect();
    let ret = substitute(&signature.ret_ty, &mapping);

    types.function_instantiations.insert(
        source,
        Instance::new(
            name.to_string(),
            generics.lifetimes.clone(),
            type_args.clone(),
        ),
    );
    types.pending_instantiations.push(PendingInstantiation {
        source,
        function_name: name.to_string(),
        caller_name: env.current_function.clone(),
        caller_type_params: env.current_type_params.clone(),
        type_params: signature.type_params,
        type_args,
    });
    Some(fn_ty(params, ret))
}

fn infer_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
    let ty = match &expr.kind {
        ExprKind::Literal(lit) => match lit {
            Literal::Int(_, Some(ty)) => int_ty(*ty),
            Literal::Int(_, None) => subst.fresh_int_var(),
            Literal::Float(_, Some(ty)) => float_ty(*ty),
            Literal::Float(_, None) => subst.fresh_float_var(),
            Literal::Bool(_) => bool_ty(),
            Literal::Unit => unit_ty(),
            Literal::ByteStr(bytes) => array_ty(int_ty(IntTy::U8), array_len(bytes.len())),
        },
        ExprKind::Binary(lhs, op, rhs) => {
            let lhs_ty = infer_inner(env, subst, lhs, types, d);
            let rhs_ty = infer_inner(env, subst, rhs, types, d);
            if let Err(e) = subst.unify(&lhs_ty, &rhs_ty) {
                d.push_error(e.to_diag(expr.source));
            }

            let resolved = subst.resolve(&lhs_ty);
            match &resolved.kind {
                TypeKind::Int(_)
                | TypeKind::Float(_)
                | TypeKind::Var(_)
                | TypeKind::IntVar(_)
                | TypeKind::FloatVar(_)
                | TypeKind::Never
                | TypeKind::Error => {}
                _ => {
                    d.push_error(source_diagnostic(
                        BinaryOpNonNumeric,
                        lhs.source,
                        format!(
                            "binary operations only supported on numeric types, found {}",
                            resolved
                        ),
                    ));
                    return error_ty();
                }
            }

            let is_cmp = matches!(
                op,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
            );
            if is_cmp {
                bool_ty()
            } else {
                lhs_ty.clone()
            }
        }
        ExprKind::Unary(op, operand) => {
            let operand_ty = infer_inner(env, subst, operand, types, d);
            let resolved = subst.resolve(&operand_ty);
            match op {
                UnOp::Neg => match &resolved.kind {
                    TypeKind::Int(int_ty) if int_ty.is_signed() => {}
                    TypeKind::Float(_) => {}
                    TypeKind::IntVar(_)
                    | TypeKind::FloatVar(_)
                    | TypeKind::Var(_)
                    | TypeKind::Never
                    | TypeKind::Error => {}
                    _ => {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::UnaryOpInvalidOperand,
                            operand.source,
                            format!(
                                "unary '-' requires a signed integer or float operand, found {}",
                                resolved
                            ),
                        ));
                        return error_ty();
                    }
                },
            }
            operand_ty
        }
        ExprKind::Variable(name) => {
            if let Some(ty) = env.lookup_var(name) {
                ty
            } else if env.functions.contains_key(name) {
                instantiate_function(
                    env,
                    subst,
                    name,
                    &GenericArgs::empty(),
                    expr.source,
                    types,
                    d,
                )
                .unwrap_or_else(error_ty)
            } else {
                d.push_error(source_diagnostic(
                    UndeclaredVariable,
                    expr.source,
                    format!("undeclared variable '{}'", name),
                ));
                return error_ty();
            }
        }
        ExprKind::FieldAccess(target, field) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            let struct_ty = match &resolved.kind {
                TypeKind::Ref(_, _, inner) => subst.resolve(inner),
                _ => resolved.clone(),
            };
            if let TypeKind::Custom(Instance {
                name: struct_name,
                type_args: args,
                ..
            }) = &struct_ty.kind
            {
                if let Some(s_decl) = env.structs.get(struct_name).cloned() {
                    if let Some(f) = s_decl
                        .fields
                        .iter()
                        .find(|field_decl| field_decl.name == *field)
                    {
                        match build_subst_map(
                            struct_name,
                            &s_decl.type_params,
                            args,
                            expr.source,
                            d,
                        ) {
                            Some(mapping) => substitute(&f.ty, &mapping),
                            None => return error_ty(),
                        }
                    } else {
                        d.push_error(source_diagnostic(
                            NoSuchField,
                            target.source,
                            format!("struct '{}' has no field '{}'", struct_name, field),
                        ));
                        return error_ty();
                    }
                } else {
                    d.push_error(source_diagnostic(
                        UndeclaredStruct,
                        target.source,
                        format!("undeclared struct '{}'", struct_name),
                    ));
                    return error_ty();
                }
            } else {
                d.push_error(source_diagnostic(
                    ExpectedStruct,
                    target.source,
                    format!("expected struct type, found {}", resolved),
                ));
                return error_ty();
            }
        }
        ExprKind::Cast(target, to_ty) => {
            let from_ty = infer_inner(env, subst, target, types, d);
            let from_resolved = subst.resolve(&from_ty);
            if from_resolved.kind == TypeKind::Error {
                return error_ty();
            }
            let scope = env.current_type_params.clone();
            env.validate_type(to_ty, &scope, d);
            if !is_cast_supported(&from_resolved, to_ty) {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::InvalidCast,
                    expr.source,
                    format!("cast from {} to {} is not supported", from_resolved, to_ty),
                ));
                return error_ty();
            }
            if matches!(&to_ty.kind, TypeKind::Ref(_, _, _)) && !env.in_unsafe {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::UnsafeRequired,
                    expr.source,
                    "cast to reference type requires unsafe block".to_string(),
                ));
            }
            to_ty.clone()
        }
        ExprKind::Deref(target) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            match resolved.kind {
                TypeKind::Ref(_, _, inner) => *inner,
                TypeKind::RawPtr(inner) => {
                    if !env.in_unsafe {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::UnsafeRequired,
                            expr.source,
                            "dereference of raw pointer requires unsafe block".to_string(),
                        ));
                    }
                    *inner
                }
                other => {
                    d.push_error(source_diagnostic(
                        ExpectedPointer,
                        target.source,
                        format!("cannot dereference non-pointer type {}", other),
                    ));
                    return error_ty();
                }
            }
        }
        ExprKind::Borrow(kind, target) => {
            let inner_ty = infer_inner(env, subst, target, types, d);
            ref_ty(*kind, inner_ty)
        }
        ExprKind::RawBorrow(target) => {
            let inner_ty = infer_inner(env, subst, target, types, d);
            raw_ptr_ty(inner_ty)
        }
        ExprKind::Call(fn_expr, generics, args) => {
            let direct_name = match &fn_expr.kind {
                ExprKind::Variable(name)
                    if env.lookup_var(name).is_none() && env.functions.contains_key(name) =>
                {
                    Some(name)
                }
                _ => None,
            };
            let fn_ty = if let Some(name) = direct_name {
                if let Some(signature) = env.functions.get(name) {
                    if signature.is_unsafe && !env.in_unsafe {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::UnsafeRequired,
                            fn_expr.source,
                            format!("call to unsafe function '{}' requires unsafe block", name),
                        ));
                    }
                }
                let Some(fn_ty) =
                    instantiate_function(env, subst, name, generics, fn_expr.source, types, d)
                else {
                    return error_ty();
                };
                record_expression_type(env, types, fn_expr.source, fn_ty.clone());
                fn_ty
            } else {
                if !generics.is_empty() {
                    d.push_error(source_diagnostic(
                        GenericArgsOnFunctionValue,
                        fn_expr.source,
                        "explicit generic arguments require a named function",
                    ));
                    return error_ty();
                }
                infer_inner(env, subst, fn_expr, types, d)
            };
            let resolved = subst.resolve(&fn_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            if let TypeKind::Fn(param_tys, ret_ty) = resolved.kind {
                if param_tys.len() != args.len() {
                    d.push_error(source_diagnostic(
                        ArityMismatch,
                        expr.source,
                        format!(
                            "function expected {} arguments, found {}",
                            param_tys.len(),
                            args.len()
                        ),
                    ));
                    return error_ty();
                }
                for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                    check_inner(env, subst, arg, param_ty, types, d);
                }
                *ret_ty
            } else {
                d.push_error(source_diagnostic(
                    ExpectedFunction,
                    expr.source,
                    format!("expected function type, found {}", resolved),
                ));
                return error_ty();
            }
        }
        ExprKind::Block(stmts, last_expr, is_unsafe) => {
            let old_unsafe = env.in_unsafe;
            if *is_unsafe {
                env.in_unsafe = true;
            }
            env.push_scope();
            check_block_statements(env, subst, stmts, types, d);
            let res = if let Some(last) = last_expr {
                infer_inner(env, subst, last, types, d)
            } else {
                unit_ty()
            };
            env.pop_scope();
            env.in_unsafe = old_unsafe;
            res
        }
        ExprKind::If(cond, true_block, false_block) => {
            check_inner(env, subst, cond, &bool_ty(), types, d);
            let t1 = infer_inner(env, subst, true_block, types, d);
            let t2 = infer_inner(env, subst, false_block, types, d);
            if let Err(e) = subst.unify(&t1, &t2) {
                d.push_error(e.to_diag(expr.source));
            }
            subst.resolve(&t1)
        }
        ExprKind::Loop(body) => {
            check_inner(env, subst, body, &unit_ty(), types, d);
            never_ty()
        }
        ExprKind::Break(val_expr) => {
            if let Some(val) = val_expr {
                infer_inner(env, subst, val, types, d);
            }
            never_ty()
        }
        ExprKind::Continue => never_ty(),
        ExprKind::Return(val_expr) => {
            let ret_ty = env.current_ret_ty.clone().unwrap_or_else(unit_ty);
            if let Some(val) = val_expr {
                check_inner(env, subst, val, &ret_ty, types, d);
            } else {
                if let Err(e) = subst.unify(&ret_ty, &unit_ty()) {
                    d.push_error(e.to_diag(expr.source));
                }
            }
            never_ty()
        }
        ExprKind::Assign(lhs, rhs) => {
            let lhs_ty = infer_inner(env, subst, lhs, types, d);
            check_inner(env, subst, rhs, &lhs_ty, types, d);
            unit_ty()
        }
        ExprKind::Match(target, arms) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            if let TypeKind::Custom(Instance {
                name: enum_name,
                type_args: args,
                ..
            }) = resolved.kind
            {
                let e_decl = match env.enums.get(&enum_name).cloned() {
                    Some(decl) => decl,
                    None => {
                        d.push_error(source_diagnostic(
                            UndeclaredEnum,
                            expr.source,
                            format!("undeclared enum '{}'", enum_name),
                        ));
                        return error_ty();
                    }
                };
                let mapping =
                    match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.source, d) {
                        Some(m) => m,
                        None => return error_ty(),
                    };
                let mut arm_tys = Vec::new();
                for (pattern, body) in arms {
                    let Pattern::Variant(variant, bound_var) = pattern;
                    if let Some(v) = e_decl
                        .variants
                        .iter()
                        .find(|var_decl| var_decl.name == *variant)
                    {
                        env.push_scope();
                        if let Some(var_name) = bound_var {
                            env.insert_var(var_name.clone(), substitute(&v.ty, &mapping));
                        }
                        let body_ty = infer_inner(env, subst, body, types, d);
                        env.pop_scope();
                        arm_tys.push(body_ty);
                    } else {
                        d.push_error(source_diagnostic(
                            NoSuchVariant,
                            expr.source,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        ));
                        // Continue checking remaining arms
                        arm_tys.push(error_ty());
                    }
                }
                if arm_tys.is_empty() {
                    d.push_error(source_diagnostic(
                        EmptySwitch,
                        expr.source,
                        "empty switch expression",
                    ));
                    return error_ty();
                }
                let first_ty = arm_tys[0].clone();
                for ty in &arm_tys[1..] {
                    if let Err(e) = subst.unify(&first_ty, ty) {
                        d.push_error(e.to_diag(expr.source));
                    }
                }
                subst.resolve(&first_ty)
            } else {
                d.push_error(source_diagnostic(
                    ExpectedEnum,
                    expr.source,
                    format!("expected enum type for switch target, found {}", resolved),
                ));
                return error_ty();
            }
        }
        ExprKind::StructConstr(name, fields) => {
            let s_decl = match env.structs.get(name).cloned() {
                Some(decl) => decl,
                None => {
                    d.push_error(source_diagnostic(
                        UndeclaredStruct,
                        expr.source,
                        format!("undeclared struct '{}'", name),
                    ));
                    return error_ty();
                }
            };

            if fields.len() != s_decl.fields.len() {
                d.push_error(source_diagnostic(
                    StructFieldCountMismatch,
                    expr.source,
                    format!(
                        "struct '{}' has {} fields, but {} were initialized",
                        name,
                        s_decl.fields.len(),
                        fields.len()
                    ),
                ));
                return error_ty();
            }

            // Fresh type variable per declared type parameter, so
            // field-value inference can pin them from constructor args.
            let type_args: Vec<Type> = s_decl
                .type_params
                .iter()
                .map(|_| subst.fresh_var())
                .collect();
            let mut mapping: HashMap<String, Type> = HashMap::new();
            for (tp, arg) in s_decl.type_params.iter().zip(type_args.iter()) {
                mapping.insert(tp.name.clone(), arg.clone());
            }

            for f_decl in &s_decl.fields {
                let mut matches = fields.iter().filter(|(fname, _)| fname == &f_decl.name);
                let Some((_, val_expr)) = matches.next() else {
                    d.push_error(source_diagnostic(
                        MissingField,
                        expr.source,
                        format!(
                            "missing field '{}' in constructor for '{}'",
                            f_decl.name, name
                        ),
                    ));
                    return error_ty();
                };
                if matches.next().is_some() {
                    d.push_error(source_diagnostic(
                        DuplicateField,
                        expr.source,
                        format!(
                            "duplicate field '{}' in constructor for '{}'",
                            f_decl.name, name
                        ),
                    ));
                    return error_ty();
                }
                let expected = substitute(&f_decl.ty, &mapping);
                check_inner(env, subst, val_expr, &expected, types, d);
            }

            custom_ty_with_args(name.clone(), type_args)
        }
        ExprKind::EnumConstr(enum_name, variant_name, payload) => {
            let e_decl = match env.enums.get(enum_name).cloned() {
                Some(decl) => decl,
                None => {
                    d.push_error(source_diagnostic(
                        UndeclaredEnum,
                        expr.source,
                        format!("undeclared enum '{}'", enum_name),
                    ));
                    return error_ty();
                }
            };

            let variant_decl = match e_decl.variants.iter().find(|v| v.name == *variant_name) {
                Some(v) => v.clone(),
                None => {
                    d.push_error(source_diagnostic(
                        NoSuchVariant,
                        expr.source,
                        format!("enum '{}' has no variant '{}'", enum_name, variant_name),
                    ));
                    return error_ty();
                }
            };

            // Fresh var per declared type parameter — payload inference
            // pins them via the substituted variant type.
            let type_args: Vec<Type> = e_decl
                .type_params
                .iter()
                .map(|_| subst.fresh_var())
                .collect();
            let mut mapping: HashMap<String, Type> = HashMap::new();
            for (tp, arg) in e_decl.type_params.iter().zip(type_args.iter()) {
                mapping.insert(tp.name.clone(), arg.clone());
            }
            let expected_payload = substitute(&variant_decl.ty, &mapping);
            check_inner(env, subst, payload, &expected_payload, types, d);
            custom_ty_with_args(enum_name.clone(), type_args)
        }
        ExprKind::Array(elements) => {
            if elements.is_empty() {
                let elem_ty = subst.fresh_var();
                array_ty(elem_ty, 0)
            } else {
                let first_ty = infer_inner(env, subst, &elements[0], types, d);
                for el in &elements[1..] {
                    check_inner(env, subst, el, &first_ty, types, d);
                }
                array_ty(first_ty, array_len(elements.len()))
            }
        }
        ExprKind::ArrayIndex(arr, idx) => {
            let arr_ty = infer_inner(env, subst, arr, types, d);
            let resolved = subst.resolve(&arr_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            if let TypeKind::Array(inner, _) = resolved.kind {
                let idx_ty = infer_inner(env, subst, idx, types, d);
                let idx_resolved = subst.resolve(&idx_ty);
                match &idx_resolved.kind {
                    TypeKind::Int(_) => {}
                    TypeKind::Var(_) | TypeKind::IntVar(_) => {
                        if let Err(e) =
                            subst.unify(&idx_resolved, &int_ty(crate::mir::ast::IntTy::I64))
                        {
                            d.push_error(e.to_diag(expr.source));
                        }
                    }
                    TypeKind::Error => {}
                    other => {
                        d.push_error(source_diagnostic(
                            ArrayIndexNotInt,
                            idx.source,
                            format!("array index must be an integer, found {}", other),
                        ));
                        return error_ty();
                    }
                }
                *inner
            } else {
                d.push_error(source_diagnostic(
                    ExpectedArray,
                    arr.source,
                    format!("expected array type, found {}", resolved),
                ));
                return error_ty();
            }
        }
    };

    record_expression_type(env, types, expr.source, ty.clone());
    ty
}

fn check_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    expected: &Type,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) {
    let resolved_expected = subst.resolve(expected);
    match (&expr.kind, &resolved_expected.kind) {
        (ExprKind::Block(stmts, last_expr, is_unsafe), _) => {
            let old_unsafe = env.in_unsafe;
            if *is_unsafe {
                env.in_unsafe = true;
            }
            env.push_scope();
            check_block_statements(env, subst, stmts, types, d);
            let errors_before = d.error_count();
            if let Some(last) = last_expr {
                check_inner(env, subst, last, &resolved_expected, types, d);
            } else {
                if let Err(e) = subst.unify(&resolved_expected, &unit_ty()) {
                    d.push_error(e.to_diag(expr.source));
                }
            }
            env.pop_scope();
            env.in_unsafe = old_unsafe;
            if d.error_count() == errors_before {
                record_expression_type(env, types, expr.source, resolved_expected.clone());
            }
        }
        (ExprKind::If(cond, true_block, false_block), _) => {
            check_inner(env, subst, cond, &bool_ty(), types, d);
            check_inner(env, subst, true_block, &resolved_expected, types, d);
            check_inner(env, subst, false_block, &resolved_expected, types, d);
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Match(target, arms), _) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved.kind == TypeKind::Error {
                return;
            }
            if arms.is_empty() {
                d.push_error(source_diagnostic(
                    EmptySwitch,
                    expr.source,
                    "empty switch expression",
                ));
                return;
            }
            if let TypeKind::Custom(Instance {
                name: enum_name,
                type_args: args,
                ..
            }) = resolved.kind
            {
                let e_decl = match env.enums.get(&enum_name).cloned() {
                    Some(decl) => decl,
                    None => {
                        d.push_error(source_diagnostic(
                            UndeclaredEnum,
                            expr.source,
                            format!("undeclared enum '{}'", enum_name),
                        ));
                        return;
                    }
                };
                let mapping =
                    match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.source, d) {
                        Some(m) => m,
                        None => return,
                    };
                for (pattern, body) in arms {
                    let Pattern::Variant(variant, bound_var) = pattern;
                    if let Some(v) = e_decl
                        .variants
                        .iter()
                        .find(|var_decl| var_decl.name == *variant)
                    {
                        env.push_scope();
                        if let Some(var_name) = bound_var {
                            env.insert_var(var_name.clone(), substitute(&v.ty, &mapping));
                        }
                        check_inner(env, subst, body, &resolved_expected, types, d);
                        env.pop_scope();
                    } else {
                        d.push_error(source_diagnostic(
                            NoSuchVariant,
                            expr.source,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        ));
                    }
                }
                record_expression_type(env, types, expr.source, resolved_expected.clone());
            } else {
                d.push_error(source_diagnostic(
                    ExpectedEnum,
                    expr.source,
                    format!("expected enum type for switch target, found {}", resolved),
                ));
            }
        }
        (ExprKind::Literal(Literal::Int(_val, None)), TypeKind::Int(_ty)) => {
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Literal(Literal::Float(_val, None)), TypeKind::Float(_ty)) => {
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
        (ExprKind::Array(elements), TypeKind::Array(expected_elem, expected_size)) => {
            let actual_size = array_len(elements.len());
            if actual_size != *expected_size {
                d.push_error(source_diagnostic(
                    ArrayLengthMismatch,
                    expr.source,
                    format!(
                        "expected array of length {}, found length {}",
                        expected_size,
                        elements.len()
                    ),
                ));
                return;
            }
            for el in elements {
                check_inner(env, subst, el, expected_elem, types, d);
            }
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }

        _ => {
            let inferred = infer_inner(env, subst, expr, types, d);
            if let Err(e) = subst.unify(&inferred, &resolved_expected) {
                d.push_error(e.to_diag(expr.source));
            }
            record_expression_type(env, types, expr.source, resolved_expected.clone());
        }
    }
}

fn check_block_statements(
    env: &mut TypeEnv,
    subst: &mut Subst,
    statements: &[Stmt],
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) {
    for statement in statements {
        match statement {
            Stmt::Let {
                name,
                ty,
                init,
                source,
                ..
            } => {
                if let Some(annotation) = ty {
                    env.validate_type(annotation, &env.current_type_params, d);
                }
                let binding_type = match (ty, init) {
                    (Some(annotation), Some(initializer)) => {
                        check_inner(env, subst, initializer, annotation, types, d);
                        annotation.clone()
                    }
                    (Some(annotation), None) => annotation.clone(),
                    (None, Some(initializer)) => infer_inner(env, subst, initializer, types, d),
                    (None, None) => {
                        d.push_error(source_diagnostic(
                            HllTypeCheckCode::AmbiguousType,
                            *source,
                            "let binding without initializer requires an explicit type annotation",
                        ));
                        error_ty()
                    }
                };
                env.insert_var(name.clone(), binding_type);
            }
            Stmt::Defer { body, .. } => {
                check_no_control_flow(body, 0, d);
                let body_type = infer_inner(env, subst, body, types, d);
                if let Err(error) = subst.unify(&body_type, &unit_ty()) {
                    d.push_error(error.to_diag(body.source));
                }
            }
            Stmt::Expr(expression) => {
                infer_inner(env, subst, expression, types, d);
            }
        }
    }
}

fn check_no_control_flow(expr: &Expr, loop_depth: usize, d: &mut Diagnostics) {
    match &expr.kind {
        ExprKind::Break(_) => {
            if loop_depth == 0 {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.source,
                    "break is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Continue => {
            if loop_depth == 0 {
                d.push_error(source_diagnostic(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.source,
                    "continue is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Return(_) => {
            d.push_error(source_diagnostic(
                HllTypeCheckCode::ControlFlowInDefer,
                expr.source,
                "return is not allowed inside defer".to_string(),
            ));
        }
        ExprKind::Block(stmts, last, _) => {
            for stmt in stmts {
                match stmt {
                    Stmt::Let {
                        init: Some(init), ..
                    } => check_no_control_flow(init, loop_depth, d),
                    Stmt::Let { init: None, .. } => {}
                    Stmt::Defer { body, .. } => check_no_control_flow(body, loop_depth, d),
                    Stmt::Expr(e) => check_no_control_flow(e, loop_depth, d),
                }
            }
            if let Some(e) = last {
                check_no_control_flow(e, loop_depth, d);
            }
        }
        ExprKind::If(cond, thn, els) => {
            check_no_control_flow(cond, loop_depth, d);
            check_no_control_flow(thn, loop_depth, d);
            check_no_control_flow(els, loop_depth, d);
        }
        ExprKind::Loop(body) => {
            check_no_control_flow(body, loop_depth + 1, d);
        }
        ExprKind::Assign(lhs, rhs) => {
            check_no_control_flow(lhs, loop_depth, d);
            check_no_control_flow(rhs, loop_depth, d);
        }
        ExprKind::Binary(lhs, _, rhs) => {
            check_no_control_flow(lhs, loop_depth, d);
            check_no_control_flow(rhs, loop_depth, d);
        }
        ExprKind::Unary(_, operand) => {
            check_no_control_flow(operand, loop_depth, d);
        }
        ExprKind::FieldAccess(base, _) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Cast(base, _) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::ArrayIndex(base, index) => {
            check_no_control_flow(base, loop_depth, d);
            check_no_control_flow(index, loop_depth, d);
        }
        ExprKind::Deref(base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Borrow(_, base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::RawBorrow(base) => {
            check_no_control_flow(base, loop_depth, d);
        }
        ExprKind::Call(callee, _generics, args) => {
            check_no_control_flow(callee, loop_depth, d);
            for arg in args {
                check_no_control_flow(arg, loop_depth, d);
            }
        }
        ExprKind::StructConstr(_, fields) => {
            for (_, f_init) in fields {
                check_no_control_flow(f_init, loop_depth, d);
            }
        }
        ExprKind::EnumConstr(_, _, payload) => {
            check_no_control_flow(payload, loop_depth, d);
        }
        ExprKind::Match(target, arms) => {
            check_no_control_flow(target, loop_depth, d);
            for (_, body_expr) in arms {
                check_no_control_flow(body_expr, loop_depth, d);
            }
        }
        ExprKind::Array(elements) => {
            for el in elements {
                check_no_control_flow(el, loop_depth, d);
            }
        }
        ExprKind::Literal(_) | ExprKind::Variable(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{GeneratedKind, Lifetime, Span};
    use crate::hll::parser::Parser;

    fn test_source(line: u32) -> SourceInfo {
        SourceInfo::written(Span {
            line,
            col: 1,
            end_line: line,
            end_col: 2,
        })
    }

    fn metadata_bearing_type(leaf: Type, outer_source: SourceInfo, ref_source: SourceInfo) -> Type {
        Type::new(
            TypeKind::Custom(Instance::new(
                "Wrap",
                vec![Lifetime("outer".into())],
                vec![Type::new(
                    TypeKind::Ref(
                        RefKind::Shared,
                        Some(Lifetime("inner".into())),
                        Box::new(leaf),
                    ),
                    ref_source,
                )],
            )),
            outer_source,
        )
    }

    fn assert_metadata_preserved(
        ty: &Type,
        outer_source: SourceInfo,
        ref_source: SourceInfo,
        leaf_source: SourceInfo,
    ) {
        assert_eq!(ty.source, outer_source);
        let TypeKind::Custom(Instance {
            name,
            lifetime_args: lifetimes,
            type_args: args,
        }) = &ty.kind
        else {
            panic!("expected custom type");
        };
        assert_eq!(name, "Wrap");
        assert_eq!(lifetimes, &[Lifetime("outer".into())]);
        let [arg] = args.as_slice() else {
            panic!("expected one custom type argument");
        };
        assert_eq!(arg.source, ref_source);
        let TypeKind::Ref(RefKind::Shared, lifetime, pointee) = &arg.kind else {
            panic!("expected shared reference argument");
        };
        assert_eq!(lifetime, &Some(Lifetime("inner".into())));
        assert_eq!(pointee.source, leaf_source);
        assert_eq!(pointee.kind, TypeKind::Int(IntTy::I64));
    }

    #[test]
    fn substitution_preserves_lifetimes_and_sources() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let parameter_source = test_source(3);
        let argument_source = test_source(4);
        let declared = metadata_bearing_type(
            Type::new(TypeKind::Param("T".into()), parameter_source),
            outer_source,
            ref_source,
        );
        let argument = Type::new(TypeKind::Int(IntTy::I64), argument_source);
        let mapping = HashMap::from([("T".to_string(), argument)]);

        let substituted = substitute(&declared, &mapping);
        assert_metadata_preserved(&substituted, outer_source, ref_source, argument_source);
    }

    #[test]
    fn resolution_preserves_lifetimes_and_sources() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let variable_source = test_source(3);
        let resolved_source = test_source(4);
        let unresolved = metadata_bearing_type(
            Type::new(TypeKind::Var(0), variable_source),
            outer_source,
            ref_source,
        );
        let mut subst = Subst::new();
        subst
            .map
            .insert(0, Type::new(TypeKind::Int(IntTy::I64), resolved_source));

        let resolved = subst.resolve(&unresolved);
        assert_metadata_preserved(&resolved, outer_source, ref_source, resolved_source);
    }

    #[test]
    fn default_resolution_defaults_variables_without_dropping_container_metadata() {
        let outer_source = test_source(1);
        let ref_source = test_source(2);
        let variable_source = test_source(3);
        let intermediate_source = test_source(4);
        let defaulted_variable_source = test_source(5);
        let unresolved = metadata_bearing_type(
            Type::new(TypeKind::Var(0), variable_source),
            outer_source,
            ref_source,
        );
        let mut subst = Subst::new();
        subst.map.insert(
            0,
            Type::new(
                TypeKind::Ref(
                    RefKind::Shared,
                    None,
                    Box::new(Type::new(TypeKind::IntVar(1), defaulted_variable_source)),
                ),
                // This replacement intentionally adds another structural layer so
                // `resolve_default` must recurse through a resolved variable.
                intermediate_source,
            ),
        );

        let resolved = subst.resolve_default(&unresolved);
        assert_eq!(resolved.source, outer_source);
        let TypeKind::Custom(Instance {
            lifetime_args: outer_lifetimes,
            type_args: outer_args,
            ..
        }) = &resolved.kind
        else {
            panic!("expected custom type");
        };
        assert_eq!(outer_lifetimes, &[Lifetime("outer".into())]);
        let TypeKind::Ref(_, inner_lifetime, first_pointee) = &outer_args[0].kind else {
            panic!("expected original reference layer");
        };
        assert_eq!(outer_args[0].source, ref_source);
        assert_eq!(inner_lifetime, &Some(Lifetime("inner".into())));
        let TypeKind::Ref(_, None, second_pointee) = &first_pointee.kind else {
            panic!("expected resolved reference layer");
        };
        assert_eq!(first_pointee.source, intermediate_source);
        assert_eq!(second_pointee.kind, TypeKind::Int(IntTy::I64));
    }

    #[test]
    fn unify_mismatch_retains_structured_types_and_sources() {
        let expected_source = test_source(1);
        let found_source = test_source(2);
        let expected = Type::new(TypeKind::Bool, expected_source);
        let found = Type::new(TypeKind::Int(IntTy::I64), found_source);

        let error = Subst::new()
            .unify(&expected, &found)
            .expect_err("bool and i64 must not unify");
        let UnifyError::Mismatch {
            expected: retained_expected,
            found: retained_found,
        } = error
        else {
            panic!("expected a structured mismatch");
        };
        assert_eq!(retained_expected.kind, TypeKind::Bool);
        assert_eq!(retained_expected.source, expected_source);
        assert_eq!(retained_found.kind, TypeKind::Int(IntTy::I64));
        assert_eq!(retained_found.source, found_source);
    }

    #[test]
    fn numeric_unify_mismatch_retains_the_found_type() {
        let variable_source = test_source(1);
        let found_source = test_source(2);
        let integer_variable = Type::new(TypeKind::IntVar(0), variable_source);
        let found = Type::new(TypeKind::Bool, found_source);

        let error = Subst::new()
            .unify(&integer_variable, &found)
            .expect_err("an integer variable must not unify with bool");
        let UnifyError::ExpectedInteger { found: retained } = error else {
            panic!("expected an integer-category mismatch");
        };
        assert_eq!(retained.kind, TypeKind::Bool);
        assert_eq!(retained.source, found_source);
    }

    #[test]
    fn implicit_else_type_mismatch_preserves_generated_source() {
        let program = Parser::parse_or_panic("fn f() -> i64 { if true { 1 } }");

        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].code(),
            DiagCode::HllTypeCheck(HllTypeCheckCode::TypeMismatch)
        );
        assert_eq!(
            errors[0].source().generated_kind(),
            Some(GeneratedKind::HllDesugaring)
        );
    }

    #[test]
    fn ambiguous_generated_expression_preserves_its_source() {
        let mut program = Parser::parse_or_panic("fn f() { let x = []; }");
        let [Declaration::Fn(function)] = program.declarations.as_mut_slice() else {
            panic!("expected one function declaration");
        };
        let Some(body) = &mut function.body else {
            panic!("expected a function body");
        };
        let ExprKind::Block(statements, _, _) = &mut body.kind else {
            panic!("expected a block body");
        };
        let [Stmt::Let {
            init: Some(initializer),
            ..
        }] = statements.as_mut_slice()
        else {
            panic!("expected one initialized let statement");
        };
        let generated_source =
            SourceInfo::generated(GeneratedKind::HllDesugaring, initializer.source.span());
        initializer.source = generated_source;

        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].code(),
            DiagCode::HllTypeCheck(HllTypeCheckCode::AmbiguousType)
        );
        assert_eq!(errors[0].source(), generated_source);
    }

    fn check_program(source: &str) -> Result<(), String> {
        let mut parse_d = Diagnostics::default();
        let program = Parser::new(source)
            .parse(&mut parse_d)
            .ok_or_else(|| parse_d.errors_str().join("\n"))?;
        // Render Diagnostic errors as strings for the existing
        // `.contains(...)` substring assertions.
        let d = typecheck_program(&program);
        if d.has_errors() {
            Err(d.errors_str().join("\n"))
        } else {
            Ok(())
        }
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
    fn invalid_nested_declared_type_uses_its_own_source() {
        let source = "fn f(x: &Nope) {}";
        let program = Parser::parse_or_panic(source);
        let diagnostics = typecheck_program(&program);
        let errors: Vec<_> = diagnostics.errors().collect();
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].span(),
            Span {
                line: 1,
                col: 10,
                end_line: 1,
                end_col: 14,
            }
        );
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

    #[test]
    fn test_defer_with_nested_loop_ok() {
        let source = "
            fn check() {
                defer {
                    loop {
                        break;
                    };
                };
            }
        ";
        assert!(check_program(source).is_ok());
    }
}
