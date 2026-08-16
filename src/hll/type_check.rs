use crate::common::{IntTy, Lifetime, LifetimeParam, Marker, Markers, RefKind, SourceInfo};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::hll::ast::*;
use crate::hll::helpers::*;
use crate::hll::type_fold::TypeFolder;
use indexmap::IndexMap;
use std::collections::{BTreeMap, HashMap, HashSet};

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
/// against bounds — both need the complete bounds for each name.
fn type_params_scope(params: &[TypeParam]) -> HashMap<String, Bounds> {
    params
        .iter()
        .map(|p| (p.name.clone(), p.bounds.clone()))
        .collect()
}

/// Substitute type-parameter references in `ty` using `mapping`. Used
/// when reading a declared field/variant/param type on a generic decl:
/// e.g. `Box::inner` has declared type `T`, but on `Box<i64>` the
/// caller sees `i64`. `mapping` binds each declared type-parameter
/// name to the concrete argument at the use site.
fn substitute(ty: &Type, mapping: &HashMap<String, Type>) -> Type {
    let lifetime_mapping = BTreeMap::new();
    SubstituteFolder {
        type_mapping: mapping,
        lifetime_mapping: &lifetime_mapping,
    }
    .fold_type(ty)
}

fn substitute_all(
    ty: &Type,
    type_mapping: &HashMap<String, Type>,
    lifetime_mapping: &BTreeMap<Lifetime, Lifetime>,
) -> Type {
    SubstituteFolder {
        type_mapping,
        lifetime_mapping,
    }
    .fold_type(ty)
}

struct SubstituteFolder<'a> {
    type_mapping: &'a HashMap<String, Type>,
    lifetime_mapping: &'a BTreeMap<Lifetime, Lifetime>,
}

impl TypeFolder for SubstituteFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        match &ty.kind {
            TypeKind::Param(name) => self.type_mapping.get(name).cloned(),
            // Only named type parameters are substitution sites. Every other
            // variant uses the shared structural recursion.
            _ => None,
        }
    }

    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        self.lifetime_mapping
            .get(lifetime)
            .cloned()
            .unwrap_or_else(|| lifetime.clone())
    }
}

fn substitute_bound(
    bound: &TraitBound,
    type_mapping: &HashMap<String, Type>,
    lifetime_mapping: &BTreeMap<Lifetime, Lifetime>,
) -> Instance {
    Instance::new(
        bound.trait_path.name.clone(),
        bound
            .trait_path
            .lifetime_args
            .iter()
            .map(|lifetime| {
                lifetime_mapping
                    .get(lifetime)
                    .cloned()
                    .unwrap_or_else(|| lifetime.clone())
            })
            .collect(),
        bound
            .trait_path
            .type_args
            .iter()
            .map(|argument| substitute_all(argument, type_mapping, lifetime_mapping))
            .collect(),
    )
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

/// Zip a decl's lifetime parameters with the concrete lifetimes at a use
/// site. Returns `None` when the arities disagree so callers can bail out
/// on a type that [`TypeEnv::validate_type`] has already flagged, rather
/// than substituting a truncated mapping.
fn build_lifetime_mapping(
    lifetime_params: &[LifetimeParam],
    lifetime_args: &[Lifetime],
) -> Option<BTreeMap<Lifetime, Lifetime>> {
    if lifetime_params.len() != lifetime_args.len() {
        return None;
    }
    Some(
        lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(lifetime_args.iter().cloned())
            .collect(),
    )
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
    /// A type-parameter bound references a trait that isn't declared.
    UndeclaredTrait,
    /// A trait bound supplies the wrong number of generic arguments.
    TraitArgArityMismatch,
    /// Trait self-bounds form a cycle.
    TraitBoundCycle,
    /// Generic type instantiation has the wrong number of type arguments
    /// (e.g. `Box<i64, i64>` on a 1-parameter decl, or a bare `Box` on a
    /// generic decl).
    TypeArgArityMismatch,
    /// A type argument at a generic instantiation site doesn't satisfy
    /// the declared marker bound on the corresponding type parameter
    /// (e.g. `Box<Linear>` where the decl is `struct<T: Copy> Box`).
    BoundNotSatisfied,
    /// A function call or a nominal type mention supplies the wrong
    /// number of explicit lifetime arguments.
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
    /// An impl method's safety does not match its trait declaration.
    ImplMethodSafetyMismatch,
    /// `extern "..."` names an ABI other than `"C"`.
    UnknownAbi,
    /// `expr as Type` where the pair isn't a supported cast.
    /// Today's supported cells: numeric widths & signedness, int↔float,
    /// bool→int. Casts *to* bool aren't supported (use `!= 0`); casts
    /// to/from pointer/ref types are not yet supported.
    InvalidCast,
    /// More than one callable in the highest-priority applicable receiver-call
    /// tier has the requested name.
    AmbiguousReceiverCall,
    /// Receiver syntax found no applicable method, callable field, or free
    /// function.
    UnresolvedReceiverCall,
    /// An explicitly qualified inherent or trait method does not exist for the
    /// selected type and qualification.
    UnresolvedQualifiedMethod,
}

impl From<HllTypeCheckCode> for DiagCode {
    fn from(code: HllTypeCheckCode) -> DiagCode {
        DiagCode::HllTypeCheck(code)
    }
}

pub struct Subst {
    map: HashMap<usize, Type>,
    next_id: usize,
    lifetime_map: BTreeMap<Lifetime, Lifetime>,
    lifetime_variables: HashSet<Lifetime>,
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

    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        self.subst.resolve_lifetime(lifetime)
    }
}

impl Subst {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            next_id: 0,
            lifetime_map: BTreeMap::new(),
            lifetime_variables: HashSet::new(),
        }
    }

    fn register_lifetime_variable(&mut self, lifetime: Lifetime) {
        self.lifetime_variables.insert(lifetime);
    }

    fn resolve_lifetime(&self, lifetime: &Lifetime) -> Lifetime {
        let mut resolved = lifetime.clone();
        while let Some(next) = self.lifetime_map.get(&resolved) {
            if next == &resolved {
                break;
            }
            resolved = next.clone();
        }
        resolved
    }

    fn unify_lifetimes(&mut self, left: &Lifetime, right: &Lifetime) {
        let left = self.resolve_lifetime(left);
        let right = self.resolve_lifetime(right);
        if left == right {
            return;
        }
        if self.lifetime_variables.contains(&left) {
            self.lifetime_map.insert(left, right);
        } else if self.lifetime_variables.contains(&right) {
            self.lifetime_map.insert(right, left);
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
                    lifetime_args: l1,
                    type_args: a1,
                }),
                TypeKind::Custom(Instance {
                    name: n2,
                    lifetime_args: l2,
                    type_args: a2,
                }),
            ) if n1 == n2 && l1.len() == l2.len() && a1.len() == a2.len() => {
                let l1 = l1.clone();
                let l2 = l2.clone();
                let a1 = a1.clone();
                let a2 = a2.clone();
                for (left, right) in l1.iter().zip(l2.iter()) {
                    self.unify_lifetimes(left, right);
                }
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (TypeKind::Param(p1), TypeKind::Param(p2)) if p1 == p2 => Ok(()),
            (TypeKind::Ref(k1, l1, inner1), TypeKind::Ref(k2, l2, inner2)) if k1 == k2 => {
                if let (Some(left), Some(right)) = (l1, l2) {
                    self.unify_lifetimes(left, right);
                }
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

    fn can_unify(&self, t1: &Type, t2: &Type) -> bool {
        let mut probe = Self {
            map: self.map.clone(),
            next_id: self.next_id,
            lifetime_map: self.lifetime_map.clone(),
            lifetime_variables: self.lifetime_variables.clone(),
        };
        probe.unify(t1, t2).is_ok()
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
    traits: HashMap<String, TraitDecl>,
    functions: HashMap<String, FnDecl>,
    impls: Vec<ImplBlock>,
    current_ret_ty: Option<Type>,
    /// Type-parameter names → declared bounds for the fn being checked.
    /// Empty outside a fn body.
    current_type_params: HashMap<String, Bounds>,
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
            traits: HashMap::new(),
            functions: HashMap::new(),
            impls: Vec::new(),
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
    fn class_of(&self, ty: &Type, scope: &HashMap<String, Bounds>) -> Markers {
        let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never => all(),
            TypeKind::Fn(_, _) | TypeKind::RawPtr(_) => all(),
            TypeKind::Ref(kind, _, _) => kind.value_markers(),
            TypeKind::Custom(Instance { name, .. }) => {
                if let Some(s) = self.structs.get(name) {
                    s.markers
                } else if let Some(e) = self.enums.get(name) {
                    e.markers
                } else {
                    Markers::empty()
                }
            }
            TypeKind::Param(name) => scope
                .get(name)
                .map(|bounds| self.markers_from_bounds(bounds, &mut HashSet::new()))
                .unwrap_or_else(Markers::empty),
            TypeKind::Array(elem, _) => self.class_of(elem, scope),
            TypeKind::Var(_) | TypeKind::IntVar(_) | TypeKind::FloatVar(_) | TypeKind::Error => {
                all()
            }
        }
    }

    fn markers_from_bounds(&self, bounds: &Bounds, visiting: &mut HashSet<String>) -> Markers {
        let mut markers = bounds.markers.iter_declared().collect::<Vec<_>>();
        for bound in &bounds.traits {
            let name = &bound.trait_path.name;
            if !visiting.insert(name.clone()) {
                continue;
            }
            if let Some(trait_decl) = self.traits.get(name) {
                markers.extend(
                    self.markers_from_bounds(&trait_decl.self_bounds, visiting)
                        .iter_declared(),
                );
            }
            visiting.remove(name);
        }
        Markers::from_iter(markers)
    }

    /// Walk `ty` and push a diagnostic per problem: an undeclared
    /// `Custom` name, a `Param` not in scope, wrong type-arg arity,
    /// or an arg that fails the declared bound. Each is reported at
    /// the source of the precise type node that is invalid. Continues past
    /// errors so a single top-level `Type` with multiple defects surfaces
    /// them all.
    pub fn validate_type(&self, ty: &Type, scope: &HashMap<String, Bounds>, d: &mut Diagnostics) {
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
                lifetime_args,
                type_args: args,
            }) => {
                for a in args {
                    self.validate_type(a, scope, d);
                }
                let (lifetime_params, type_params): (&[LifetimeParam], &[TypeParam]) =
                    if let Some(s) = self.structs.get(name) {
                        (&s.lifetime_params, &s.type_params)
                    } else if let Some(e) = self.enums.get(name) {
                        (&e.lifetime_params, &e.type_params)
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
                if lifetime_args.len() != lifetime_params.len() {
                    d.push_error(Diagnostic::new(
                        LifetimeArgArityMismatch,
                        ty.source,
                        format!(
                            "'{}' takes {} lifetime argument(s), found {}",
                            name,
                            lifetime_params.len(),
                            lifetime_args.len()
                        ),
                    ));
                    return;
                }
                let mapping = type_params
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .zip(args.iter().cloned())
                    .collect::<HashMap<_, _>>();
                let lifetime_mapping = lifetime_params
                    .iter()
                    .map(|parameter| parameter.lifetime.clone())
                    .zip(lifetime_args.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
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
                    for bound in &tp.bounds.traits {
                        let bound = substitute_bound(bound, &mapping, &lifetime_mapping);
                        if !type_satisfies_trait(self, arg, &bound, scope) {
                            d.push_error(Diagnostic::new(
                                BoundNotSatisfied,
                                arg.source,
                                format!(
                                    "type argument '{}' for '{}::{}' does not satisfy trait bound '{}'",
                                    arg, name, tp.name, bound
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReceiverAdjustment {
    None,
    Borrow(RefKind),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedMethodTarget {
    Inherent {
        self_ty: Type,
        method: Instance,
    },
    Trait {
        trait_path: Instance,
        self_ty: Type,
        method: Instance,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedReceiverTarget {
    Method(ResolvedMethodTarget),
    Field,
    FreeFunction(Instance),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedReceiverCall {
    pub target: ResolvedReceiverTarget,
    pub adjustment: ReceiverAdjustment,
}

struct PendingInstantiation {
    source: SourceInfo,
    function_name: String,
    caller_name: Option<String>,
    caller_type_params: HashMap<String, Bounds>,
    type_params: Vec<TypeParam>,
    type_args: Vec<Type>,
    type_mapping: HashMap<String, Type>,
    lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
}

#[derive(Default)]
pub struct TypeCheckResults {
    pub expression_types: ExpressionTypes,
    pub function_instantiations: IndexMap<SourceInfo, Instance>,
    pub receiver_calls: IndexMap<SourceInfo, ResolvedReceiverCall>,
    pub qualified_calls: IndexMap<SourceInfo, ResolvedMethodTarget>,
    expression_contexts: IndexMap<SourceInfo, String>,
    pending_instantiations: Vec<PendingInstantiation>,
    synthesized_lifetime_params: IndexMap<String, Vec<LifetimeParam>>,
    reserved_lifetime_names: HashSet<String>,
    next_inferred_lifetime: usize,
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

impl TypeCheckResults {
    fn fresh_inferred_lifetime(
        &mut self,
        env: &TypeEnv,
        subst: &mut Subst,
        source: SourceInfo,
    ) -> Option<Lifetime> {
        let context = env.current_function.as_ref()?;
        let params = self
            .synthesized_lifetime_params
            .entry(context.clone())
            .or_default();
        loop {
            let name = format!("s{}", self.next_inferred_lifetime);
            self.next_inferred_lifetime += 1;
            if self.reserved_lifetime_names.insert(name.clone()) {
                let lifetime = Lifetime(name);
                params.push(LifetimeParam::generated(
                    lifetime.clone(),
                    crate::common::GeneratedKind::LifetimeElision,
                    source.span(),
                ));
                subst.register_lifetime_variable(lifetime.clone());
                return Some(lifetime);
            }
        }
    }

    pub(crate) fn synthesized_lifetimes(&self, context: &str) -> &[LifetimeParam] {
        self.synthesized_lifetime_params
            .get(context)
            .map(Vec::as_slice)
            .unwrap_or_default()
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
    let mut reserved_lifetime_names = HashSet::new();
    for declaration in &program.declarations {
        match declaration {
            Declaration::Struct(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Enum(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Fn(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Trait(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .chain(
                            declaration
                                .methods
                                .iter()
                                .flat_map(|method| method.lifetime_params.iter()),
                        )
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
            Declaration::Impl(declaration) => {
                reserved_lifetime_names.extend(
                    declaration
                        .lifetime_params
                        .iter()
                        .chain(
                            declaration
                                .methods
                                .iter()
                                .flat_map(|method| method.lifetime_params.iter()),
                        )
                        .map(|parameter| parameter.lifetime.0.clone()),
                );
            }
        }
    }
    let mut types = TypeCheckResults {
        reserved_lifetime_names,
        ..TypeCheckResults::default()
    };

    // Preload prelude wrappers (`size_of<T>`, `ptr_offset<T>`) so user
    // code can spell them by name. Bodies live at the MIR level; here
    // we only need the surface signatures.
    for f in crate::hll::prelude::prelude_fn_decls() {
        env.functions.insert(f.name.clone(), f);
    }
    for trait_decl in crate::hll::prelude::prelude_trait_decls() {
        env.traits.insert(trait_decl.name.clone(), trait_decl);
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
            Declaration::Trait(t) => {
                env.traits.insert(t.name.clone(), t.clone());
            }
            Declaration::Impl(i) => {
                env.impls.push(i.clone());
            }
        }
    }

    validate_trait_bound_cycles(program, &env, d);
    validate_impl_method_safety(&env, d);

    // Validate every decl-level type: fields, variant payloads, fn
    // params, fn returns. Every referenced `Custom` must be declared
    // with matching arity, every arg must satisfy the declared bound,
    // and every `Param` must be in scope for its enclosing decl.
    for decl in &program.declarations {
        match decl {
            Declaration::Struct(s) => {
                let scope = type_params_scope(&s.type_params);
                validate_type_param_bounds(&env, &s.type_params, &scope, d);
                for f in &s.fields {
                    env.validate_type(&f.ty, &scope, d);
                }
            }
            Declaration::Enum(e) => {
                let scope = type_params_scope(&e.type_params);
                validate_type_param_bounds(&env, &e.type_params, &scope, d);
                for v in &e.variants {
                    env.validate_type(&v.ty, &scope, d);
                }
            }
            Declaration::Fn(f) => {
                let scope = type_params_scope(&f.type_params);
                validate_type_param_bounds(&env, &f.type_params, &scope, d);
                let errors_before = d.error_count();
                for p in &f.params {
                    env.validate_type(&p.ty, &scope, d);
                }
                env.validate_type(&f.ret_ty, &scope, d);
                d.annotate_errors_in_function(errors_before, &f.name);
            }
            Declaration::Trait(t) => {
                let mut trait_scope = type_params_scope(&t.type_params);
                trait_scope.insert("Self".to_string(), t.self_bounds.clone());
                validate_type_param_bounds(&env, &t.type_params, &trait_scope, d);
                validate_bounds(
                    &env,
                    &format!("trait '{}'", t.name),
                    &t.self_bounds,
                    &trait_scope,
                    d,
                );
                for method in &t.methods {
                    let mut params = t.type_params.clone();
                    params.push(TypeParam {
                        name: "Self".to_string(),
                        bounds: t.self_bounds.clone(),
                        source: t.source,
                    });
                    params.extend(method.type_params.clone());
                    let scope = type_params_scope(&params);
                    validate_type_param_bounds(&env, &method.type_params, &scope, d);
                    let context = trait_method_context(&t.name, &method.name);
                    validate_fn_signature(&env, method, &params, &context, d);
                }
            }
            Declaration::Impl(i) => {
                let impl_scope = type_params_scope(&i.type_params);
                validate_type_param_bounds(&env, &i.type_params, &impl_scope, d);
                env.validate_type(&i.target, &impl_scope, d);
                if let Some(trait_path) = &i.trait_path {
                    for arg in &trait_path.type_args {
                        env.validate_type(arg, &impl_scope, d);
                    }
                    if let Some(trait_decl) = env.traits.get(&trait_path.name) {
                        for marker in trait_decl.self_bounds.markers.iter_declared() {
                            if !env.class_of(&i.target, &impl_scope).implies(marker) {
                                d.push_error(source_diagnostic(
                                    BoundNotSatisfied,
                                    i.source,
                                    format!(
                                        "impl of '{}' for {} requires Self: {}",
                                        trait_path,
                                        i.target,
                                        marker.name()
                                    ),
                                ));
                            }
                        }
                        for bound in &trait_decl.self_bounds.traits {
                            let required = instantiate_trait_self_bound(
                                trait_decl, trait_path, &i.target, bound,
                            );
                            if !type_satisfies_trait(&env, &i.target, &required, &impl_scope) {
                                d.push_error(source_diagnostic(
                                    BoundNotSatisfied,
                                    i.source,
                                    format!(
                                        "impl of '{}' for {} requires Self: {}",
                                        trait_path, i.target, required
                                    ),
                                ));
                            }
                        }
                    }
                }
                for method in &i.methods {
                    let mut params = i.type_params.clone();
                    params.extend(method.type_params.clone());
                    let scope = type_params_scope(&params);
                    validate_type_param_bounds(&env, &method.type_params, &scope, d);
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
    let resolve_instance = |instantiation: &mut Instance| {
        for lifetime in &mut instantiation.lifetime_args {
            *lifetime = subst.resolve_lifetime(lifetime);
        }
        for ty in &mut instantiation.type_args {
            *ty = subst.resolve_default(ty);
        }
    };
    for instantiation in types.function_instantiations.values_mut() {
        resolve_instance(instantiation);
    }
    let resolve_method_target = |target: &mut ResolvedMethodTarget| match target {
        ResolvedMethodTarget::Inherent { self_ty, method } => {
            *self_ty = subst.resolve_default(self_ty);
            resolve_instance(method);
        }
        ResolvedMethodTarget::Trait {
            trait_path,
            self_ty,
            method,
        } => {
            *self_ty = subst.resolve_default(self_ty);
            resolve_instance(trait_path);
            resolve_instance(method);
        }
    };
    for call in types.receiver_calls.values_mut() {
        match &mut call.target {
            ResolvedReceiverTarget::Method(target) => resolve_method_target(target),
            ResolvedReceiverTarget::FreeFunction(instance) => resolve_instance(instance),
            ResolvedReceiverTarget::Field => {}
        }
    }
    for target in types.qualified_calls.values_mut() {
        resolve_method_target(target);
    }
    for params in types.synthesized_lifetime_params.values_mut() {
        params.retain(|param| subst.resolve_lifetime(&param.lifetime) == param.lifetime);
    }
    types.pending_instantiations.clear();
    types
}

fn validate_trait_bound_cycles(program: &Program, env: &TypeEnv, d: &mut Diagnostics) {
    fn visit(
        env: &TypeEnv,
        name: &str,
        stack: &mut Vec<String>,
        complete: &mut HashSet<String>,
        d: &mut Diagnostics,
    ) {
        if complete.contains(name) {
            return;
        }
        let Some(trait_decl) = env.traits.get(name) else {
            return;
        };
        stack.push(name.to_string());
        for bound in &trait_decl.self_bounds.traits {
            if let Some(start) = stack
                .iter()
                .position(|ancestor| ancestor == &bound.trait_path.name)
            {
                let mut cycle = stack[start..].to_vec();
                cycle.push(bound.trait_path.name.clone());
                d.push_error(source_diagnostic(
                    TraitBoundCycle,
                    bound.source,
                    format!("trait-bound cycle: {}", cycle.join(" -> ")),
                ));
                continue;
            }
            visit(env, &bound.trait_path.name, stack, complete, d);
        }
        stack.pop();
        complete.insert(name.to_string());
    }

    let mut complete = HashSet::new();
    for declaration in &program.declarations {
        let Declaration::Trait(trait_decl) = declaration else {
            continue;
        };
        visit(env, &trait_decl.name, &mut Vec::new(), &mut complete, d);
    }
}

fn validate_impl_method_safety(env: &TypeEnv, d: &mut Diagnostics) {
    for (impl_block, trait_path) in env.impls.iter().filter_map(|impl_block| {
        impl_block
            .trait_path
            .as_ref()
            .map(|path| (impl_block, path))
    }) {
        let Some(trait_decl) = env.traits.get(&trait_path.name) else {
            // The MIR declaration checker diagnoses an undeclared trait; there
            // is no trait safety contract to compare here.
            continue;
        };
        for method in &impl_block.methods {
            let Some(trait_method) = trait_decl
                .methods
                .iter()
                .find(|trait_method| trait_method.name == method.name)
            else {
                // The MIR declaration checker diagnoses extra impl methods;
                // only declared trait methods carry a safety contract.
                continue;
            };
            if method.is_unsafe != trait_method.is_unsafe {
                let expected = if trait_method.is_unsafe {
                    "unsafe"
                } else {
                    "safe"
                };
                let found = if method.is_unsafe { "unsafe" } else { "safe" };
                d.push_error(
                    source_diagnostic(
                        HllTypeCheckCode::ImplMethodSafetyMismatch,
                        method.source,
                        format!(
                            "impl method '{}' is {}, but trait declaration is {}",
                            method.name, found, expected
                        ),
                    )
                    .in_function(impl_method_context(
                        &impl_block.target,
                        Some(trait_path),
                        &method.name,
                    )),
                );
            }
        }
    }
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

fn validate_type_param_bounds(
    env: &TypeEnv,
    params: &[TypeParam],
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for parameter in params {
        validate_bounds(
            env,
            &format!("type parameter '{}'", parameter.name),
            &parameter.bounds,
            scope,
            d,
        );
    }
}

fn validate_bounds(
    env: &TypeEnv,
    owner: &str,
    bounds: &Bounds,
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for bound in &bounds.traits {
        validate_trait_instance(
            env,
            owner,
            "trait bound",
            &bound.trait_path,
            bound.source,
            scope,
            d,
        );
    }
}

fn validate_trait_instance(
    env: &TypeEnv,
    owner: &str,
    reference_kind: &str,
    trait_path: &Instance,
    source: SourceInfo,
    scope: &HashMap<String, Bounds>,
    d: &mut Diagnostics,
) {
    for argument in &trait_path.type_args {
        env.validate_type(argument, scope, d);
    }
    let Some(trait_decl) = env.traits.get(&trait_path.name) else {
        d.push_error(source_diagnostic(
            UndeclaredTrait,
            source,
            format!(
                "{} has undeclared {} '{}'",
                owner, reference_kind, trait_path.name
            ),
        ));
        return;
    };
    if trait_path.lifetime_args.len() != trait_decl.lifetime_params.len()
        || trait_path.type_args.len() != trait_decl.type_params.len()
    {
        d.push_error(source_diagnostic(
            TraitArgArityMismatch,
            source,
            format!(
                "{} '{}' expects {} lifetime and {} type argument(s), found {} lifetime and {} type argument(s)",
                reference_kind,
                trait_path.name,
                trait_decl.lifetime_params.len(),
                trait_decl.type_params.len(),
                trait_path.lifetime_args.len(),
                trait_path.type_args.len()
            ),
        ));
        return;
    }
    let mapping = trait_decl
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(trait_path.type_args.iter().cloned())
        .collect::<HashMap<_, _>>();
    let lifetime_mapping = trait_decl
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(trait_path.lifetime_args.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    for (trait_parameter, argument) in trait_decl.type_params.iter().zip(&trait_path.type_args) {
        let markers_satisfied = trait_parameter
            .bounds
            .markers
            .iter_declared()
            .all(|marker| env.class_of(argument, scope).implies(marker));
        let traits_satisfied = trait_parameter.bounds.traits.iter().all(|required| {
            let required = substitute_bound(required, &mapping, &lifetime_mapping);
            type_satisfies_trait(env, argument, &required, scope)
        });
        if !markers_satisfied || !traits_satisfied {
            d.push_error(source_diagnostic(
                BoundNotSatisfied,
                source,
                format!(
                    "type argument '{}' for {} '{}::{}' does not satisfy its declared bounds",
                    argument, reference_kind, trait_path.name, trait_parameter.name
                ),
            ));
        }
    }
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
        let mapping = pending
            .type_mapping
            .iter()
            .map(|(name, argument)| (name.clone(), subst.resolve(argument)))
            .collect::<HashMap<_, _>>();
        let lifetime_mapping = pending
            .lifetime_mapping
            .iter()
            .map(|(parameter, argument)| (parameter.clone(), subst.resolve_lifetime(argument)))
            .collect::<BTreeMap<_, _>>();
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
            for bound in &parameter.bounds.traits {
                let bound = substitute_bound(bound, &mapping, &lifetime_mapping);
                if !type_satisfies_trait(env, &argument, &bound, &pending.caller_type_params) {
                    d.push_error(source_diagnostic(
                        BoundNotSatisfied,
                        pending.source,
                        format!(
                            "type argument '{}' for '{}::{}' does not satisfy trait bound '{}'",
                            argument, pending.function_name, parameter.name, bound
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
) -> Option<(Type, Instance)> {
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
    let lifetime_args = if generics.lifetimes.is_empty() {
        signature
            .lifetime_params
            .iter()
            .map(|_| types.fresh_inferred_lifetime(env, subst, source))
            .collect::<Option<Vec<_>>>()?
    } else {
        generics.lifetimes.clone()
    };
    let lifetime_mapping = signature
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(lifetime_args.iter().cloned())
        .collect();
    let params = signature
        .params
        .iter()
        .map(|parameter| substitute_all(&parameter.ty, &mapping, &lifetime_mapping))
        .collect();
    let ret = substitute_all(&signature.ret_ty, &mapping, &lifetime_mapping);

    let instance = Instance::new(name.to_string(), lifetime_args, type_args.clone());
    types.pending_instantiations.push(PendingInstantiation {
        source,
        function_name: name.to_string(),
        caller_name: env.current_function.clone(),
        caller_type_params: env.current_type_params.clone(),
        type_params: signature.type_params,
        type_args,
        type_mapping: mapping,
        lifetime_mapping,
    });
    Some((fn_ty(params, ret), instance))
}

#[derive(Clone, Default)]
struct ImplBindings {
    lifetimes: BTreeMap<Lifetime, Lifetime>,
    types: BTreeMap<String, Type>,
}

fn match_impl_lifetime(
    pattern: &Option<Lifetime>,
    actual: &Option<Lifetime>,
    parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    match (pattern, actual) {
        (Some(pattern), Some(actual)) if parameters.contains(pattern) => {
            match bindings.lifetimes.get(pattern) {
                Some(bound) => bound == actual,
                None => {
                    bindings.lifetimes.insert(pattern.clone(), actual.clone());
                    true
                }
            }
        }
        (Some(pattern), Some(actual)) => pattern == actual,
        (None, _) => true,
        _ => false,
    }
}

fn match_impl_instance(
    pattern: &Instance,
    actual: &Instance,
    type_parameters: &HashSet<String>,
    lifetime_parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    pattern.name == actual.name
        && pattern.lifetime_args.len() == actual.lifetime_args.len()
        && pattern.type_args.len() == actual.type_args.len()
        && pattern
            .lifetime_args
            .iter()
            .zip(&actual.lifetime_args)
            .all(|(pattern, actual)| {
                match_impl_lifetime(
                    &Some(pattern.clone()),
                    &Some(actual.clone()),
                    lifetime_parameters,
                    bindings,
                )
            })
        && pattern
            .type_args
            .iter()
            .zip(&actual.type_args)
            .all(|(pattern, actual)| {
                match_impl_type(
                    pattern,
                    actual,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
            })
}

fn match_impl_type(
    pattern: &Type,
    actual: &Type,
    type_parameters: &HashSet<String>,
    lifetime_parameters: &HashSet<Lifetime>,
    bindings: &mut ImplBindings,
) -> bool {
    if let TypeKind::Param(name) = &pattern.kind {
        if type_parameters.contains(name) {
            return match bindings.types.get(name) {
                Some(bound) => bound == actual,
                None => {
                    bindings.types.insert(name.clone(), actual.clone());
                    true
                }
            };
        }
    }

    match (&pattern.kind, &actual.kind) {
        (_, TypeKind::Var(_)) => true,
        (TypeKind::Int(_), TypeKind::IntVar(_)) => true,
        (TypeKind::Float(_), TypeKind::FloatVar(_)) => true,
        (TypeKind::Int(pattern), TypeKind::Int(actual)) => pattern == actual,
        (TypeKind::Float(pattern), TypeKind::Float(actual)) => pattern == actual,
        (TypeKind::Bool, TypeKind::Bool)
        | (TypeKind::Unit, TypeKind::Unit)
        | (TypeKind::Never, TypeKind::Never) => true,
        (TypeKind::Param(pattern), TypeKind::Param(actual)) => pattern == actual,
        (TypeKind::Custom(pattern), TypeKind::Custom(actual)) => match_impl_instance(
            pattern,
            actual,
            type_parameters,
            lifetime_parameters,
            bindings,
        ),
        (TypeKind::Fn(pattern_params, pattern_ret), TypeKind::Fn(actual_params, actual_ret)) => {
            pattern_params.len() == actual_params.len()
                && pattern_params
                    .iter()
                    .zip(actual_params)
                    .all(|(pattern, actual)| {
                        match_impl_type(
                            pattern,
                            actual,
                            type_parameters,
                            lifetime_parameters,
                            bindings,
                        )
                    })
                && match_impl_type(
                    pattern_ret,
                    actual_ret,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        (
            TypeKind::Ref(pattern_kind, pattern_lifetime, pattern_inner),
            TypeKind::Ref(actual_kind, actual_lifetime, actual_inner),
        ) => {
            pattern_kind == actual_kind
                && match_impl_lifetime(
                    pattern_lifetime,
                    actual_lifetime,
                    lifetime_parameters,
                    bindings,
                )
                && match_impl_type(
                    pattern_inner,
                    actual_inner,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        (TypeKind::RawPtr(pattern), TypeKind::RawPtr(actual)) => match_impl_type(
            pattern,
            actual,
            type_parameters,
            lifetime_parameters,
            bindings,
        ),
        (TypeKind::Array(pattern, pattern_len), TypeKind::Array(actual, actual_len)) => {
            pattern_len == actual_len
                && match_impl_type(
                    pattern,
                    actual,
                    type_parameters,
                    lifetime_parameters,
                    bindings,
                )
        }
        _ => false,
    }
}

fn impl_bindings(impl_block: &ImplBlock, self_ty: &Type, env: &TypeEnv) -> Option<ImplBindings> {
    impl_bindings_inner(
        impl_block,
        self_ty,
        None,
        env,
        &env.current_type_params,
        &mut Vec::new(),
    )
}

fn impl_bindings_inner(
    impl_block: &ImplBlock,
    self_ty: &Type,
    required_trait: Option<&Instance>,
    env: &TypeEnv,
    scope: &HashMap<String, Bounds>,
    obligations: &mut Vec<(Type, Instance)>,
) -> Option<ImplBindings> {
    let type_parameters = impl_block
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect::<HashSet<_>>();
    let lifetime_parameters = impl_block
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .collect::<HashSet<_>>();
    let mut bindings = ImplBindings::default();
    if !match_impl_type(
        &impl_block.target,
        self_ty,
        &type_parameters,
        &lifetime_parameters,
        &mut bindings,
    ) {
        return None;
    }
    if let Some(required_trait) = required_trait {
        let impl_trait = impl_block.trait_path.as_ref()?;
        if !match_impl_instance(
            impl_trait,
            required_trait,
            &type_parameters,
            &lifetime_parameters,
            &mut bindings,
        ) {
            return None;
        }
    }
    if impl_block.type_params.iter().any(|parameter| {
        let Some(argument) = bindings.types.get(&parameter.name) else {
            return true;
        };
        parameter
            .bounds
            .markers
            .iter_declared()
            .any(|bound| !env.class_of(argument, scope).implies(bound))
            || parameter.bounds.traits.iter().any(|bound| {
                let bound = substitute_impl_instance(&bound.trait_path, &bindings);
                !type_satisfies_trait_inner(env, argument, &bound, scope, obligations)
            })
    }) {
        return None;
    }
    Some(bindings)
}

fn type_satisfies_trait(
    env: &TypeEnv,
    ty: &Type,
    trait_path: &Instance,
    scope: &HashMap<String, Bounds>,
) -> bool {
    type_satisfies_trait_inner(env, ty, trait_path, scope, &mut Vec::new())
}

fn instantiate_trait_self_bound(
    trait_decl: &TraitDecl,
    trait_path: &Instance,
    self_ty: &Type,
    bound: &TraitBound,
) -> Instance {
    let mut type_mapping = trait_decl
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(trait_path.type_args.iter().cloned())
        .collect::<HashMap<_, _>>();
    type_mapping.insert("Self".to_string(), self_ty.clone());
    let lifetime_mapping = trait_decl
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .zip(trait_path.lifetime_args.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    substitute_bound(bound, &type_mapping, &lifetime_mapping)
}

fn trait_bound_implies(
    env: &TypeEnv,
    available: &Instance,
    self_ty: &Type,
    required: &Instance,
    visiting: &mut HashSet<String>,
) -> bool {
    if available == required {
        return true;
    }
    if !visiting.insert(available.name.clone()) {
        return false;
    }
    let Some(trait_decl) = env.traits.get(&available.name) else {
        visiting.remove(&available.name);
        return false;
    };
    let implied = trait_decl.self_bounds.traits.iter().any(|bound| {
        let bound = instantiate_trait_self_bound(trait_decl, available, self_ty, bound);
        trait_bound_implies(env, &bound, self_ty, required, visiting)
    });
    visiting.remove(&available.name);
    implied
}

fn implied_trait_paths(env: &TypeEnv, direct: &Instance, self_ty: &Type) -> Vec<Instance> {
    fn collect(
        env: &TypeEnv,
        path: Instance,
        self_ty: &Type,
        result: &mut Vec<Instance>,
        visiting: &mut HashSet<String>,
    ) {
        if result.contains(&path) {
            return;
        }
        let path_name = path.name.clone();
        if !visiting.insert(path_name.clone()) {
            return;
        }
        let Some(trait_decl) = env.traits.get(&path_name) else {
            result.push(path);
            visiting.remove(&path_name);
            return;
        };
        let implied = trait_decl
            .self_bounds
            .traits
            .iter()
            .map(|bound| instantiate_trait_self_bound(trait_decl, &path, self_ty, bound))
            .collect::<Vec<_>>();
        result.push(path);
        for bound in implied {
            collect(env, bound, self_ty, result, visiting);
        }
        visiting.remove(&path_name);
    }

    let mut result = Vec::new();
    collect(
        env,
        direct.clone(),
        self_ty,
        &mut result,
        &mut HashSet::new(),
    );
    result
}

fn type_satisfies_trait_inner(
    env: &TypeEnv,
    ty: &Type,
    trait_path: &Instance,
    scope: &HashMap<String, Bounds>,
    obligations: &mut Vec<(Type, Instance)>,
) -> bool {
    if let TypeKind::Param(name) = &ty.kind {
        return scope.get(name).is_some_and(|bounds| {
            bounds.traits.iter().any(|bound| {
                trait_bound_implies(env, &bound.trait_path, ty, trait_path, &mut HashSet::new())
            })
        });
    }
    let obligation = (ty.clone(), trait_path.clone());
    if obligations.contains(&obligation) {
        return false;
    }
    obligations.push(obligation);
    let satisfied = env.impls.iter().any(|impl_block| {
        impl_bindings_inner(impl_block, ty, Some(trait_path), env, scope, obligations).is_some()
    });
    obligations.pop();
    satisfied
}

fn match_impl_method_receiver(
    impl_block: &ImplBlock,
    method: &FnDecl,
    receiver_ty: &Type,
    env: &TypeEnv,
) -> Option<(Type, ImplBindings, ReceiverAdjustment)> {
    let receiver_param = method.params.first()?;
    let mut possible_self_types = vec![receiver_ty.clone()];
    if let (TypeKind::Ref(expected_kind, _, _), TypeKind::Ref(actual_kind, _, actual_inner)) =
        (&receiver_param.ty.kind, &receiver_ty.kind)
    {
        if expected_kind == actual_kind {
            possible_self_types.push(*actual_inner.clone());
        }
    }

    let type_parameters = impl_block
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .collect::<HashSet<_>>();
    let lifetime_parameters = impl_block
        .lifetime_params
        .iter()
        .map(|parameter| parameter.lifetime.clone())
        .collect::<HashSet<_>>();
    let matches = possible_self_types
        .into_iter()
        .filter_map(|self_ty| {
            let mut bindings = impl_bindings(impl_block, &self_ty, env)?;
            let mut mapping = bindings
                .types
                .iter()
                .map(|(name, ty)| (name.clone(), ty.clone()))
                .collect::<HashMap<_, _>>();
            mapping.insert("Self".to_string(), self_ty.clone());
            let expected_receiver = substitute(&receiver_param.ty, &mapping);
            let mut exact_bindings = bindings.clone();
            if match_impl_type(
                &expected_receiver,
                receiver_ty,
                &type_parameters,
                &lifetime_parameters,
                &mut exact_bindings,
            ) {
                return Some((self_ty, exact_bindings, ReceiverAdjustment::None));
            }
            let TypeKind::Ref(kind, _, pointee) = &expected_receiver.kind else {
                return None;
            };
            match_impl_type(
                pointee,
                receiver_ty,
                &type_parameters,
                &lifetime_parameters,
                &mut bindings,
            )
            .then_some((self_ty, bindings, ReceiverAdjustment::Borrow(*kind)))
        })
        .collect::<Vec<_>>();
    matches
        .iter()
        .find(|(_, _, adjustment)| *adjustment == ReceiverAdjustment::None)
        .cloned()
        .or_else(|| matches.into_iter().next())
}

fn receiver_adjustment_for_fn(
    subst: &Subst,
    function_ty: &Type,
    receiver_ty: &Type,
) -> ReceiverAdjustment {
    let TypeKind::Fn(params, _) = &subst.resolve(function_ty).kind else {
        return ReceiverAdjustment::None;
    };
    let Some(receiver_param) = params.first() else {
        return ReceiverAdjustment::None;
    };
    if subst.can_unify(receiver_param, receiver_ty) {
        return ReceiverAdjustment::None;
    }
    let TypeKind::Ref(kind, _, pointee) = &receiver_param.kind else {
        return ReceiverAdjustment::None;
    };
    if subst.can_unify(pointee, receiver_ty) {
        ReceiverAdjustment::Borrow(*kind)
    } else {
        ReceiverAdjustment::None
    }
}

fn receiver_adjustment_for_expected(
    subst: &Subst,
    expected: &Type,
    actual: &Type,
) -> Option<ReceiverAdjustment> {
    if subst.can_unify(expected, actual) {
        return Some(ReceiverAdjustment::None);
    }
    let TypeKind::Ref(kind, _, pointee) = &expected.kind else {
        return None;
    };
    subst
        .can_unify(pointee, actual)
        .then_some(ReceiverAdjustment::Borrow(*kind))
}

enum TraitReceiverCandidate<'a> {
    Bound {
        trait_path: Instance,
        self_ty: Type,
        method: &'a FnDecl,
        mapping: HashMap<String, Type>,
        lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
        adjustment: ReceiverAdjustment,
    },
    Impl {
        impl_block: &'a ImplBlock,
        method: &'a FnDecl,
        trait_path: Instance,
        self_ty: Type,
        bindings: ImplBindings,
        adjustment: ReceiverAdjustment,
        is_unsafe: bool,
    },
}

impl TraitReceiverCandidate<'_> {
    fn adjustment(&self) -> ReceiverAdjustment {
        match self {
            Self::Bound { adjustment, .. } | Self::Impl { adjustment, .. } => *adjustment,
        }
    }

    fn identity(&self) -> (&Instance, &Type, &str) {
        match self {
            Self::Bound {
                trait_path,
                self_ty,
                method,
                ..
            }
            | Self::Impl {
                trait_path,
                self_ty,
                method,
                ..
            } => (trait_path, self_ty, &method.name),
        }
    }

    fn context(&self) -> String {
        match self {
            Self::Bound {
                trait_path,
                self_ty,
                method,
                ..
            } => impl_method_context(self_ty, Some(trait_path), &method.name),
            Self::Impl {
                impl_block,
                trait_path,
                method,
                ..
            } => impl_method_context(&impl_block.target, Some(trait_path), &method.name),
        }
    }
}

fn substitute_impl_instance(instance: &Instance, bindings: &ImplBindings) -> Instance {
    let type_mapping = bindings
        .types
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect::<HashMap<_, _>>();
    Instance::new(
        instance.name.clone(),
        instance
            .lifetime_args
            .iter()
            .map(|lifetime| {
                bindings
                    .lifetimes
                    .get(lifetime)
                    .cloned()
                    .unwrap_or_else(|| lifetime.clone())
            })
            .collect(),
        instance
            .type_args
            .iter()
            .map(|ty| substitute_all(ty, &type_mapping, &bindings.lifetimes))
            .collect(),
    )
}

fn instantiate_method(
    env: &TypeEnv,
    subst: &mut Subst,
    impl_block: &ImplBlock,
    bindings: &ImplBindings,
    method: &FnDecl,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Instance)> {
    let mut mapping = bindings
        .types
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect::<HashMap<_, _>>();
    mapping.insert("Self".to_string(), substitute(&impl_block.target, &mapping));
    instantiate_method_signature(
        env,
        subst,
        method,
        mapping,
        bindings.lifetimes.clone(),
        generics,
        source,
        types,
        d,
    )
}

fn instantiate_method_signature(
    env: &TypeEnv,
    subst: &mut Subst,
    method: &FnDecl,
    mut mapping: HashMap<String, Type>,
    mut lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
    generics: &GenericArgs,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Instance)> {
    if !generics.lifetimes.is_empty() && generics.lifetimes.len() != method.lifetime_params.len() {
        d.push_error(source_diagnostic(
            LifetimeArgArityMismatch,
            source,
            format!(
                "method '{}' takes {} lifetime argument(s), found {}",
                method.name,
                method.lifetime_params.len(),
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
    let method_type_args = if generics.types.is_empty() {
        method
            .type_params
            .iter()
            .map(|_| subst.fresh_var())
            .collect::<Vec<_>>()
    } else {
        if generics.types.len() != method.type_params.len() {
            d.push_error(source_diagnostic(
                TypeArgArityMismatch,
                source,
                format!(
                    "method '{}' takes {} type argument(s), found {}",
                    method.name,
                    method.type_params.len(),
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
    mapping.extend(
        method
            .type_params
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(method_type_args.iter().cloned()),
    );
    let method_lifetime_args = if generics.lifetimes.is_empty() {
        method
            .lifetime_params
            .iter()
            .map(|_| types.fresh_inferred_lifetime(env, subst, source))
            .collect::<Option<Vec<_>>>()?
    } else {
        generics.lifetimes.clone()
    };
    lifetime_mapping.extend(
        method
            .lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(method_lifetime_args.iter().cloned()),
    );
    let params = method
        .params
        .iter()
        .map(|parameter| substitute_all(&parameter.ty, &mapping, &lifetime_mapping))
        .collect();
    let ret = substitute_all(&method.ret_ty, &mapping, &lifetime_mapping);
    types.pending_instantiations.push(PendingInstantiation {
        source,
        function_name: method.name.clone(),
        caller_name: env.current_function.clone(),
        caller_type_params: env.current_type_params.clone(),
        type_params: method.type_params.clone(),
        type_args: method_type_args.clone(),
        type_mapping: mapping,
        lifetime_mapping,
    });
    Some((
        fn_ty(params, ret),
        Instance::new(method.name.clone(), method_lifetime_args, method_type_args),
    ))
}

fn infer_field_access(
    env: &mut TypeEnv,
    subst: &mut Subst,
    target: &Expr,
    field: &str,
    source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Type {
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
        lifetime_args,
        type_args: args,
    }) = &struct_ty.kind
    {
        if let Some(s_decl) = env.structs.get(struct_name).cloned() {
            if let Some(field_decl) = s_decl.fields.iter().find(|decl| decl.name == field) {
                let Some(mapping) =
                    build_subst_map(struct_name, &s_decl.type_params, args, source, d)
                else {
                    return error_ty();
                };
                let Some(lifetime_mapping) =
                    build_lifetime_mapping(&s_decl.lifetime_params, lifetime_args)
                else {
                    return error_ty();
                };
                substitute_all(&field_decl.ty, &mapping, &lifetime_mapping)
            } else {
                d.push_error(source_diagnostic(
                    NoSuchField,
                    target.source,
                    format!("struct '{}' has no field '{}'", struct_name, field),
                ));
                error_ty()
            }
        } else {
            d.push_error(source_diagnostic(
                UndeclaredStruct,
                target.source,
                format!("undeclared struct '{}'", struct_name),
            ));
            error_ty()
        }
    } else {
        d.push_error(source_diagnostic(
            ExpectedStruct,
            target.source,
            format!("expected struct type, found {}", resolved),
        ));
        error_ty()
    }
}

fn receiver_field_type(
    env: &TypeEnv,
    subst: &Subst,
    receiver_ty: &Type,
    field: &str,
) -> Option<Type> {
    let resolved = subst.resolve(receiver_ty);
    let struct_ty = match &resolved.kind {
        TypeKind::Ref(_, _, inner) => subst.resolve(inner),
        _ => resolved,
    };
    let TypeKind::Custom(Instance {
        name,
        lifetime_args,
        type_args,
    }) = &struct_ty.kind
    else {
        return None;
    };
    let declaration = env.structs.get(name)?;
    let field = declaration
        .fields
        .iter()
        .find(|candidate| candidate.name == field)?;
    let mapping = declaration
        .type_params
        .iter()
        .map(|parameter| parameter.name.clone())
        .zip(type_args.iter().cloned())
        .collect();
    let lifetime_mapping = build_lifetime_mapping(&declaration.lifetime_params, lifetime_args)?;
    Some(substitute_all(&field.ty, &mapping, &lifetime_mapping))
}

fn resolve_qualified_call(
    env: &TypeEnv,
    subst: &mut Subst,
    self_ty: &Type,
    trait_path: Option<&Instance>,
    method_name: &str,
    generics: &GenericArgs,
    method_source: SourceInfo,
    selector_source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<Type> {
    let errors_before = d.error_count();
    env.validate_type(self_ty, &env.current_type_params, d);
    let self_ty = subst.resolve(self_ty);

    let (fn_ty, target) = if let Some(trait_path) = trait_path {
        for lifetime in &trait_path.lifetime_args {
            if !env.current_lifetimes.contains(lifetime) {
                d.push_error(source_diagnostic(
                    UndeclaredLifetime,
                    selector_source,
                    format!("undeclared lifetime {}", lifetime),
                ));
            }
        }
        validate_trait_instance(
            env,
            "qualified method",
            "trait",
            trait_path,
            selector_source,
            &env.current_type_params,
            d,
        );
        if d.error_count() != errors_before {
            return None;
        }
        let trait_decl = env.traits.get(&trait_path.name)?;
        let Some(method) = trait_decl
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)
        else {
            d.push_error(source_diagnostic(
                UnresolvedQualifiedMethod,
                method_source,
                format!("trait '{}' has no method '{}'", trait_path, method_name),
            ));
            return None;
        };
        if !type_satisfies_trait(env, &self_ty, trait_path, &env.current_type_params) {
            d.push_error(source_diagnostic(
                BoundNotSatisfied,
                selector_source,
                format!(
                    "type '{}' does not satisfy trait '{}' required by qualified method",
                    self_ty, trait_path
                ),
            ));
            return None;
        }
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe trait method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let mut mapping = trait_decl
            .type_params
            .iter()
            .map(|parameter| parameter.name.clone())
            .zip(trait_path.type_args.iter().cloned())
            .collect::<HashMap<_, _>>();
        mapping.insert("Self".to_string(), self_ty.clone());
        let lifetime_mapping = trait_decl
            .lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(trait_path.lifetime_args.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let (fn_ty, method) = instantiate_method_signature(
            env,
            subst,
            method,
            mapping,
            lifetime_mapping,
            generics,
            method_source,
            types,
            d,
        )?;
        (
            fn_ty,
            ResolvedMethodTarget::Trait {
                trait_path: trait_path.clone(),
                self_ty,
                method,
            },
        )
    } else {
        if d.error_count() != errors_before {
            return None;
        }
        let candidates = env
            .impls
            .iter()
            .filter(|impl_block| impl_block.trait_path.is_none())
            .filter_map(|impl_block| {
                let bindings = impl_bindings(impl_block, &self_ty, env)?;
                let method = impl_block
                    .methods
                    .iter()
                    .find(|candidate| candidate.name == method_name)?;
                Some((impl_block, method, bindings))
            })
            .collect::<Vec<_>>();
        if candidates.len() > 1 {
            let candidates = candidates
                .iter()
                .map(|(impl_block, method, _)| {
                    impl_method_context(&impl_block.target, None, &method.name)
                })
                .collect::<Vec<_>>()
                .join(", ");
            d.push_error(source_diagnostic(
                AmbiguousReceiverCall,
                method_source,
                format!(
                    "qualified call '<{}>::{}' is ambiguous; inherent candidates: {}",
                    self_ty, method_name, candidates
                ),
            ));
            return None;
        }
        let Some((impl_block, method, bindings)) = candidates.into_iter().next() else {
            d.push_error(source_diagnostic(
                UnresolvedQualifiedMethod,
                method_source,
                format!(
                    "type '{}' has no inherent method '{}'",
                    self_ty, method_name
                ),
            ));
            return None;
        };
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, method) = instantiate_method(
            env,
            subst,
            impl_block,
            &bindings,
            method,
            generics,
            method_source,
            types,
            d,
        )?;
        (fn_ty, ResolvedMethodTarget::Inherent { self_ty, method })
    };
    types.qualified_calls.insert(selector_source, target);
    Some(fn_ty)
}

fn resolve_receiver_call(
    env: &mut TypeEnv,
    subst: &mut Subst,
    receiver: &Expr,
    method_name: &str,
    generics: &GenericArgs,
    method_source: SourceInfo,
    selector_source: SourceInfo,
    call_source: SourceInfo,
    types: &mut TypeCheckResults,
    d: &mut Diagnostics,
) -> Option<(Type, Option<Type>)> {
    let receiver_ty = infer_inner(env, subst, receiver, types, d);
    let resolved_receiver_ty = subst.resolve(&receiver_ty);
    if resolved_receiver_ty.kind == TypeKind::Error {
        return None;
    }

    let inherent = env
        .impls
        .iter()
        .filter(|impl_block| impl_block.trait_path.is_none())
        .filter_map(|impl_block| {
            let method = impl_block
                .methods
                .iter()
                .find(|candidate| candidate.name == method_name)?;
            let (self_ty, bindings, adjustment) =
                match_impl_method_receiver(impl_block, method, &resolved_receiver_ty, env)?;
            Some((impl_block, method, self_ty, bindings, adjustment))
        })
        .collect::<Vec<_>>();
    let has_exact_inherent = inherent
        .iter()
        .any(|(_, _, _, _, adjustment)| *adjustment == ReceiverAdjustment::None);
    let inherent = inherent
        .into_iter()
        .filter(|(_, _, _, _, adjustment)| {
            !has_exact_inherent || *adjustment == ReceiverAdjustment::None
        })
        .collect::<Vec<_>>();
    if inherent.len() > 1 {
        let candidates = inherent
            .iter()
            .map(|(impl_block, method, _, _, _)| {
                impl_method_context(&impl_block.target, None, &method.name)
            })
            .collect::<Vec<_>>()
            .join(", ");
        d.push_error(source_diagnostic(
            AmbiguousReceiverCall,
            method_source,
            format!(
                "receiver call '{}.{}' is ambiguous; inherent candidates: {}",
                resolved_receiver_ty, method_name, candidates
            ),
        ));
        return None;
    }
    if let Some((impl_block, method, self_ty, bindings, adjustment)) = inherent.into_iter().next() {
        if method.is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, method_instance) = instantiate_method(
            env,
            subst,
            &impl_block,
            &bindings,
            &method,
            generics,
            method_source,
            types,
            d,
        )?;
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Method(ResolvedMethodTarget::Inherent {
                    self_ty,
                    method: method_instance,
                }),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    let bound_self_ty = match &resolved_receiver_ty.kind {
        TypeKind::Param(name) if env.current_type_params.contains_key(name) => {
            Some(resolved_receiver_ty.clone())
        }
        TypeKind::Ref(_, _, pointee) => {
            let pointee = subst.resolve(pointee);
            matches!(&pointee.kind, TypeKind::Param(name) if env.current_type_params.contains_key(name))
                .then_some(pointee)
        }
        _ => None,
    };
    let mut trait_methods = Vec::new();
    let mut seen_bound_methods = Vec::new();
    if let Some(self_ty) = bound_self_ty {
        if let TypeKind::Param(parameter_name) = &self_ty.kind {
            if let Some(bounds) = env.current_type_params.get(parameter_name) {
                for bound in &bounds.traits {
                    for trait_path in implied_trait_paths(env, &bound.trait_path, &self_ty) {
                        let Some(trait_decl) = env.traits.get(&trait_path.name) else {
                            continue;
                        };
                        let Some(method) = trait_decl
                            .methods
                            .iter()
                            .find(|candidate| candidate.name == method_name)
                        else {
                            continue;
                        };
                        if seen_bound_methods.contains(&(trait_path.clone(), self_ty.clone())) {
                            continue;
                        }
                        let mut mapping = trait_decl
                            .type_params
                            .iter()
                            .map(|parameter| parameter.name.clone())
                            .zip(trait_path.type_args.iter().cloned())
                            .collect::<HashMap<_, _>>();
                        mapping.insert("Self".to_string(), self_ty.clone());
                        let lifetime_mapping = trait_decl
                            .lifetime_params
                            .iter()
                            .map(|parameter| parameter.lifetime.clone())
                            .zip(trait_path.lifetime_args.iter().cloned())
                            .collect::<BTreeMap<_, _>>();
                        let Some(receiver_param) = method.params.first() else {
                            continue;
                        };
                        let expected_receiver =
                            substitute_all(&receiver_param.ty, &mapping, &lifetime_mapping);
                        let Some(adjustment) = receiver_adjustment_for_expected(
                            subst,
                            &expected_receiver,
                            &resolved_receiver_ty,
                        ) else {
                            continue;
                        };
                        seen_bound_methods.push((trait_path.clone(), self_ty.clone()));
                        trait_methods.push(TraitReceiverCandidate::Bound {
                            trait_path,
                            self_ty: self_ty.clone(),
                            method,
                            mapping,
                            lifetime_mapping,
                            adjustment,
                        });
                    }
                }
            }
        }
    }
    let bound_method_count = trait_methods.len();
    let impl_methods = env.impls.iter().filter_map(|impl_block| {
        let trait_path = impl_block.trait_path.as_ref()?;
        let trait_method = env
            .traits
            .get(&trait_path.name)?
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)?;
        let method = impl_block
            .methods
            .iter()
            .find(|candidate| candidate.name == method_name)?;
        let (self_ty, bindings, adjustment) =
            match_impl_method_receiver(impl_block, method, &resolved_receiver_ty, env)?;
        let trait_path = substitute_impl_instance(trait_path, &bindings);
        Some(TraitReceiverCandidate::Impl {
            impl_block,
            method,
            trait_path,
            self_ty,
            bindings,
            adjustment,
            is_unsafe: trait_method.is_unsafe,
        })
    });
    for candidate in impl_methods {
        let (candidate_trait, candidate_self, candidate_method) = candidate.identity();
        let duplicates_bound = trait_methods[..bound_method_count].iter().any(|bound| {
            let (bound_trait, bound_self, bound_method) = bound.identity();
            bound_trait == candidate_trait
                && bound_self == candidate_self
                && bound_method == candidate_method
        });
        if !duplicates_bound {
            trait_methods.push(candidate);
        }
    }
    let has_exact_trait = trait_methods
        .iter()
        .any(|candidate| candidate.adjustment() == ReceiverAdjustment::None);
    let trait_methods = trait_methods
        .into_iter()
        .filter(|candidate| !has_exact_trait || candidate.adjustment() == ReceiverAdjustment::None)
        .collect::<Vec<_>>();
    if trait_methods.len() > 1 {
        let only_direct_bounds = trait_methods
            .iter()
            .all(|candidate| matches!(candidate, TraitReceiverCandidate::Bound { .. }));
        let ambiguity_receiver = if only_direct_bounds {
            trait_methods[0].identity().1
        } else {
            &resolved_receiver_ty
        };
        let candidates = trait_methods
            .iter()
            .map(TraitReceiverCandidate::context)
            .collect::<Vec<_>>()
            .join(", ");
        d.push_error(source_diagnostic(
            AmbiguousReceiverCall,
            method_source,
            format!(
                "receiver call '{}.{}' is ambiguous; trait candidates: {}",
                ambiguity_receiver, method_name, candidates
            ),
        ));
        return None;
    }
    if let Some(candidate) = trait_methods.into_iter().next() {
        let is_unsafe = match &candidate {
            TraitReceiverCandidate::Bound { method, .. } => method.is_unsafe,
            TraitReceiverCandidate::Impl { is_unsafe, .. } => *is_unsafe,
        };
        if is_unsafe && !env.in_unsafe {
            d.push_error(source_diagnostic(
                UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe trait method '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (trait_path, self_ty, adjustment, fn_ty, method_instance) = match candidate {
            TraitReceiverCandidate::Bound {
                trait_path,
                self_ty,
                method,
                mapping,
                lifetime_mapping,
                adjustment,
            } => {
                let (fn_ty, method_instance) = instantiate_method_signature(
                    env,
                    subst,
                    method,
                    mapping,
                    lifetime_mapping,
                    generics,
                    method_source,
                    types,
                    d,
                )?;
                (trait_path, self_ty, adjustment, fn_ty, method_instance)
            }
            TraitReceiverCandidate::Impl {
                impl_block,
                method,
                trait_path,
                self_ty,
                bindings,
                adjustment,
                ..
            } => {
                let (fn_ty, method_instance) = instantiate_method(
                    env,
                    subst,
                    impl_block,
                    &bindings,
                    method,
                    generics,
                    method_source,
                    types,
                    d,
                )?;
                (trait_path, self_ty, adjustment, fn_ty, method_instance)
            }
        };
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Method(ResolvedMethodTarget::Trait {
                    trait_path,
                    self_ty,
                    method: method_instance,
                }),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    let field_ty = receiver_field_type(env, subst, &receiver_ty, method_name);
    let callable_field = matches!(
        field_ty.as_ref().map(|ty| &ty.kind),
        Some(TypeKind::Fn(_, _))
    );
    if callable_field && generics.is_empty() {
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::Field,
                adjustment: ReceiverAdjustment::None,
            },
        );
        return field_ty.map(|field_ty| (field_ty, None));
    }

    if env.functions.contains_key(method_name) {
        if env
            .functions
            .get(method_name)
            .is_some_and(|function| function.is_unsafe)
            && !env.in_unsafe
        {
            d.push_error(source_diagnostic(
                UnsafeRequired,
                method_source,
                format!(
                    "call to unsafe function '{}' requires unsafe block",
                    method_name
                ),
            ));
        }
        let (fn_ty, instance) =
            instantiate_function(env, subst, method_name, generics, method_source, types, d)?;
        let adjustment = receiver_adjustment_for_fn(subst, &fn_ty, &receiver_ty);
        types.receiver_calls.insert(
            selector_source,
            ResolvedReceiverCall {
                target: ResolvedReceiverTarget::FreeFunction(instance),
                adjustment,
            },
        );
        let receiver_arg_ty = match adjustment {
            ReceiverAdjustment::None => receiver_ty.clone(),
            ReceiverAdjustment::Borrow(kind) => ref_ty(kind, receiver_ty.clone()),
        };
        return Some((fn_ty, Some(receiver_arg_ty)));
    }

    if callable_field {
        d.push_error(source_diagnostic(
            GenericArgsOnFunctionValue,
            method_source,
            "explicit generic arguments require a named function",
        ));
    } else if let Some(field_ty) = field_ty {
        d.push_error(source_diagnostic(
            ExpectedFunction,
            call_source,
            format!("expected function type, found {}", field_ty),
        ));
    } else {
        d.push_error(source_diagnostic(
            UnresolvedReceiverCall,
            method_source,
            format!(
                "no method, callable field, or free function '{}' applies to receiver type {}",
                method_name, resolved_receiver_ty
            ),
        ));
    }
    None
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
                let Some((fn_ty, instance)) = instantiate_function(
                    env,
                    subst,
                    name,
                    &GenericArgs::empty(),
                    expr.source,
                    types,
                    d,
                ) else {
                    return error_ty();
                };
                types.function_instantiations.insert(expr.source, instance);
                fn_ty
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
            infer_field_access(env, subst, target, field, expr.source, types, d)
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
        ExprKind::Call(target, generics, args) => {
            let (fn_ty, receiver_ty) = match target {
                CallTarget::Expr(fn_expr) => {
                    let direct_name = match &fn_expr.kind {
                        ExprKind::Variable(name)
                            if env.lookup_var(name).is_none()
                                && env.functions.contains_key(name) =>
                        {
                            Some(name)
                        }
                        _ => None,
                    };
                    if let Some(name) = direct_name {
                        if let Some(signature) = env.functions.get(name) {
                            if signature.is_unsafe && !env.in_unsafe {
                                d.push_error(source_diagnostic(
                                    HllTypeCheckCode::UnsafeRequired,
                                    fn_expr.source,
                                    format!(
                                        "call to unsafe function '{}' requires unsafe block",
                                        name
                                    ),
                                ));
                            }
                        }
                        let Some((fn_ty, instance)) = instantiate_function(
                            env,
                            subst,
                            name,
                            generics,
                            fn_expr.source,
                            types,
                            d,
                        ) else {
                            return error_ty();
                        };
                        types
                            .function_instantiations
                            .insert(fn_expr.source, instance);
                        record_expression_type(env, types, fn_expr.source, fn_ty.clone());
                        (fn_ty, None)
                    } else {
                        if !generics.is_empty() {
                            d.push_error(source_diagnostic(
                                GenericArgsOnFunctionValue,
                                fn_expr.source,
                                "explicit generic arguments require a named function",
                            ));
                            return error_ty();
                        }
                        (infer_inner(env, subst, fn_expr, types, d), None)
                    }
                }
                CallTarget::Receiver {
                    receiver,
                    method,
                    method_source,
                    selector_source,
                } => {
                    let Some((fn_ty, receiver_ty)) = resolve_receiver_call(
                        env,
                        subst,
                        receiver,
                        method,
                        generics,
                        *method_source,
                        *selector_source,
                        expr.source,
                        types,
                        d,
                    ) else {
                        return error_ty();
                    };
                    (fn_ty, receiver_ty)
                }
                CallTarget::Qualified {
                    self_ty,
                    trait_path,
                    method,
                    method_source,
                    selector_source,
                } => {
                    let Some(fn_ty) = resolve_qualified_call(
                        env,
                        subst,
                        self_ty,
                        trait_path.as_ref(),
                        method,
                        generics,
                        *method_source,
                        *selector_source,
                        types,
                        d,
                    ) else {
                        return error_ty();
                    };
                    (fn_ty, None)
                }
            };
            let resolved = subst.resolve(&fn_ty);
            if resolved.kind == TypeKind::Error {
                return error_ty();
            }
            if let TypeKind::Fn(param_tys, ret_ty) = resolved.kind {
                let implicit_count = usize::from(receiver_ty.is_some());
                if param_tys.len() != args.len() + implicit_count {
                    let (expected, found) = if param_tys.len() < implicit_count {
                        (param_tys.len(), args.len() + implicit_count)
                    } else {
                        (param_tys.len() - implicit_count, args.len())
                    };
                    d.push_error(source_diagnostic(
                        ArityMismatch,
                        expr.source,
                        format!("function expected {} arguments, found {}", expected, found),
                    ));
                    return error_ty();
                }
                let explicit_params = if let Some(receiver_ty) = receiver_ty {
                    if let Err(error) = subst.unify(&param_tys[0], &receiver_ty) {
                        d.push_error(error.to_diag(match target {
                            CallTarget::Receiver { receiver, .. } => receiver.source,
                            CallTarget::Expr(_) | CallTarget::Qualified { .. } => expr.source,
                        }));
                    }
                    &param_tys[1..]
                } else {
                    &param_tys[..]
                };
                for (arg, param_ty) in args.iter().zip(explicit_params) {
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
                lifetime_args,
                type_args: args,
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
                let Some(lifetime_mapping) =
                    build_lifetime_mapping(&e_decl.lifetime_params, &lifetime_args)
                else {
                    return error_ty();
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
                            env.insert_var(
                                var_name.clone(),
                                substitute_all(&v.ty, &mapping, &lifetime_mapping),
                            );
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

            let type_args: Vec<Type> = s_decl
                .type_params
                .iter()
                .map(|_| subst.fresh_var())
                .collect();
            let lifetime_args = s_decl
                .lifetime_params
                .iter()
                .map(|_| {
                    types
                        .fresh_inferred_lifetime(env, subst, expr.source)
                        .expect("constructor expression outside a function body")
                })
                .collect::<Vec<_>>();
            let mapping: HashMap<String, Type> = s_decl
                .type_params
                .iter()
                .map(|tp| tp.name.clone())
                .zip(type_args.iter().cloned())
                .collect();
            let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = s_decl
                .lifetime_params
                .iter()
                .map(|lp| lp.lifetime.clone())
                .zip(lifetime_args.iter().cloned())
                .collect();

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
                let expected = substitute_all(&f_decl.ty, &mapping, &lifetime_mapping);
                check_inner(env, subst, val_expr, &expected, types, d);
            }

            Type::synthesized(TypeKind::Custom(Instance::new(
                name.clone(),
                lifetime_args,
                type_args,
            )))
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

            let type_args: Vec<Type> = e_decl
                .type_params
                .iter()
                .map(|_| subst.fresh_var())
                .collect();
            let lifetime_args = e_decl
                .lifetime_params
                .iter()
                .map(|_| {
                    types
                        .fresh_inferred_lifetime(env, subst, expr.source)
                        .expect("constructor expression outside a function body")
                })
                .collect::<Vec<_>>();
            let mapping: HashMap<String, Type> = e_decl
                .type_params
                .iter()
                .map(|tp| tp.name.clone())
                .zip(type_args.iter().cloned())
                .collect();
            let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = e_decl
                .lifetime_params
                .iter()
                .map(|lp| lp.lifetime.clone())
                .zip(lifetime_args.iter().cloned())
                .collect();
            let expected_payload = substitute_all(&variant_decl.ty, &mapping, &lifetime_mapping);
            check_inner(env, subst, payload, &expected_payload, types, d);
            Type::synthesized(TypeKind::Custom(Instance::new(
                enum_name.clone(),
                lifetime_args,
                type_args,
            )))
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
                lifetime_args,
                type_args: args,
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
                let Some(lifetime_mapping) =
                    build_lifetime_mapping(&e_decl.lifetime_params, &lifetime_args)
                else {
                    return;
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
                            env.insert_var(
                                var_name.clone(),
                                substitute_all(&v.ty, &mapping, &lifetime_mapping),
                            );
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
        ExprKind::Call(target, _generics, args) => {
            match target {
                CallTarget::Expr(callee) => check_no_control_flow(callee, loop_depth, d),
                CallTarget::Receiver { receiver, .. } => {
                    check_no_control_flow(receiver, loop_depth, d)
                }
                CallTarget::Qualified { .. } => {}
            }
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
    fn compatibility_probe_discards_successful_and_partial_bindings() {
        let mut subst = Subst::new();
        let variable = subst.fresh_var();

        assert!(subst.can_unify(&variable, &i64_ty()));
        assert_eq!(subst.resolve(&variable), variable);

        let expected = fn_ty(vec![variable.clone(), bool_ty()], unit_ty());
        let found = fn_ty(vec![i64_ty(), i64_ty()], unit_ty());
        assert!(!subst.can_unify(&expected, &found));
        assert_eq!(subst.resolve(&variable), variable);
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
