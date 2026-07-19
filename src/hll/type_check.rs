use crate::common::{Marker, Markers, RefKind, Span};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::hll::ast::*;
use crate::hll::helpers::*;
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

/// Build a `name → bounds` map from a decl's type parameters. Used
/// when computing a type's substructural class or validating uses
/// against bounds — both need per-name marker info.
fn type_params_scope(params: &[TypeParam]) -> HashMap<String, Markers> {
    params.iter().map(|p| (p.name.clone(), p.bounds)).collect()
}

/// Substitute type-parameter references in `ty` using `mapping`. Used
/// when reading a declared field/variant/param type on a generic decl:
/// e.g. `Box::inner` has declared type `T`, but on `Box<i64>` the
/// caller sees `i64`. `mapping` binds each declared type-parameter
/// name to the concrete argument at the use site.
fn substitute(ty: &Type, mapping: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Param(name) => mapping.get(name).cloned().unwrap_or_else(|| ty.clone()),
        Type::Custom(name, _, args) => {
            let new_args = args.iter().map(|a| substitute(a, mapping)).collect();
            custom_ty_with_args(name.clone(), new_args)
        }
        Type::Ref(kind, _, inner) => ref_ty(*kind, substitute(inner, mapping)),
        Type::RawPtr(inner) => raw_ptr_ty(substitute(inner, mapping)),
        Type::Array(inner, size) => array_ty(substitute(inner, mapping), *size),
        Type::Fn(params, ret) => {
            let new_params = params.iter().map(|p| substitute(p, mapping)).collect();
            fn_ty(new_params, substitute(ret, mapping))
        }
        _ => ty.clone(),
    }
}

/// Build a `param_name -> arg_type` substitution map, checking that
/// the number of args matches the number of declared type parameters.
/// Pushes an error diagnostic on arity mismatch and returns `None`.
fn build_subst_map(
    decl_name: &str,
    type_params: &[TypeParam],
    args: &[Type],
    span: Span,
    d: &mut Diagnostics,
) -> Option<HashMap<String, Type>> {
    if args.len() != type_params.len() {
        d.push_error(Diagnostic::new(
            ArityMismatch,
            span,
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

/// Distinguish unification failure modes returned by [`Subst::unify`] so
/// call sites can attach the right span and diagnostic code.
#[derive(Debug)]
pub enum UnifyError {
    Mismatch(String),
    Infinite,
    ArityMismatch,
}

impl UnifyError {
    fn to_diag(self, span: Span) -> Diagnostic {
        match self {
            UnifyError::Mismatch(msg) => Diagnostic::new(TypeMismatch, span, msg),
            UnifyError::Infinite => Diagnostic::new(
                InfiniteType,
                span,
                "infinite type detected during unification",
            ),
            UnifyError::ArityMismatch => {
                Diagnostic::new(ArityMismatch, span, "function arity mismatch")
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
        Type::Var(id)
    }

    pub fn fresh_int_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        Type::IntVar(id)
    }

    pub fn fresh_float_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        Type::FloatVar(id)
    }

    pub fn resolve(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) | Type::IntVar(id) | Type::FloatVar(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            Type::Ref(kind, _, inner) => ref_ty(*kind, self.resolve(inner)),
            Type::RawPtr(inner) => raw_ptr_ty(self.resolve(inner)),
            Type::Fn(params, ret) => {
                let resolved_params = params.iter().map(|p| self.resolve(p)).collect();
                fn_ty(resolved_params, self.resolve(ret))
            }
            Type::Array(inner, size) => array_ty(self.resolve(inner), *size),
            Type::Custom(name, _, args) => {
                let resolved_args = args.iter().map(|a| self.resolve(a)).collect();
                custom_ty_with_args(name.clone(), resolved_args)
            }
            other => other.clone(),
        }
    }
    pub fn resolve_default(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve_default(resolved)
                } else {
                    Type::Error
                }
            }
            Type::IntVar(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve_default(resolved)
                } else {
                    i64_ty()
                }
            }
            Type::FloatVar(id) => {
                if let Some(resolved) = self.map.get(id) {
                    self.resolve_default(resolved)
                } else {
                    f64_ty()
                }
            }
            Type::Ref(kind, _, inner) => ref_ty(*kind, self.resolve_default(inner)),
            Type::RawPtr(inner) => raw_ptr_ty(self.resolve_default(inner)),
            Type::Array(inner, size) => array_ty(self.resolve_default(inner), *size),
            Type::Fn(params, ret) => {
                let resolved_params = params.iter().map(|p| self.resolve_default(p)).collect();
                fn_ty(resolved_params, self.resolve_default(ret))
            }
            Type::Custom(name, _, args) => {
                let resolved_args = args.iter().map(|a| self.resolve_default(a)).collect();
                custom_ty_with_args(name.clone(), resolved_args)
            }
            other => other.clone(),
        }
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnifyError> {
        let r1 = self.resolve(t1);
        let r2 = self.resolve(t2);
        match (&r1, &r2) {
            (Type::Error, _) | (_, Type::Error) => Ok(()),
            (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(()),
            (Type::IntVar(id1), Type::IntVar(id2)) if id1 == id2 => Ok(()),
            (Type::FloatVar(id1), Type::FloatVar(id2)) if id1 == id2 => Ok(()),
            (Type::Var(id), other) | (other, Type::Var(id)) => {
                if self.occurs_in(*id, other) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, other.clone());
                Ok(())
            }
            (Type::Never, _) | (_, Type::Never) => Ok(()),
            (Type::IntVar(id), other) | (other, Type::IntVar(id)) => match other {
                Type::IntVar(_) | Type::Int(_) => {
                    self.map.insert(*id, other.clone());
                    Ok(())
                }
                Type::Error => Ok(()),
                _ => Err(UnifyError::Mismatch(format!(
                    "type mismatch: expected integer type, found {}",
                    other
                ))),
            },
            (Type::FloatVar(id), other) | (other, Type::FloatVar(id)) => match other {
                Type::FloatVar(_) | Type::Float(_) => {
                    self.map.insert(*id, other.clone());
                    Ok(())
                }
                Type::Error => Ok(()),
                _ => Err(UnifyError::Mismatch(format!(
                    "type mismatch: expected float type, found {}",
                    other
                ))),
            },
            (Type::Int(i1), Type::Int(i2)) if i1 == i2 => Ok(()),
            (Type::Float(f1), Type::Float(f2)) if f1 == f2 => Ok(()),
            (Type::Bool, Type::Bool) => Ok(()),
            (Type::Unit, Type::Unit) => Ok(()),
            (Type::Custom(n1, _, a1), Type::Custom(n2, _, a2))
                if n1 == n2 && a1.len() == a2.len() =>
            {
                let a1 = a1.clone();
                let a2 = a2.clone();
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Type::Param(p1), Type::Param(p2)) if p1 == p2 => Ok(()),
            (Type::Ref(k1, _, inner1), Type::Ref(k2, _, inner2)) if k1 == k2 => {
                self.unify(inner1, inner2)
            }
            (Type::RawPtr(inner1), Type::RawPtr(inner2)) => self.unify(inner1, inner2),
            (Type::Array(inner1, size1), Type::Array(inner2, size2)) if size1 == size2 => {
                self.unify(inner1, inner2)
            }
            (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
                if p1.len() != p2.len() {
                    return Err(UnifyError::ArityMismatch);
                }
                for (a1, a2) in p1.iter().zip(p2.iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(r1, r2)
            }
            (a, b) => Err(UnifyError::Mismatch(format!(
                "type mismatch: expected {}, found {}",
                a, b
            ))),
        }
    }

    fn occurs_in(&self, id: usize, ty: &Type) -> bool {
        match ty {
            Type::Var(v) | Type::IntVar(v) | Type::FloatVar(v) => {
                if *v == id {
                    true
                } else if let Some(resolved) = self.map.get(v) {
                    self.occurs_in(id, resolved)
                } else {
                    false
                }
            }
            Type::Ref(_, _, inner) => self.occurs_in(id, inner),
            Type::RawPtr(inner) => self.occurs_in(id, inner),
            Type::Array(inner, _) => self.occurs_in(id, inner),
            Type::Fn(params, ret) => {
                params.iter().any(|p| self.occurs_in(id, p)) || self.occurs_in(id, ret)
            }
            Type::Custom(_, _, args) => args.iter().any(|a| self.occurs_in(id, a)),
            _ => false,
        }
    }
}

pub struct TypeEnv {
    variables: Vec<HashMap<String, Type>>,
    structs: HashMap<String, StructDecl>,
    enums: HashMap<String, EnumDecl>,
    functions: HashMap<String, (Vec<Type>, Type, bool)>,
    /// Fn name → list of declared type-parameter names. Used at call
    /// sites to freshen the signature into new inference vars.
    fn_type_params: HashMap<String, Vec<String>>,
    current_ret_ty: Option<Type>,
    /// Type-parameter names → declared marker bounds for the fn being
    /// checked. Empty outside a fn body.
    current_type_params: HashMap<String, Markers>,
    in_unsafe: bool,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            variables: vec![HashMap::new()],
            structs: HashMap::new(),
            enums: HashMap::new(),
            functions: HashMap::new(),
            fn_type_params: HashMap::new(),
            current_ret_ty: None,
            current_type_params: HashMap::new(),
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
        match ty {
            Type::Int(_) | Type::Float(_) | Type::Bool | Type::Unit | Type::Never => all(),
            Type::Fn(_, _) | Type::RawPtr(_) => all(),
            Type::Ref(kind, _, _) => match kind {
                RefKind::Shared => all(),
                RefKind::Mut | RefKind::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
                RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
            },
            Type::Custom(name, _, _args) => {
                if let Some(s) = self.structs.get(name) {
                    s.markers
                } else if let Some(e) = self.enums.get(name) {
                    e.markers
                } else {
                    Markers::empty()
                }
            }
            Type::Param(name) => scope.get(name).copied().unwrap_or_else(Markers::empty),
            Type::Array(elem, _) => self.class_of(elem, scope),
            Type::Var(_) | Type::IntVar(_) | Type::FloatVar(_) | Type::Error => all(),
        }
    }

    /// Walk `ty` and push a diagnostic per problem: an undeclared
    /// `Custom` name, a `Param` not in scope, wrong type-arg arity,
    /// or an arg that fails the declared bound. Each is reported at
    /// `span`. Continues past errors so a single top-level `Type`
    /// with multiple defects surfaces them all.
    pub fn validate_type(
        &self,
        ty: &Type,
        scope: &HashMap<String, Markers>,
        span: Span,
        d: &mut Diagnostics,
    ) {
        match ty {
            Type::Int(_)
            | Type::Float(_)
            | Type::Bool
            | Type::Unit
            | Type::Never
            | Type::Var(_)
            | Type::IntVar(_)
            | Type::FloatVar(_)
            | Type::Error => {}
            Type::Param(name) => {
                if !scope.contains_key(name) {
                    d.push_error(Diagnostic::new(
                        UndeclaredType,
                        span,
                        format!("undeclared type '{}'", name),
                    ));
                }
            }
            Type::Ref(_, _, inner) | Type::RawPtr(inner) | Type::Array(inner, _) => {
                self.validate_type(inner, scope, span, d);
            }
            Type::Fn(params, ret) => {
                for p in params {
                    self.validate_type(p, scope, span, d);
                }
                self.validate_type(ret, scope, span, d);
            }
            Type::Custom(name, _, args) => {
                for a in args {
                    self.validate_type(a, scope, span, d);
                }
                let type_params: &[TypeParam] = if let Some(s) = self.structs.get(name) {
                    &s.type_params
                } else if let Some(e) = self.enums.get(name) {
                    &e.type_params
                } else {
                    d.push_error(Diagnostic::new(
                        UndeclaredType,
                        span,
                        format!("undeclared type '{}'", name),
                    ));
                    return;
                };
                if args.len() != type_params.len() {
                    d.push_error(Diagnostic::new(
                        TypeArgArityMismatch,
                        span,
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
                        if tp.bounds.declared(m) && !arg_class.implies(m) {
                            d.push_error(Diagnostic::new(
                                BoundNotSatisfied,
                                span,
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

/// Run HLL type-checking, pushing errors into `d`. Returns the
/// per-expression type map; errors accumulate in `d`.
pub fn run_type_check(program: &Program, d: &mut Diagnostics) -> Option<IndexMap<Span, Type>> {
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

/// Run HLL type-checking, pushing all errors into `d` and returning the
/// per-expression type map unconditionally. Production callers should use
/// `run_type_check`.
pub(super) fn typecheck_program_collect(
    program: &Program,
    d: &mut Diagnostics,
) -> IndexMap<Span, Type> {
    let mut env = TypeEnv::new();
    let mut subst = Subst::new();
    let mut types = IndexMap::new();

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
                let params_tys: Vec<Type> = f.params.iter().map(|p| p.ty.clone()).collect();
                env.functions
                    .insert(f.name.clone(), (params_tys, f.ret_ty.clone(), f.is_unsafe));
                env.fn_type_params.insert(
                    f.name.clone(),
                    f.type_params.iter().map(|tp| tp.name.clone()).collect(),
                );
            }
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
                    env.validate_type(&f.ty, &scope, f.span, d);
                }
            }
            Declaration::Enum(e) => {
                let scope = type_params_scope(&e.type_params);
                for v in &e.variants {
                    env.validate_type(&v.ty, &scope, v.span, d);
                }
            }
            Declaration::Fn(f) => {
                let scope = type_params_scope(&f.type_params);
                let errors_before = d.error_count();
                for p in &f.params {
                    env.validate_type(&p.ty, &scope, p.span, d);
                }
                env.validate_type(&f.ret_ty, &scope, f.ret_ty_span, d);
                d.annotate_errors_in_function(errors_before, &f.name);
            }
        }
    }

    // Typecheck function bodies
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            // Extern fn declarations carry no body; validate the ABI
            // string (bare `extern` or `extern "C"` only for now) and
            // skip body-checking. Signature was already registered
            // into `env.functions` above.
            let Some(body) = &f.body else {
                if let Some(abi) = &f.abi {
                    if abi != "C" {
                        // Prefer the ABI string's span; fall back to
                        // the whole decl if it isn't populated (safety
                        // net — parser always fills it when abi is Some).
                        let span = f.abi_span.unwrap_or(f.span);
                        d.push_error(Diagnostic::new(
                            HllTypeCheckCode::UnknownAbi,
                            span,
                            format!("unknown extern ABI '{}' — expected 'C' or bare extern", abi),
                        ));
                    }
                }
                continue;
            };
            env.current_type_params = type_params_scope(&f.type_params);
            env.push_scope();
            env.current_ret_ty = Some(f.ret_ty.clone());
            env.in_unsafe = f.is_unsafe;
            for param in &f.params {
                env.insert_var(param.name.clone(), param.ty.clone());
            }
            let errors_before = d.error_count();
            check_inner(&mut env, &mut subst, body, &f.ret_ty, &mut types, d);
            d.annotate_errors_in_function(errors_before, &f.name);
            env.pop_scope();
            env.in_unsafe = false;
            env.current_type_params = HashMap::new();
        }
    }

    // Check for unresolved type variables
    let mut reported_vars = HashSet::new();
    for (span, ty) in &types {
        let resolved = subst.resolve(ty);
        let mut unresolved = HashSet::new();
        collect_unresolved_vars(&resolved, &subst, &mut unresolved);
        if !unresolved.is_empty() {
            let has_unreported = unresolved.iter().any(|id| !reported_vars.contains(id));
            if has_unreported {
                reported_vars.extend(unresolved);
                d.push_error(Diagnostic::new(
                    HllTypeCheckCode::AmbiguousType,
                    *span,
                    format!("type annotations needed: type of expression is ambiguous (could not resolve type variable in {})", resolved),
                ));
            }
        }
    }

    // Resolve all captured expression types in the final map
    let mut resolved_types = IndexMap::new();
    for (span, ty) in types {
        resolved_types.insert(span, subst.resolve_default(&ty));
    }

    resolved_types
}

fn collect_unresolved_vars(ty: &Type, subst: &Subst, vars: &mut HashSet<usize>) {
    match ty {
        Type::Var(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            } else {
                vars.insert(*id);
            }
        }
        Type::IntVar(id) | Type::FloatVar(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            }
        }
        Type::Ref(_, _, inner) => collect_unresolved_vars(inner, subst, vars),
        Type::RawPtr(inner) => collect_unresolved_vars(inner, subst, vars),
        Type::Array(inner, _) => collect_unresolved_vars(inner, subst, vars),
        Type::Fn(params, ret) => {
            for p in params {
                collect_unresolved_vars(p, subst, vars);
            }
            collect_unresolved_vars(ret, subst, vars);
        }
        Type::Custom(_, _, args) => {
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
    match (from, to) {
        (Type::Int(_), Type::Int(_)) => true,
        (Type::Float(_), Type::Float(_)) => true,
        (Type::Int(_), Type::Float(_)) => true,
        (Type::Float(_), Type::Int(_)) => true,
        (Type::Bool, Type::Int(_)) => true,
        _ => false,
    }
}

/// Return the intrinsic name that implements `expr as to`, or `None`
/// if `from == to` (no cast needed). Caller must have checked
/// `is_cast_supported` first — this helper panics on unsupported pairs.
pub fn cast_intrinsic_name(from: &Type, to: &Type) -> Option<String> {
    if from == to {
        return None;
    }
    let ty_name = |ty: &Type| match ty {
        Type::Int(k) => k.name().to_string(),
        Type::Float(k) => k.name().to_string(),
        Type::Bool => "bool".to_string(),
        _ => panic!("cast_intrinsic_name: unsupported type {:?}", ty),
    };
    Some(format!("${}_to_{}", ty_name(from), ty_name(to)))
}

fn infer_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    types: &mut IndexMap<Span, Type>,
    d: &mut Diagnostics,
) -> Type {
    let ty = match &expr.kind {
        ExprKind::Literal(lit) => match lit {
            Literal::Int(_, Some(ty)) => Type::Int(*ty),
            Literal::Int(_, None) => subst.fresh_int_var(),
            Literal::Float(_, Some(ty)) => Type::Float(*ty),
            Literal::Float(_, None) => subst.fresh_float_var(),
            Literal::Bool(_) => bool_ty(),
            Literal::Unit => unit_ty(),
        },
        ExprKind::Binary(lhs, op, rhs) => {
            let lhs_ty = infer_inner(env, subst, lhs, types, d);
            let rhs_ty = infer_inner(env, subst, rhs, types, d);
            if let Err(e) = subst.unify(&lhs_ty, &rhs_ty) {
                d.push_error(e.to_diag(expr.span));
            }

            let resolved = subst.resolve(&lhs_ty);
            match &resolved {
                Type::Int(_)
                | Type::Float(_)
                | Type::Var(_)
                | Type::IntVar(_)
                | Type::FloatVar(_)
                | Type::Never
                | Type::Error => {}
                _ => {
                    d.push_error(Diagnostic::new(
                        BinaryOpNonNumeric,
                        lhs.span,
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
                UnOp::Neg => {
                    match &resolved {
                        Type::Int(int_ty) if int_ty.is_signed() => {}
                        Type::Float(_) => {}
                        Type::IntVar(_)
                        | Type::FloatVar(_)
                        | Type::Var(_)
                        | Type::Never
                        | Type::Error => {}
                        _ => {
                            d.push_error(Diagnostic::new(
                            HllTypeCheckCode::UnaryOpInvalidOperand,
                            operand.span,
                            format!("unary '-' requires a signed integer or float operand, found {}", resolved),
                        ));
                            return error_ty();
                        }
                    }
                }
            }
            operand_ty
        }
        ExprKind::Variable(name) => {
            if let Some(ty) = env.lookup_var(name) {
                ty
            } else if let Some((params, ret, _is_unsafe)) = env.functions.get(name).cloned() {
                // Freshen the fn's declared type parameters into new
                // inference vars, then substitute through the signature.
                // Each call site gets its own independent binding of T.
                // The freshening also decouples the signature from any
                // Params still visible from the caller's scope.
                let type_params = env.fn_type_params.get(name).cloned().unwrap_or_default();
                let mut mapping: HashMap<String, Type> = HashMap::new();
                for tp in &type_params {
                    mapping.insert(tp.clone(), subst.fresh_var());
                }
                let fresh_params: Vec<Type> =
                    params.iter().map(|p| substitute(p, &mapping)).collect();
                let fresh_ret = substitute(&ret, &mapping);
                fn_ty(fresh_params, fresh_ret)
            } else {
                d.push_error(Diagnostic::new(
                    UndeclaredVariable,
                    expr.span,
                    format!("undeclared variable '{}'", name),
                ));
                return error_ty();
            }
        }
        ExprKind::FieldAccess(target, field) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved == Type::Error {
                return error_ty();
            }
            let struct_ty = match &resolved {
                Type::Ref(_, _, inner) => subst.resolve(inner),
                other => other.clone(),
            };
            if let Type::Custom(struct_name, _, args) = struct_ty {
                if let Some(s_decl) = env.structs.get(&struct_name).cloned() {
                    if let Some(f) = s_decl
                        .fields
                        .iter()
                        .find(|field_decl| field_decl.name == *field)
                    {
                        match build_subst_map(
                            &struct_name,
                            &s_decl.type_params,
                            &args,
                            expr.span,
                            d,
                        ) {
                            Some(mapping) => substitute(&f.ty, &mapping),
                            None => return error_ty(),
                        }
                    } else {
                        d.push_error(Diagnostic::new(
                            NoSuchField,
                            target.span,
                            format!("struct '{}' has no field '{}'", struct_name, field),
                        ));
                        return error_ty();
                    }
                } else {
                    d.push_error(Diagnostic::new(
                        UndeclaredStruct,
                        target.span,
                        format!("undeclared struct '{}'", struct_name),
                    ));
                    return error_ty();
                }
            } else {
                d.push_error(Diagnostic::new(
                    ExpectedStruct,
                    target.span,
                    format!("expected struct type, found {}", resolved),
                ));
                return error_ty();
            }
        }
        ExprKind::Cast(target, to_ty) => {
            let from_ty = infer_inner(env, subst, target, types, d);
            let from_resolved = subst.resolve(&from_ty);
            if from_resolved == Type::Error {
                return error_ty();
            }
            let scope = env.current_type_params.clone();
            env.validate_type(to_ty, &scope, expr.span, d);
            if !is_cast_supported(&from_resolved, to_ty) {
                d.push_error(Diagnostic::new(
                    HllTypeCheckCode::InvalidCast,
                    expr.span,
                    format!("cast from {} to {} is not supported", from_resolved, to_ty),
                ));
                return error_ty();
            }
            to_ty.clone()
        }
        ExprKind::Deref(target) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if resolved == Type::Error {
                return error_ty();
            }
            match resolved {
                Type::Ref(_, _, inner) => *inner,
                Type::RawPtr(inner) => {
                    if !env.in_unsafe {
                        d.push_error(Diagnostic::new(
                            HllTypeCheckCode::UnsafeRequired,
                            expr.span,
                            "dereference of raw pointer requires unsafe block".to_string(),
                        ));
                    }
                    *inner
                }
                other => {
                    d.push_error(Diagnostic::new(
                        ExpectedPointer,
                        target.span,
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
        ExprKind::Call(fn_expr, args) => {
            if let ExprKind::Variable(ref name) = fn_expr.kind {
                if let Some((_, _, is_unsafe)) = env.functions.get(name) {
                    if *is_unsafe && !env.in_unsafe {
                        d.push_error(Diagnostic::new(
                            HllTypeCheckCode::UnsafeRequired,
                            fn_expr.span,
                            format!("call to unsafe function '{}' requires unsafe block", name),
                        ));
                    }
                }
            }
            let fn_ty = infer_inner(env, subst, fn_expr, types, d);
            let resolved = subst.resolve(&fn_ty);
            if resolved == Type::Error {
                return error_ty();
            }
            if let Type::Fn(param_tys, ret_ty) = resolved {
                if param_tys.len() != args.len() {
                    d.push_error(Diagnostic::new(
                        ArityMismatch,
                        expr.span,
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
                d.push_error(Diagnostic::new(
                    ExpectedFunction,
                    expr.span,
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
            for stmt in stmts {
                match stmt {
                    Stmt::Let {
                        is_mut: _,
                        name,
                        ty,
                        init,
                        span,
                    } => {
                        let var_ty = match (ty, init) {
                            (Some(annotated_ty), Some(init)) => {
                                let scope = env.current_type_params.clone();
                                env.validate_type(annotated_ty, &scope, *span, d);
                                check_inner(env, subst, init, annotated_ty, types, d);
                                annotated_ty.clone()
                            }
                            (Some(annotated_ty), None) => {
                                let scope = env.current_type_params.clone();
                                env.validate_type(annotated_ty, &scope, *span, d);
                                annotated_ty.clone()
                            }
                            (None, Some(init)) => infer_inner(env, subst, init, types, d),
                            (None, None) => {
                                d.push_error(Diagnostic::new(
                                    HllTypeCheckCode::AmbiguousType,
                                    *span,
                                    "let binding without initializer requires an explicit type annotation",
                                ));
                                error_ty()
                            }
                        };
                        env.insert_var(name.clone(), var_ty);
                    }
                    Stmt::Defer { body, span: _ } => {
                        let body_ty = infer_inner(env, subst, body, types, d);
                        if let Err(e) = subst.unify(&body_ty, &unit_ty()) {
                            d.push_error(e.to_diag(body.span));
                        }
                    }
                    Stmt::Expr(e) => {
                        infer_inner(env, subst, e, types, d);
                    }
                }
            }
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
                d.push_error(e.to_diag(expr.span));
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
        ExprKind::Continue => Type::Never,
        ExprKind::Return(val_expr) => {
            let ret_ty = env.current_ret_ty.clone().unwrap_or_else(unit_ty);
            if let Some(val) = val_expr {
                check_inner(env, subst, val, &ret_ty, types, d);
            } else {
                if let Err(e) = subst.unify(&ret_ty, &unit_ty()) {
                    d.push_error(e.to_diag(expr.span));
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
            if resolved == Type::Error {
                return error_ty();
            }
            if let Type::Custom(enum_name, _, args) = resolved {
                let e_decl = match env.enums.get(&enum_name).cloned() {
                    Some(decl) => decl,
                    None => {
                        d.push_error(Diagnostic::new(
                            UndeclaredEnum,
                            expr.span,
                            format!("undeclared enum '{}'", enum_name),
                        ));
                        return error_ty();
                    }
                };
                let mapping =
                    match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.span, d) {
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
                        d.push_error(Diagnostic::new(
                            NoSuchVariant,
                            expr.span,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        ));
                        // Continue checking remaining arms
                        arm_tys.push(error_ty());
                    }
                }
                if arm_tys.is_empty() {
                    d.push_error(Diagnostic::new(
                        EmptySwitch,
                        expr.span,
                        "empty switch expression",
                    ));
                    return error_ty();
                }
                let first_ty = arm_tys[0].clone();
                for ty in &arm_tys[1..] {
                    if let Err(e) = subst.unify(&first_ty, ty) {
                        d.push_error(e.to_diag(expr.span));
                    }
                }
                subst.resolve(&first_ty)
            } else {
                d.push_error(Diagnostic::new(
                    ExpectedEnum,
                    expr.span,
                    format!("expected enum type for switch target, found {}", resolved),
                ));
                return error_ty();
            }
        }
        ExprKind::StructConstr(name, fields) => {
            let s_decl = match env.structs.get(name).cloned() {
                Some(decl) => decl,
                None => {
                    d.push_error(Diagnostic::new(
                        UndeclaredStruct,
                        expr.span,
                        format!("undeclared struct '{}'", name),
                    ));
                    return error_ty();
                }
            };

            if fields.len() != s_decl.fields.len() {
                d.push_error(Diagnostic::new(
                    StructFieldCountMismatch,
                    expr.span,
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
                    d.push_error(Diagnostic::new(
                        MissingField,
                        expr.span,
                        format!(
                            "missing field '{}' in constructor for '{}'",
                            f_decl.name, name
                        ),
                    ));
                    return error_ty();
                };
                if matches.next().is_some() {
                    d.push_error(Diagnostic::new(
                        DuplicateField,
                        expr.span,
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
                    d.push_error(Diagnostic::new(
                        UndeclaredEnum,
                        expr.span,
                        format!("undeclared enum '{}'", enum_name),
                    ));
                    return error_ty();
                }
            };

            let variant_decl = match e_decl.variants.iter().find(|v| v.name == *variant_name) {
                Some(v) => v.clone(),
                None => {
                    d.push_error(Diagnostic::new(
                        NoSuchVariant,
                        expr.span,
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
                array_ty(first_ty, elements.len())
            }
        }
        ExprKind::ArrayIndex(arr, idx) => {
            let arr_ty = infer_inner(env, subst, arr, types, d);
            let resolved = subst.resolve(&arr_ty);
            if resolved == Type::Error {
                return error_ty();
            }
            if let Type::Array(inner, _) = resolved {
                let idx_ty = infer_inner(env, subst, idx, types, d);
                let idx_resolved = subst.resolve(&idx_ty);
                match idx_resolved {
                    Type::Int(_) => {}
                    Type::Var(_) | Type::IntVar(_) => {
                        if let Err(e) =
                            subst.unify(&idx_resolved, &Type::Int(crate::mir::ast::IntTy::I64))
                        {
                            d.push_error(e.to_diag(expr.span));
                        }
                    }
                    Type::Error => {}
                    other => {
                        d.push_error(Diagnostic::new(
                            ArrayIndexNotInt,
                            idx.span,
                            format!("array index must be an integer, found {}", other),
                        ));
                        return error_ty();
                    }
                }
                *inner
            } else {
                d.push_error(Diagnostic::new(
                    ExpectedArray,
                    arr.span,
                    format!("expected array type, found {}", resolved),
                ));
                return error_ty();
            }
        }
    };

    types.insert(expr.span, ty.clone());
    ty
}

fn check_inner(
    env: &mut TypeEnv,
    subst: &mut Subst,
    expr: &Expr,
    expected: &Type,
    types: &mut IndexMap<Span, Type>,
    d: &mut Diagnostics,
) {
    let resolved_expected = subst.resolve(expected);
    match (&expr.kind, &resolved_expected) {
        (ExprKind::Block(stmts, last_expr, is_unsafe), expected_ty) => {
            let old_unsafe = env.in_unsafe;
            if *is_unsafe {
                env.in_unsafe = true;
            }
            env.push_scope();
            for stmt in stmts {
                match stmt {
                    Stmt::Let {
                        is_mut: _,
                        name,
                        ty,
                        init,
                        span,
                    } => {
                        let var_ty = match (ty, init) {
                            (Some(annotated_ty), Some(init)) => {
                                check_inner(env, subst, init, annotated_ty, types, d);
                                annotated_ty.clone()
                            }
                            (Some(annotated_ty), None) => annotated_ty.clone(),
                            (None, Some(init)) => infer_inner(env, subst, init, types, d),
                            (None, None) => {
                                d.push_error(Diagnostic::new(
                                    HllTypeCheckCode::AmbiguousType,
                                    *span,
                                    "let binding without initializer requires an explicit type annotation",
                                ));
                                error_ty()
                            }
                        };
                        env.insert_var(name.clone(), var_ty);
                    }
                    Stmt::Defer { body, span: _ } => {
                        check_no_control_flow(body, 0, d);
                        let body_ty = infer_inner(env, subst, body, types, d);
                        if let Err(e) = subst.unify(&body_ty, &unit_ty()) {
                            d.push_error(e.to_diag(body.span));
                        }
                    }
                    Stmt::Expr(e) => {
                        infer_inner(env, subst, e, types, d);
                    }
                }
            }
            let errors_before = d.error_count();
            if let Some(last) = last_expr {
                check_inner(env, subst, last, expected_ty, types, d);
            } else {
                if let Err(e) = subst.unify(expected_ty, &unit_ty()) {
                    d.push_error(e.to_diag(expr.span));
                }
            }
            env.pop_scope();
            env.in_unsafe = old_unsafe;
            if d.error_count() == errors_before {
                types.insert(expr.span, resolved_expected.clone());
            }
        }
        (ExprKind::If(cond, true_block, false_block), expected_ty) => {
            check_inner(env, subst, cond, &bool_ty(), types, d);
            check_inner(env, subst, true_block, expected_ty, types, d);
            check_inner(env, subst, false_block, expected_ty, types, d);
            types.insert(expr.span, resolved_expected.clone());
        }
        (ExprKind::Match(target, arms), expected_ty) => {
            let target_ty = infer_inner(env, subst, target, types, d);
            let resolved = subst.resolve(&target_ty);
            if let Type::Custom(enum_name, _, args) = resolved {
                let e_decl = match env.enums.get(&enum_name).cloned() {
                    Some(decl) => decl,
                    None => {
                        d.push_error(Diagnostic::new(
                            UndeclaredEnum,
                            expr.span,
                            format!("undeclared enum '{}'", enum_name),
                        ));
                        return;
                    }
                };
                let mapping =
                    match build_subst_map(&enum_name, &e_decl.type_params, &args, expr.span, d) {
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
                        check_inner(env, subst, body, expected_ty, types, d);
                        env.pop_scope();
                    } else {
                        d.push_error(Diagnostic::new(
                            NoSuchVariant,
                            expr.span,
                            format!("enum '{}' has no variant '{}'", enum_name, variant),
                        ));
                    }
                }
                types.insert(expr.span, resolved_expected.clone());
            } else {
                d.push_error(Diagnostic::new(
                    ExpectedEnum,
                    expr.span,
                    format!("expected enum type for switch target, found {}", resolved),
                ));
            }
        }
        (ExprKind::Literal(Literal::Int(_val, None)), Type::Int(_ty)) => {
            types.insert(expr.span, resolved_expected.clone());
        }
        (ExprKind::Literal(Literal::Float(_val, None)), Type::Float(_ty)) => {
            types.insert(expr.span, resolved_expected.clone());
        }
        (ExprKind::Array(elements), Type::Array(expected_elem, expected_size)) => {
            if elements.len() != *expected_size {
                d.push_error(Diagnostic::new(
                    ArrayLengthMismatch,
                    expr.span,
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
            types.insert(expr.span, resolved_expected.clone());
        }

        _ => {
            let inferred = infer_inner(env, subst, expr, types, d);
            if let Err(e) = subst.unify(&inferred, &resolved_expected) {
                d.push_error(e.to_diag(expr.span));
            }
            types.insert(expr.span, resolved_expected.clone());
        }
    }
}

fn check_no_control_flow(expr: &Expr, loop_depth: usize, d: &mut Diagnostics) {
    match &expr.kind {
        ExprKind::Break(_) => {
            if loop_depth == 0 {
                d.push_error(Diagnostic::new(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.span,
                    "break is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Continue => {
            if loop_depth == 0 {
                d.push_error(Diagnostic::new(
                    HllTypeCheckCode::ControlFlowInDefer,
                    expr.span,
                    "continue is not allowed inside defer".to_string(),
                ));
            }
        }
        ExprKind::Return(_) => {
            d.push_error(Diagnostic::new(
                HllTypeCheckCode::ControlFlowInDefer,
                expr.span,
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
        ExprKind::Call(callee, args) => {
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
    use crate::hll::parser::Parser;

    fn check_program(source: &str) -> Result<(), String> {
        let program = Parser::new(source)
            .parse()
            .map_err(|d| d.errors_str().join("\n"))?;
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
