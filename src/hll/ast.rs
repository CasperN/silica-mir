pub use crate::common::{
    Abi, FloatTy, GeneratedKind, IntTy, Lifetime, LifetimeParam, Linkage, Markers, OutlivesBound,
    RefKind, SourceInfo, Span,
};

/// An HLL type with the source syntax or compiler operation that produced it.
/// Provenance is diagnostic metadata and does not participate in type identity.
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub source: SourceInfo,
}

impl Type {
    pub fn new(kind: TypeKind, source: SourceInfo) -> Self {
        Self { kind, source }
    }

    /// Construct a compiler-synthesized type with no meaningful source
    /// attribution. Parsed types and transformations with an attribution
    /// should use [`Type::new`] instead.
    pub fn synthesized(kind: TypeKind) -> Self {
        Self::new(
            kind,
            SourceInfo::generated(GeneratedKind::TypeSynthesis, Span::default()),
        )
    }

    pub fn span(&self) -> Span {
        self.source.span()
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Type {}

/// Named use-site instantiation of a generic decl: `Foo<'a, 'b, T, U>`.
/// HLL-side twin of `mir::Instance`; distinct because it holds
/// `hll::Type` (which can contain inference variables).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    pub name: String,
    pub lifetime_args: Vec<Lifetime>,
    pub type_args: Vec<Type>,
}

impl Instance {
    pub fn new(
        name: impl Into<String>,
        lifetime_args: Vec<Lifetime>,
        type_args: Vec<Type>,
    ) -> Self {
        Self {
            name: name.into(),
            lifetime_args,
            type_args,
        }
    }

    pub fn bare(name: impl Into<String>) -> Self {
        Self::new(name, Vec::new(), Vec::new())
    }
}

impl std::fmt::Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.lifetime_args.is_empty() || !self.type_args.is_empty() {
            write!(f, "<")?;
            let mut first = true;
            for lt in &self.lifetime_args {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "{}", lt)?;
            }
            for a in &self.type_args {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "{}", a)?;
            }
            write!(f, ">")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    /// Tuple type: `()` (0-tuple), `(T,)` (1-tuple), `(T1, T2)` (N-tuple).
    Tuple(Vec<Type>),
    Never,
    /// Struct or enum reference. See [`Instance`] for the shape.
    Custom(Instance),
    /// A reference to a generic type parameter declared on the
    /// enclosing decl. Named parameter, not a solver metavariable —
    /// unifies only with itself or with a `Var`, never substituted.
    Param(String),
    Ref(RefKind, Option<Lifetime>, Box<Type>),
    RawPtr(Box<Type>),
    Fn {
        abi: Abi,
        params: Vec<Type>,
        ret: Box<Type>,
    },
    Var(usize),
    IntVar(usize),
    FloatVar(usize),
    Error,
    Array(Box<Type>, u64),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Int(t) => write!(f, "{}", t.name()),
            TypeKind::Float(t) => write!(f, "{}", t.name()),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Tuple(types) => {
                write!(f, "(")?;
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", t)?;
                }
                if types.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            TypeKind::Never => write!(f, "never"),
            TypeKind::Custom(inst) => inst.fmt(f),
            TypeKind::Param(name) => write!(f, "{}", name),
            TypeKind::Ref(kind, lifetime, inner) => {
                kind.write_type_prefix(f, lifetime.as_ref())?;
                inner.fmt(f)
            }
            TypeKind::RawPtr(inner) => write!(f, "*{}", inner),
            TypeKind::Fn { abi, params, ret } => {
                write!(f, "fn")?;
                let abi_str = abi.as_str();
                if !abi_str.is_empty() {
                    write!(f, " {}", abi_str)?;
                }
                write!(f, "(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")?;
                if !matches!(&ret.kind, TypeKind::Tuple(elems) if elems.is_empty()) {
                    write!(f, " -> {}", ret)?;
                }
                Ok(())
            }
            TypeKind::Var(id) => write!(f, "?{}", id),
            TypeKind::IntVar(id) => write!(f, "?i{}", id),
            TypeKind::FloatVar(id) => write!(f, "?f{}", id),
            TypeKind::Error => write!(f, "<error>"),
            TypeKind::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub source: SourceInfo,
}

impl Param {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

/// Everything a type-parameter binder promises about its parameter.
/// Trait references share the type-reference shape: name plus lifetime and
/// type arguments.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Bounds {
    pub markers: Markers,
    pub traits: Vec<TraitBound>,
}

#[derive(Debug, Clone)]
pub struct TraitBound {
    pub trait_path: Instance,
    pub source: SourceInfo,
}

impl PartialEq for TraitBound {
    fn eq(&self, other: &Self) -> bool {
        self.trait_path == other.trait_path
    }
}

impl Eq for TraitBound {}

impl Bounds {
    pub fn from_markers(markers: Markers) -> Self {
        Self {
            markers,
            traits: Vec::new(),
        }
    }
}

/// Generic type parameter declared on a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParam {
    pub name: String,
    pub bounds: Bounds,
    pub source: SourceInfo,
}

impl TypeParam {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: String,
    pub linkage: Linkage,
    pub abi: Abi,
    pub is_unsafe: bool,
    pub lifetime_params: Vec<LifetimeParam>,
    /// Inline outlives axioms declared on the fn's lifetime params
    /// (`fn<'a, 'b: 'a>`). Each `(subject, must_outlive)` pair is
    /// copied through to `DeclMeta::outlives` at lowering; the
    /// lifetime checker consumes it as a signature axiom.
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    /// Body of a Local function. `None` on a Foreign declaration
    /// (extern) and on trait method signatures. The structural check
    /// enforces which combinations are legal in each context.
    pub body: Option<Expr>,
    pub source: SourceInfo,
}

impl FnDecl {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub source: SourceInfo,
}

impl StructField {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDecl {
    pub name: String,
    pub lifetime_params: Vec<LifetimeParam>,
    /// Inline outlives axioms on the struct's lifetime params
    /// (`struct<'a, 'b: 'a> Wrap { ... }`). Copied through to the
    /// MIR side at lowering.
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub markers: Markers,
    pub fields: Vec<StructField>,
    pub source: SourceInfo,
}

impl StructDecl {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: String,
    pub ty: Type,
    pub source: SourceInfo,
}

impl EnumVariant {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: String,
    pub lifetime_params: Vec<LifetimeParam>,
    /// Inline outlives axioms on the enum's lifetime params
    /// (`enum<'a, 'b: 'a> E { ... }`). Copied through to the MIR
    /// side at lowering.
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub markers: Markers,
    pub variants: Vec<EnumVariant>,
    pub source: SourceInfo,
}

impl EnumDecl {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDecl {
    pub name: String,
    pub lifetime_params: Vec<LifetimeParam>,
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub self_bounds: Bounds,
    pub methods: Vec<FnDecl>,
    pub source: SourceInfo,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplBlock {
    pub lifetime_params: Vec<LifetimeParam>,
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub trait_path: Option<Instance>,
    pub target: Type,
    pub methods: Vec<FnDecl>,
    pub source: SourceInfo,
}

/// User-facing identity of a method nested in an impl block. Method names are
/// not globally unique, so diagnostics must retain both the target type and,
/// for trait impls, the implemented trait path.
pub fn impl_method_context(
    target: &Type,
    trait_path: Option<&Instance>,
    method_name: &str,
) -> String {
    match trait_path {
        Some(trait_path) => format!("<{} as {}>::{}", target, trait_path, method_name),
        None => format!("<{}>::{}", target, method_name),
    }
}

/// User-facing identity of a method signature nested in a trait declaration.
pub fn trait_method_context(trait_name: &str, method_name: &str) -> String {
    format!("{}::{}", trait_name, method_name)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    Struct(StructDecl),
    Enum(EnumDecl),
    Fn(FnDecl),
    Trait(TraitDecl),
    Impl(ImplBlock),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub declarations: Vec<Declaration>,
    pub source: std::sync::Arc<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(u64, Option<IntTy>),
    Float(f64, Option<FloatTy>),
    Bool(bool),
    /// The empty tuple `()`.
    Tuple,
    ByteStr(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallTarget {
    /// An ordinary callee expression, including an explicitly parenthesized
    /// function-valued field such as `(value.callback)(arg)`.
    Expr(Box<Expr>),
    /// Unresolved `receiver.name(args)` syntax. Type checking may resolve this
    /// to a method, a callable field, or free-function UFCS.
    Receiver {
        receiver: Box<Expr>,
        method: String,
        method_source: SourceInfo,
        selector_source: SourceInfo,
    },
    /// Explicit method selection. Unlike receiver syntax, argument zero is
    /// written in the call's ordinary argument list.
    Qualified {
        self_ty: Type,
        trait_path: Option<Instance>,
        method: String,
        method_source: SourceInfo,
        selector_source: SourceInfo,
    },
    /// Scoped path call: `Target::member(args...)` or `Target<T>::member(args...)`.
    /// May resolve to an enum constructor, inherent static method, or trait static method.
    Path {
        target: Type,
        member: String,
        member_source: SourceInfo,
        selector_source: SourceInfo,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Literal(Literal),
    Variable(String),
    FieldAccess(Box<Expr>, String),
    /// `expr as Type` — numeric cast. Enum downcasts have no HLL
    /// surface (MIR has them; HLL uses `match` for exhaustive variant
    /// inspection).
    Cast(Box<Expr>, Type),
    Deref(Box<Expr>),
    Borrow(RefKind, Box<Expr>),
    RawBorrow(Box<Expr>),
    Call(CallTarget, GenericArgs, Vec<Expr>),
    Path(Type, String),
    Block(Vec<Stmt>, Option<Box<Expr>>, bool), // true if it is an `unsafe { ... }` block
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Loop(Box<Expr>),
    Break(Option<Box<Expr>>),
    Continue,
    Return(Option<Box<Expr>>),
    Assign(Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    StructConstr(String, Vec<(String, Expr)>),
    EnumConstr(String, String, Box<Expr>),
    Lambda {
        params: Vec<LambdaParam>,
        ret_ty: Option<Type>,
        body: Box<Expr>,
    },
    Array(Vec<Expr>),
    ArrayIndex(Box<Expr>, Box<Expr>),
    Tuple(Vec<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    Unary(UnOp, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaParam {
    pub is_mut: bool,
    pub name: String,
    pub ty: Option<Type>,
    pub source: SourceInfo,
}

impl LambdaParam {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Variant(String, Option<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub source: SourceInfo,
}

impl Expr {
    pub fn span(&self) -> Span {
        self.source.span()
    }
}

/// Explicit lifetime and type arguments at a call site: `foo<'a, T>(x)`.
/// Empty when the caller relies on inference (`foo(x)`); non-empty when
/// the caller writes them out to disambiguate or override inference.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct GenericArgs {
    pub lifetimes: Vec<Lifetime>,
    pub types: Vec<Type>,
}

impl GenericArgs {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.lifetimes.is_empty() && self.types.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        is_mut: bool,
        name: String,
        ty: Option<Type>,
        /// `None` = uninitialized (`let p: P;`). Type annotation is
        /// required in that case; the type checker rejects a bare
        /// `let p;` with `HTC-AmbiguousType`.
        init: Option<Expr>,
        source: SourceInfo,
    },
    Defer {
        body: Expr,
        source: SourceInfo,
    },
    Expr(Expr),
}

impl Stmt {
    pub fn span(&self) -> Span {
        match self {
            Stmt::Let { source, .. } | Stmt::Defer { source, .. } => source.span(),
            Stmt::Expr(expr) => expr.span(),
        }
    }
}
