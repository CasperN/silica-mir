use crate::common::{
    FloatTy, GeneratedKind, IntTy, Lifetime, LifetimeParam, Markers, OutlivesBound, RefKind,
    SourceInfo, Span,
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
    Unit,
    Never,
    /// Struct or enum reference. See [`Instance`] for the shape.
    Custom(Instance),
    /// A reference to a generic type parameter declared on the
    /// enclosing decl. Named parameter, not a solver metavariable —
    /// unifies only with itself or with a `Var`, never substituted.
    Param(String),
    Ref(RefKind, Option<Lifetime>, Box<Type>),
    RawPtr(Box<Type>),
    Fn(Vec<Type>, Box<Type>),
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
            TypeKind::Unit => write!(f, "unit"),
            TypeKind::Never => write!(f, "never"),
            TypeKind::Custom(inst) => inst.fmt(f),
            TypeKind::Param(name) => write!(f, "{}", name),
            TypeKind::Ref(kind, lt, inner) => match lt {
                Some(lt) => write!(f, "{} {} {}", kind, lt, inner),
                None => write!(f, "{} {}", kind, inner),
            },
            TypeKind::RawPtr(inner) => write!(f, "*{}", inner),
            TypeKind::Fn(params, ret) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")?;
                if ret.kind != TypeKind::Unit {
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
/// `markers` carries the compiler-internal substructural vocabulary
/// (Copy/Drop/Move); `traits` carries user-declared trait bounds as
/// `Instance` values — trait references share the type-reference shape
/// (name + lifetime args + type args), and until trait bounds grow
/// bound-specific state a plain `Vec<Instance>` says everything.
/// Empty today; populated once trait-decl syntax lands.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Bounds {
    pub markers: Markers,
    pub traits: Vec<Instance>,
}

impl Bounds {
    pub fn from_markers(markers: Markers) -> Self {
        Self {
            markers,
            traits: Vec::new(),
        }
    }
}

/// Generic type parameter declared on a struct/enum/fn. Bounds are
/// unconditional markers plus (later) trait references (`T: Copy + Iter`).
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
    pub is_unsafe: bool,
    /// ABI string. `None` = Silica ABI (sret via `&out $return`);
    /// `Some("C")` = C ABI (register return). Additional ABI strings
    /// may be added later (`"system"`, `"fastcall"`, ...); the type
    /// checker rejects unknown strings so lowering can trust it.
    pub abi: Option<String>,
    /// Source attribution of the ABI string literal (including the quotes),
    /// if present.
    /// Used by the type checker to point diagnostics at just `"..."` on
    /// an unknown ABI rather than at the whole `extern fn` declaration.
    pub abi_source: Option<SourceInfo>,
    pub lifetime_params: Vec<LifetimeParam>,
    /// Inline outlives axioms declared on the fn's lifetime params
    /// (`fn<'a, 'b: 'a>`). Each `(subject, must_outlive)` pair is
    /// copied through to `DeclMeta::outlives` at lowering; the
    /// lifetime checker consumes it as a signature axiom.
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    /// `None` for extern declarations (signature only). Downstream
    /// passes branch on this rather than on a separate ExternFn
    /// variant; keeping extern-ness as a modifier of the same node
    /// leaves room for other modifiers (`co`, ABI variants, ...) to
    /// slot in without a full-item split.
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
pub enum Declaration {
    Struct(StructDecl),
    Enum(EnumDecl),
    Fn(FnDecl),
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
    Unit,
    ByteStr(Vec<u8>),
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
    Call(Box<Expr>, GenericArgs, Vec<Expr>),
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
    Array(Vec<Expr>),
    ArrayIndex(Box<Expr>, Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    Unary(UnOp, Box<Expr>),
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
