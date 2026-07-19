use crate::common::{FloatTy, IntTy, Lifetime, Markers, RefKind, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Unit,
    Never,
    /// Struct or enum reference. `lifetime_args` + `type_args` are the
    /// two use-site parameter lists. Order is lifetimes-first.
    Custom(String, Vec<Lifetime>, Vec<Type>),
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
    Array(Box<Type>, usize),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int(t) => write!(f, "{}", t.name()),
            Type::Float(t) => write!(f, "{}", t.name()),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "unit"),
            Type::Never => write!(f, "never"),
            Type::Custom(name, lifetimes, args) => {
                write!(f, "{}", name)?;
                if !lifetimes.is_empty() || !args.is_empty() {
                    write!(f, "<")?;
                    let mut first = true;
                    for lt in lifetimes {
                        if !first {
                            write!(f, ", ")?;
                        }
                        first = false;
                        write!(f, "{}", lt)?;
                    }
                    for a in args {
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
            Type::Param(name) => write!(f, "{}", name),
            Type::Ref(kind, lt, inner) => match lt {
                Some(lt) => write!(f, "{} {} {}", kind, lt, inner),
                None => write!(f, "{} {}", kind, inner),
            },
            Type::RawPtr(inner) => write!(f, "*{}", inner),
            Type::Fn(params, ret) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")?;
                if **ret != Type::Unit {
                    write!(f, " -> {}", ret)?;
                }
                Ok(())
            }
            Type::Var(id) => write!(f, "?{}", id),
            Type::IntVar(id) => write!(f, "?i{}", id),
            Type::FloatVar(id) => write!(f, "?f{}", id),
            Type::Error => write!(f, "<error>"),
            Type::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

/// Generic type parameter declared on a struct/enum/fn. Bounds are
/// unconditional markers (`T: Copy + Drop`); conditional bounds are
/// deferred behind this form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParam {
    pub name: String,
    pub bounds: Markers,
    pub span: Span,
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
    /// Span of the ABI string literal (including the quotes), if present.
    /// Used by the type checker to point diagnostics at just `"..."` on
    /// an unknown ABI rather than at the whole `extern fn` declaration.
    pub abi_span: Option<Span>,
    pub lifetime_params: Vec<Lifetime>,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    /// Span of the declared return type in source. When the `-> R` arrow
    /// is omitted (unit return), this falls back to `span` (the whole fn
    /// decl) so callers always have SOMETHING to point at.
    pub ret_ty_span: Span,
    /// `None` for extern declarations (signature only). Downstream
    /// passes branch on this rather than on a separate ExternFn
    /// variant; keeping extern-ness as a modifier of the same node
    /// leaves room for other modifiers (`co`, ABI variants, ...) to
    /// slot in without a full-item split.
    pub body: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDecl {
    pub name: String,
    pub lifetime_params: Vec<Lifetime>,
    pub type_params: Vec<TypeParam>,
    pub markers: Markers,
    pub fields: Vec<StructField>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: String,
    pub lifetime_params: Vec<Lifetime>,
    pub type_params: Vec<TypeParam>,
    pub markers: Markers,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
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
    Int(i64, Option<IntTy>),
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
    Call(Box<Expr>, Vec<Expr>),
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
    pub span: Span,
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
        span: Span,
    },
    Defer {
        body: Expr,
        span: Span,
    },
    Expr(Expr),
}
