use crate::mir::ast::{IntTy, FloatTy, RefKind, Span, Markers};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Unit,
    Never,
    /// Struct or enum reference. `args` is the list of type
    /// arguments — empty for non-generic decls (`Foo`), non-empty
    /// for instantiations of generic decls (`Foo<T, U>`).
    Custom(String, Vec<Type>),
    /// A reference to a generic type parameter declared on the
    /// enclosing decl. Named parameter, not a solver metavariable —
    /// unifies only with itself or with a `Var`, never substituted.
    Param(String),
    Ref(RefKind, Box<Type>),
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
            Type::Custom(name, args) => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", a)?;
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
            Type::Param(name) => write!(f, "{}", name),
            Type::Ref(kind, inner) => {
                let kind_str = match kind {
                    RefKind::Shared => "&",
                    RefKind::Mut => "&mut ",
                    RefKind::Out => "&out ",
                    RefKind::Drop => "&drop ",
                    RefKind::Uninit => "&uninit ",
                };
                if *kind == RefKind::Shared {
                    write!(f, "& {}", inner)
                } else {
                    write!(f, "{}{}", kind_str, inner)
                }
            }
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
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    pub body: Expr,
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Literal(Literal),
    Variable(String),
    FieldAccess(Box<Expr>, String),
    Downcast(Box<Expr>, String),
    Deref(Box<Expr>),
    Borrow(RefKind, Box<Expr>),
    RawBorrow(Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Block(Vec<Stmt>, Option<Box<Expr>>),
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
        init: Expr,
        span: Span,
    },
    Defer {
        body: Expr,
        span: Span,
    },
    Expr(Expr),
}
