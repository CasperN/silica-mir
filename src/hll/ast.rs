use crate::mir::ast::{IntTy, FloatTy, RefKind, Span};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Unit,
    Never,
    Custom(String),
    Ref(RefKind, Box<Type>),
    RawPtr(Box<Type>),
    Fn(Vec<Type>, Box<Type>),
    Var(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: String,
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
    Expr(Expr),
}
