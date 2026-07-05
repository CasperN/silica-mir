#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Markers {
    pub copy: bool,
    pub drop: bool,
}

/// Source position (1-based line and column) of the syntax that a node
/// represents. Used to prefix error messages with `at L:C:`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefKind {
    Shared,   // &
    Mut,      // &mut
    Out,      // &out
    Drop,     // &drop
    Uninit,   // &uninit
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Number,
    Boolean,
    Unit,
    Custom(String), // struct or enum type reference
    Fn(Vec<Type>),
    Ref(RefKind, Box<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Place {
    Var(String),
    Field(Box<Place>, String),
    Downcast(Box<Place>, String),
    Deref(Box<Place>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstVal {
    Number(u64),
    Boolean(bool),
    Unit,
    FnName(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(ConstVal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RValue {
    Use(Operand),
    Ref(RefKind, Place),
    EnumConstr(String, String, Operand), // EnumName, VariantName, payload
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, RValue),
    Call(Operand, Vec<Operand>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    Goto(String),
    Return,
    Branch {
        cond: Operand,
        true_label: String,
        false_label: String,
    },
    SwitchEnum {
        place: Place,
        cases: Vec<(String, String)>, // (Variant, Label)
    },
    Abort,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub label: String,
    pub label_span: Span,
    pub statements: Vec<(Statement, Span)>,
    pub terminator: Terminator,
    pub terminator_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionBody {
    pub locals: Vec<Local>,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub name_span: Span,
    pub is_extern: bool,
    pub params: Vec<Param>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDecl {
    pub name: String,
    pub name_span: Span,
    pub markers: Markers,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: String,
    pub name_span: Span,
    pub markers: Markers,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declaration {
    Struct(StructDecl),
    Enum(EnumDecl),
    Fn(Function),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Declaration>,
}
