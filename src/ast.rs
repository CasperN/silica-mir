#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Markers {
    pub copy: bool,
    pub drop: bool,
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
    Struct(String),
    Enum(String),
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
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionBody {
    pub locals: Vec<(String, Type)>,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub is_extern: bool,
    pub params: Vec<(String, Type)>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDecl {
    pub name: String,
    pub markers: Markers,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: String,
    pub markers: Markers,
    pub variants: Vec<(String, Type)>,
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
