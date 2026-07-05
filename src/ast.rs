use std::collections::HashMap;

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

/// A single projection step from a root Var. Used by analyses that need to
/// walk down a Place chain uniformly.
#[derive(Debug, Clone)]
pub enum PathStep {
    Field(String),
    Downcast(String),
}

/// Extract `(root_var, projection_steps)` from `place`, returning `None` if
/// the chain passes through a `Deref` (we don't follow references at this
/// level).
pub fn extract_path(place: &Place) -> Option<(String, Vec<PathStep>)> {
    let mut steps = Vec::new();
    let mut cur = place;
    loop {
        match cur {
            Place::Var(name) => {
                steps.reverse();
                return Some((name.clone(), steps));
            }
            Place::Field(inner, f) => {
                steps.push(PathStep::Field(f.clone()));
                cur = inner;
            }
            Place::Downcast(inner, v) => {
                steps.push(PathStep::Downcast(v.clone()));
                cur = inner;
            }
            Place::Deref(_) => return None,
        }
    }
}

/// The `Place` referenced by an operand's `copy`/`move`, or `None` for
/// constants.
pub fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p),
        Operand::Const(_) => None,
    }
}

/// Labels of the blocks a terminator flows into. Empty for terminators
/// with no successors (`return`, `abort`, `unreachable`).
pub fn terminator_successors(term: &Terminator) -> Vec<&str> {
    match term {
        Terminator::Goto(label) => vec![label.as_str()],
        Terminator::Return | Terminator::Abort | Terminator::Unreachable => vec![],
        Terminator::Branch { true_label, false_label, .. } => {
            vec![true_label.as_str(), false_label.as_str()]
        }
        Terminator::SwitchEnum { cases, .. } => {
            cases.iter().map(|(_, label)| label.as_str()).collect()
        }
    }
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
    /// Consume a place. In the current MIR this is a bitwise forget; once
    /// user-defined `Drop::drop` exists, this lowers to a call to it.
    /// Legal only on `Drop`-classed places (enforced by the substructural
    /// checker, not here).
    Drop(Place),
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

impl FunctionBody {
    /// Index blocks by label for O(1) lookup during dataflow.
    pub fn blocks_by_label(&self) -> HashMap<&str, &BasicBlock> {
        self.blocks.iter().map(|b| (b.label.as_str(), b)).collect()
    }
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
