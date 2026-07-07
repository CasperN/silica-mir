use indexmap::IndexMap;

/// Substructural markers declared on a struct/enum. Independent flags:
/// - `copy`: values may be bitwise duplicated (Copy).
/// - `drop`: values may be forgotten in place (Drop).
/// - `mov`: values may be bitwise relocated (Move). Named `mov` because
///   `move` is a Rust keyword.
///
/// The "effective" Move class is `mov || (copy && drop)` — declaring
/// both Copy and Drop is enough; explicit Move is only needed for
/// types that aren't Copy+Drop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Markers {
    pub copy: bool,
    pub drop: bool,
    pub mov: bool,
}

impl Markers {
    /// Effective Move class: declared Move, or Copy AND Drop.
    pub fn effective_move(&self) -> bool {
        self.mov || (self.copy && self.drop)
    }
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
    Shared, // &
    Mut,    // &mut
    Out,    // &out
    Drop,   // &drop
    Uninit, // &uninit
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Var(String),
    Field(Box<Place>, String),
    Downcast(Box<Place>, String),
    Deref(Box<Place>),
}

/// A single projection step from a root Var. Used by analyses that need to
/// walk down a Place chain uniformly. `Deref` steps only appear in paths
/// returned by [`extract_path_with_deref`]; the plain [`extract_path`] bails
/// on Deref since analyses that use it (init-state locals tracking, variant
/// flow) can't reason across reference boundaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathStep {
    Field(String),
    Downcast(String),
    Deref,
}

/// Extract `(root_var, projection_steps)` from `place`, returning `None` if
/// the chain passes through a `Deref`. Use this when your analysis only
/// makes sense on paths rooted in a concrete local — moving through a ref
/// would break the abstraction.
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

/// True if `place` is an *owned path* — a chain of Field/Downcast steps
/// rooted in a Var, no Deref. Used as an invariant on RefState/loan
/// keys: a reference physically lives in a place we can name (a local,
/// or a nested field of a local).
pub fn is_owned_path(place: &Place) -> bool {
    match place {
        Place::Var(_) => true,
        Place::Field(inner, _) | Place::Downcast(inner, _) => is_owned_path(inner),
        Place::Deref(_) => false,
    }
}

/// If `place` is an owned path (no Deref anywhere), return it as an
/// owned Place clone. Used to canonicalize the LHS of a borrow assign
/// or an ancestor path when cascading through consumption.
pub fn as_owned_path(place: &Place) -> Option<Place> {
    if is_owned_path(place) {
        Some(place.clone())
    } else {
        None
    }
}

/// Iterate all owned-path prefixes of `place`, longest first. If
/// `place` is `b.p.q`, yields `b.p.q`, `b.p`, `b`. If `place` contains
/// a `Deref` anywhere, stops at the innermost Deref boundary — the
/// prefixes above the Deref aren't owned paths in the local frame.
pub fn owned_path_prefixes(place: &Place) -> Vec<Place> {
    let mut out = Vec::new();
    let mut cur = place.clone();
    loop {
        if !is_owned_path(&cur) {
            return out;
        }
        out.push(cur.clone());
        match cur {
            Place::Var(_) => return out,
            Place::Field(inner, _) | Place::Downcast(inner, _) => {
                cur = *inner;
            }
            Place::Deref(_) => unreachable!("filtered above"),
        }
    }
}

/// Extract `(root_var, projection_steps)` including `Deref` steps in the
/// path. Used by the lifetime pass so a loan on `*r` can be tracked as
/// (root=r, path=[Deref]) and prefix-compared against `r`, `*r`, `(*r).f`,
/// etc. Always returns `Some` (every place has a root Var).
pub fn extract_path_with_deref(place: &Place) -> (String, Vec<PathStep>) {
    let mut steps = Vec::new();
    let mut cur = place;
    loop {
        match cur {
            Place::Var(name) => {
                steps.reverse();
                return (name.clone(), steps);
            }
            Place::Field(inner, f) => {
                steps.push(PathStep::Field(f.clone()));
                cur = inner;
            }
            Place::Downcast(inner, v) => {
                steps.push(PathStep::Downcast(v.clone()));
                cur = inner;
            }
            Place::Deref(inner) => {
                steps.push(PathStep::Deref);
                cur = inner;
            }
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
        Terminator::Branch {
            true_label,
            false_label,
            ..
        } => {
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
    /// Legal only on Drop places (enforced by the substructural
    /// checker, not here).
    Drop(Place),
    /// Explicitly end a reference's loan. Requires the referenced place
    /// to hold a bound reference with its (cur, post) obligation
    /// fulfilled (cur == post). After: the borrower is consumed and its
    /// loan is removed. Inserted by `lifetime::elaboration` at last-use
    /// points; the checker just observes the marker.
    Unborrow(Place),
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
    pub fn blocks_by_label(&self) -> IndexMap<&str, &BasicBlock> {
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

impl Function {
    /// Build a `name -> type` map from the function's parameters and (if
    /// present) its body's locals. Iteration follows declaration order:
    /// params, then locals. Used by every analysis pass that needs to
    /// look up the type of a place-root.
    pub fn locals_map(&self) -> IndexMap<String, Type> {
        let mut m = IndexMap::new();
        for p in &self.params {
            m.insert(p.name.clone(), p.ty.clone());
        }
        if let Some(body) = &self.body {
            for l in &body.locals {
                m.insert(l.name.clone(), l.ty.clone());
            }
        }
        m
    }
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
