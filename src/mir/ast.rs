pub use crate::common::{
    FloatTy, GeneratedKind, HllTemporaryKind, IntTy, Lifetime, LifetimeParam, Marker, Markers,
    OutlivesBound, RefKind, SourceInfo, Span,
};

use indexmap::IndexMap;

/// A MIR type value with source attribution. See [`TypeKind`] for the
/// shape variants. Two types with the same kind but different source metadata
/// compare equal — provenance is for diagnostics, not type identity.
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
    /// attribution.
    /// Parsed types and transformations with a meaningful attribution should
    /// use [`Type::new`] instead.
    pub fn synthesized(kind: TypeKind) -> Self {
        Self {
            kind,
            source: SourceInfo::generated(GeneratedKind::TypeSynthesis, Span::default()),
        }
    }

    pub(crate) fn with_written_span(mut self, span: Span) -> Self {
        self.source = SourceInfo::written(span);
        self
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
impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Type {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.kind.cmp(&other.kind)
    }
}
impl std::hash::Hash for Type {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

/// Named use-site instantiation of a generic decl: `Foo<'a, 'b, T, U>`.
/// Holds the referenced decl's name plus the two argument lists in
/// lifetimes-first order. Both empty for a non-generic reference.
///
/// Load-bearing across every site that names a decl at a use position —
/// `TypeKind::Custom` today, extended to trait references and other
/// generic-instantiation sites as the type system grows.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKind {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Unit,
    Never,
    /// Struct or enum type reference. See [`Instance`] for the shape.
    Custom(Instance),
    /// A reference to a generic type parameter declared on the
    /// enclosing decl (struct/enum/fn). Written as a bare identifier
    /// in source; the parser emits this variant when the name is in
    /// the current decl's type-parameter scope. This is a *named*
    /// parameter, not a solver metavariable — the checker never
    /// substitutes or unifies it. Substructural markers come from the
    /// param's declared bounds. Codegen internal-errors on this
    /// variant; concretization happens at monomorphization time.
    Param(String),
    Fn(Vec<Type>),
    Ref(RefKind, Option<Lifetime>, Box<Type>),
    /// Raw pointer. Aliasing is unrestricted; no loan tracking, no
    /// `(cur, post)` obligation. Deref is unchecked — the caller is
    /// responsible for the pointee's init state and lifetime. The
    /// pointer value itself is `Copy Drop Move`, like `&T`.
    RawPtr(Box<Type>),
    /// Fixed-size array `[T; N]`. Layout is `N * size_of(T)`, align
    /// equals `T`'s align. Element access via `Place::Index`. Init
    /// state is tracked per-slot for constant indices (using slot
    /// numbers as `Partial` keys); dynamic indices cannot name a
    /// specific slot, so state-changing operations through them are
    /// rejected and reads/`&mut`/`&` borrows require uniform init
    /// across all slots.
    Array(Box<Type>, u64),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.kind, f)
    }
}

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeKind::Int(i) => write!(f, "{}", i.name()),
            TypeKind::Float(fl) => write!(f, "{}", fl.name()),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Unit => write!(f, "unit"),
            TypeKind::Never => write!(f, "never"),
            TypeKind::Custom(inst) => inst.fmt(f),
            TypeKind::Param(name) => write!(f, "{}", name),
            TypeKind::Fn(params) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")
            }
            TypeKind::Ref(kind, lt, inner) => match lt {
                Some(lt) => write!(f, "{} {} {}", kind, lt, inner),
                None => write!(f, "{} {}", kind, inner),
            },
            TypeKind::RawPtr(inner) => write!(f, "*{}", inner),
            TypeKind::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Place {
    Var(String),
    Field(Box<Place>, String),
    Downcast(Box<Place>, String),
    Deref(Box<Place>),
    /// Array element access `place[operand]`. The operand is an
    /// arbitrary rvalue-shaped index; analyses that need static
    /// tracking (init state, per-slot loans) inspect the operand
    /// for an integer const and treat it like a numbered field
    /// step. A dynamic (non-const) index has no per-slot identity:
    /// state-changing operations through it are rejected outright,
    /// non-state-changing operations require the containing array
    /// to be uniformly initialized, and loan conflict detection
    /// treats a dynamic index as matching every slot.
    Index(Box<Place>, Box<Operand>),
}

/// A single projection step from a root Var. Used by analyses that need to
/// walk down a Place chain uniformly. `Deref` steps only appear in paths
/// returned by [`extract_path_with_deref`]; the plain [`extract_path`] bails
/// on Deref since analyses that use it (init-state locals tracking, variant
/// flow) can't reason across reference boundaries.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PathStep {
    Field(String),
    Downcast(String),
    Deref,
    /// Array slot access. `Some(k)` = constant slot k; `None` =
    /// dynamic index (unknown slot). `extract_path` returns `None`
    /// if any index step is dynamic — init-state tracking cannot
    /// name a specific slot, so callers requiring a trackable path
    /// bail. `extract_path_with_deref` preserves both forms so loan
    /// conflict detection (`paths_conflict`, `is_ancestor_or_self`)
    /// can treat a dynamic index as matching every slot when
    /// deciding whether an active loan blocks a subsequent access.
    Index(Option<u64>),
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
            Place::Index(inner, op) => {
                // Dynamic (non-const) indices aren't trackable in the
                // locals tree; bail like Deref does.
                let k = const_int_operand(op)?;
                steps.push(PathStep::Index(Some(k)));
                cur = inner;
            }
            Place::Deref(_) => return None,
        }
    }
}

/// If `op` is `Const(Int { bits, ty })` treat its bits as an unsigned
/// slot index (masked to the type's width). Returns `None` for
/// `Copy`/`Move` operands (dynamic index) and non-integer consts.
pub fn const_int_operand(op: &Operand) -> Option<u64> {
    match op {
        Operand::Const(ConstVal::Int { bits, ty }) => {
            let mask: u64 = if ty.bits() == 64 {
                u64::MAX
            } else {
                (1u64 << ty.bits()) - 1
            };
            Some(bits & mask)
        }
        _ => None,
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
        Place::Index(inner, op) => {
            // Dynamic index breaks the owned-path invariant (we can't
            // name a specific slot). Constant index preserves it.
            const_int_operand(op).is_some() && is_owned_path(inner)
        }
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

/// If `key` is `src` or an owned-path descendant of it, return the
/// parallel path under `dst`. `rekey_owned_path(b, y, b.p)` → `y.p`;
/// `rekey_owned_path(b, w as W, b.p)` → `(w as W).p`. Returns `None`
/// if `key` is not below `src`. Both `src` and `key` must be owned
/// paths (no `Deref`); `dst` may contain any projection since we
/// only extend it.
pub fn rekey_owned_path(src: &Place, dst: &Place, key: &Place) -> Option<Place> {
    if !is_ancestor_or_self(src, key) {
        return None;
    }
    let (_, src_path) = extract_path(src).expect("owned-path invariant");
    let (_, key_path) = extract_path(key).expect("owned-path invariant");
    let suffix = &key_path[src_path.len()..];
    let mut out = dst.clone();
    for step in suffix {
        out = match step {
            PathStep::Field(f) => Place::Field(Box::new(out), f.clone()),
            PathStep::Downcast(v) => Place::Downcast(Box::new(out), v.clone()),
            PathStep::Index(Some(k)) => {
                // Reconstruct a const-int operand from the slot number.
                // We default to i64 as the index type — analyses only
                // compare the const value, not its declared type.
                let op = Operand::Const(ConstVal::Int {
                    bits: *k,
                    ty: IntTy::I64,
                });
                Place::Index(Box::new(out), Box::new(op))
            }
            PathStep::Index(None) => {
                unreachable!("extract_path never yields Index(None); this is an owned path")
            }
            PathStep::Deref => unreachable!("owned-path invariant"),
        };
    }
    Some(out)
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
            Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
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
            Place::Index(inner, op) => {
                steps.push(PathStep::Index(const_int_operand(op)));
                cur = inner;
            }
            Place::Deref(inner) => {
                steps.push(PathStep::Deref);
                cur = inner;
            }
        }
    }
}

/// True if `ancestor` is `descendant` or a prefix of it (comparing
/// projections step-by-step). Handles Field, Downcast, and Deref
/// uniformly — a loan on `*r` is a prefix of `*r.f`, and `b` is a
/// prefix of `b.p`. Callers that need "owned-path prefix only" can
/// pre-check `is_owned_path` on both arguments.
pub fn is_ancestor_or_self(ancestor: &Place, descendant: &Place) -> bool {
    let (ar, ap) = extract_path_with_deref(ancestor);
    let (dr, dp) = extract_path_with_deref(descendant);
    if ar != dr || ap.len() > dp.len() {
        return false;
    }
    ap.iter().zip(dp.iter()).all(|(a, b)| match (a, b) {
        (PathStep::Field(x), PathStep::Field(y)) => x == y,
        (PathStep::Downcast(x), PathStep::Downcast(y)) => x == y,
        (PathStep::Deref, PathStep::Deref) => true,
        // Index steps: two constant indices conflict iff equal.
        // A dynamic index (None) may refer to any slot, so it
        // conflicts with any index step — widening.
        (PathStep::Index(a), PathStep::Index(b)) => match (a, b) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        },
        _ => false,
    })
}

/// Canonical diagnostic rendering of a place. `Var("x")` → `x`;
/// `Field(Var("b"), "p")` → `b.p`; `Deref(Var("r"))` → `r.*`;
/// `Field(Deref(Var("r")), "f")` renders as `r.*.f`. Use this
/// everywhere a place needs to appear in an error message.
pub fn format_place(place: &Place) -> String {
    let (root, path) = extract_path_with_deref(place);
    let mut s = root;
    for step in &path {
        match step {
            PathStep::Field(f) => {
                s.push('.');
                s.push_str(f);
            }
            PathStep::Downcast(v) => {
                s.push_str(" as ");
                s.push_str(v);
            }
            PathStep::Deref => {
                // Postfix deref — always chains cleanly left-to-right.
                s.push_str(".*");
            }
            PathStep::Index(Some(k)) => {
                s.push('[');
                s.push_str(&k.to_string());
                s.push(']');
            }
            PathStep::Index(None) => {
                s.push_str("[?]");
            }
        }
    }
    s
}

/// If `place` is `Deref(inner)` and `inner` is an owned path, return
/// `inner`. This is where a reborrowed reference physically lives —
/// e.g. `*r` → `r`, `*b.p` → `b.p`.
pub fn deref_inner(place: &Place) -> Option<Place> {
    let Place::Deref(inner) = place else {
        return None;
    };
    as_owned_path(inner)
}

/// The `Place` referenced by an operand's `copy`/`move`/`take`, or
/// `None` for constants.
pub fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) | Operand::Take(p) => Some(p),
        Operand::Const(_) => None,
    }
}

/// Labels of the blocks a terminator flows into. Empty for terminators
/// with no successors (`return`, `abort`, `unreachable`).
pub fn terminator_successors(term: &Terminator) -> Vec<&str> {
    match &term.kind {
        TerminatorKind::Goto(label) => vec![label.as_str()],
        TerminatorKind::Return | TerminatorKind::Abort | TerminatorKind::Unreachable => vec![],
        TerminatorKind::Branch {
            true_label,
            false_label,
            ..
        } => {
            vec![true_label.as_str(), false_label.as_str()]
        }
        TerminatorKind::SwitchEnum { cases, .. } => {
            cases.iter().map(|(_, label)| label.as_str()).collect()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstVal {
    /// Integer literal. `bits` is the raw bit pattern; interpretation
    /// as signed/unsigned comes from `ty`. Bit widths narrower than 64
    /// use the low `ty.bits()` bits, upper bits zero.
    Int {
        bits: u64,
        ty: IntTy,
    },
    /// Floating-point literal, stored as its IEEE-754 bit pattern.
    /// `f32` literals are stored in the low 32 bits (upper 32 bits
    /// zero); `f64` fills all 64. Bit-pattern storage lets ConstVal
    /// stay `Eq` (NaN comparisons preserved as bit-equality).
    Float {
        bits: u64,
        ty: FloatTy,
    },
    Bool(bool),
    Unit,
    /// Function-name const, used as the target of `call`. `args` is
    /// the list of type arguments — empty for non-generic fns, non-
    /// empty for generic-fn instantiations (`call foo<i32>(x)`).
    FnName(String, Vec<Type>),
    /// Trait-method callee, spelled UFCS-style at the surface:
    /// `<SelfTy as Trait<Args>>::method<MethodArgs>`. The type checker
    /// resolves this against the env's impl table for concrete
    /// `self_ty`; `Param(T)` receivers require trait bounds and are
    /// deferred behind that work.
    TraitFn {
        trait_path: Instance,
        self_ty: Type,
        method: Instance,
    },
    /// Byte string literal `b"..."`. Value semantics: has type
    /// `[u8; N]` where N = bytes.len(). Codegen emits an inline LLVM
    /// aggregate constant `c"..."`; larger strings could be moved to
    /// module-scope private constants later if size matters.
    ByteStr(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    /// Deferred read of `place`: copy relaxation specializes each
    /// `Take` operand to either `Copy` or `Move` before subsequent
    /// passes run. Emitted by HLL lowering for reads whose optimal
    /// specialization depends on flow-sensitive demand. No `Take`
    /// operand survives past `place_state::copy_relaxation::elaborate`
    /// — later passes hitting one is an internal compiler error.
    Take(Place),
    Const(ConstVal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RValue {
    Use(Operand),
    Ref(RefKind, Place),
    /// Take the address of `place` as a raw pointer. Does NOT create
    /// a loan — this is the unsafe part. Written `&raw place`.
    RawRef(Place),
    /// Enum construction: `EnumName<T,U>::Variant(payload)`. The
    /// `Vec<Type>` is the list of type arguments — empty for non-generic
    /// enums, non-empty for generic instantiations.
    EnumConstr(String, Vec<Type>, String, Operand),
    /// Aggregate array literal `[e0, e1, ..., eN-1]`. All operands
    /// must share the target's element type; the vec length must
    /// equal the target's `[T; N]` length. Init state treats this
    /// as whole-array atomic init.
    ArrayLit(Vec<Operand>),
    /// Cast a raw pointer or reference operand to another raw pointer or reference type.
    /// Written `ptr_cast(operand, Type)`.
    PtrCast(Operand, Type),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    pub kind: StatementKind,
    pub source: SourceInfo,
}

impl Statement {
    pub fn new(kind: StatementKind, source: SourceInfo) -> Self {
        Self { kind, source }
    }

    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementKind {
    Assign(Place, RValue),
    Call(Operand, Vec<Operand>),
    /// Consume a place. In the current MIR this is a bitwise forget
    /// (trivial `Drop`); once `Destroy` and higher tiers exist, this
    /// lowers to a call to the type's destructor. Legal only on `Drop`
    /// places (enforced by the substructural checker, not here).
    Drop(Place),
    /// Explicitly end a reference's loan. Requires the referenced place
    /// to hold a bound reference with its (cur, post) obligation
    /// fulfilled (cur == post). After: the borrower is consumed and its
    /// loan is removed. Inserted by `lifetime::nll` at last-use
    /// points; the checker just observes the marker.
    Unborrow(Place),
    /// Ghost ownership assertion: `place` must not hold a live owned value
    /// at this point. Place-state elaboration may insert cleanup before this
    /// statement; the final checker verifies the requirement. It has no
    /// runtime effect and is erased by codegen.
    RequireUninit(Place),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub source: SourceInfo,
}

impl Terminator {
    pub fn new(kind: TerminatorKind, source: SourceInfo) -> Self {
        Self { kind, source }
    }

    pub fn span(&self) -> Span {
        self.source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminatorKind {
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
    pub label_source: SourceInfo,
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

impl BasicBlock {
    pub fn label_span(&self) -> Span {
        self.label_source.span()
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
    pub source: SourceInfo,
}

impl Local {
    pub fn span(&self) -> Span {
        self.source.span()
    }
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

    /// Compute the set of block labels that can reach a `return`
    /// terminator via any CFG path. Blocks that only lead to `abort`,
    /// `unreachable`, or infinite loops with no return exit are excluded.
    ///
    /// Backward reachability from return-terminated blocks. Used by
    /// elaboration passes to skip inserting cleanup on paths that die
    /// before the caller could observe missing initialization —
    /// consistent with drop-elab, which only inserts before `return`.
    pub fn return_reachable(&self) -> std::collections::BTreeSet<String> {
        let blocks_by_label = self.blocks_by_label();
        // Reverse edges: succ -> predecessors.
        let mut preds: IndexMap<&str, Vec<&str>> = IndexMap::new();
        for block in &self.blocks {
            for succ in terminator_successors(&block.terminator) {
                if blocks_by_label.contains_key(succ) {
                    preds.entry(succ).or_default().push(block.label.as_str());
                }
            }
        }
        // Seed: blocks with `Return` terminator.
        let mut reachable = std::collections::BTreeSet::new();
        let mut worklist: Vec<&str> = Vec::new();
        for block in &self.blocks {
            if matches!(block.terminator.kind, TerminatorKind::Return) {
                reachable.insert(block.label.clone());
                worklist.push(block.label.as_str());
            }
        }
        while let Some(label) = worklist.pop() {
            if let Some(pred_labels) = preds.get(label) {
                for pred in pred_labels {
                    if reachable.insert(pred.to_string()) {
                        worklist.push(pred);
                    }
                }
            }
        }
        reachable
    }
}

/// Everything a type-parameter binder promises about its parameter.
/// `markers` carries the compiler-internal substructural vocabulary
/// (Copy/Drop/Move); `traits` carries user-declared trait bounds as
/// `Instance` values — trait references share the type-reference shape
/// (name + lifetime args + type args), and until trait bounds grow
/// bound-specific state (source attribution, negativity, HRTB) a plain
/// `Vec<Instance>` says everything. Empty today; populated once
/// trait-decl syntax lands.
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub meta: DeclMeta,
    pub is_extern: bool,
    pub abi: Option<String>,
    pub params: Vec<Param>,
    pub body: Option<FunctionBody>,
}

/// A `Function` without its body — the name-resolution view used by
/// [`Env`](crate::mir::type_check::Env). Bodies live in [`Program`] and
/// are mutated by elaboration; `Env` caches only what's stable across
/// elaboration so no resync is needed between passes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionSignature {
    pub meta: DeclMeta,
    pub is_extern: bool,
    pub abi: Option<String>,
    pub params: Vec<Param>,
}

impl FunctionSignature {
    pub fn from_function(f: &Function) -> Self {
        Self {
            meta: f.meta.clone(),
            is_extern: f.is_extern,
            abi: f.abi.clone(),
            params: f.params.clone(),
        }
    }

    /// Instantiate parameter types by substituting `type_args` for the function's declared type parameters.
    pub fn instantiate_params(&self, type_args: &[Type]) -> Vec<Type> {
        self.params
            .iter()
            .map(|p| {
                self.meta
                    .try_substitute_types(&p.ty, type_args)
                    .unwrap_or_else(|| p.ty.clone())
            })
            .collect()
    }
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


/// A set of generic parameters and bounds introduced in either a declaration or impl block.
// e.g. struct Foo<A: Bar, 'b: 'c>
//                ^^^^^^^^^^^^^^^^
// e.g. impl<A: Bar, 'b: 'c> Baz for A { .. }
//          ^^^^^^^^^^^^^^^^
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamsIntro {
    pub lifetime_params: Vec<LifetimeParam>,
    pub outlives: Vec<OutlivesBound>,
    pub type_params: Vec<TypeParam>,
    pub source: SourceInfo,  // Source of the introducer <...>.
}

impl ParamsIntro {
    pub fn empty(source: SourceInfo) -> Self {
        Self {
            lifetime_params: Vec::new(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            source,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.lifetime_params.is_empty() && self.outlives.is_empty() && self.type_params.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclMeta {
    pub name: String,
    pub name_source: SourceInfo,
    pub params: ParamsIntro,
    pub markers: Markers,
}

impl DeclMeta {
    pub fn name_span(&self) -> Span {
        self.name_source.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructDecl {
    pub meta: DeclMeta,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub meta: DeclMeta,
    pub variants: Vec<EnumVariant>,
}

/// A trait declaration: name, generics, and a set of method signatures.
/// Methods are stored as body-less `FunctionSignature`s. `Self` is a
/// reserved identifier in the trait's scope, resolved to
/// `TypeKind::Param("Self")` during parsing; impls substitute it with
/// the target type at check time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitDecl {
    pub meta: DeclMeta,
    pub methods: Vec<FunctionSignature>,
}

/// An `impl Trait<Args> for Target` block. `meta` carries the impl-
/// header generics (bound throughout `trait_path`, `target`, and every
/// method body). `trait_path` is the trait ref as an `Instance` (name
/// + lifetime + type args); `target` is the type filling the trait's
/// `Self` slot. Methods are full `Function`s (body required).
///
/// The type checker verifies each method's signature matches the
/// trait's declared signature after substituting `Self := target` and
/// the trait's type_params from `trait_path`'s arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplBlock {
    pub params: ParamsIntro,
    pub trait_path: Instance,
    pub target: Type,
    pub methods: Vec<Function>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declaration {
    Struct(StructDecl),
    Enum(EnumDecl),
    Fn(Function),
    Trait(TraitDecl),
    Impl(ImplBlock),
}

impl Declaration {
    /// Shared declaration metadata (name, generics, markers). Present
    /// on Struct, Enum, Fn, and Trait variants.
    pub fn meta(&self) -> Option<&DeclMeta> {
        match self {
            Declaration::Struct(s) => Some(&s.meta),
            Declaration::Enum(e) => Some(&e.meta),
            Declaration::Fn(f) => Some(&f.meta),
            Declaration::Trait(t) => Some(&t.meta),
            Declaration::Impl(_) => None,
        }
    }

    /// Shared parameter introduction for all declarations (including impl blocks).
    pub fn params(&self) -> &ParamsIntro {
        match self {
            Declaration::Struct(s) => &s.meta.params,
            Declaration::Enum(e) => &e.meta.params,
            Declaration::Fn(f) => &f.meta.params,
            Declaration::Trait(t) => &t.meta.params,
            Declaration::Impl(i) => &i.params,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Declaration>,
    pub source: std::sync::Arc<String>,
}

impl Program {
    /// Iterate over function declarations in declaration order. Callers
    /// that need bodies (checkers walking blocks, elaborators inspecting
    /// state, drop-elab planning drops) go through here rather than
    /// through [`Env`](crate::mir::type_check::Env), which caches only
    /// signatures.
    pub fn functions(&self) -> impl Iterator<Item = &Function> + '_ {
        self.declarations.iter().filter_map(|d| match d {
            Declaration::Fn(f) => Some(f),
            _ => None,
        })
    }

    /// Mutable counterpart of [`functions`](Self::functions). Elaboration
    /// passes iterate through here to splice statements and rewrite
    /// bodies in place; the immutable form is preferred everywhere else.
    pub fn functions_mut(&mut self) -> impl Iterator<Item = &mut Function> + '_ {
        self.declarations.iter_mut().filter_map(|d| match d {
            Declaration::Fn(f) => Some(f),
            _ => None,
        })
    }

    /// Look up a function declaration by name. `None` if no `Declaration::Fn`
    /// with the matching name exists — callers that need the presence
    /// invariant use `.expect(...)`; production code branches on the
    /// `Option`.
    pub fn find_fn(&self, name: &str) -> Option<&Function> {
        self.functions().find(|f| f.meta.name == name)
    }

    /// Iterate `(fn, body)` pairs for every function with a body. Skips
    /// externs. Convenience over `functions().filter_map(|f| f.body...)`
    /// used by every check pass.
    pub fn function_bodies(&self) -> impl Iterator<Item = (&Function, &FunctionBody)> + '_ {
        self.functions()
            .filter_map(|f| f.body.as_ref().map(|b| (f, b)))
    }
}

#[cfg(test)]
mod instance_tests {
    use super::*;
    use crate::mir::helpers::*;

    #[test]
    fn new_preserves_all_three_field_slots() {
        let inst = Instance::new(
            "Foo",
            vec![Lifetime("a".into()), Lifetime("b".into())],
            vec![i64_ty(), bool_ty()],
        );
        assert_eq!(inst.name, "Foo");
        assert_eq!(inst.lifetime_args.len(), 2);
        assert_eq!(inst.lifetime_args[0], Lifetime("a".into()));
        assert_eq!(inst.lifetime_args[1], Lifetime("b".into()));
        assert_eq!(inst.type_args.len(), 2);
        assert_eq!(inst.type_args[0].kind, TypeKind::Int(IntTy::I64));
        assert_eq!(inst.type_args[1].kind, TypeKind::Bool);
    }

    #[test]
    fn bare_yields_empty_arg_lists() {
        let inst = Instance::bare("Foo");
        assert_eq!(inst.name, "Foo");
        assert!(inst.lifetime_args.is_empty());
        assert!(inst.type_args.is_empty());
    }

    #[test]
    fn display_bare_is_just_the_name() {
        let inst = Instance::bare("Foo");
        assert_eq!(inst.to_string(), "Foo");
    }

    #[test]
    fn display_full_instance_uses_lifetimes_first_order() {
        let inst = Instance::new(
            "Foo",
            vec![Lifetime("a".into()), Lifetime("b".into())],
            vec![i64_ty(), bool_ty()],
        );
        assert_eq!(inst.to_string(), "Foo<'a, 'b, i64, bool>");
    }

    #[test]
    fn display_lifetimes_only() {
        let inst = Instance::new("Foo", vec![Lifetime("a".into())], vec![]);
        assert_eq!(inst.to_string(), "Foo<'a>");
    }

    #[test]
    fn display_types_only() {
        let inst = Instance::new("Foo", vec![], vec![i64_ty()]);
        assert_eq!(inst.to_string(), "Foo<i64>");
    }
}
