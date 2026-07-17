use indexmap::IndexMap;

/// A single substructural marker in the vocabulary. Phase 1 has only
/// the trivial-tier markers (Copy, Drop, Move); higher tiers
/// (AutoClone, Clone, CoClone, etc.) land with the methods project.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Marker {
    Copy,
    Drop,
    Move,
}

impl Marker {
    /// Canonical spelling used in surface syntax and pretty-print.
    pub fn name(self) -> &'static str {
        match self {
            Marker::Copy => "Copy",
            Marker::Drop => "Drop",
            Marker::Move => "Move",
        }
    }
}

/// Per-column implementation tier. Phase 1 has only Trivial —
/// Auto/Pure/Co variants land alongside the methods project. The
/// ordering `Trivial < Auto < Pure < Co` reflects the vertical
/// closure: Trivial-Copy satisfies AutoClone/Clone/CoClone bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tier {
    Trivial,
}

/// Substructural markers declared on a struct/enum, or the effective
/// class of an arbitrary type. Opaque so the internal representation
/// stays flexible as the marker vocabulary grows.
///
/// Two query modes:
/// - [`declared`] — literal presence of a marker on the decl. Used
///   by composition checking to avoid cascading redundant errors
///   from the closure.
/// - [`implies`] — semantic satisfaction, accounting for the
///   vertical closure (higher tiers imply lower) and the horizontal
///   closure (Copy + Drop implies Move). Used by every other query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Markers {
    // One tier per column, `None` = the type has no impl for that
    // operation (linear in that dimension). Kept private so callers
    // can't build inconsistent states.
    copy: Option<Tier>,
    drop: Option<Tier>,
    mov: Option<Tier>,
}

impl Markers {
    /// A marker set with nothing declared — linear in every dimension.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Build from a set of declared markers. Duplicates are idempotent.
    /// The result is canonicalized: markers derivable from the others
    /// via closure are removed, so any two equivalent inputs produce
    /// the same `Markers` value. E.g., `[Copy, Drop, Move]` and
    /// `[Copy, Drop]` both yield `{copy, drop}` — `Move` is redundant
    /// since it's already implied by Copy + Drop.
    pub fn from_iter(ms: impl IntoIterator<Item = Marker>) -> Self {
        let mut out = Self::empty();
        for m in ms {
            match m {
                Marker::Copy => out.copy = Some(Tier::Trivial),
                Marker::Drop => out.drop = Some(Tier::Trivial),
                Marker::Move => out.mov = Some(Tier::Trivial),
            }
        }
        out.canonicalize();
        out
    }

    /// Strip declarations that the closure already implies. Called
    /// from `from_iter` so `Markers` values are always canonical.
    fn canonicalize(&mut self) {
        // Copy + Drop implies Move via the horizontal closure — an
        // explicit Move declaration alongside them is redundant.
        if self.copy.is_some() && self.drop.is_some() {
            self.mov = None;
        }
    }

    /// True iff the user literally wrote this marker on the decl.
    /// Does *not* consider the closure. Composition uses this to
    /// avoid emitting redundant errors on closure-derived markers.
    pub fn declared(&self, m: Marker) -> bool {
        match m {
            Marker::Copy => self.copy.is_some(),
            Marker::Drop => self.drop.is_some(),
            Marker::Move => self.mov.is_some(),
        }
    }

    /// True iff the type semantically satisfies this marker, considering
    /// the horizontal closure (Copy + Drop → Move). Vertical closure
    /// (Auto, Pure, Co tiers) lands with those variants of `Marker`.
    pub fn implies(&self, m: Marker) -> bool {
        match m {
            Marker::Copy => self.copy.is_some(),
            Marker::Drop => self.drop.is_some(),
            Marker::Move => self.mov.is_some() || (self.copy.is_some() && self.drop.is_some()),
        }
    }

    /// Iterate declared markers in canonical order (Copy, Drop, Move).
    /// Closure-derived markers are not included. Used by pretty-print.
    pub fn iter_declared(&self) -> impl Iterator<Item = Marker> + '_ {
        [
            (self.copy.is_some(), Marker::Copy),
            (self.drop.is_some(), Marker::Drop),
            (self.mov.is_some(), Marker::Move),
        ]
        .into_iter()
        .filter_map(|(present, m)| if present { Some(m) } else { None })
    }
}

#[cfg(test)]
mod markers_tests {
    use super::*;

    #[test]
    fn empty_declares_and_implies_nothing() {
        let m = Markers::empty();
        for marker in [Marker::Copy, Marker::Drop, Marker::Move] {
            assert!(!m.declared(marker));
            assert!(!m.implies(marker));
        }
        assert_eq!(m.iter_declared().count(), 0);
    }

    #[test]
    fn from_iter_records_each_marker() {
        let m = Markers::from_iter([Marker::Copy, Marker::Drop]);
        assert!(m.declared(Marker::Copy));
        assert!(m.declared(Marker::Drop));
        assert!(!m.declared(Marker::Move));
    }

    #[test]
    fn horizontal_closure_copy_and_drop_implies_move() {
        // Copy + Drop declared → Move is implied but not declared.
        let m = Markers::from_iter([Marker::Copy, Marker::Drop]);
        assert!(!m.declared(Marker::Move), "Move must not be declared");
        assert!(m.implies(Marker::Move), "Copy + Drop must imply Move");
    }

    #[test]
    fn copy_alone_does_not_imply_move() {
        let m = Markers::from_iter([Marker::Copy]);
        assert!(!m.implies(Marker::Move));
    }

    #[test]
    fn iter_declared_uses_canonical_order() {
        // Move alone (without Copy+Drop) survives canonicalization,
        // so this exercises the ordering directly.
        let m = Markers::from_iter([Marker::Move, Marker::Copy]);
        let got: Vec<Marker> = m.iter_declared().collect();
        assert_eq!(got, vec![Marker::Copy, Marker::Move]);
    }

    #[test]
    fn from_iter_is_idempotent_on_duplicates() {
        let a = Markers::from_iter([Marker::Copy, Marker::Copy]);
        let b = Markers::from_iter([Marker::Copy]);
        assert_eq!(a, b);
    }

    #[test]
    fn canonical_form_strips_redundant_move() {
        // Copy + Drop + Move and Copy + Drop are semantically the same
        // (Move is implied by the pair). Both should produce the same
        // canonical Markers value.
        let a = Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        let b = Markers::from_iter([Marker::Copy, Marker::Drop]);
        assert_eq!(a, b);
        assert!(!a.declared(Marker::Move));
        assert!(a.implies(Marker::Move));
    }

    #[test]
    fn move_alone_stays_declared() {
        // With no Copy or Drop, the Move declaration isn't redundant.
        let m = Markers::from_iter([Marker::Move]);
        assert!(m.declared(Marker::Move));
        assert!(m.implies(Marker::Move));
    }
}

/// Source position (1-based line and column) of the syntax that a node
/// represents. Used to prefix error messages with `at L:C:`.
///
/// `Default::default()` yields `Span { line: 0, col: 0 }`, which
/// `Diagnostic::fmt` treats as "no position" (omits the `at L:C:`
/// prefix). Real syntax always has 1-based positions.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RefKind {
    Shared, // &
    Mut,    // &mut
    Out,    // &out
    Drop,   // &drop
    Uninit, // &uninit
}

/// Integer scalar type. Grouped in `Type::Int(IntTy)` rather than a
/// separate `Type` variant per width — passes that treat all integers
/// uniformly (Copy/Drop class, ref-ness, etc.) match on `Type::Int(_)`;
/// passes that dispatch per-width (layout, codegen) match on the inner
/// `IntTy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntTy {
    I8, I16, I32, I64,
    U8, U16, U32, U64,
}

impl IntTy {
    pub fn is_signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
    }

    /// Width in bits.
    pub fn bits(self) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            IntTy::I64 | IntTy::U64 => 64,
        }
    }

    /// Width in bytes.
    pub fn bytes(self) -> u64 {
        self.bits() as u64 / 8
    }

    /// Canonical MIR / LLVM name (`"i8"`, `"u32"`, …).
    pub fn name(self) -> &'static str {
        match self {
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::U8 => "u8",
            IntTy::U16 => "u16",
            IntTy::U32 => "u32",
            IntTy::U64 => "u64",
        }
    }
}

/// Floating-point scalar type. Grouped like `IntTy` — see its comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatTy {
    F32,
    F64,
}

impl FloatTy {
    pub fn bits(self) -> u32 {
        match self {
            FloatTy::F32 => 32,
            FloatTy::F64 => 64,
        }
    }

    pub fn bytes(self) -> u64 {
        self.bits() as u64 / 8
    }

    /// Canonical MIR name (`"f32"`, `"f64"`).
    pub fn name(self) -> &'static str {
        match self {
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Type {
    Int(IntTy),
    Float(FloatTy),
    Bool,
    Unit,
    Never,
    /// Struct or enum type reference. `args` is the list of type
    /// arguments — empty for non-generic decls (`Foo`), non-empty
    /// for instantiations of generic decls (`Vec<i32>`).
    Custom(String, Vec<Type>),
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
    Ref(RefKind, Box<Type>),
    /// Raw pointer. Aliasing is unrestricted; no loan tracking, no
    /// `(cur, post)` obligation. Deref is unchecked — the caller is
    /// responsible for the pointee's init state and lifetime. The
    /// pointer value itself is `Copy Drop Move`, like `&T`.
    RawPtr(Box<Type>),
    /// Fixed-size array `[T; N]`. Layout is `N * size_of(T)`, align
    /// equals `T`'s align. Element access via `Place::Index`. Init
    /// state is tracked per-slot for constant indices (using slot
    /// numbers as `Partial` keys); dynamic indices widen to the
    /// whole array.
    Array(Box<Type>, u64),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int(i) => write!(f, "{}", i.name()),
            Type::Float(fl) => write!(f, "{}", fl.name()),
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
            Type::Fn(params) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ")")
            }
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
            Type::Array(elem, size) => write!(f, "[{}; {}]", elem, size),
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
    /// step. Dynamic (non-const) indices widen to the whole array.
    Index(Box<Place>, Box<Operand>),
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
    /// Array slot access. `Some(k)` = constant slot k; `None` =
    /// dynamic index (unknown slot). `extract_path` returns `None`
    /// if any index step is dynamic (untrackable in the locals
    /// tree); `extract_path_with_deref` preserves both forms so the
    /// loan tracker can widen dynamic indices to "matches any slot"
    /// via the conflict helper.
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstVal {
    /// Integer literal. `bits` is the raw bit pattern; interpretation
    /// as signed/unsigned comes from `ty`. Bit widths narrower than 64
    /// use the low `ty.bits()` bits, upper bits zero.
    Int { bits: u64, ty: IntTy },
    /// Floating-point literal, stored as its IEEE-754 bit pattern.
    /// `f32` literals are stored in the low 32 bits (upper 32 bits
    /// zero); `f64` fills all 64. Bit-pattern storage lets ConstVal
    /// stay `Eq` (NaN comparisons preserved as bit-equality).
    Float { bits: u64, ty: FloatTy },
    Bool(bool),
    Unit,
    /// Function-name const, used as the target of `call`. `args` is
    /// the list of type arguments — empty for non-generic fns, non-
    /// empty for generic-fn instantiations (`call foo<i32>(x)`).
    FnName(String, Vec<Type>),
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
    Const(ConstVal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RValue {
    Use(Operand),
    Ref(RefKind, Place),
    /// Take the address of `place` as a raw pointer. Does NOT create
    /// a loan — this is the unsafe part. Written `&raw place`.
    RawRef(Place),
    EnumConstr(String, String, Operand), // EnumName, VariantName, payload
    /// Aggregate array literal `[e0, e1, ..., eN-1]`. All operands
    /// must share the target's element type; the vec length must
    /// equal the target's `[T; N]` length. Init state treats this
    /// as whole-array atomic init.
    ArrayLit(Vec<Operand>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
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
            if matches!(block.terminator, Terminator::Return) {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeParam {
    pub name: String,
    pub bounds: Markers,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub name_span: Span,
    pub is_extern: bool,
    pub type_params: Vec<TypeParam>,
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
    pub type_params: Vec<TypeParam>,
    pub markers: Markers,
    pub fields: Vec<StructField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: String,
    pub name_span: Span,
    pub type_params: Vec<TypeParam>,
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
    pub source: std::sync::Arc<String>,
}
