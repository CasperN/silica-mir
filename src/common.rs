/// A single substructural marker in the vocabulary. Only the trivial-
/// tier markers (Copy, Drop, Move) are represented today; higher tiers
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

    /// Parse a marker from its canonical name.
    pub fn from_name(name: &str) -> Option<Marker> {
        match name {
            "Copy" => Some(Marker::Copy),
            "Drop" => Some(Marker::Drop),
            "Move" => Some(Marker::Move),
            _ => None,
        }
    }
}

/// Per-column implementation tier. Only Trivial exists today;
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
/// - [`declared`] — literal presence of a marker in the canonical set.
///   Used by composition checking to avoid cascading redundant errors
///   from the closure.
/// - [`implies`] — semantic satisfaction, accounting for the
///   vertical closure (higher tiers imply lower) and the horizontal
///   closure (Copy + Drop implies Move). Used by every other query.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Markers {
    copy: Option<Tier>,
    drop: Option<Tier>,
    mov: Option<Tier>,
}

impl Markers {
    /// A marker set with nothing declared — linear in every dimension.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Build from a set of markers. Duplicates are idempotent. The
    /// result is canonicalized: markers derivable from the others via
    /// closure are removed, so any two equivalent inputs produce the
    /// same value. E.g., `[Copy, Drop, Move]` and `[Copy, Drop]` both
    /// yield `{copy, drop}` — `Move` is redundant because it is already
    /// implied by Copy + Drop.
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

    fn canonicalize(&mut self) {
        if self.copy.is_some() && self.drop.is_some() {
            self.mov = None;
        }
    }

    /// Intersection of two marker sets. A marker is satisfied in the result
    /// iff it is implied by both inputs.
    pub fn intersection(self, other: Self) -> Self {
        let mut out = Self::empty();
        if self.implies(Marker::Copy) && other.implies(Marker::Copy) {
            out.copy = Some(Tier::Trivial);
        }
        if self.implies(Marker::Drop) && other.implies(Marker::Drop) {
            out.drop = Some(Tier::Trivial);
        }
        if self.implies(Marker::Move) && other.implies(Marker::Move) {
            out.mov = Some(Tier::Trivial);
        }
        out.canonicalize();
        out
    }

    /// True iff this marker is present in the canonical set (post-
    /// canonicalization). Composition uses this to avoid emitting
    /// redundant errors on closure-derived markers.
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

    /// Iterate the canonical set in canonical order (Copy, Drop, Move).
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

    /// Same as `from_iter` but also returns whether the user's token
    /// list included a redundant `Move` alongside both `Copy` and `Drop`.
    /// Callers (typically parsers) pair the flag with their own DiagCode
    /// to emit an info diagnostic — see [`Markers::redundant_move_message`].
    pub fn from_declared(tokens: impl IntoIterator<Item = Marker>) -> (Self, bool) {
        let seen: Vec<Marker> = tokens.into_iter().collect();
        let redundant = seen.contains(&Marker::Copy)
            && seen.contains(&Marker::Drop)
            && seen.contains(&Marker::Move);
        (Markers::from_iter(seen), redundant)
    }

    /// Message body for the redundant-Move info diagnostic. Shared so
    /// both parsers emit identical text.
    pub fn redundant_move_message(decl_name: &str) -> String {
        format!(
            "Move marker is redundant on '{}' because both Copy and Drop are present",
            decl_name
        )
    }
}

/// Where a function's definition lives, relative to the translation unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Linkage {
    Local,
    Foreign,
}

/// Calling convention of a function, when lowered to LLVM.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Abi {
    Silica,
    C,
}

impl Abi {
    /// Surface spelling as it appears after `extern`. Quoted for named
    /// ABIs; empty for the default (spelled by omitting the clause).
    pub fn as_str(self) -> &'static str {
        match self {
            Abi::Silica => "",
            Abi::C => "\"C\"",
        }
    }

    /// Inverse of `as_str`. Accepts the raw ABI clause including its
    /// quotes; empty string means the default ABI.
    pub fn from_str(s: &str) -> Option<Abi> {
        match s {
            "" => Some(Abi::Silica),
            "\"C\"" => Some(Abi::C),
            _ => None,
        }
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

    #[test]
    fn intersection_combines_shared_markers() {
        let all = Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        let move_only = Markers::from_iter([Marker::Move]);
        let copy_drop = Markers::from_iter([Marker::Copy, Marker::Drop]);
        let drop_move = Markers::from_iter([Marker::Drop, Marker::Move]);

        assert_eq!(all.intersection(move_only), move_only);
        assert_eq!(copy_drop.intersection(drop_move), Markers::from_iter([Marker::Drop, Marker::Move]));
        assert_eq!(move_only.intersection(copy_drop), move_only);
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

/// Why an AST or analysis node exists, independently of the source range to
/// which diagnostics should attribute it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HllTemporaryKind {
    /// Storage for a source-language expression value whose lifetime is the
    /// surrounding HLL temporary region.
    Expression,
    /// Compiler bookkeeping storage introduced while lowering an expression
    /// (for example an intrinsic's `&out` slot or a saved array index).
    Lowering,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GeneratedKind {
    HllTemporary(HllTemporaryKind),
    HllDesugaring,
    TypeSynthesis,
    LifetimeElision,
    ControlFlowElaboration,
    NllElaboration,
    DropElaboration,
    CopyRelaxation,
    ParserInfrastructure,
    Intrinsic,
    Prelude,
    TestHelper,
}

/// Source attribution shared by surface AST, MIR, and diagnostic analysis
/// records. A generated node may carry a real span when it should be blamed on
/// source syntax, or `Span::default()` when it has no useful source location.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceInfo {
    Written(Span),
    Generated {
        kind: GeneratedKind,
        attributed_to: Span,
    },
}

impl SourceInfo {
    pub fn written(span: Span) -> Self {
        Self::Written(span)
    }

    pub fn generated(kind: GeneratedKind, attributed_to: Span) -> Self {
        Self::Generated {
            kind,
            attributed_to,
        }
    }

    pub fn span(self) -> Span {
        match self {
            Self::Written(span) => span,
            Self::Generated { attributed_to, .. } => attributed_to,
        }
    }

    pub fn generated_kind(self) -> Option<GeneratedKind> {
        match self {
            Self::Written(_) => None,
            Self::Generated { kind, .. } => Some(kind),
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lifetime(pub String);

impl std::fmt::Display for Lifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LifetimeParam {
    pub lifetime: Lifetime,
    pub source: SourceInfo,
}

impl LifetimeParam {
    pub fn written(lifetime: Lifetime, span: Span) -> Self {
        Self {
            lifetime,
            source: SourceInfo::written(span),
        }
    }

    pub fn generated(lifetime: Lifetime, kind: GeneratedKind, attributed_to: Span) -> Self {
        Self {
            lifetime,
            source: SourceInfo::generated(kind, attributed_to),
        }
    }
}

impl std::ops::Deref for LifetimeParam {
    type Target = Lifetime;

    fn deref(&self) -> &Self::Target {
        &self.lifetime
    }
}

impl std::fmt::Display for LifetimeParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.lifetime.fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OutlivesBound {
    pub longer: Lifetime,
    pub shorter: Lifetime,
    pub source: SourceInfo,
}

impl OutlivesBound {
    pub fn written(longer: Lifetime, shorter: Lifetime, span: Span) -> Self {
        Self {
            longer,
            shorter,
            source: SourceInfo::written(span),
        }
    }

    pub fn generated(
        longer: Lifetime,
        shorter: Lifetime,
        kind: GeneratedKind,
        attributed_to: Span,
    ) -> Self {
        Self {
            longer,
            shorter,
            source: SourceInfo::generated(kind, attributed_to),
        }
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

impl RefKind {
    pub fn value_markers(self) -> Markers {
        match self {
            Self::Shared => Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]),
            Self::Mut | Self::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
            Self::Out | Self::Drop => Markers::from_iter([Marker::Move]),
        }
    }

    pub fn write_type_prefix<W, L>(self, out: &mut W, lifetime: Option<&L>) -> std::fmt::Result
    where
        W: std::fmt::Write + ?Sized,
        L: std::fmt::Display + ?Sized,
    {
        if let Some(lifetime) = lifetime {
            match self {
                Self::Shared => write!(out, "&{} ", lifetime)?,
                Self::Mut => write!(out, "&{} mut ", lifetime)?,
                Self::Out => write!(out, "&{} out ", lifetime)?,
                Self::Drop => write!(out, "&{} drop ", lifetime)?,
                Self::Uninit => write!(out, "&{} uninit ", lifetime)?,
            }
        } else {
            match self {
                Self::Shared => write!(out, "&")?,
                Self::Mut => write!(out, "&mut ")?,
                Self::Out => write!(out, "&out ")?,
                Self::Drop => write!(out, "&drop ")?,
                Self::Uninit => write!(out, "&uninit ")?,
            }
        }
        Ok(())
    }
}

impl std::fmt::Display for RefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let s = match self {
            RefKind::Shared => "&",
            RefKind::Mut => "&mut",
            RefKind::Out => "&out",
            RefKind::Drop => "&drop",
            RefKind::Uninit => "&uninit",
        };
        write!(f, "{}", s)
    }
}

/// Integer scalar type. Grouped in `TypeKind::Int(IntTy)` rather than a
/// separate `Type` variant per width — passes that treat all integers
/// uniformly (Copy/Drop class, ref-ness, etc.) match on `TypeKind::Int(_)`;
/// passes that dispatch per-width (layout, codegen) match on the inner
/// `IntTy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
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
