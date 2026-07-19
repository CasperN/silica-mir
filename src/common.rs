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
