use crate::common::SourceInfo;
use crate::diagnostics::{DiagCode, Diagnostic};

/// Construct an HLL type-check diagnostic without discarding whether its
/// source node was written or generated.
pub fn source_diagnostic(
    code: HllTypeCheckCode,
    source: SourceInfo,
    message: impl Into<String>,
) -> Diagnostic {
    Diagnostic::new(code, source, message)
}

/// Machine-readable code for each HLL type-check error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HllTypeCheckCode {
    /// Unification failed — two types couldn't be reconciled.
    TypeMismatch,
    /// Occurs-check failed during unification.
    InfiniteType,
    /// Function call with the wrong number of arguments.
    ArityMismatch,
    /// Reference to a variable/function not in scope.
    UndeclaredVariable,
    /// Reference to a struct type that isn't declared.
    UndeclaredStruct,
    /// Reference to an enum type that isn't declared.
    UndeclaredEnum,
    /// Field access on a struct that has no such field.
    NoSuchField,
    /// Downcast or match arm names an enum variant that doesn't exist.
    NoSuchVariant,
    /// Field access on a value whose type isn't a struct.
    ExpectedStruct,
    /// Match target / downcast target isn't an enum type.
    ExpectedEnum,
    /// Call target isn't a function type.
    ExpectedFunction,
    /// Array indexing on a non-array type.
    ExpectedArray,
    /// Deref applied to a value that isn't a reference or raw pointer.
    ExpectedPointer,
    /// Match expression with zero arms.
    EmptySwitch,
    /// Binary operator applied to non-numeric operand types.
    BinaryOpNonNumeric,
    /// Unary operator applied to an incompatible operand type
    /// (e.g. unary `-` on an unsigned int or bool).
    UnaryOpInvalidOperand,
    /// Struct constructor initializes wrong number of fields.
    StructFieldCountMismatch,
    /// Struct constructor is missing a field.
    MissingField,
    /// Struct constructor initializes a field twice.
    DuplicateField,
    /// Array index expression isn't an integer.
    ArrayIndexNotInt,
    /// Array literal doesn't match the expected length.
    ArrayLengthMismatch,
    /// Tuple arity exceeds maximum supported by the compiler (12).
    TupleArityExceeded,
    /// Control flow statement (break, continue, return) inside a defer block.
    ControlFlowInDefer,
    /// Type annotation references a struct/enum name that isn't declared.
    UndeclaredType,
    /// A type-parameter bound references a trait that isn't declared.
    UndeclaredTrait,
    /// A trait bound supplies the wrong number of generic arguments.
    TraitArgArityMismatch,
    /// Trait self-bounds form a cycle.
    TraitBoundCycle,
    /// Generic type instantiation has the wrong number of type arguments
    /// (e.g. `Box<i64, i64>` on a 1-parameter decl, or a bare `Box` on a
    /// generic decl).
    TypeArgArityMismatch,
    /// A type argument at a generic instantiation site doesn't satisfy
    /// the declared marker bound on the corresponding type parameter
    /// (e.g. `Box<Linear>` where the decl is `struct<T: Copy> Box`).
    BoundNotSatisfied,
    /// A function call or a nominal type mention supplies the wrong
    /// number of explicit lifetime arguments.
    LifetimeArgArityMismatch,
    /// An explicit lifetime argument is not visible at the call site.
    UndeclaredLifetime,
    /// Explicit generic arguments were applied to a function-valued
    /// expression rather than a named generic function.
    GenericArgsOnFunctionValue,
    /// Ambiguous type (type annotations needed).
    AmbiguousType,
    /// Dereferencing a raw pointer outside an unsafe block.
    UnsafeRequired,
    /// An impl method's safety does not match its trait declaration.
    ImplMethodSafetyMismatch,
    /// A function decl combines linkage, ABI, and safety in a way the
    /// language does not accept — e.g., `extern "C"` without `unsafe`,
    /// `extern` (Silica) with `unsafe`, or a Silica-defined function
    /// with a non-Silica ABI clause (deferred to the ABI-in-type work).
    InvalidFnModifiers,
    /// `expr as Type` where the pair isn't a supported cast.
    /// Today's supported cells: numeric widths & signedness, int↔float,
    /// bool→int. Casts *to* bool aren't supported (use `!= 0`); casts
    /// to/from pointer/ref types are not yet supported.
    InvalidCast,
    /// More than one callable in the highest-priority applicable receiver-call
    /// tier has the requested name.
    AmbiguousReceiverCall,
    /// Receiver syntax found no applicable method, callable field, or free
    /// function.
    UnresolvedReceiverCall,
    /// An explicitly qualified inherent or trait method does not exist for the
    /// selected type and qualification.
    UnresolvedQualifiedMethod,
}

impl From<HllTypeCheckCode> for DiagCode {
    fn from(code: HllTypeCheckCode) -> DiagCode {
        DiagCode::HllTypeCheck(code)
    }
}
