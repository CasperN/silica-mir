//! MIR type-checking pass and its supporting environment.
//!
//! - [`env`]: the type environment (`Env`) and structural
//!   type-of-expression queries (`type_of_place` / `_operand` /
//!   `_rvalue`). Pure queries; no diagnostics beyond the failures
//!   these queries surface.
//! - [`check`]: the checker pass proper. Walks declarations,
//!   statements, and terminators, verifying they type against the
//!   environment and pushing errors into `Diagnostics`.
//!
//! MIR type checking is *checking*, not inference — every
//! expression's type is determined structurally. There are no type
//! variables to solve; only well-typedness to verify.

use crate::diagnostics::DiagCode;
use crate::mir::ast::{DeclMeta, EnumDecl, StructDecl};

pub mod check;
pub mod env;

pub use env::Env;

/// Machine-readable error codes emitted by the type checker.
///
/// Deliberately small: one variant per user-observable failure kind.
/// Multiple push sites that surface the same conceptual error share
/// a single variant (e.g. all "goto/branch/switch to an undefined
/// block" cases fold into `TerminatorUndefinedTarget`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeCheckCode {
    // ---- Declaration scope ----
    /// Two top-level declarations share a name (struct/enum/function).
    DuplicateDeclaration,
    /// A struct declares the same field name twice.
    DuplicateStructField,
    /// An enum declares the same variant name twice.
    DuplicateEnumVariant,
    /// A parameter and a local (or two parameters, or two locals)
    /// share a name within one function.
    DuplicateLocalName,
    /// A struct field, enum variant payload, parameter, or local
    /// references a type that hasn't been declared. Wraps
    /// `validate_type`'s errors — the specific reason lives in the
    /// message.
    InvalidDeclaredType,
    /// A function has an empty body — no basic blocks. Every fn
    /// definition must have at least an entry block.
    NoEntryBlock,
    /// `fn main` has a parameter list that doesn't match one of the
    /// two accepted shapes (`()` or `(&out i32)`).
    MainBadSignature,
    /// A type mentions a named lifetime (`'a`, `'other`, ...) that
    /// isn't declared on the enclosing decl's lifetime parameter
    /// list. Fires on struct field, enum variant, fn param, local,
    /// or type-argument positions.
    UndeclaredLifetime,

    // ---- Statement typing ----
    /// LHS and RHS of an assignment have incompatible types.
    AssignmentTypeMismatch,
    /// A call operand doesn't resolve to a function type.
    CallTargetNotFunction,
    /// Call site arg count differs from the function's param count.
    CallWrongArity,
    /// A call arg's type doesn't match the corresponding param type.
    CallArgTypeMismatch,
    /// `unborrow` was applied to a non-reference-typed place.
    UnborrowNonReference,

    // ---- Terminator typing ----
    /// `goto`, `branch true/false`, or `switchEnum` variant targets a
    /// block label that isn't defined in this function.
    TerminatorUndefinedTarget,
    /// `branch` condition operand doesn't have type `bool`.
    BranchConditionNotBool,
    /// `switchEnum(place)` where `place`'s type isn't a known enum.
    SwitchOnNonEnum,
    /// A `switchEnum` arm names a variant that isn't declared on
    /// the switched enum.
    SwitchArmUnknownVariant,

    // ---- Place resolution (from type_of_place) ----
    /// A place references a name that isn't in the locals map.
    UndeclaredVariable,
    /// Deref applied to a value whose type isn't a `&T` / `*T`.
    DerefOfNonPointer,
    /// Field projection applied to a non-struct type.
    FieldOfNonStruct,
    /// Field projection names a field that doesn't exist on the
    /// struct.
    NoSuchField,
    /// Downcast applied to a non-enum type.
    DowncastOfNonEnum,
    /// Downcast names a variant that doesn't exist on the enum.
    /// Shared with the rvalue-side `EnumConstr` check.
    NoSuchVariant,
    /// A place, field type, variant payload, param type, or local
    /// type mentions a type name that isn't declared.
    UndeclaredType,
    /// Index applied to a non-array type.
    IndexOfNonArray,
    /// Array index operand isn't an integer type.
    ArrayIndexNotInteger,
    /// Constant array index is out of bounds for the array's length.
    ArrayIndexOutOfBounds,

    // ---- Operand resolution (from type_of_operand) ----
    /// `Const::FnName` referenced a function that isn't declared.
    UndeclaredFunction,

    // ---- Rvalue resolution (from type_of_rvalue) ----
    /// `EnumConstr(N, V, _)` where `V` isn't a valid variant of `N`,
    /// or `N` isn't a declared enum.
    ///
    /// Note: `NoSuchVariant` handles the "V not on N" flavor; this
    /// covers "N doesn't exist" / "N is a struct".
    EnumConstrOnNonEnum,
    /// `EnumConstr(N, V, op)` where `op`'s type doesn't match V's
    /// declared payload type.
    EnumConstrPayloadTypeMismatch,
    /// Two array-literal elements have different types.
    ArrayLitElementTypeMismatch,
    /// Source of a pointer cast is not a pointer or reference.
    PtrCastSourceNotPointer,
    /// Target of a pointer cast is not a pointer or reference.
    PtrCastTargetNotPointer,

    // ---- Generic instantiation ----
    /// A `Custom(name, args)` reference passes the wrong number of
    /// type arguments for the decl (e.g. `Vec<i32, bool>` when `Vec`
    /// declared only one type parameter).
    TypeArgArity,
    /// A `Custom(name, args)` reference passes a type argument whose
    /// substructural class doesn't satisfy the corresponding param's
    /// declared bound (e.g. `Foo<Linear>` when `Foo<T: Copy>`).
    TypeArgBoundNotSatisfied,
}

impl From<TypeCheckCode> for DiagCode {
    fn from(code: TypeCheckCode) -> DiagCode {
        DiagCode::TypeCheck(code)
    }
}

#[derive(Debug, Clone)]
pub enum TypeDecl {
    Struct(StructDecl),
    Enum(EnumDecl),
}

impl TypeDecl {
    /// Shared declaration metadata (name, generics, markers). Present
    /// on both struct and enum variants at the same field name — this
    /// accessor lets callers read the metadata without pattern-matching
    /// on the variant.
    pub fn meta(&self) -> &DeclMeta {
        match self {
            TypeDecl::Struct(s) => &s.meta,
            TypeDecl::Enum(e) => &e.meta,
        }
    }
}
