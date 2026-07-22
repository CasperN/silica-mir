//! Constructors for MIR AST shapes. Glob-import for concise builders:
//!
//! ```ignore
//! use crate::mir::helpers::*;
//! let t = mut_ref_ty(i64_ty());
//! ```
//!
//! Naming: uniform suffix per category so `use ... ::*` never collides.
//! - Types get `_ty`.
//! - Places get `_place`.
//! - Operands get `_op`.
//! - ConstVals get `_const`.
//! - RValues get `_rv`.
//! - Statements get `_stmt`.
//! - Terminators get `_term`.

use crate::diagnostics::{DiagCode, Diagnostic};
use crate::mir::ast::*;

// ---------- Misc --------------

pub fn trivial_markers() -> Markers {
    Markers::from_iter([Marker::Copy, Marker::Drop])
}
pub fn basic_meta(name: impl Into<String>) -> DeclMeta {
    DeclMeta {
        name: name.into(),
        name_span: Span::default(),
        markers: trivial_markers(),
        lifetime_params: vec![],
        outlives: vec![],
        type_params: vec![],
    }
}

// ---------- Scalars ----------
//
// The `_ty` helpers return `Type` with `Span::default()`. Intended for
// synthetic construction (tests, checker-manufactured types, pretty-
// print round-trips) where no source position is meaningful. Parsers
// plumb real spans via `TypeKind::X.at(span)` directly.

pub fn i8_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::I8))
}
pub fn i16_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::I16))
}
pub fn i32_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::I32))
}
pub fn i64_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::I64))
}
pub fn u8_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::U8))
}
pub fn u16_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::U16))
}
pub fn u32_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::U32))
}
pub fn u64_ty() -> Type {
    Type::no_span(TypeKind::Int(IntTy::U64))
}
pub fn f32_ty() -> Type {
    Type::no_span(TypeKind::Float(FloatTy::F32))
}
pub fn f64_ty() -> Type {
    Type::no_span(TypeKind::Float(FloatTy::F64))
}
pub fn bool_ty() -> Type {
    Type::no_span(TypeKind::Bool)
}
pub fn unit_ty() -> Type {
    Type::no_span(TypeKind::Unit)
}
pub fn never_ty() -> Type {
    Type::no_span(TypeKind::Never)
}

pub fn int_ty(kind: IntTy) -> Type {
    Type::no_span(TypeKind::Int(kind))
}

pub fn float_ty(kind: FloatTy) -> Type {
    Type::no_span(TypeKind::Float(kind))
}

// ---------- Custom / Param ----------

/// A non-generic struct/enum reference: `Foo`.
pub fn custom_ty(name: impl Into<String>) -> Type {
    Type::no_span(TypeKind::Custom(name.into(), Vec::new(), Vec::new()))
}

/// A generic struct/enum instantiation: `Foo<T, U>`.
pub fn custom_ty_with_args(name: impl Into<String>, args: Vec<Type>) -> Type {
    Type::no_span(TypeKind::Custom(name.into(), Vec::new(), args))
}

/// A generic struct/enum instantiation with both lifetime and type
/// arguments: `Foo<'a, 'b, T, U>`.
pub fn custom_ty_generic(
    name: impl Into<String>,
    lifetimes: Vec<Lifetime>,
    args: Vec<Type>,
) -> Type {
    Type::no_span(TypeKind::Custom(name.into(), lifetimes, args))
}

/// A reference to an in-scope type parameter.
pub fn param_ty(name: impl Into<String>) -> Type {
    Type::no_span(TypeKind::Param(name.into()))
}

// ---------- References ----------

pub fn ref_ty(kind: RefKind, pointee: Type) -> Type {
    Type::no_span(TypeKind::Ref(kind, None, Box::new(pointee)))
}

/// Reference with an explicit lifetime annotation: `&'a T`, `&'a mut T`,
/// etc. For refs without a source-visible lifetime, use [`ref_ty`].
pub fn named_ref_ty(kind: RefKind, lt: Lifetime, pointee: Type) -> Type {
    Type::no_span(TypeKind::Ref(kind, Some(lt), Box::new(pointee)))
}
pub fn shared_ref_ty(pointee: Type) -> Type {
    ref_ty(RefKind::Shared, pointee)
}
pub fn mut_ref_ty(pointee: Type) -> Type {
    ref_ty(RefKind::Mut, pointee)
}
pub fn out_ref_ty(pointee: Type) -> Type {
    ref_ty(RefKind::Out, pointee)
}
pub fn drop_ref_ty(pointee: Type) -> Type {
    ref_ty(RefKind::Drop, pointee)
}
pub fn uninit_ref_ty(pointee: Type) -> Type {
    ref_ty(RefKind::Uninit, pointee)
}

/// Raw pointer `*T` — unsafe, no loan tracking.
pub fn raw_ptr_ty(pointee: Type) -> Type {
    Type::no_span(TypeKind::RawPtr(Box::new(pointee)))
}

// ---------- Aggregates ----------

pub fn array_ty(elem: Type, n: u64) -> Type {
    Type::no_span(TypeKind::Array(Box::new(elem), n))
}

/// Function-pointer type. MIR has no return type — results go through
/// `&out $return`.
pub fn fn_ty(params: Vec<Type>) -> Type {
    Type::no_span(TypeKind::Fn(params))
}

// ---------- Places ----------

pub fn var_place(name: impl Into<String>) -> Place {
    Place::Var(name.into())
}
pub fn field_place(base: Place, field: impl Into<String>) -> Place {
    Place::Field(Box::new(base), field.into())
}
pub fn downcast_place(base: Place, variant: impl Into<String>) -> Place {
    Place::Downcast(Box::new(base), variant.into())
}
pub fn deref_place(base: Place) -> Place {
    Place::Deref(Box::new(base))
}
pub fn index_place(base: Place, idx: Operand) -> Place {
    Place::Index(Box::new(base), Box::new(idx))
}

// ---------- Consts ----------

pub fn int_const(bits: u64, ty: IntTy) -> ConstVal {
    ConstVal::Int { bits, ty }
}
pub fn float_const(bits: u64, ty: FloatTy) -> ConstVal {
    ConstVal::Float { bits, ty }
}
pub fn bool_const(b: bool) -> ConstVal {
    ConstVal::Bool(b)
}
pub fn unit_const() -> ConstVal {
    ConstVal::Unit
}
/// Bare function-name const (non-generic).
pub fn fn_name_const(name: impl Into<String>) -> ConstVal {
    ConstVal::FnName(name.into(), Vec::new())
}
pub fn fn_name_const_with_args(name: impl Into<String>, args: Vec<Type>) -> ConstVal {
    ConstVal::FnName(name.into(), args)
}
pub fn byte_str_const(bytes: Vec<u8>) -> ConstVal {
    ConstVal::ByteStr(bytes)
}

// ---------- Operands ----------

pub fn copy_op(place: Place) -> Operand {
    Operand::Copy(place)
}
pub fn move_op(place: Place) -> Operand {
    Operand::Move(place)
}
pub fn const_op(c: ConstVal) -> Operand {
    Operand::Const(c)
}

// ---------- RValues ----------

pub fn use_rv(op: Operand) -> RValue {
    RValue::Use(op)
}
pub fn ref_rv(kind: RefKind, place: Place) -> RValue {
    RValue::Ref(kind, place)
}
pub fn raw_ref_rv(place: Place) -> RValue {
    RValue::RawRef(place)
}
pub fn enum_constr_rv(
    enum_name: impl Into<String>,
    variant: impl Into<String>,
    payload: Operand,
) -> RValue {
    RValue::EnumConstr(enum_name.into(), Vec::new(), variant.into(), payload)
}

pub fn enum_constr_rv_with_args(
    enum_name: impl Into<String>,
    args: Vec<Type>,
    variant: impl Into<String>,
    payload: Operand,
) -> RValue {
    RValue::EnumConstr(enum_name.into(), args, variant.into(), payload)
}
pub fn array_lit_rv(elems: Vec<Operand>) -> RValue {
    RValue::ArrayLit(elems)
}

// ---------- Statements ----------

pub fn assign_stmt(dst: Place, src: RValue, span: Span) -> Statement {
    Statement::new(StatementKind::Assign(dst, src), span)
}
pub fn call_stmt(callee: Operand, args: Vec<Operand>, span: Span) -> Statement {
    Statement::new(StatementKind::Call(callee, args), span)
}
pub fn drop_stmt(place: Place, span: Span) -> Statement {
    Statement::new(StatementKind::Drop(place), span)
}
pub fn unborrow_stmt(place: Place, span: Span) -> Statement {
    Statement::new(StatementKind::Unborrow(place), span)
}
pub fn require_uninit_stmt(place: Place, span: Span) -> Statement {
    Statement::new(StatementKind::RequireUninit(place), span)
}

// ---------- Terminators ----------

pub fn goto_term(label: impl Into<String>, span: Span) -> Terminator {
    Terminator::new(TerminatorKind::Goto(label.into()), span)
}
pub fn return_term(span: Span) -> Terminator {
    Terminator::new(TerminatorKind::Return, span)
}
pub fn branch_term(
    cond: Operand,
    true_label: impl Into<String>,
    false_label: impl Into<String>,
    span: Span,
) -> Terminator {
    Terminator::new(
        TerminatorKind::Branch {
            cond,
            true_label: true_label.into(),
            false_label: false_label.into(),
        },
        span,
    )
}
pub fn switch_enum_term(place: Place, cases: Vec<(String, String)>, span: Span) -> Terminator {
    Terminator::new(TerminatorKind::SwitchEnum { place, cases }, span)
}
pub fn abort_term(span: Span) -> Terminator {
    Terminator::new(TerminatorKind::Abort, span)
}
pub fn unreachable_term(span: Span) -> Terminator {
    Terminator::new(TerminatorKind::Unreachable, span)
}

// ---------- Diagnostics ----------

/// Build a diagnostic with function and block context attached. Every
/// per-fn per-block checker emits errors through this shape; the helper
/// lives here so each subsystem doesn't redefine the same 3-line
/// builder. Declaration-scope checks (e.g.
/// `substructural::composition`) don't have a block cursor and use
/// `Diagnostic::new(...)` directly.
pub fn diag(
    code: impl Into<DiagCode>,
    span: Span,
    func: &Function,
    block: &BasicBlock,
    msg: String,
) -> Diagnostic {
    Diagnostic::new(code, span, msg)
        .in_function(&func.meta.name)
        .in_block(&block.label)
}
