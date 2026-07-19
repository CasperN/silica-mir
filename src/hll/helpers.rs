//! Constructors for HLL AST shapes. Glob-import for concise builders:
//!
//! ```ignore
//! use crate::hll::helpers::*;
//! let t = mut_ref_ty(i64_ty());
//! ```
//!
//! Mirrors `crate::mir::helpers` — same names for the shared type
//! shapes, so lowering code can qualify one side (`use hll::helpers as h;`)
//! and glob-import the other.

use crate::common::{FloatTy, IntTy, RefKind};
use crate::hll::ast::*;

// ---------- Scalars ----------

pub fn i8_ty() -> Type {
    Type::Int(IntTy::I8)
}
pub fn i16_ty() -> Type {
    Type::Int(IntTy::I16)
}
pub fn i32_ty() -> Type {
    Type::Int(IntTy::I32)
}
pub fn i64_ty() -> Type {
    Type::Int(IntTy::I64)
}
pub fn u8_ty() -> Type {
    Type::Int(IntTy::U8)
}
pub fn u16_ty() -> Type {
    Type::Int(IntTy::U16)
}
pub fn u32_ty() -> Type {
    Type::Int(IntTy::U32)
}
pub fn u64_ty() -> Type {
    Type::Int(IntTy::U64)
}
pub fn f32_ty() -> Type {
    Type::Float(FloatTy::F32)
}
pub fn f64_ty() -> Type {
    Type::Float(FloatTy::F64)
}
pub fn bool_ty() -> Type {
    Type::Bool
}
pub fn unit_ty() -> Type {
    Type::Unit
}
pub fn never_ty() -> Type {
    Type::Never
}

pub fn int_ty(kind: IntTy) -> Type {
    Type::Int(kind)
}
pub fn float_ty(kind: FloatTy) -> Type {
    Type::Float(kind)
}

// ---------- Custom / Param ----------

/// A non-generic struct/enum reference: `Foo`.
pub fn custom_ty(name: impl Into<String>) -> Type {
    Type::Custom(name.into(), Vec::new(), Vec::new())
}

/// A generic struct/enum instantiation: `Foo<T, U>`.
pub fn custom_ty_with_args(name: impl Into<String>, args: Vec<Type>) -> Type {
    Type::Custom(name.into(), Vec::new(), args)
}

/// A reference to an in-scope type parameter.
pub fn param_ty(name: impl Into<String>) -> Type {
    Type::Param(name.into())
}

// ---------- References ----------

pub fn ref_ty(kind: RefKind, pointee: Type) -> Type {
    Type::Ref(kind, None, Box::new(pointee))
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

pub fn raw_ptr_ty(pointee: Type) -> Type {
    Type::RawPtr(Box::new(pointee))
}

// ---------- Aggregates ----------

pub fn array_ty(elem: Type, n: usize) -> Type {
    Type::Array(Box::new(elem), n)
}

/// HLL function type has an explicit return type (unlike MIR, whose
/// results go through `&out $return`).
pub fn fn_ty(params: Vec<Type>, ret: Type) -> Type {
    Type::Fn(params, Box::new(ret))
}

// ---------- Inference ----------

/// Fresh type-variable for HM inference. Only builders in `type_check`
/// should call this — general code shouldn't produce raw `Var`s.
pub fn var_ty(id: usize) -> Type {
    Type::Var(id)
}
pub fn int_var_ty(id: usize) -> Type {
    Type::IntVar(id)
}
pub fn float_var_ty(id: usize) -> Type {
    Type::FloatVar(id)
}
pub fn error_ty() -> Type {
    Type::Error
}
