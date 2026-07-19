//! Intrinsic functions — a compiler-recognized "library" of primitive
//! operations. Silica-MIR has no built-in arithmetic syntax; instead,
//! operations are ordinary `call` statements to functions whose names
//! use the reserved `$` prefix. Users can't spell `$*` identifiers in
//! the higher-level language, so the intrinsic namespace is
//! guaranteed collision-free.
//!
//! ## Contract
//! - Intrinsic specs live in [`all`]. Each entry declares operand
//!   types (used to build extern signatures via [`prelude_fns`]) and
//!   an `emit` closure that owns its LLVM lowering.
//! - `Env::build` preloads the signatures into `Env::functions`.
//! - Codegen intercepts `call $name(...)`, materializes the input
//!   operands, calls `spec.emit(inputs, mk_name)` to get back the
//!   LLVM lines + the SSA name holding the result, then stores the
//!   result through the `&out` pointer. The intrinsic symbol never
//!   appears in the emitted `.ll`.
//! - Codegen dumps the union of every spec's `llvm_declares` into
//!   the module preamble, so intrinsics that lower to `@llvm.*`
//!   calls get their `declare` lines automatically.
//!
//! ## Naming
//! `$<type>_<op>` for ops, `$<from>_to_<to>` for casts. Signedness of
//! the operand type determines which LLVM instruction the emit fn
//! picks (`sdiv`/`udiv`, `ashr`/`lshr`, `sitofp`/`uitofp`, etc.).

use crate::mir::ast::*;
use crate::mir::helpers::*;

/// One intrinsic. `inputs`/`result` build the extern signature; `emit`
/// handles LLVM lowering.
pub struct IntrinsicSpec {
    pub name: String,
    pub inputs: Vec<Type>,
    pub result: Type,
    /// Emit the intrinsic's LLVM instruction sequence. See [`Emit`].
    pub emit: Emit,
    /// LLVM `declare ...` lines this intrinsic requires (e.g.
    /// `"declare i64 @llvm.ctpop.i64(i64)"`). Deduplicated across
    /// all specs; emitted once in the module preamble. Empty for
    /// intrinsics that lower to inline instructions only.
    pub llvm_declares: &'static [&'static str],
}

/// The emit closure's signature.
///
/// - `inputs`: SSA names already holding each input value (in
///   declaration order, `&out` param excluded).
/// - `mk_name`: allocates a fresh `%t.N` SSA name.
///
/// Returns `(lines_to_write, result_ssa)`: the LLVM lines to append
/// to the current function body and the SSA name holding the final
/// result. Codegen stores that result through the intrinsic's
/// `&out` param afterward.
///
/// Boxed (rather than a plain `fn` pointer) so factory functions
/// like [`bin_int`] can return closures that capture their op
/// mnemonic. One heap allocation per intrinsic, built once by
/// [`all`].
pub type Emit = Box<dyn Fn(&[String], &mut dyn FnMut() -> String) -> (Vec<String>, String)>;

const ALL_INT_TYS: &[IntTy] = &[
    IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64,
    IntTy::U8, IntTy::U16, IntTy::U32, IntTy::U64,
];
const SIGNED_INT_TYS: &[IntTy] = &[IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64];
const FLOAT_TYS: &[FloatTy] = &[FloatTy::F32, FloatTy::F64];

#[cfg(test)]
const UNSIGNED_INT_TYS: &[IntTy] = &[IntTy::U8, IntTy::U16, IntTy::U32, IntTy::U64];

/// Every intrinsic the compiler recognizes. Adding a new intrinsic =
/// adding one row (or one loop iteration) here.
// TODO: Should this be an IndexMap for fast lookup by name?
pub fn all() -> Vec<IntrinsicSpec> {
    let mut out = Vec::new();

    // ---------- Integer arithmetic ----------

    for &int_kind in ALL_INT_TYS {
        let value_ty = int_ty(int_kind);
        let type_name = int_kind.name();
        let bits = int_kind.bits();
        out.push(int_binop(format!("${}_add", type_name), value_ty.clone(), "add", bits));
        out.push(int_binop(format!("${}_sub", type_name), value_ty.clone(), "sub", bits));
        out.push(int_binop(format!("${}_mul", type_name), value_ty.clone(), "mul", bits));
        // Signedness-dispatched division / remainder.
        let (div_op, rem_op) = if int_kind.is_signed() {
            ("sdiv", "srem")
        } else {
            ("udiv", "urem")
        };
        out.push(int_binop(format!("${}_div", type_name), value_ty.clone(), div_op, bits));
        out.push(int_binop(format!("${}_rem", type_name), value_ty.clone(), rem_op, bits));
        // Bitwise — same LLVM ops for signed/unsigned.
        out.push(int_binop(format!("${}_and", type_name), value_ty.clone(), "and", bits));
        out.push(int_binop(format!("${}_or", type_name), value_ty.clone(), "or", bits));
        out.push(int_binop(format!("${}_xor", type_name), value_ty.clone(), "xor", bits));
        // Shifts. shl is signedness-independent; right shift dispatches.
        out.push(int_binop(format!("${}_shl", type_name), value_ty.clone(), "shl", bits));
        let shr_op = if int_kind.is_signed() { "ashr" } else { "lshr" };
        out.push(int_binop(format!("${}_shr", type_name), value_ty.clone(), shr_op, bits));
    }

    // Negation (signed only — unsigned negation without conversion is
    // nonsense at the type level).
    for &int_kind in SIGNED_INT_TYS {
        let value_ty = int_ty(int_kind);
        let bits = int_kind.bits();
        out.push(IntrinsicSpec {
            name: format!("${}_neg", int_kind.name()),
            inputs: vec![value_ty.clone()],
            result: value_ty,
            emit: int_neg(bits),
            llvm_declares: &[],
        });
    }

    // ---------- Integer comparisons (result: bool) ----------

    for &int_kind in ALL_INT_TYS {
        let value_ty = int_ty(int_kind);
        let type_name = int_kind.name();
        let bits = int_kind.bits();
        // eq/ne are signedness-independent.
        out.push(int_cmp(format!("${}_eq", type_name), value_ty.clone(), "eq", bits));
        out.push(int_cmp(format!("${}_ne", type_name), value_ty.clone(), "ne", bits));
        // Ordered comparisons pick signed vs unsigned predicates.
        let (lt, le, gt, ge) = if int_kind.is_signed() {
            ("slt", "sle", "sgt", "sge")
        } else {
            ("ult", "ule", "ugt", "uge")
        };
        out.push(int_cmp(format!("${}_lt", type_name), value_ty.clone(), lt, bits));
        out.push(int_cmp(format!("${}_le", type_name), value_ty.clone(), le, bits));
        out.push(int_cmp(format!("${}_gt", type_name), value_ty.clone(), gt, bits));
        out.push(int_cmp(format!("${}_ge", type_name), value_ty.clone(), ge, bits));
    }

    // ---------- Float arithmetic ----------

    for &float_kind in FLOAT_TYS {
        let value_ty = float_ty(float_kind);
        let type_name = float_kind.name();
        let llvm_ty = float_llvm_ty(float_kind);
        out.push(float_binop_spec(format!("${}_add", type_name), value_ty.clone(), "fadd", llvm_ty));
        out.push(float_binop_spec(format!("${}_sub", type_name), value_ty.clone(), "fsub", llvm_ty));
        out.push(float_binop_spec(format!("${}_mul", type_name), value_ty.clone(), "fmul", llvm_ty));
        out.push(float_binop_spec(format!("${}_div", type_name), value_ty.clone(), "fdiv", llvm_ty));
        out.push(IntrinsicSpec {
            name: format!("${}_neg", type_name),
            inputs: vec![value_ty.clone()],
            result: value_ty,
            emit: float_neg(llvm_ty),
            llvm_declares: &[],
        });
    }

    // ---------- Float comparisons (result: bool) ----------
    //
    // Ordered predicates: NaN inputs make the comparison false.
    // Silica has no unordered predicates yet; users who need
    // NaN-permissive semantics can build them from these plus
    // an explicit `$fN_ne(x, x)` NaN check.

    for &float_kind in FLOAT_TYS {
        let value_ty = float_ty(float_kind);
        let type_name = float_kind.name();
        let llvm_ty = float_llvm_ty(float_kind);
        for (op, pred) in [
            ("eq", "oeq"),
            ("ne", "one"),
            ("lt", "olt"),
            ("le", "ole"),
            ("gt", "ogt"),
            ("ge", "oge"),
        ] {
            out.push(IntrinsicSpec {
                name: format!("${}_{}", type_name, op),
                inputs: vec![value_ty.clone(), value_ty.clone()],
                result: bool_ty(),
                emit: fcmp(pred, llvm_ty),
                llvm_declares: &[],
            });
        }
    }

    // ---------- Casts ----------

    // Integer width conversions:
    //   - signed source, wider target  → sext
    //   - unsigned source, wider target → zext
    //   - same signedness, narrower    → trunc
    // Width preserved but signedness changed (i32 ↔ u32) is a
    // no-op at the LLVM level; we don't emit a dedicated intrinsic
    // for it (bit-identical, no conversion needed).
    for &from in ALL_INT_TYS {
        for &to in ALL_INT_TYS {
            if from == to {
                continue;
            }
            if from.bits() == to.bits() {
                // Same-width signedness reinterpret (e.g. `i32 as u32`).
                // Nop at the LLVM level; the intrinsic exists so the
                // MIR type system can express the type change explicitly.
                out.push(IntrinsicSpec {
                    name: format!("${}_to_{}", from.name(), to.name()),
                    inputs: vec![int_ty(from)],
                    result: int_ty(to),
                    emit: nop_reinterpret_emit(),
                    llvm_declares: &[],
                });
                continue;
            }
            let (op, name) = if to.bits() > from.bits() {
                if from.is_signed() {
                    ("sext", format!("${}_to_{}", from.name(), to.name()))
                } else {
                    ("zext", format!("${}_to_{}", from.name(), to.name()))
                }
            } else {
                ("trunc", format!("${}_to_{}", from.name(), to.name()))
            };
            out.push(int_cast_spec(name, int_ty(from), int_ty(to), op));
        }
    }

    // Int ↔ Float. We cover the 8 int types × 2 float types both
    // directions; the LLVM op picks signedness for the int side.
    for &int_kind in ALL_INT_TYS {
        for &float_kind in FLOAT_TYS {
            // int → float
            let op = if int_kind.is_signed() { "sitofp" } else { "uitofp" };
            out.push(IntrinsicSpec {
                name: format!("${}_to_{}", int_kind.name(), float_kind.name()),
                inputs: vec![int_ty(int_kind)],
                result: float_ty(float_kind),
                emit: cast_emit(op, int_llvm_ty(int_kind), float_llvm_ty(float_kind)),
                llvm_declares: &[],
            });
            // float → int
            let op = if int_kind.is_signed() { "fptosi" } else { "fptoui" };
            out.push(IntrinsicSpec {
                name: format!("${}_to_{}", float_kind.name(), int_kind.name()),
                inputs: vec![float_ty(float_kind)],
                result: int_ty(int_kind),
                emit: cast_emit(op, float_llvm_ty(float_kind), int_llvm_ty(int_kind)),
                llvm_declares: &[],
            });
        }
    }

    // Float ↔ Float.
    out.push(IntrinsicSpec {
        name: "$f32_to_f64".to_string(),
        inputs: vec![f32_ty()],
        result: f64_ty(),
        emit: cast_emit("fpext", "float", "double"),
        llvm_declares: &[],
    });
    out.push(IntrinsicSpec {
        name: "$f64_to_f32".to_string(),
        inputs: vec![f64_ty()],
        result: f32_ty(),
        emit: cast_emit("fptrunc", "double", "float"),
        llvm_declares: &[],
    });

    // Bool ↔ Int. `bool_to_iN` = zext from i1. `iN_to_bool` =
    // truncate to i1 (only the low bit matters).
    for &int_kind in ALL_INT_TYS {
        out.push(IntrinsicSpec {
            name: format!("$bool_to_{}", int_kind.name()),
            inputs: vec![bool_ty()],
            result: int_ty(int_kind),
            emit: cast_emit("zext", "i1", int_llvm_ty(int_kind)),
            llvm_declares: &[],
        });
        // Truncation of an int wider than 1 bit to bool. For i8
        // (same width as i1 storage but different semantics), the
        // trunc from i8 to i1 keeps only the low bit — matching the
        // C "nonzero-becomes-true" semantics if the caller pre-
        // computes `x != 0`. We don't collapse to icmp here; that's
        // the caller's job via `$iN_ne(x, 0)`.
        if int_kind.bits() > 1 {
            out.push(IntrinsicSpec {
                name: format!("${}_to_bool", int_kind.name()),
                inputs: vec![int_ty(int_kind)],
                result: bool_ty(),
                emit: cast_emit("trunc", int_llvm_ty(int_kind), "i1"),
                llvm_declares: &[],
            });
        }
    }

    // ---------- LLVM-intrinsic-backed ops ----------

    // Population count / leading zeros / trailing zeros — per width.
    for &int_kind in ALL_INT_TYS {
        let value_ty = int_ty(int_kind);
        let bits = int_kind.bits();
        let type_name = int_kind.name();
        out.push(llvm_unary_intrinsic(
            format!("${}_popcount", type_name),
            value_ty.clone(),
            format!("@llvm.ctpop.i{}", bits),
            bits,
        ));
        out.push(llvm_unary_intrinsic(
            format!("${}_clz", type_name),
            value_ty.clone(),
            format!("@llvm.ctlz.i{}", bits),
            bits,
        ));
        out.push(llvm_unary_intrinsic(
            format!("${}_ctz", type_name),
            value_ty,
            format!("@llvm.cttz.i{}", bits),
            bits,
        ));
    }

    // Square root (float).
    for &float_kind in FLOAT_TYS {
        let value_ty = float_ty(float_kind);
        let llvm_ty = float_llvm_ty(float_kind);
        let type_name = float_kind.name();
        out.push(llvm_float_unary(
            format!("${}_sqrt", type_name),
            value_ty,
            format!("@llvm.sqrt.{}", llvm_ty),
            llvm_ty,
        ));
    }

    out
}

/// Look up an intrinsic by name.
pub fn lookup(name: &str) -> Option<IntrinsicSpec> {
    all().into_iter().find(|s| s.name == name)
}

/// Return prebuilt `Function` signatures for every intrinsic in [`all`],
/// ready to insert into `Env::functions`.
pub fn prelude_fns() -> Vec<Function> {
    all().into_iter().map(spec_to_function).collect()
}


fn spec_to_function(spec: IntrinsicSpec) -> Function {
    let mut params = Vec::with_capacity(spec.inputs.len() + 1);
    for (i, ty) in spec.inputs.iter().enumerate() {
        params.push(Param {
            name: format!("in{}", i),
            ty: ty.clone(),
            span: SPAN,
        });
    }
    params.push(Param {
        name: "out".to_string(),
        ty: out_ref_ty(spec.result),
        span: SPAN,
    });
    Function {
        name: spec.name,
        name_span: SPAN,
        is_extern: true,
        lifetime_params: Vec::new(),
            signature_outlives: Vec::new(),
        type_params: Vec::new(),
        params,
        body: None,
    }
}

const SPAN: Span = Span { line: 0, col: 0, end_line: 0, end_col: 0 };

/// True if `name` is an intrinsic name (starts with the reserved `$`).
pub fn is_intrinsic(name: &str) -> bool {
    name.starts_with('$')
}

// ---------- Spec-builder helpers ----------
//
// These build IntrinsicSpecs for the common shapes. Kept in this file
// — codegen never sees them — so the "one-file rule" for adding
// intrinsics stays true.

/// Two-operand integer op producing the same integer type.
fn int_binop(name: String, ty: Type, llvm_op: &'static str, bits: u32) -> IntrinsicSpec {
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone(), ty.clone()],
        result: ty,
        emit: bin_int(llvm_op, bits),
        llvm_declares: &[],
    }
}

/// Two-operand integer comparison → bool.
fn int_cmp(name: String, ty: Type, pred: &'static str, bits: u32) -> IntrinsicSpec {
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone(), ty],
        result: bool_ty(),
        emit: icmp(pred, bits),
        llvm_declares: &[],
    }
}

/// Two-operand float op producing the same float type.
fn float_binop_spec(
    name: String,
    ty: Type,
    llvm_op: &'static str,
    llvm_ty: &'static str,
) -> IntrinsicSpec {
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone(), ty.clone()],
        result: ty,
        emit: float_binop(llvm_op, llvm_ty),
        llvm_declares: &[],
    }
}

/// One-operand int-to-int cast (sext / zext / trunc).
fn int_cast_spec(name: String, from: Type, to: Type, op: &'static str) -> IntrinsicSpec {
    let from_llvm = int_kindpe_llvm(&from);
    let to_llvm = int_kindpe_llvm(&to);
    IntrinsicSpec {
        name,
        inputs: vec![from],
        result: to,
        emit: cast_emit(op, from_llvm, to_llvm),
        llvm_declares: &[],
    }
}

fn int_kindpe_llvm(ty: &Type) -> &'static str {
    match ty {
        Type::Int(t) => int_llvm_ty(*t),
        _ => panic!("int_kindpe_llvm: not an int type: {:?}", ty),
    }
}

fn int_llvm_ty(t: IntTy) -> &'static str {
    match t {
        IntTy::I8 | IntTy::U8 => "i8",
        IntTy::I16 | IntTy::U16 => "i16",
        IntTy::I32 | IntTy::U32 => "i32",
        IntTy::I64 | IntTy::U64 => "i64",
    }
}

fn float_llvm_ty(t: FloatTy) -> &'static str {
    match t {
        FloatTy::F32 => "float",
        FloatTy::F64 => "double",
    }
}

/// Two-operand integer op emitted as `%r = <op> i<bits> %a, %b`.
pub fn bin_int(op: &'static str, bits: u32) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = {} i{} {}, {}", result, op, bits, inputs[0], inputs[1]);
        (vec![line], result)
    })
}

/// Integer comparison emitted as `%r = icmp <pred> i<bits> %a, %b`.
/// Result is always `i1` (Silica `bool`).
pub fn icmp(pred: &'static str, bits: u32) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = icmp {} i{} {}, {}", result, pred, bits, inputs[0], inputs[1]);
        (vec![line], result)
    })
}

/// Two-operand float op emitted as `%r = <op> <fty> %a, %b`.
/// `llvm_ty` is `"float"` or `"double"`.
pub fn float_binop(op: &'static str, llvm_ty: &'static str) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = {} {} {}, {}", result, op, llvm_ty, inputs[0], inputs[1]);
        (vec![line], result)
    })
}

/// Float comparison emitted as `%r = fcmp <pred> <fty> %a, %b`.
/// Result is always `i1` (Silica `bool`).
pub fn fcmp(pred: &'static str, llvm_ty: &'static str) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = fcmp {} {} {}, {}", result, pred, llvm_ty, inputs[0], inputs[1]);
        (vec![line], result)
    })
}

/// Integer negation via LLVM's `sub 0, x` idiom (LLVM has no dedicated
/// integer `neg`).
pub fn int_neg(bits: u32) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = sub i{} 0, {}", result, bits, inputs[0]);
        (vec![line], result)
    })
}

/// Float negation via LLVM's `fneg` (available since LLVM 8).
pub fn float_neg(llvm_ty: &'static str) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = fneg {} {}", result, llvm_ty, inputs[0]);
        (vec![line], result)
    })
}

/// One-operand cast emitted as `%r = <op> <from_ty> %in to <to_ty>`.
/// Handles sext/zext/trunc/sitofp/uitofp/fptosi/fptoui/fpext/fptrunc.
pub fn cast_emit(op: &'static str, from_ty: &'static str, to_ty: &'static str) -> Emit {
    Box::new(move |inputs, mk_name| {
        let result = mk_name();
        let line = format!("  {} = {} {} {} to {}", result, op, from_ty, inputs[0], to_ty);
        (vec![line], result)
    })
}

/// Same-width signedness reinterpret (e.g. `i32 as u32`, `u64 as i64`).
/// LLVM has no distinction between signed and unsigned integer types —
/// both are `iN` — so the reinterpret is a nop. The Silica MIR type
/// system still differs on the two, so we need an intrinsic to bridge
/// them. Emit returns the input register directly; no LLVM instructions.
pub fn nop_reinterpret_emit() -> Emit {
    Box::new(move |inputs, _mk_name| (vec![], inputs[0].clone()))
}

/// One-argument `@llvm.<name>.iN` call. `ctlz` and `cttz` take a
/// second `i1` "is_zero_undef" argument; we always pass `false`.
fn llvm_unary_intrinsic(name: String, ty: Type, llvm_name: String, bits: u32) -> IntrinsicSpec {
    // The @llvm.ctlz/cttz intrinsics take an extra `i1` arg.
    let takes_zero_undef = llvm_name.contains(".ctlz.") || llvm_name.contains(".cttz.");
    // Deduplicated declare line — leak once to the static pool.
    let decl = format!(
        "declare i{bits} {llvm_name}(i{bits}{})",
        if takes_zero_undef { ", i1" } else { "" }
    );
    let decl_static: &'static str = Box::leak(decl.into_boxed_str());
    let llvm_name_owned = llvm_name.clone();
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone()],
        result: ty,
        emit: Box::new(move |inputs, mk_name| {
            let result = mk_name();
            let extra = if takes_zero_undef { ", i1 false" } else { "" };
            let line = format!(
                "  {} = call i{} {}(i{} {}{})",
                result, bits, llvm_name_owned, bits, inputs[0], extra
            );
            (vec![line], result)
        }),
        llvm_declares: Box::leak(vec![decl_static].into_boxed_slice()),
    }
}

/// One-argument `@llvm.<name>.<f32|f64>` call.
fn llvm_float_unary(
    name: String,
    ty: Type,
    llvm_name: String,
    llvm_ty: &'static str,
) -> IntrinsicSpec {
    let decl = format!("declare {llvm_ty} {llvm_name}({llvm_ty})");
    let decl_static: &'static str = Box::leak(decl.into_boxed_str());
    let llvm_name_owned = llvm_name.clone();
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone()],
        result: ty,
        emit: Box::new(move |inputs, mk_name| {
            let result = mk_name();
            let line = format!(
                "  {} = call {} {}({} {})",
                result, llvm_ty, llvm_name_owned, llvm_ty, inputs[0]
            );
            (vec![line], result)
        }),
        llvm_declares: Box::leak(vec![decl_static].into_boxed_slice()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---------- is_intrinsic ----------

    #[test]
    fn is_intrinsic_matches_dollar_prefix() {
        assert!(is_intrinsic("$i64_add"));
        assert!(is_intrinsic("$foo"));
        assert!(is_intrinsic("$"));
    }

    #[test]
    fn is_intrinsic_rejects_plain_names() {
        assert!(!is_intrinsic("i64_add"));
        assert!(!is_intrinsic("silica_print"));
        assert!(!is_intrinsic(""));
    }

    // ---------- lookup ----------

    #[test]
    fn lookup_finds_known_intrinsic() {
        let spec = lookup("$i64_add").expect("$i64_add should exist");
        assert_eq!(spec.name, "$i64_add");
        assert_eq!(spec.inputs.len(), 2);
        assert_eq!(spec.result, i64_ty());
    }

    #[test]
    fn lookup_returns_none_for_unknown() {
        assert!(lookup("$never_defined").is_none());
        assert!(lookup("i64_add").is_none()); // missing $
        assert!(lookup("").is_none());
    }

    #[test]
    fn all_intrinsic_names_unique() {
        // Guard against accidental duplication in the generation
        // loops — every name in `all()` must be distinct.
        let mut seen = std::collections::BTreeSet::new();
        for spec in all() {
            assert!(
                seen.insert(spec.name.clone()),
                "duplicate intrinsic name: {}",
                spec.name
            );
        }
    }

    #[test]
    fn per_width_arith_coverage() {
        // Every int type has the full arithmetic surface.
        for int_kind in ALL_INT_TYS {
            let type_name = int_kind.name();
            for op in ["add", "sub", "mul", "div", "rem", "and", "or", "xor", "shl", "shr"] {
                let full = format!("${}_{}", type_name, op);
                assert!(
                    lookup(&full).is_some(),
                    "expected intrinsic {}",
                    full
                );
            }
        }
        // Neg only for signed.
        for int_kind in SIGNED_INT_TYS {
            assert!(lookup(&format!("${}_neg", int_kind.name())).is_some());
        }
        for int_kind in UNSIGNED_INT_TYS {
            assert!(lookup(&format!("${}_neg", int_kind.name())).is_none());
        }
    }

    #[test]
    fn per_width_cmp_coverage() {
        for int_kind in ALL_INT_TYS {
            let type_name = int_kind.name();
            for op in ["eq", "ne", "lt", "le", "gt", "ge"] {
                assert!(
                    lookup(&format!("${}_{}", type_name, op)).is_some(),
                    "missing ${}_{}", type_name, op
                );
            }
        }
    }

    #[test]
    fn float_full_surface() {
        for float_kind in FLOAT_TYS {
            let type_name = float_kind.name();
            for op in ["add", "sub", "mul", "div", "neg", "sqrt"] {
                assert!(
                    lookup(&format!("${}_{}", type_name, op)).is_some(),
                    "missing ${}_{}", type_name, op
                );
            }
            for op in ["eq", "ne", "lt", "le", "gt", "ge"] {
                assert!(
                    lookup(&format!("${}_{}", type_name, op)).is_some(),
                    "missing ${}_{}", type_name, op
                );
            }
        }
    }

    // ---------- prelude_fns ----------

    #[test]
    fn prelude_produces_one_extern_fn_per_spec() {
        let fns = prelude_fns();
        assert_eq!(fns.len(), all().len());
        for f in &fns {
            assert!(f.is_extern, "intrinsic {} should be extern", f.name);
            assert!(f.body.is_none(), "intrinsic {} should have no body", f.name);
        }
    }

    #[test]
    fn prelude_signatures_end_in_out_ref() {
        // Every intrinsic's last param is `&out ResultTy`.
        for f in prelude_fns() {
            let last = f.params.last().unwrap();
            assert_eq!(last.name, "out");
            match &last.ty {
                Type::Ref(RefKind::Out, _, _) => {}
                other => panic!(
                    "intrinsic {} last param should be &out, got {:?}",
                    f.name, other
                ),
            }
        }
    }

    #[test]
    fn prelude_signature_shape_matches_spec() {
        // `$i64_add` → params [in0: i64, in1: i64, out: &out i64].
        let f = prelude_fns()
            .into_iter()
            .find(|f| f.name == "$i64_add")
            .unwrap();
        assert_eq!(f.params.len(), 3);
        assert_eq!(f.params[0].ty, i64_ty());
        assert_eq!(f.params[1].ty, i64_ty());
        assert_eq!(f.params[2].ty, out_ref_ty(i64_ty()));
    }

    // ---------- llvm_declares (on the spec, not the union) ----------

    #[test]
    fn popcount_spec_carries_its_declare() {
        // Guards the "spec owns its declare" contract. Codegen's
        // `llvm_declares_needed` (in `codegen/mod.rs`) reads from
        // this per-spec field, so the sanity check lives here.
        let spec = lookup("$i64_popcount").unwrap();
        assert_eq!(spec.llvm_declares, &["declare i64 @llvm.ctpop.i64(i64)"]);
    }

    #[test]
    fn ctlz_declare_includes_i1_arg() {
        // ctlz/cttz take an extra i1 "is_zero_undef" arg on the LLVM
        // side. The declare line must include it.
        let spec = lookup("$i32_clz").unwrap();
        assert_eq!(spec.llvm_declares, &["declare i32 @llvm.ctlz.i32(i32, i1)"]);
    }

    // ---------- emit closures ----------

    /// Build an SSA-name allocator that hands out sequential `%t.0`,
    /// `%t.1`, ... — matches what codegen does. Useful for exercising
    /// emit closures directly.
    fn alloc_ssa_name_for_tests() -> impl FnMut() -> String {
        let mut counter = 0u32;
        move || {
            let name = format!("%t.{}", counter);
            counter += 1;
            name
        }
    }

    #[test]
    fn emit_i64_add_produces_single_add_line() {
        let spec = lookup("$i64_add").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, result) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = add i64 %a, %b".to_string()]);
        assert_eq!(result, "%t.0");
    }

    #[test]
    fn emit_i64_neg_uses_sub_zero_idiom() {
        let spec = lookup("$i64_neg").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = sub i64 0, %x".to_string()]);
    }

    #[test]
    fn emit_f64_mul_uses_double_type() {
        let spec = lookup("$f64_mul").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = fmul double %a, %b".to_string()]);
    }

    #[test]
    fn emit_f64_neg_uses_fneg() {
        let spec = lookup("$f64_neg").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = fneg double %x".to_string()]);
    }

    #[test]
    fn emit_f64_lt_uses_ordered_predicate() {
        let spec = lookup("$f64_lt").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = fcmp olt double %a, %b".to_string()]);
    }

    #[test]
    fn emit_signed_shr_uses_ashr() {
        let spec = lookup("$i32_shr").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = ashr i32 %a, %b".to_string()]);
    }

    #[test]
    fn emit_unsigned_shr_uses_lshr() {
        let spec = lookup("$u32_shr").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = lshr i32 %a, %b".to_string()]);
    }

    #[test]
    fn emit_signed_div_uses_sdiv() {
        let spec = lookup("$i32_div").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = sdiv i32 %a, %b".to_string()]);
    }

    #[test]
    fn emit_unsigned_div_uses_udiv() {
        let spec = lookup("$u32_div").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = udiv i32 %a, %b".to_string()]);
    }

    #[test]
    fn emit_widening_sext() {
        let spec = lookup("$i8_to_i64").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = sext i8 %x to i64".to_string()]);
    }

    #[test]
    fn emit_widening_zext() {
        let spec = lookup("$u8_to_u64").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = zext i8 %x to i64".to_string()]);
    }

    #[test]
    fn emit_narrowing_trunc() {
        let spec = lookup("$i64_to_i32").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = trunc i64 %x to i32".to_string()]);
    }

    #[test]
    fn emit_int_to_float_sitofp() {
        let spec = lookup("$i64_to_f64").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = sitofp i64 %x to double".to_string()]);
    }

    #[test]
    fn emit_float_to_int_fptoui() {
        let spec = lookup("$f64_to_u32").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = fptoui double %x to i32".to_string()]);
    }

    #[test]
    fn emit_float_widening_uses_fpext() {
        let spec = lookup("$f32_to_f64").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = fpext float %x to double".to_string()]);
    }

    #[test]
    fn emit_bool_to_i32_zext() {
        let spec = lookup("$bool_to_i32").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%b".to_string()], &mut mk_name);
        assert_eq!(lines, vec!["  %t.0 = zext i1 %b to i32".to_string()]);
    }

    #[test]
    fn emit_popcount_uses_llvm_intrinsic() {
        let spec = lookup("$i64_popcount").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, result) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(
            lines,
            vec!["  %t.0 = call i64 @llvm.ctpop.i64(i64 %x)".to_string()]
        );
        assert_eq!(result, "%t.0");
        // And it declares the extern.
        assert_eq!(spec.llvm_declares, &["declare i64 @llvm.ctpop.i64(i64)"]);
    }

    #[test]
    fn emit_ctlz_passes_zero_undef_false() {
        let spec = lookup("$i32_clz").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(
            lines,
            vec!["  %t.0 = call i32 @llvm.ctlz.i32(i32 %x, i1 false)".to_string()]
        );
    }

    #[test]
    fn emit_sqrt_uses_llvm_intrinsic() {
        let spec = lookup("$f64_sqrt").unwrap();
        let mut mk_name = alloc_ssa_name_for_tests();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk_name);
        assert_eq!(
            lines,
            vec!["  %t.0 = call double @llvm.sqrt.double(double %x)".to_string()]
        );
    }
}
