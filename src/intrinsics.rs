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
//! ## Adding an intrinsic — always one file
//! Add one row to [`all`]. Everything the intrinsic needs — signature
//! shape, LLVM instruction sequence, any external `declare` lines —
//! lives in that row. Codegen never inspects the intrinsic's identity.
//!
//! Common shapes have factory helpers ([`bin_int`], [`icmp`],
//! [`float_binop`], [`int_neg`]) — most new intrinsics can use them
//! as `emit: bin_int("and", 64)`. Exotic intrinsics (LLVM
//! `@llvm.*` calls, multi-instruction lowerings, aggregate extracts)
//! inline a `Box::new(|ins, mk| { ... })` in the row.
//!
//! ## Naming
//! `$<type>_<op>`. Signedness of the operand type determines which
//! LLVM instruction the emit fn picks (`sdiv`/`udiv`, `ashr`/`lshr`,
//! `sitofp`/`uitofp`, etc.).

use crate::ast::*;

/// One intrinsic. `inputs`/`result` build the extern signature; `emit`
/// handles LLVM lowering.
pub struct IntrinsicSpec {
    pub name: &'static str,
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

/// Every intrinsic the compiler recognizes. Adding a new intrinsic =
/// adding one row here.
pub fn all() -> Vec<IntrinsicSpec> {
    let i64_ = Type::Int(IntTy::I64);
    let u64_ = Type::Int(IntTy::U64);
    let f64_ = Type::Float(FloatTy::F64);

    vec![
        // ---------- Integer arithmetic (i64) ----------
        bin_arith("$i64_add", i64_.clone(), "add", 64),
        bin_arith("$i64_sub", i64_.clone(), "sub", 64),
        bin_arith("$i64_mul", i64_.clone(), "mul", 64),
        // ---------- Integer arithmetic (u64) ----------
        bin_arith("$u64_add", u64_.clone(), "add", 64),
        bin_arith("$u64_sub", u64_.clone(), "sub", 64),
        bin_arith("$u64_mul", u64_.clone(), "mul", 64),
        // ---------- Integer comparisons — result is boolean ----------
        // Signed (i64) — signed predicates (slt, sle, sgt, sge).
        bin_cmp("$i64_eq", i64_.clone(), "eq", 64),
        bin_cmp("$i64_ne", i64_.clone(), "ne", 64),
        bin_cmp("$i64_lt", i64_.clone(), "slt", 64),
        bin_cmp("$i64_le", i64_.clone(), "sle", 64),
        bin_cmp("$i64_gt", i64_.clone(), "sgt", 64),
        bin_cmp("$i64_ge", i64_.clone(), "sge", 64),
        // Unsigned (u64) — unsigned predicates (ult, ule, ugt, uge).
        // `eq` and `ne` are signedness-independent but we still name
        // them per-type for consistency.
        bin_cmp("$u64_eq", u64_.clone(), "eq", 64),
        bin_cmp("$u64_ne", u64_.clone(), "ne", 64),
        bin_cmp("$u64_lt", u64_.clone(), "ult", 64),
        bin_cmp("$u64_le", u64_.clone(), "ule", 64),
        bin_cmp("$u64_gt", u64_.clone(), "ugt", 64),
        bin_cmp("$u64_ge", u64_.clone(), "uge", 64),
        // ---------- Integer unary negation (i64 only — u64 negation
        // is nonsensical without a signed conversion) ----------
        IntrinsicSpec {
            name: "$i64_neg",
            inputs: vec![i64_.clone()],
            result: i64_.clone(),
            emit: int_neg(64),
            llvm_declares: &[],
        },
        // Float arithmetic (f64).
        IntrinsicSpec {
            name: "$f64_add",
            inputs: vec![f64_.clone(), f64_.clone()],
            result: f64_.clone(),
            emit: float_binop("fadd", "double"),
            llvm_declares: &[],
        },
        IntrinsicSpec {
            name: "$f64_mul",
            inputs: vec![f64_.clone(), f64_.clone()],
            result: f64_.clone(),
            emit: float_binop("fmul", "double"),
            llvm_declares: &[],
        },
        // Population count via LLVM intrinsic. Exercises the exotic
        // path: inline emit closure + auto-emitted `declare` in the
        // module preamble. Adding future LLVM-intrinsic-backed
        // operations follows this template exactly.
        IntrinsicSpec {
            name: "$i64_popcount",
            inputs: vec![i64_.clone()],
            result: i64_,
            emit: Box::new(|ins, mk| {
                let r = mk();
                let line = format!(
                    "  {} = call i64 @llvm.ctpop.i64(i64 {})",
                    r, ins[0]
                );
                (vec![line], r)
            }),
            llvm_declares: &["declare i64 @llvm.ctpop.i64(i64)"],
        },
    ]
}

/// Look up an intrinsic by name. Linear scan of [`all`]; the list is
/// small and this is only called at call sites, not in hot loops.
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
        ty: Type::Ref(RefKind::Out, Box::new(spec.result)),
        span: SPAN,
    });
    Function {
        name: spec.name.to_string(),
        name_span: SPAN,
        is_extern: true,
        params,
        body: None,
    }
}

const SPAN: Span = Span { line: 0, col: 0 };

/// True if `name` is an intrinsic name (starts with the reserved `$`).
pub fn is_intrinsic(name: &str) -> bool {
    name.starts_with('$')
}

// ---------- Emit factory helpers ----------
//
// These build closures that emit the common LLVM instruction shapes.
// Kept in this file — codegen never sees them — so the "one-file rule"
// for adding intrinsics stays true. Exotic intrinsics don't use these
// and inline their own `Box::new(|ins, mk| { ... })` closures.

/// Build an integer binop spec: `$<name>(a: T, b: T) -> T` lowered as
/// `%r = <llvm_op> i<bits> %a, %b`.
fn bin_arith(name: &'static str, ty: Type, llvm_op: &'static str, bits: u32) -> IntrinsicSpec {
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone(), ty.clone()],
        result: ty,
        emit: bin_int(llvm_op, bits),
        llvm_declares: &[],
    }
}

/// Build an integer comparison spec: `$<name>(a: T, b: T) -> boolean`
/// lowered as `%r = icmp <pred> i<bits> %a, %b`. `pred` encodes both
/// the operation (`eq`, `lt`, ...) and signedness where relevant
/// (`slt` vs `ult`).
fn bin_cmp(name: &'static str, ty: Type, pred: &'static str, bits: u32) -> IntrinsicSpec {
    IntrinsicSpec {
        name,
        inputs: vec![ty.clone(), ty],
        result: Type::Boolean,
        emit: icmp(pred, bits),
        llvm_declares: &[],
    }
}

/// Two-operand integer op emitted as `%r = <op> i<bits> %a, %b`.
pub fn bin_int(op: &'static str, bits: u32) -> Emit {
    Box::new(move |ins, mk| {
        let r = mk();
        let line = format!("  {} = {} i{} {}, {}", r, op, bits, ins[0], ins[1]);
        (vec![line], r)
    })
}

/// Integer comparison emitted as `%r = icmp <pred> i<bits> %a, %b`.
/// Result is always `i1` (Silica `boolean`).
pub fn icmp(pred: &'static str, bits: u32) -> Emit {
    Box::new(move |ins, mk| {
        let r = mk();
        let line = format!("  {} = icmp {} i{} {}, {}", r, pred, bits, ins[0], ins[1]);
        (vec![line], r)
    })
}

/// Two-operand float op emitted as `%r = <op> <fty> %a, %b`.
/// `llvm_ty` is `"float"` or `"double"`.
pub fn float_binop(op: &'static str, llvm_ty: &'static str) -> Emit {
    Box::new(move |ins, mk| {
        let r = mk();
        let line = format!("  {} = {} {} {}, {}", r, op, llvm_ty, ins[0], ins[1]);
        (vec![line], r)
    })
}

/// Integer negation via LLVM's `sub 0, x` idiom (LLVM has no dedicated
/// integer `neg`).
pub fn int_neg(bits: u32) -> Emit {
    Box::new(move |ins, mk| {
        let r = mk();
        let line = format!("  {} = sub i{} 0, {}", r, bits, ins[0]);
        (vec![line], r)
    })
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
        assert_eq!(spec.result, Type::Int(IntTy::I64));
    }

    #[test]
    fn lookup_returns_none_for_unknown() {
        assert!(lookup("$never_defined").is_none());
        assert!(lookup("i64_add").is_none()); // missing $
        assert!(lookup("").is_none());
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
                Type::Ref(RefKind::Out, _) => {}
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
        assert_eq!(f.params[0].ty, Type::Int(IntTy::I64));
        assert_eq!(f.params[1].ty, Type::Int(IntTy::I64));
        assert_eq!(
            f.params[2].ty,
            Type::Ref(RefKind::Out, Box::new(Type::Int(IntTy::I64)))
        );
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

    // ---------- emit closures ----------

    /// Build a mk_name closure that hands out sequential `%t.0`, `%t.1`,
    /// ... — matches what codegen does. Useful for exercising emit
    /// closures directly.
    fn test_mk_name() -> impl FnMut() -> String {
        let mut n = 0u32;
        move || {
            let s = format!("%t.{}", n);
            n += 1;
            s
        }
    }

    #[test]
    fn emit_i64_add_produces_single_add_line() {
        let spec = lookup("$i64_add").unwrap();
        let mut mk = test_mk_name();
        let (lines, result) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk);
        assert_eq!(lines, vec!["  %t.0 = add i64 %a, %b".to_string()]);
        assert_eq!(result, "%t.0");
    }

    #[test]
    fn emit_i64_neg_uses_sub_zero_idiom() {
        let spec = lookup("$i64_neg").unwrap();
        let mut mk = test_mk_name();
        let (lines, _) = (spec.emit)(&["%x".to_string()], &mut mk);
        assert_eq!(lines, vec!["  %t.0 = sub i64 0, %x".to_string()]);
    }

    #[test]
    fn emit_f64_mul_uses_double_type() {
        let spec = lookup("$f64_mul").unwrap();
        let mut mk = test_mk_name();
        let (lines, _) =
            (spec.emit)(&["%a".to_string(), "%b".to_string()], &mut mk);
        assert_eq!(lines, vec!["  %t.0 = fmul double %a, %b".to_string()]);
    }

    #[test]
    fn emit_popcount_uses_llvm_intrinsic() {
        let spec = lookup("$i64_popcount").unwrap();
        let mut mk = test_mk_name();
        let (lines, result) = (spec.emit)(&["%x".to_string()], &mut mk);
        assert_eq!(
            lines,
            vec!["  %t.0 = call i64 @llvm.ctpop.i64(i64 %x)".to_string()]
        );
        assert_eq!(result, "%t.0");
        // And it declares the extern.
        assert_eq!(spec.llvm_declares, &["declare i64 @llvm.ctpop.i64(i64)"]);
    }
}
