//! LLVM textual IR emitter. Lowers a checked/elaborated MIR program to a
//! self-contained `.ll` string. Runs after `elaborate_and_check_mir` succeeded.
//!
//! ## Scope
//! - Scalars: `i64` → `i64`, `bool` → `i1`, `unit`/`never` → `{}`
//!   (the `never` case is unreachable at runtime, so any zero-sized rep
//!   works).
//! - References: all five kinds erase to `ptr` (opaque pointer). The
//!   (cur, post) obligations and shared/exclusive distinction are
//!   compiler-time only.
//! - Structs: `%<Name> = type { field-tys... }` — LLVM's default layout
//!   picks per-field padding.
//! - Enums: `%<E> = type { i16, [pad x i8], [K x <lane_ty>] }` where
//!   `lane_ty` (i8/i16/i32/i64) matches the enum's overall alignment
//!   and `K = ceil(max_payload_size / sizeof(lane_ty))`. The lane type
//!   makes LLVM's inferred struct alignment equal `layout::align_of(E)`,
//!   so an enum embedded in a larger struct is placed at the correct
//!   offset. Discriminant is variant index in declaration order.
//!   Alloca sites also carry explicit `align <enum_align>` from
//!   `layout::align_of` for redundancy.
//! - Functions: extern → `declare void @f(...)`; defined → `define void
//!   @f(...)` with one `alloca` per param/local in a synthetic `.init`
//!   block that stores each argument into its slot and then `br`s to
//!   the MIR entry block. All functions are `void`; return values ride
//!   `&out` parameters (sret-by-hand).
//! - Statements: `Assign` (including `EnumConstr` as a specialized
//!   whole-value write), `Call`. `Drop` and `Unborrow` are erased —
//!   this is a POD-only world (trivial `Drop` only) until `Destroy`
//!   and above land.
//! - Terminators: `Goto`, `Return`, `Branch`, `SwitchEnum` (with an
//!   `unreachable` default block for LLVM; MIR requires the switch to
//!   be exhaustive), `Abort` (→ `@abort` + `unreachable`), `Unreachable`.
//!
//! ## Layout notes
//! Not ABI-stable — variant order in enums is declaration order; struct
//! field order is declaration order. Padding and alignment can change.

use crate::mir::ast::*;
use crate::mir::layout;
use crate::mir::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::fmt::Write;

/// Lower `program` to LLVM textual IR. Assumes `program` has already
/// passed the full check/elaborate pipeline — malformed inputs will
/// panic.
pub fn lower_mir_to_llvm(program: &Program, env: &Env) -> String {
    let mut cx = CodeGenContext {
        env,
        out: String::new(),
        v_counter: 0,
        locals: IndexMap::new(),
        pending_default_blocks: Vec::new(),
    };

    writeln!(cx.out, "; Generated from Silica-MIR").unwrap();
    writeln!(cx.out, "declare void @abort()").unwrap();
    // Intrinsics that lower to `@llvm.*` calls surface their `declare`
    // lines here. Only intrinsics actually called by the program are
    // included, deduped — keeps output tight so unused intrinsics
    // don't bloat every emitted module.
    for decl in llvm_declares_needed(program) {
        writeln!(cx.out, "{}", decl).unwrap();
    }
    writeln!(cx.out).unwrap();

    let mut had_type = false;
    for decl in &program.declarations {
        match decl {
            Declaration::Struct(s) => {
                had_type = true;
                emit_struct_decl(&mut cx, s);
            }
            Declaration::Enum(e) => {
                had_type = true;
                emit_enum_decl(&mut cx, e);
            }
            Declaration::Fn(_) => {}
        }
    }
    if had_type {
        writeln!(cx.out).unwrap();
    }

    let mut had_extern = false;
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            if f.is_extern {
                had_extern = true;
                emit_extern_fn(&mut cx, f);
            }
        }
    }
    if had_extern {
        writeln!(cx.out).unwrap();
    }

    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            if !f.is_extern {
                emit_fn_body(&mut cx, f);
            }
        }
    }

    // If the program has a Silica `fn main` (renamed to `@silica.main`
    // in emission), synthesize a C-conformant `i32 @main()` wrapper so
    // the linked binary has a proper entry point + exit code.
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            if f.name == "main" && !f.is_extern {
                emit_main_wrapper(&mut cx, f);
                break;
            }
        }
    }

    cx.out
}

/// Map a Silica function name to the LLVM symbol codegen emits for
/// it. Only `main` is renamed — codegen synthesizes an `i32 @main()`
/// wrapper, so the Silica implementation of `main` has to live under
/// a different name. `.` is used because MIR identifiers forbid it,
/// making collisions with user-defined names impossible.
fn llvm_fn_symbol(silica_name: &str) -> String {
    if silica_name == "main" {
        "silica.main".to_string()
    } else {
        silica_name.to_string()
    }
}

fn get_return_param(f: &Function) -> Option<&Param> {
    f.params.last().filter(|p| p.name == "$return")
}

// ---------- Context ----------

struct CodeGenContext<'a> {
    env: &'a Env,
    out: String,
    v_counter: u32,
    locals: IndexMap<String, Type>,
    /// Labels of synthetic default-arm blocks for `switch i16` terminators.
    /// Accumulated per-fn during block emission and flushed as
    /// `<label>: unreachable` blocks right before the fn's closing brace.
    pending_default_blocks: Vec<String>,
}

impl<'a> CodeGenContext<'a> {
    fn fresh(&mut self) -> String {
        let n = self.v_counter;
        self.v_counter += 1;
        format!("%t.{}", n)
    }

    /// Reset every per-function field to its function-entry value.
    /// Called at the top of `emit_fn_body`. Centralized so a new
    /// per-fn field can't be missed at the reset boundary.
    fn reset_for_function(&mut self, f: &Function) {
        self.v_counter = 0;
        self.locals = f.locals_map();
        self.pending_default_blocks.clear();
    }

    /// Map an AST type to its LLVM textual form. References and function
    /// pointers both erase to opaque `ptr`. Signedness of ints is not
    /// carried in LLVM — signed/unsigned differ only at operation sites
    /// (`add` vs `add`, but `sdiv` vs `udiv` etc.), not at value type.
    fn lower_type(&self, ty: &Type) -> String {
        match ty {
            Type::Int(i) => format!("i{}", i.bits()),
            Type::Float(FloatTy::F32) => "float".to_string(),
            Type::Float(FloatTy::F64) => "double".to_string(),
            Type::Bool => "i1".to_string(),
            Type::Unit | Type::Never => "{}".to_string(),
            Type::Ref(_, _) | Type::Fn(_) | Type::RawPtr(_) => "ptr".to_string(),
            Type::Custom(name, args) => {
                assert!(
                    args.is_empty(),
                    "codegen: generic type instantiation not yet supported (monomorphization pass missing) — {}<{}>",
                    name,
                    args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "),
                );
                format!("%{}", name)
            }
            Type::Param(name) => {
                panic!("codegen: unmonomorphized type parameter '{}' reached LLVM lowering", name);
            }
            Type::Array(elem, n) => format!("[{} x {}]", n, self.lower_type(elem)),
        }
    }

    /// Zero-based struct field index and its type. Panics on non-struct.
    fn field_lookup(&self, ty: &Type, field: &str) -> (usize, Type) {
        let Type::Custom(name, _) = ty else {
            panic!("field access on non-struct type {:?}", ty);
        };
        let Some(TypeDecl::Struct(s)) = self.env.types.get(name) else {
            panic!("field lookup on non-struct '{}'", name);
        };
        let (idx, f) = s
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.name == field)
            .unwrap_or_else(|| panic!("no field '{}' on struct '{}'", field, name));
        (idx, f.ty.clone())
    }

    fn enum_decl(&self, ty: &Type) -> &'a EnumDecl {
        let Type::Custom(name, _) = ty else {
            panic!("expected enum type, got {:?}", ty);
        };
        match self.env.types.get(name) {
            Some(TypeDecl::Enum(e)) => e,
            _ => panic!("expected enum type, got '{}'", name),
        }
    }
}

// ---------- Declarations ----------

fn emit_struct_decl(cx: &mut CodeGenContext, s: &StructDecl) {
    write!(cx.out, "%{} = type {{ ", s.name).unwrap();
    for (i, f) in s.fields.iter().enumerate() {
        if i > 0 {
            write!(cx.out, ", ").unwrap();
        }
        write!(cx.out, "{}", cx.lower_type(&f.ty)).unwrap();
    }
    writeln!(cx.out, " }}").unwrap();
}

fn emit_enum_decl(cx: &mut CodeGenContext, e: &EnumDecl) {
    let pay_off = payload_offset(e, cx.env);
    let pay_size = max_payload_size(e, cx.env);
    // pad_bytes = payload_offset - disc_size (2). Always ≥ 0 since
    // payload_offset ≥ 2 (aligned up from disc).
    let pad_bytes = pay_off - 2;
    // Payload lane type matches the enum's overall alignment so that
    // LLVM's inferred struct alignment equals `layout::align_of(E)`.
    // Without this, an enum embedded as a field after a smaller-aligned
    // sibling (e.g. `struct S { b: bool, e: BigEnum }`) would place
    // the payload at a stricter-than-actual offset — UB on payload
    // access. Lane count is `ceil(pay_size / sizeof(lane_ty))`, so
    // total storage is at least `pay_size` bytes.
    let overall_align = enum_overall_align(e, cx.env);
    let (lane_ty, lane_size) = payload_lane_type(overall_align);
    let lane_count = pay_size.div_ceil(lane_size);
    writeln!(
        cx.out,
        "%{} = type {{ i16, [{} x i8], [{} x {}] }}",
        e.name, pad_bytes, lane_count, lane_ty
    )
    .unwrap();
}

fn emit_extern_fn(cx: &mut CodeGenContext, f: &Function) {
    let ret_param = get_return_param(f);
    let ret_llvm = match ret_param {
        Some(p) => match &p.ty {
            Type::Ref(_, inner) => cx.lower_type(inner),
            _ => "void".to_string(),
        },
        None => "void".to_string(),
    };
    write!(cx.out, "declare {} @{}(", ret_llvm, llvm_fn_symbol(&f.name)).unwrap();
    let mut params_to_emit = &f.params[..];
    if ret_param.is_some() {
        params_to_emit = &f.params[..f.params.len() - 1];
    }
    for (i, p) in params_to_emit.iter().enumerate() {
        if i > 0 {
            write!(cx.out, ", ").unwrap();
        }
        write!(cx.out, "{}", cx.lower_type(&p.ty)).unwrap();
    }
    writeln!(cx.out, ")").unwrap();
}

/// Emit the C-conformant `i32 @main()` wrapper. `f` is the Silica
/// `fn main` (already emitted as `@silica.main`); its signature must
/// be one of the two shapes enforced by `type_check::check_main_signature`:
///
/// - `fn main()` — wrapper calls it and returns 0.
/// - `fn main(exit: &out i32)` — wrapper allocas an i32, passes a
///   pointer, then returns the loaded value.
///
/// Panics on unexpected signatures (the checker should have rejected
/// them earlier).
fn emit_main_wrapper(cx: &mut CodeGenContext, f: &Function) {
    writeln!(cx.out, "define i32 @main() {{").unwrap();
    if get_return_param(f).is_some() {
        writeln!(cx.out, "  %code = call i32 @silica.main()").unwrap();
        writeln!(cx.out, "  ret i32 %code").unwrap();
    } else {
        match f.params.len() {
            0 => {
                writeln!(cx.out, "  call void @silica.main()").unwrap();
                writeln!(cx.out, "  ret i32 0").unwrap();
            }
            1 => {
                writeln!(cx.out, "  %exit = alloca i32, align 4").unwrap();
                writeln!(cx.out, "  store i32 0, ptr %exit").unwrap();
                writeln!(cx.out, "  call void @silica.main(ptr %exit)").unwrap();
                writeln!(cx.out, "  %code = load i32, ptr %exit").unwrap();
                writeln!(cx.out, "  ret i32 %code").unwrap();
            }
            n => panic!(
                "emit_main_wrapper: unexpected main signature ({} params); \
                 type_check::check_main_signature should have rejected this",
                n
            ),
        }
    }
    writeln!(cx.out, "}}").unwrap();
    writeln!(cx.out).unwrap();
}

fn emit_fn_body(cx: &mut CodeGenContext, f: &Function) {
    cx.reset_for_function(f);

    let ret_param = get_return_param(f);
    let ret_llvm = match ret_param {
        Some(p) => match &p.ty {
            Type::Ref(_, inner) => cx.lower_type(inner),
            _ => "void".to_string(),
        },
        None => "void".to_string(),
    };

    write!(cx.out, "define {} @{}(", ret_llvm, llvm_fn_symbol(&f.name)).unwrap();
    let mut params_to_emit = &f.params[..];
    if ret_param.is_some() {
        params_to_emit = &f.params[..f.params.len() - 1];
    }
    for (i, p) in params_to_emit.iter().enumerate() {
        if i > 0 {
            write!(cx.out, ", ").unwrap();
        }
        write!(cx.out, "{} %arg.{}", cx.lower_type(&p.ty), p.name).unwrap();
    }
    writeln!(cx.out, ") {{").unwrap();

    let Some(body) = &f.body else {
        writeln!(cx.out, "}}").unwrap();
        writeln!(cx.out).unwrap();
        return;
    };

    // Synthetic `.init` block: alloca every param and local, store each
    // arg into its slot, then br to the MIR entry. `.` is a legal LLVM
    // identifier char but not a legal MIR identifier char, so `.init`
    // can never collide with a user block name.
    writeln!(cx.out, ".init:").unwrap();

    if let Some(p) = ret_param {
        if let Type::Ref(_, inner) = &p.ty {
            let inner_llvm = cx.lower_type(inner);
            let inner_align = layout::align_of(inner, cx.env);
            writeln!(cx.out, "  %local.$return_val = alloca {}, align {}", inner_llvm, inner_align).unwrap();
            emit_alloca(cx, &p.name, &p.ty);
            writeln!(cx.out, "  store ptr %local.$return_val, ptr %local.{}", p.name).unwrap();
        }
    }

    for p in params_to_emit {
        emit_alloca(cx, &p.name, &p.ty);
        let ty = cx.lower_type(&p.ty);
        writeln!(
            cx.out,
            "  store {} %arg.{}, ptr %local.{}",
            ty, p.name, p.name
        )
        .unwrap();
    }
    for l in &body.locals {
        emit_alloca(cx, &l.name, &l.ty);
    }
    let entry_label = &body.blocks[0].label;
    writeln!(cx.out, "  br label %{}", entry_label).unwrap();

    for block in &body.blocks {
        emit_block(cx, block);
    }

    // Flush switch default blocks. Each is `<label>: unreachable`. Order
    // is the order in which switches were emitted, which is stable across
    // runs given the pretty-printer's block ordering.
    for label in std::mem::take(&mut cx.pending_default_blocks) {
        writeln!(cx.out, "{}:", label).unwrap();
        writeln!(cx.out, "  unreachable").unwrap();
    }

    writeln!(cx.out, "}}").unwrap();
    writeln!(cx.out).unwrap();
}

fn emit_alloca(cx: &mut CodeGenContext, name: &str, ty: &Type) {
    let llvm_ty = cx.lower_type(ty);
    let align = layout::align_of(ty, cx.env);
    writeln!(
        cx.out,
        "  %local.{} = alloca {}, align {}",
        name, llvm_ty, align
    )
    .unwrap();
}

fn emit_block(cx: &mut CodeGenContext, block: &BasicBlock) {
    writeln!(cx.out, "{}:", block.label).unwrap();
    for (stmt, _) in &block.statements {
        emit_stmt(cx, stmt);
    }
    emit_terminator(cx, &block.terminator);
}

// ---------- Statements ----------

fn emit_stmt(cx: &mut CodeGenContext, stmt: &Statement) {
    match stmt {
        Statement::Assign(lhs, rhs) => {
            // EnumConstr is a whole-value initialization: it writes both
            // the discriminant and the payload. Handled directly at LHS
            // address rather than via materialize-then-store.
            if let RValue::EnumConstr(enum_name, variant, operand) = rhs {
                emit_enum_construction(cx, lhs, enum_name, variant, operand);
                return;
            }
            // Aggregate array literal: per-slot GEP + store, no
            // intermediate value materialization. Same shape as
            // EnumConstr.
            if let RValue::ArrayLit(operands) = rhs {
                emit_array_lit(cx, lhs, operands);
                return;
            }
            // Evaluate RHS first so `x = copy x` (or any self-referential
            // path) reads before it overwrites. Then compute LHS address
            // and store.
            let (val, val_ty) = emit_rvalue(cx, rhs);
            let (addr, _) = emit_place_addr(cx, lhs);
            let ty_llvm = cx.lower_type(&val_ty);
            writeln!(cx.out, "  store {} {}, ptr {}", ty_llvm, val, addr).unwrap();
        }
        Statement::Call(target, args) => {
            // Intercept intrinsic calls (`call $name(...)`): emit the LLVM
            // instruction sequence inline. The intrinsic symbol never
            // appears in the emitted `.ll`.
            if let Operand::Const(ConstVal::FnName(name, _)) = target {
                if crate::mir::intrinsics::is_intrinsic(name) {
                    emit_intrinsic_call(cx, name, args);
                    return;
                }
            }
            let (target_val, target_ty) = emit_operand(cx, target);
            let Type::Fn(param_tys) = &target_ty else {
                panic!("call target is not a function type: {:?}", target_ty);
            };
            let mut arg_pairs: Vec<(String, String)> = Vec::with_capacity(args.len());
            for a in args {
                let (v, t) = emit_operand(cx, a);
                arg_pairs.push((cx.lower_type(&t), v));
            }
            let _ = param_tys; // types are already implicit in arg_pairs

            let ret_llvm = if let Operand::Const(ConstVal::FnName(name, _)) = target {
                if let Some(f) = cx.env.functions.get(name) {
                    if let Some(p) = get_return_param(f) {
                        if let Type::Ref(_, inner) = &p.ty {
                            Some(cx.lower_type(inner))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if let Some(ret_ty_str) = ret_llvm {
                let (_, ret_ptr_val) = arg_pairs.pop().expect("must have at least the $return arg");
                let ret_reg = cx.fresh();
                write!(cx.out, "  {} = call {} {}(", ret_reg, ret_ty_str, target_val).unwrap();
                for (i, (t, v)) in arg_pairs.iter().enumerate() {
                    if i > 0 {
                        write!(cx.out, ", ").unwrap();
                    }
                    write!(cx.out, "{} {}", t, v).unwrap();
                }
                writeln!(cx.out, ")").unwrap();
                writeln!(cx.out, "  store {} {}, ptr {}", ret_ty_str, ret_reg, ret_ptr_val).unwrap();
            } else {
                write!(cx.out, "  call void {}(", target_val).unwrap();
                for (i, (t, v)) in arg_pairs.iter().enumerate() {
                    if i > 0 {
                        write!(cx.out, ", ").unwrap();
                    }
                    write!(cx.out, "{} {}", t, v).unwrap();
                }
                writeln!(cx.out, ")").unwrap();
            }
        }
        Statement::Drop(_) | Statement::Unborrow(_) => {
            // Erased. `Drop` lowers to a real call once `Destroy`
            // (pure custom destructor) lands; unborrow is checker-only
            // and never has runtime effect.
        }
    }
}

/// Walk `program`'s statements, collect every intrinsic called by
/// name, and return the deduped `llvm_declares` those intrinsics
/// require. Preserves the order intrinsics are listed in
/// `intrinsics::all()` so output is stable across runs.
fn llvm_declares_needed(program: &Program) -> Vec<&'static str> {
    let mut called: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for decl in &program.declarations {
        let Declaration::Fn(f) = decl else { continue };
        let Some(body) = &f.body else { continue };
        for block in &body.blocks {
            for (stmt, _) in &block.statements {
                if let Statement::Call(Operand::Const(ConstVal::FnName(name, _)), _) = stmt {
                    if crate::mir::intrinsics::is_intrinsic(name) {
                        called.insert(name.clone());
                    }
                }
            }
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for spec in crate::mir::intrinsics::all() {
        if !called.contains(&spec.name) {
            continue;
        }
        for d in spec.llvm_declares {
            if seen.insert(*d) {
                out.push(*d);
            }
        }
    }
    out
}

/// Lower an intrinsic `call $name(operand..., out)` inline.
///
/// Codegen has zero intrinsic-specific logic — it just materializes
/// input operands, hands the SSA names + a fresh-name generator to
/// the spec's `emit` closure, writes the returned lines, and stores
/// the returned SSA value through the `&out` pointer. Adding a new
/// intrinsic never touches this function.
fn emit_intrinsic_call(cx: &mut CodeGenContext, name: &str, args: &[Operand]) {
    let spec = crate::mir::intrinsics::lookup(name)
        .unwrap_or_else(|| panic!("unknown intrinsic '{}'", name));
    assert_eq!(
        args.len(),
        spec.inputs.len() + 1,
        "intrinsic '{}' called with {} args, expected {} inputs + 1 out",
        name,
        args.len(),
        spec.inputs.len()
    );
    let (out_operand, in_operands) = args.split_last().unwrap();

    // Materialize each input as an SSA value.
    let in_ssa: Vec<String> = in_operands
        .iter()
        .map(|op| emit_operand(cx, op).0)
        .collect();

    // Hand control to the intrinsic's emit closure. `mk_name` is the
    // only hook it has back into codegen state — the closure allocates
    // as many fresh SSA names as it needs, and returns the lines + the
    // SSA name holding the final result.
    let v_counter = &mut cx.v_counter;
    let mut mk_name = || {
        let n = *v_counter;
        *v_counter += 1;
        format!("%t.{}", n)
    };
    let (lines, result_ssa) = (spec.emit)(&in_ssa, &mut mk_name);
    for line in &lines {
        writeln!(cx.out, "{}", line).unwrap();
    }

    // Store result through the &out pointer. `out_operand` is `move r`
    // where `r: &out T` — load its slot to get the pointee address.
    let (out_val, _) = emit_operand(cx, out_operand);
    let result_llvm = cx.lower_type(&spec.result);
    writeln!(
        cx.out,
        "  store {} {}, ptr {}",
        result_llvm, result_ssa, out_val
    )
    .unwrap();
}

/// Lower `p = [e0, e1, ..., eN-1]`. Materializes each operand, then
/// GEPs to each slot and stores. RHS materialization happens before
/// LHS address computation to preserve read-before-write semantics.
fn emit_array_lit(cx: &mut CodeGenContext, lhs: &Place, operands: &[Operand]) {
    // Materialize all operand values first (before LHS address
    // computation, in case an operand reads from the target itself).
    let materialized: Vec<(String, Type)> =
        operands.iter().map(|op| emit_operand(cx, op)).collect();
    let (lhs_addr, lhs_ty) = emit_place_addr(cx, lhs);
    let Type::Array(elem, _) = lhs_ty else {
        panic!("ArrayLit target must have array type, got {:?}", lhs_ty);
    };
    let elem_llvm = cx.lower_type(&elem);
    for (i, (val, _)) in materialized.iter().enumerate() {
        let slot_addr = cx.fresh();
        writeln!(
            cx.out,
            "  {} = getelementptr {}, ptr {}, i64 {}",
            slot_addr, elem_llvm, lhs_addr, i
        )
        .unwrap();
        writeln!(cx.out, "  store {} {}, ptr {}", elem_llvm, val, slot_addr).unwrap();
    }
}

/// Lower `p = Name::V(operand)`. Writes the discriminant to LHS field 0
/// and, if the variant's payload is non-empty, writes the operand's value
/// to LHS field 2. RHS materialization happens before LHS address
/// computation to preserve read-before-write semantics.
fn emit_enum_construction(
    cx: &mut CodeGenContext,
    lhs: &Place,
    enum_name: &str,
    variant: &str,
    operand: &Operand,
) {
    let (operand_val, operand_ty) = emit_operand(cx, operand);
    let (lhs_addr, _) = emit_place_addr(cx, lhs);

    let e_decl = match cx.env.types.get(enum_name) {
        Some(TypeDecl::Enum(e)) => e,
        _ => panic!("expected enum '{}'", enum_name),
    };
    let v_idx = variant_index(e_decl, variant);

    // Discriminant.
    let disc_addr = cx.fresh();
    writeln!(
        cx.out,
        "  {} = getelementptr %{}, ptr {}, i32 0, i32 0",
        disc_addr, enum_name, lhs_addr
    )
    .unwrap();
    writeln!(cx.out, "  store i16 {}, ptr {}", v_idx, disc_addr).unwrap();

    // Payload — skip if zero-sized (unit / never). LLVM tolerates
    // `store {} zeroinitializer` but there's no reason to emit it.
    if layout::size_of(&operand_ty, cx.env) > 0 {
        let payload_addr = cx.fresh();
        writeln!(
            cx.out,
            "  {} = getelementptr %{}, ptr {}, i32 0, i32 2",
            payload_addr, enum_name, lhs_addr
        )
        .unwrap();
        let llvm_ty = cx.lower_type(&operand_ty);
        writeln!(
            cx.out,
            "  store {} {}, ptr {}",
            llvm_ty, operand_val, payload_addr
        )
        .unwrap();
    }
}

// ---------- RValues / Operands / Constants ----------

/// Emit code to materialize `rv` as an SSA value. Returns the value
/// (an LLVM identifier or literal) and its AST type. `EnumConstr` is
/// handled by `emit_enum_construction` before reaching here.
fn emit_rvalue(cx: &mut CodeGenContext, rv: &RValue) -> (String, Type) {
    match rv {
        RValue::Use(op) => emit_operand(cx, op),
        RValue::Ref(_, place) => {
            // A reference's runtime value is the address of the place.
            // The ref kind is compiler-time only.
            let (addr, ty) = emit_place_addr(cx, place);
            (addr, Type::Ref(RefKind::Shared, Box::new(ty)))
        }
        RValue::RawRef(place) => {
            // Raw pointer: identical LLVM emission as `&` above — an
            // address. The distinction between safe ref and raw ptr is
            // purely compiler-time (loan tracking, obligation checks).
            let (addr, ty) = emit_place_addr(cx, place);
            (addr, Type::RawPtr(Box::new(ty)))
        }
        RValue::EnumConstr(..) => {
            unreachable!("EnumConstr is handled in Assign statement, not here")
        }
        RValue::ArrayLit(..) => {
            unreachable!("ArrayLit is handled in Assign statement, not here")
        }
    }
}

fn emit_operand(cx: &mut CodeGenContext, op: &Operand) -> (String, Type) {
    match op {
        Operand::Copy(p) | Operand::Move(p) => read_place(cx, p),
        Operand::Const(c) => emit_const(cx, c),
    }
}

fn emit_const(cx: &mut CodeGenContext, c: &ConstVal) -> (String, Type) {
    match c {
        ConstVal::Int { bits, ty } => {
            // LLVM accepts a decimal integer that fits the target
            // integer type. For signed types, LLVM interprets the value
            // in two's-complement of the given width — writing the raw
            // unsigned bit pattern works as long as we mask to the
            // type's width.
            let mask: u64 = if ty.bits() == 64 {
                u64::MAX
            } else {
                (1u64 << ty.bits()) - 1
            };
            let masked = bits & mask;
            (masked.to_string(), Type::Int(*ty))
        }
        ConstVal::Float { bits, ty } => {
            // LLVM's textual IR accepts float literals as hex bit
            // patterns (`0x...`). Emitting hex avoids parse-round-trip
            // errors on subnormals and NaNs. For f32, the low 32 bits
            // of `bits` hold the IEEE-754 form; LLVM expects the
            // hexadecimal to represent the *double* form even for
            // `float`, so we widen f32 → f64 for the literal.
            let hex = match ty {
                FloatTy::F32 => {
                    let v32 = f32::from_bits(*bits as u32);
                    format!("0x{:016X}", (v32 as f64).to_bits())
                }
                FloatTy::F64 => format!("0x{:016X}", *bits),
            };
            (hex, Type::Float(*ty))
        }
        ConstVal::Bool(true) => ("true".to_string(), Type::Bool),
        ConstVal::Bool(false) => ("false".to_string(), Type::Bool),
        ConstVal::Unit => ("zeroinitializer".to_string(), Type::Unit),
        ConstVal::FnName(name, type_args) => {
            assert!(
                type_args.is_empty(),
                "codegen: generic function instantiation not yet supported (monomorphization pass missing) — {}<...>",
                name,
            );
            let f = cx
                .env
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("undeclared function '{}'", name));
            let param_tys = f.params.iter().map(|p| p.ty.clone()).collect();
            (format!("@{}", llvm_fn_symbol(name)), Type::Fn(param_tys))
        }
        ConstVal::ByteStr(bytes) => (
            llvm_byte_str_literal(bytes),
            Type::Array(Box::new(Type::Int(IntTy::U8)), bytes.len() as u64),
        ),
    }
}

/// Encode `bytes` as an LLVM byte-string literal (`c"..."`).
/// Printable ASCII bytes go verbatim; `"` and `\` and any other byte
/// are emitted as `\XX` (uppercase hex).
fn llvm_byte_str_literal(bytes: &[u8]) -> String {
    let mut s = String::from("c\"");
    for &b in bytes {
        match b {
            b'\\' | b'"' => write!(s, "\\{:02X}", b).unwrap(),
            0x20..=0x7E => s.push(b as char),
            _ => write!(s, "\\{:02X}", b).unwrap(),
        }
    }
    s.push('"');
    s
}

// ---------- Places ----------

/// Compute the address (a `ptr`) of `place`. Returns the SSA value
/// holding that pointer plus the pointee's AST type.
fn emit_place_addr(cx: &mut CodeGenContext, place: &Place) -> (String, Type) {
    match place {
        Place::Var(name) => {
            let ty = cx
                .locals
                .get(name)
                .cloned()
                .unwrap_or_else(|| panic!("unknown local '{}'", name));
            (format!("%local.{}", name), ty)
        }
        Place::Field(inner, field) => {
            let (base_addr, base_ty) = emit_place_addr(cx, inner);
            let base_llvm = cx.lower_type(&base_ty);
            let (idx, field_ty) = cx.field_lookup(&base_ty, field);
            let dst = cx.fresh();
            writeln!(
                cx.out,
                "  {} = getelementptr {}, ptr {}, i32 0, i32 {}",
                dst, base_llvm, base_addr, idx
            )
            .unwrap();
            (dst, field_ty)
        }
        Place::Deref(inner) => {
            let (base_addr, base_ty) = emit_place_addr(cx, inner);
            let pointee = match base_ty {
                Type::Ref(_, p) => p,
                Type::RawPtr(p) => p,
                other => panic!("deref of non-pointer type {:?}", other),
            };
            // `base_addr` points to the pointer's own storage (a slot
            // holding a `ptr`). Load once to obtain the pointee address.
            let dst = cx.fresh();
            writeln!(cx.out, "  {} = load ptr, ptr {}", dst, base_addr).unwrap();
            (dst, *pointee)
        }
        Place::Downcast(inner, variant) => {
            let (base_addr, base_ty) = emit_place_addr(cx, inner);
            let e_decl = cx.enum_decl(&base_ty);
            let payload_ty = e_decl
                .variants
                .iter()
                .find(|v| v.name == *variant)
                .map(|v| v.ty.clone())
                .unwrap_or_else(|| {
                    panic!("no variant '{}' on enum {:?}", variant, base_ty)
                });
            let base_llvm = cx.lower_type(&base_ty);
            // Payload lives at field index 2: {i16, [pad x i8], [N x i8]}.
            let dst = cx.fresh();
            writeln!(
                cx.out,
                "  {} = getelementptr {}, ptr {}, i32 0, i32 2",
                dst, base_llvm, base_addr
            )
            .unwrap();
            (dst, payload_ty)
        }
        Place::Index(inner, op) => {
            let (base_addr, base_ty) = emit_place_addr(cx, inner);
            let Type::Array(elem, _) = base_ty else {
                panic!("index into non-array type {:?}", base_ty);
            };
            let elem_ty = *elem;
            let elem_llvm = cx.lower_type(&elem_ty);
            // Materialize the index operand as an i64 SSA value.
            let idx_ssa = emit_operand_as_i64(cx, op);
            let dst = cx.fresh();
            // Element-type single-index GEP: treats base_addr as a
            // pointer-to-element and offsets by idx. Semantically the
            // same as `getelementptr [N x elem], ptr base, i64 0, i64
            // idx` and one instruction shorter.
            writeln!(
                cx.out,
                "  {} = getelementptr {}, ptr {}, i64 {}",
                dst, elem_llvm, base_addr, idx_ssa
            )
            .unwrap();
            (dst, elem_ty)
        }
    }
}

/// Materialize an operand as an SSA `i64` value suitable for use as
/// a GEP index. Integer operands are extended/truncated to i64 to
/// match LLVM's canonical index type; non-integer operands panic
/// (type_check should have rejected them).
fn emit_operand_as_i64(cx: &mut CodeGenContext, op: &Operand) -> String {
    let (val, ty) = emit_operand(cx, op);
    match ty {
        Type::Int(IntTy::I64) | Type::Int(IntTy::U64) => val,
        Type::Int(i) => {
            let dst = cx.fresh();
            let src_ty = format!("i{}", i.bits());
            // Signed types get sext, unsigned get zext.
            let op = if i.is_signed() { "sext" } else { "zext" };
            writeln!(cx.out, "  {} = {} {} {} to i64", dst, op, src_ty, val).unwrap();
            dst
        }
        other => panic!("array index must be an integer, got {:?}", other),
    }
}

/// Emit a `load` of the value at `place`. Returns the SSA value and
/// its AST type.
fn read_place(cx: &mut CodeGenContext, place: &Place) -> (String, Type) {
    let (addr, ty) = emit_place_addr(cx, place);
    let ty_llvm = cx.lower_type(&ty);
    let dst = cx.fresh();
    writeln!(cx.out, "  {} = load {}, ptr {}", dst, ty_llvm, addr).unwrap();
    (dst, ty)
}

// ---------- Terminators ----------

fn emit_terminator(cx: &mut CodeGenContext, term: &Terminator) {
    match term {
        Terminator::Goto(label) => {
            writeln!(cx.out, "  br label %{}", label).unwrap();
        }
        Terminator::Return => {
            if let Some(Type::Ref(RefKind::Out, inner_ty)) = cx.locals.get("$return") {
                let llvm_ty = cx.lower_type(inner_ty);
                let val_reg = cx.fresh();
                writeln!(
                    cx.out,
                    "  {} = load {}, ptr %local.$return_val",
                    val_reg, llvm_ty
                )
                .unwrap();
                writeln!(cx.out, "  ret {} {}", llvm_ty, val_reg).unwrap();
            } else {
                writeln!(cx.out, "  ret void").unwrap();
            }
        }
        Terminator::Branch {
            cond,
            true_label,
            false_label,
        } => {
            let (v, _) = emit_operand(cx, cond);
            writeln!(
                cx.out,
                "  br i1 {}, label %{}, label %{}",
                v, true_label, false_label
            )
            .unwrap();
        }
        Terminator::SwitchEnum { place, cases } => {
            let (place_addr, place_ty) = emit_place_addr(cx, place);
            let e_decl = cx.enum_decl(&place_ty).clone();
            let base_llvm = cx.lower_type(&place_ty);
            // GEP to discriminant (field 0), then load i16.
            let disc_addr = cx.fresh();
            writeln!(
                cx.out,
                "  {} = getelementptr {}, ptr {}, i32 0, i32 0",
                disc_addr, base_llvm, place_addr
            )
            .unwrap();
            let disc_val = cx.fresh();
            writeln!(cx.out, "  {} = load i16, ptr {}", disc_val, disc_addr).unwrap();

            // Reserve a `.switch_default.N` label. MIR guarantees the
            // switch is exhaustive (variant_flow); the default block is
            // just LLVM's syntactic requirement, filled with `unreachable`.
            let default_label = format!(
                ".switch_default.{}",
                cx.pending_default_blocks.len()
            );
            cx.pending_default_blocks.push(default_label.clone());

            writeln!(
                cx.out,
                "  switch i16 {}, label %{} [",
                disc_val, default_label
            )
            .unwrap();
            for (variant, arm_label) in cases {
                let idx = variant_index(&e_decl, variant);
                writeln!(cx.out, "    i16 {}, label %{}", idx, arm_label).unwrap();
            }
            writeln!(cx.out, "  ]").unwrap();
        }
        Terminator::Abort => {
            writeln!(cx.out, "  call void @abort()").unwrap();
            writeln!(cx.out, "  unreachable").unwrap();
        }
        Terminator::Unreachable => {
            writeln!(cx.out, "  unreachable").unwrap();
        }
    }
}

// ---------- Enum layout helpers ----------

/// Overall alignment of an enum: the stricter of the discriminant's
/// alignment (i16 = 2) and any variant payload's alignment.
fn enum_overall_align(e: &EnumDecl, env: &Env) -> u64 {
    let mut a = 2u64;
    for v in &e.variants {
        a = a.max(layout::align_of(&v.ty, env));
    }
    a
}

/// Byte offset of the payload within an enum's LLVM struct. Equals the
/// discriminant size (2) rounded up to the enum's overall alignment.
fn payload_offset(e: &EnumDecl, env: &Env) -> u64 {
    align_up(2, enum_overall_align(e, env))
}

/// LLVM integer type used for the payload lane so LLVM infers the
/// enum's true struct alignment. `sizeof(lane_ty) == align`.
fn payload_lane_type(align: u64) -> (&'static str, u64) {
    match align {
        1 => ("i8", 1),
        2 => ("i16", 2),
        4 => ("i32", 4),
        8 => ("i64", 8),
        _ => panic!("unsupported enum alignment: {}", align),
    }
}

fn max_payload_size(e: &EnumDecl, env: &Env) -> u64 {
    e.variants
        .iter()
        .map(|v| layout::size_of(&v.ty, env))
        .max()
        .unwrap_or(0)
}

fn variant_index(e: &EnumDecl, variant: &str) -> u64 {
    e.variants
        .iter()
        .position(|v| v.name == variant)
        .unwrap_or_else(|| panic!("no variant '{}' on enum '{}'", variant, e.name))
        as u64
}

fn align_up(x: u64, a: u64) -> u64 {
    (x + a - 1) & !(a - 1)
}

