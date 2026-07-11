//! LLVM textual IR emitter. Lowers a checked/elaborated MIR program to a
//! self-contained `.ll` string. Runs after `run_all_passes` succeeded.
//!
//! ## Scope (slice 1)
//! - Scalars: `number` → `i64`, `boolean` → `i1`, `unit`/`never` → `{}`
//!   (the `never` case is unreachable at runtime, so any zero-sized rep
//!   works).
//! - References: all five kinds erase to `ptr` (opaque pointer). The
//!   (cur, post) obligations and shared/exclusive distinction are
//!   compiler-time only.
//! - Structs: `%<Name> = type { field-tys... }`.
//! - Functions: extern → `declare void @f(...)`; defined → `define void
//!   @f(...)` with one `alloca` per param/local in a synthetic `.init`
//!   block that stores each argument into its slot and then `br`s to
//!   the MIR entry block. All functions are `void`; return values ride
//!   `&out` parameters (sret-by-hand).
//! - Statements: `Assign`, `Call`. `Drop` and `Unborrow` are erased —
//!   this is a POD-only world until user `Drop::drop` exists.
//! - Terminators: `Goto`, `Return`, `Branch`, `Abort` (→ `@abort` +
//!   `unreachable`), `Unreachable`.
//!
//! ## Not yet (slice 2)
//! - Enums, `Downcast` places, `EnumConstr` rvalues, `SwitchEnum`.
//!   Planned layout: `%<E> = type { i16, [N x i8] }` with variant order
//!   = declaration order; N = max payload size (target-dependent).
//!
//! ## Layout notes
//! Not ABI-stable — layout is whatever LLVM picks for the emitted
//! struct/pointer types on the target. Booleans stored in memory get
//! LLVM's default `i1` extension to a byte at alloca.

use crate::ast::*;
use indexmap::IndexMap;
use std::fmt::Write;

/// Lower `program` to LLVM textual IR. Assumes `program` has already
/// passed the full check/elaborate pipeline — malformed inputs will
/// panic.
pub fn generate_llvm(program: &Program) -> String {
    let types = collect_types(program);
    let functions = collect_functions(program);
    let mut cx = Ctx {
        types: &types,
        functions: &functions,
        out: String::new(),
        v_counter: 0,
        locals: IndexMap::new(),
    };

    writeln!(cx.out, "; Generated from Silica-MIR").unwrap();
    writeln!(cx.out, "declare void @abort()").unwrap();
    writeln!(cx.out).unwrap();

    let mut had_type = false;
    for decl in &program.declarations {
        if let Declaration::Struct(s) = decl {
            had_type = true;
            emit_struct_decl(&mut cx, s);
        }
        // Enums: slice 2.
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

    cx.out
}

// ---------- Lookup tables ----------

fn collect_types(program: &Program) -> IndexMap<String, &Declaration> {
    let mut out = IndexMap::new();
    for d in &program.declarations {
        match d {
            Declaration::Struct(s) => {
                out.insert(s.name.clone(), d);
            }
            Declaration::Enum(e) => {
                out.insert(e.name.clone(), d);
            }
            Declaration::Fn(_) => {}
        }
    }
    out
}

fn collect_functions(program: &Program) -> IndexMap<String, &Function> {
    let mut out = IndexMap::new();
    for d in &program.declarations {
        if let Declaration::Fn(f) = d {
            out.insert(f.name.clone(), f);
        }
    }
    out
}

// ---------- Context ----------

struct Ctx<'a> {
    types: &'a IndexMap<String, &'a Declaration>,
    functions: &'a IndexMap<String, &'a Function>,
    out: String,
    v_counter: u32,
    locals: IndexMap<String, Type>,
}

impl<'a> Ctx<'a> {
    fn fresh(&mut self) -> String {
        let n = self.v_counter;
        self.v_counter += 1;
        format!("%t.{}", n)
    }

    /// Map an AST type to its LLVM textual form. References and function
    /// pointers both erase to opaque `ptr`.
    fn lower_type(&self, ty: &Type) -> String {
        match ty {
            Type::Number => "i64".to_string(),
            Type::Boolean => "i1".to_string(),
            Type::Unit | Type::Never => "{}".to_string(),
            Type::Ref(_, _) | Type::Fn(_) => "ptr".to_string(),
            Type::Custom(name) => format!("%{}", name),
        }
    }

    /// Zero-based struct field index and its type.
    fn field_lookup(&self, ty: &Type, field: &str) -> (usize, Type) {
        let Type::Custom(name) = ty else {
            panic!("field access on non-struct type {:?}", ty);
        };
        let Some(Declaration::Struct(s)) = self.types.get(name).copied() else {
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
}

// ---------- Declarations ----------

fn emit_struct_decl(cx: &mut Ctx, s: &StructDecl) {
    write!(cx.out, "%{} = type {{ ", s.name).unwrap();
    for (i, f) in s.fields.iter().enumerate() {
        if i > 0 {
            write!(cx.out, ", ").unwrap();
        }
        write!(cx.out, "{}", cx.lower_type(&f.ty)).unwrap();
    }
    writeln!(cx.out, " }}").unwrap();
}

fn emit_extern_fn(cx: &mut Ctx, f: &Function) {
    write!(cx.out, "declare void @{}(", f.name).unwrap();
    for (i, p) in f.params.iter().enumerate() {
        if i > 0 {
            write!(cx.out, ", ").unwrap();
        }
        write!(cx.out, "{}", cx.lower_type(&p.ty)).unwrap();
    }
    writeln!(cx.out, ")").unwrap();
}

fn emit_fn_body(cx: &mut Ctx, f: &Function) {
    cx.v_counter = 0;
    cx.locals = f.locals_map();

    write!(cx.out, "define void @{}(", f.name).unwrap();
    for (i, p) in f.params.iter().enumerate() {
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
    for p in &f.params {
        let ty = cx.lower_type(&p.ty);
        writeln!(cx.out, "  %local.{} = alloca {}", p.name, ty).unwrap();
        writeln!(
            cx.out,
            "  store {} %arg.{}, ptr %local.{}",
            ty, p.name, p.name
        )
        .unwrap();
    }
    for l in &body.locals {
        let ty = cx.lower_type(&l.ty);
        writeln!(cx.out, "  %local.{} = alloca {}", l.name, ty).unwrap();
    }
    let entry_label = &body.blocks[0].label;
    writeln!(cx.out, "  br label %{}", entry_label).unwrap();

    for block in &body.blocks {
        emit_block(cx, block);
    }
    writeln!(cx.out, "}}").unwrap();
    writeln!(cx.out).unwrap();
}

fn emit_block(cx: &mut Ctx, block: &BasicBlock) {
    writeln!(cx.out, "{}:", block.label).unwrap();
    for (stmt, _) in &block.statements {
        emit_stmt(cx, stmt);
    }
    emit_terminator(cx, &block.terminator);
}

// ---------- Statements ----------

fn emit_stmt(cx: &mut Ctx, stmt: &Statement) {
    match stmt {
        Statement::Assign(lhs, rhs) => {
            // Evaluate RHS first so `x = copy x` (or any self-referential
            // path) reads before it overwrites. Then compute LHS address
            // and store.
            let (val, val_ty) = emit_rvalue(cx, rhs);
            let (addr, _) = emit_place_addr(cx, lhs);
            let ty_llvm = cx.lower_type(&val_ty);
            writeln!(cx.out, "  store {} {}, ptr {}", ty_llvm, val, addr).unwrap();
        }
        Statement::Call(target, args) => {
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
            write!(cx.out, "  call void {}(", target_val).unwrap();
            for (i, (t, v)) in arg_pairs.iter().enumerate() {
                if i > 0 {
                    write!(cx.out, ", ").unwrap();
                }
                write!(cx.out, "{} {}", t, v).unwrap();
            }
            writeln!(cx.out, ")").unwrap();
        }
        Statement::Drop(_) | Statement::Unborrow(_) => {
            // Erased. Drop lowers to a real call once user Drop::drop
            // exists; unborrow is checker-only and never has runtime effect.
        }
    }
}

// ---------- RValues / Operands / Constants ----------

/// Emit code to materialize `rv` as an SSA value. Returns the value
/// (an LLVM identifier or literal) and its AST type.
fn emit_rvalue(cx: &mut Ctx, rv: &RValue) -> (String, Type) {
    match rv {
        RValue::Use(op) => emit_operand(cx, op),
        RValue::Ref(_, place) => {
            // A reference's runtime value is the address of the place.
            // The ref kind is compiler-time only.
            let (addr, ty) = emit_place_addr(cx, place);
            (addr, Type::Ref(RefKind::Shared, Box::new(ty)))
        }
        RValue::EnumConstr(..) => panic!("EnumConstr: enums are not yet lowered (slice 2)"),
    }
}

fn emit_operand(cx: &mut Ctx, op: &Operand) -> (String, Type) {
    match op {
        Operand::Copy(p) | Operand::Move(p) => read_place(cx, p),
        Operand::Const(c) => emit_const(cx, c),
    }
}

fn emit_const(cx: &mut Ctx, c: &ConstVal) -> (String, Type) {
    match c {
        ConstVal::Number(n) => (n.to_string(), Type::Number),
        ConstVal::Boolean(true) => ("true".to_string(), Type::Boolean),
        ConstVal::Boolean(false) => ("false".to_string(), Type::Boolean),
        ConstVal::Unit => ("zeroinitializer".to_string(), Type::Unit),
        ConstVal::FnName(name) => {
            let f = cx
                .functions
                .get(name)
                .unwrap_or_else(|| panic!("undeclared function '{}'", name));
            let param_tys = f.params.iter().map(|p| p.ty.clone()).collect();
            (format!("@{}", name), Type::Fn(param_tys))
        }
    }
}

// ---------- Places ----------

/// Compute the address (a `ptr`) of `place`. Returns the SSA value
/// holding that pointer plus the pointee's AST type.
fn emit_place_addr(cx: &mut Ctx, place: &Place) -> (String, Type) {
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
            let Type::Ref(_, pointee) = base_ty else {
                panic!("deref of non-reference type");
            };
            // `base_addr` points to the reference's own storage (a slot
            // holding a `ptr`). Load once to obtain the pointee address.
            let dst = cx.fresh();
            writeln!(cx.out, "  {} = load ptr, ptr {}", dst, base_addr).unwrap();
            (dst, *pointee)
        }
        Place::Downcast(..) => panic!("Downcast: enums are not yet lowered (slice 2)"),
    }
}

/// Emit a `load` of the value at `place`. Returns the SSA value and
/// its AST type.
fn read_place(cx: &mut Ctx, place: &Place) -> (String, Type) {
    let (addr, ty) = emit_place_addr(cx, place);
    let ty_llvm = cx.lower_type(&ty);
    let dst = cx.fresh();
    writeln!(cx.out, "  {} = load {}, ptr {}", dst, ty_llvm, addr).unwrap();
    (dst, ty)
}

// ---------- Terminators ----------

fn emit_terminator(cx: &mut Ctx, term: &Terminator) {
    match term {
        Terminator::Goto(label) => {
            writeln!(cx.out, "  br label %{}", label).unwrap();
        }
        Terminator::Return => {
            writeln!(cx.out, "  ret void").unwrap();
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
        Terminator::SwitchEnum { .. } => {
            panic!("SwitchEnum: enums are not yet lowered (slice 2)")
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

#[cfg(test)]
mod test_util;
#[cfg(test)]
mod declaration_tests;
#[cfg(test)]
mod function_body_tests;
#[cfg(test)]
mod place_tests;
#[cfg(test)]
mod statement_tests;
#[cfg(test)]
mod terminator_tests;
