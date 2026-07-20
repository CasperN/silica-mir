//! Monomorphization pass.
//!
//! Runs after all type-checks and elaboration, immediately before
//! codegen. Takes a MIR `Program` that may contain generic decls
//! (`struct<T> Box`, `fn<T> id`) and their instantiations
//! (`Box<i32>`, `id<i32>(x)`) and produces a `Program` where:
//!
//!   - Every `Custom(name, args)` has `args = []`; `name` is the
//!     mangled instantiation name (e.g. `Box<i32>`).
//!   - Every `FnName(name, args)` has `args = []`; `name` is the
//!     mangled instantiation name.
//!   - No `Function.type_params`, `StructDecl.type_params`, or
//!     `EnumDecl.type_params` remain — every decl is a concrete
//!     instantiation.
//!   - Generic decls that are never instantiated are dropped.
//!
//! ## Algorithm
//!
//! Reachability-driven fixed point:
//!
//! 1. Seed the work queue with every **non-generic** decl (each
//!    is trivially an instantiation with empty args).
//! 2. For each queued `(name, args)`:
//!    a. Clone the original decl.
//!    b. Substitute the decl's type parameters with `args` in every
//!       type reference (fields, variants, params, locals, and all
//!       type args inside statements).
//!    c. Walk every resulting `Custom(inner_name, inner_args)` — the
//!       args are now concrete. Register `(inner_name, inner_args)` as
//!       a needed instantiation (queue if new) and rewrite the type as
//!       `Custom(mangled(inner_name, inner_args), [])`. Same for
//!       `FnName`.
//!    d. Emit the specialized decl with `type_params = []` and the new
//!       mangled name.
//! 3. Repeat until the queue is empty.
//!
//! ## Mangling
//!
//! Non-generic name → itself. Generic instantiation `Foo<T, U>` →
//! `Foo<T, U>` literal (the arg types printed by `Type::Display`).
//! Nested instantiations mangle bottom-up, so `Box<Box<i32>>` mangles
//! its inner arg as `Box<i32>` first and then wraps to `Box<Box<i32>>`.
//! LLVM identifiers with `<`/`>` require quoted `@"..."` / `%"..."`
//! syntax, which codegen emits.
//!
//! ## What mono does not do
//!
//! - Lifetime handling. Lifetimes are checked pre-mono (via NLL and
//!   the loan checker) and not carried into mono. If lifetime
//!   annotations at the type level land later, mono will still see
//!   erased-lifetime types.
//! - Substructural checks. All markers and bounds were verified
//!   pre-mono; the specialized decls inherit the generic decl's
//!   markers unchanged.
//! - Cycle unrolling. Types recursive through a pointer
//!   (`struct Node<T> { next: *Node<T> }`) instantiate exactly once
//!   per concrete arg — the second time the walker sees `Node<i32>`
//!   the instantiation is already registered, so no infinite loop.

use crate::mir::helpers::{call_stmt, drop_stmt, unborrow_stmt};
use crate::mir::type_util::substitute_params;
use crate::mir::{ast::*, helpers::*};
use std::collections::{BTreeMap, VecDeque};

/// Rewrite `program` in place: erase generic decls, emit specialized
/// copies for every reachable instantiation.
pub fn monomorphize(program: &mut Program) {
    // Index the original decls by name for lookup during specialization.
    let originals: BTreeMap<String, Declaration> = program
        .declarations
        .iter()
        .map(|d| (d.meta().name.clone(), d.clone()))
        .collect();

    let mut ctx = MonoCtx {
        originals,
        needed: BTreeMap::new(),
        pending: VecDeque::new(),
    };

    // Seed: every non-generic decl is trivially reachable. Generic
    // decls are only pulled in via instantiations found while walking
    // reachable code.
    for decl in &program.declarations {
        let m = decl.meta();
        if m.type_params.is_empty() {
            ctx.need(&m.name, &[]);
        }
    }

    let mut out: Vec<Declaration> = Vec::new();
    while let Some((name, args)) = ctx.pending.pop_front() {
        let mangled = ctx.needed[&(name.clone(), args.clone())].clone();
        // Intrinsic references (`$i64_add` and the like) show up as
        // FnName consts inside function bodies but are not user-declared
        // decls in the program — codegen synthesizes them from
        // `mir::intrinsics`. Skip specializing them; the mangled name
        // (which for empty args is just the original name) is what gets
        // emitted at the call site.
        let Some(decl) = ctx.originals.get(&name).cloned() else {
            debug_assert!(
                args.is_empty(),
                "mono: unknown decl '{}' with type args {:?}",
                name,
                args
            );
            continue;
        };
        out.push(ctx.specialize(decl, &args, mangled));
    }
    program.declarations = out;
}

struct MonoCtx {
    originals: BTreeMap<String, Declaration>,
    /// Map from (original decl name, concrete args) to mangled name.
    /// Insertion order determines the emit order — post-mono decls
    /// come out in reachability order.
    needed: BTreeMap<(String, Vec<Type>), String>,
    pending: VecDeque<(String, Vec<Type>)>,
}

impl MonoCtx {
    /// Register a needed instantiation and return its mangled name.
    /// Idempotent — a second call with the same key returns the same
    /// mangled name and does not re-queue.
    fn need(&mut self, name: &str, args: &[Type]) -> String {
        let key = (name.to_string(), args.to_vec());
        if let Some(mangled) = self.needed.get(&key) {
            return mangled.clone();
        }
        let mangled = mangle(name, args);
        self.needed.insert(key.clone(), mangled.clone());
        self.pending.push_back(key);
        mangled
    }

    /// Rewrite `ty` in-place: substitute Params via the outer decl's
    /// type-param mapping, then rewrite every Custom's args to
    /// concrete via `need`.
    fn walk_type(&mut self, ty: &Type) -> Type {
        match &ty.kind {
            TypeKind::Custom(name, _, args) => {
                let new_args: Vec<Type> = args.iter().map(|a| self.walk_type(a)).collect();
                let mangled = self.need(name, &new_args);
                Type::no_span(TypeKind::Custom(mangled, Vec::new(), Vec::new()))
            }
            TypeKind::Ref(kind, lt, inner) => Type::no_span(TypeKind::Ref(*kind, lt.clone(), Box::new(self.walk_type(inner)))),
            TypeKind::RawPtr(inner) => Type::no_span(TypeKind::RawPtr(Box::new(self.walk_type(inner)))),
            TypeKind::Array(inner, n) => Type::no_span(TypeKind::Array(Box::new(self.walk_type(inner)), *n)),
            TypeKind::Fn(params) => {
                Type::no_span(TypeKind::Fn(params.iter().map(|p| self.walk_type(p)).collect()))
            }
            TypeKind::Param(name) => panic!(
                "mono: unsubstituted TypeKind::Param '{}' — caller should have subst'd it before walk_type",
                name
            ),
            _ => ty.clone(),
        }
    }

    fn walk_operand(&mut self, op: &Operand) -> Operand {
        match op {
            Operand::Copy(p) => Operand::Copy(p.clone()),
            Operand::Move(p) => Operand::Move(p.clone()),
            Operand::Const(c) => Operand::Const(self.walk_const(c)),
        }
    }

    fn walk_const(&mut self, c: &ConstVal) -> ConstVal {
        match c {
            ConstVal::FnName(name, args) => {
                let new_args: Vec<Type> = args.iter().map(|a| self.walk_type(a)).collect();
                let mangled = self.need(name, &new_args);
                ConstVal::FnName(mangled, Vec::new())
            }
            _ => c.clone(),
        }
    }

    fn walk_rvalue(&mut self, r: &RValue) -> RValue {
        match r {
            RValue::Use(op) => RValue::Use(self.walk_operand(op)),
            RValue::Ref(k, p) => RValue::Ref(*k, p.clone()),
            RValue::RawRef(p) => RValue::RawRef(p.clone()),
            RValue::EnumConstr(name, args, variant, payload) => {
                let new_args: Vec<Type> = args.iter().map(|a| self.walk_type(a)).collect();
                let mangled = self.need(name, &new_args);
                RValue::EnumConstr(
                    mangled,
                    Vec::new(),
                    variant.clone(),
                    self.walk_operand(payload),
                )
            }
            RValue::ArrayLit(ops) => {
                RValue::ArrayLit(ops.iter().map(|o| self.walk_operand(o)).collect())
            }
        }
    }

    fn walk_stmt(&mut self, s: &Statement) -> Statement {
        match &s.kind {
            StatementKind::Assign(p, r) => assign_stmt(p.clone(), self.walk_rvalue(r), s.span),
            StatementKind::Call(callee, args) => call_stmt(
                self.walk_operand(callee),
                args.iter().map(|a| self.walk_operand(a)).collect(),
                s.span,
            ),
            StatementKind::Drop(p) => drop_stmt(p.clone(), s.span),
            StatementKind::Unborrow(p) => unborrow_stmt(p.clone(), s.span),
        }
    }

    fn walk_terminator(&mut self, t: &Terminator) -> Terminator {
        match &t.kind {
            TerminatorKind::Branch {
                cond,
                true_label,
                false_label,
            } => branch_term(
                self.walk_operand(cond),
                true_label.clone(),
                false_label.clone(),
                t.span,
            ),
            _ => t.clone(),
        }
    }

    fn specialize(&mut self, decl: Declaration, args: &[Type], mangled: String) -> Declaration {
        match decl {
            Declaration::Struct(s) => {
                let type_params = s.meta.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let fields = s
                    .fields
                    .iter()
                    .map(|f| StructField {
                        name: f.name.clone(),
                        ty: self.walk_type(&subst(&f.ty)),
                        span: f.span,
                    })
                    .collect();
                Declaration::Struct(StructDecl {
                    meta: DeclMeta { 
                        name: mangled,
                        name_span: s.meta.name_span,
                        lifetime_params: Vec::new(),
                        type_params: Vec::new(),
                        markers: s.meta.markers,
                        outlives: vec![],  // TODO
                    },
                    fields,
                })
            }
            Declaration::Enum(e) => {
                let type_params = e.meta.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let variants = e
                    .variants
                    .iter()
                    .map(|v| EnumVariant {
                        name: v.name.clone(),
                        ty: self.walk_type(&subst(&v.ty)),
                        span: v.span,
                    })
                    .collect();
                Declaration::Enum(EnumDecl {
                    meta: DeclMeta {
                        name: mangled,
                        name_span: e.meta.name_span,
                        lifetime_params: Vec::new(),
                        type_params: Vec::new(),
                        outlives: Vec::new(),
                        markers: e.meta.markers,
                    },
                    variants,
                })
            }
            Declaration::Fn(f) => {
                let type_params = f.meta.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let params = f
                    .params
                    .iter()
                    .map(|p| Param {
                        name: p.name.clone(),
                        ty: self.walk_type(&subst(&p.ty)),
                        span: p.span,
                    })
                    .collect();
                let body = f.body.map(|b| FunctionBody {
                    locals: b
                        .locals
                        .iter()
                        .map(|l| Local {
                            name: l.name.clone(),
                            ty: self.walk_type(&subst(&l.ty)),
                            span: l.span,
                        })
                        .collect(),
                    blocks: b
                        .blocks
                        .iter()
                        .map(|blk| BasicBlock {
                            label: blk.label.clone(),
                            label_span: blk.label_span,
                            statements: blk
                                .statements
                                .iter()
                                .map(|s| {
                                    // Substitute params in any FnName /
                                    // EnumConstr type args before walk.
                                    let s = substitute_stmt_types(s, &type_params, args);
                                    self.walk_stmt(&s)
                                })
                                .collect(),
                            terminator: {
                                let t = substitute_terminator_types(
                                    &blk.terminator,
                                    &type_params,
                                    args,
                                );
                                self.walk_terminator(&t)
                            },
                        })
                        .collect(),
                });
                Declaration::Fn(Function {
                    meta: DeclMeta {
                        name: mangled,
                        name_span: f.meta.name_span,
                        lifetime_params: Vec::new(),
                        outlives: Vec::new(),
                        type_params: Vec::new(),
                        markers: trivial_markers(),
                    },
                    is_extern: f.is_extern,
                    abi: f.abi.clone(),
                    params,
                    body,
                })
            }
        }
    }
}

/// `foo<i32, u32>` mangling. Non-generic → unchanged name; generic →
/// `name<arg1, arg2, ...>` with each arg's `Display` form. Nested
/// args have already been mangled (their name field carries the
/// nested `<...>` shape), so nested printing composes correctly.
fn mangle(name: &str, args: &[Type]) -> String {
    if args.is_empty() {
        return name.to_string();
    }
    let parts: Vec<String> = args.iter().map(|a| format!("{}", a)).collect();
    format!("{}<{}>", name, parts.join(", "))
}

/// Substitute Params in every Type-carrying position inside a statement.
fn substitute_stmt_types(s: &Statement, type_params: &[TypeParam], args: &[Type]) -> Statement {
    match &s.kind {
        StatementKind::Assign(p, r) => assign_stmt(
            p.clone(),
            substitute_rvalue_types(r, type_params, args),
            s.span,
        ),
        StatementKind::Call(callee, cargs) => call_stmt(
            substitute_operand_types(callee, type_params, args),
            cargs
                .iter()
                .map(|a| substitute_operand_types(a, type_params, args))
                .collect(),
            s.span,
        ),
        StatementKind::Drop(p) => drop_stmt(p.clone(), s.span),
        StatementKind::Unborrow(p) => unborrow_stmt(p.clone(), s.span),
    }
}

fn substitute_rvalue_types(r: &RValue, type_params: &[TypeParam], args: &[Type]) -> RValue {
    match r {
        RValue::EnumConstr(name, targs, variant, payload) => RValue::EnumConstr(
            name.clone(),
            targs
                .iter()
                .map(|a| substitute_params(a, type_params, args))
                .collect(),
            variant.clone(),
            substitute_operand_types(payload, type_params, args),
        ),
        RValue::Use(op) => RValue::Use(substitute_operand_types(op, type_params, args)),
        RValue::Ref(k, p) => RValue::Ref(*k, p.clone()),
        RValue::RawRef(p) => RValue::RawRef(p.clone()),
        RValue::ArrayLit(ops) => RValue::ArrayLit(
            ops.iter()
                .map(|o| substitute_operand_types(o, type_params, args))
                .collect(),
        ),
    }
}

fn substitute_operand_types(op: &Operand, type_params: &[TypeParam], args: &[Type]) -> Operand {
    match op {
        Operand::Const(ConstVal::FnName(name, targs)) => Operand::Const(ConstVal::FnName(
            name.clone(),
            targs
                .iter()
                .map(|a| substitute_params(a, type_params, args))
                .collect(),
        )),
        _ => op.clone(),
    }
}

fn substitute_terminator_types(
    t: &Terminator,
    _type_params: &[TypeParam],
    _args: &[Type],
) -> Terminator {
    // Branch's `cond` is an Operand that's always a bool operand — bool
    // isn't parameterizable, so no substitution needed. Other terminators
    // don't carry types.
    t.clone()
}
