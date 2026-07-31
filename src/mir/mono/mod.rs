//! Monomorphization pass.
//!
//! Runs after all type-checks and elaboration, immediately before
//! codegen. Takes a MIR [`IndexedProgram`] that may contain generic decls
//! (`struct<T> Box`, `fn<T> id`) and their instantiations
//! (`Box<i32>`, `id<i32>(x)`) and produces an indexed program where:
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
//! - Lifetime specialization. Lifetimes are checked before mono and have no
//!   runtime representation, so they do not participate in instantiation keys
//!   or mangled names. Their declarations, bounds, and type occurrences remain
//!   intact in the transformed MIR.
//! - Substructural checks. All markers and bounds were verified
//!   pre-mono; the specialized decls inherit the generic decl's
//!   markers unchanged.
//! - Cycle unrolling. Types recursive through a pointer
//!   (`struct Node<T> { next: *Node<T> }`) instantiate exactly once
//!   per concrete arg — the second time the walker sees `Node<i32>`
//!   the instantiation is already registered, so no infinite loop.

use crate::common::GeneratedKind;
use crate::mir::env::{DeclarationRef, IndexedProgram};
use crate::mir::type_fold::TypeFolder;
use crate::mir::type_util::{
    substitute_params, substitute_stmt_types, substitute_terminator_types,
};
use crate::mir::{ast::*, helpers::*};
use std::collections::{BTreeMap, VecDeque};

/// Rewrite `program` in place: erase generic decls, emit specialized
/// copies for every reachable instantiation.
pub fn monomorphize(program: &mut IndexedProgram) {
    let declarations: Vec<Declaration> = program
        .declarations()
        .into_iter()
        .map(|declaration| match declaration {
            DeclarationRef::Struct(s) => Declaration::Struct(s.clone()),
            DeclarationRef::Enum(e) => Declaration::Enum(e.clone()),
            DeclarationRef::Function(f) => Declaration::Fn(f.clone()),
            DeclarationRef::Trait(t) => Declaration::Trait(t.clone()),
            DeclarationRef::Impl(i) => Declaration::Impl(i.clone()),
        })
        .collect();

    // Index the original decls by name for lookup during specialization.
    // Impl blocks bypass mono entirely — they're not name-keyed decls
    // that mono can specialize by args, and their methods are addressed
    // via `(trait, target)` lookup. Skip them here and prepend back
    // onto the mono output at the end.
    let is_mono_target = |d: &Declaration| !matches!(d, Declaration::Impl(_));
    let originals: BTreeMap<String, Declaration> = declarations
        .iter()
        .filter(|d| is_mono_target(d))
        .map(|d| (d.meta().unwrap().name.clone(), d.clone()))
        .collect();

    let mut ctx = MonoCtx {
        originals,
        needed: BTreeMap::new(),
        pending: VecDeque::new(),
    };

    // Seed: every non-generic decl is trivially reachable. Generic
    // decls are only pulled in via instantiations found while walking
    // reachable code.
    for decl in declarations.iter().filter(|d| is_mono_target(d)) {
        if let Some(m) = decl.meta() {
            if m.params.type_params.is_empty() {
                ctx.need(&m.name, &[]);
            }
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
    // Preserve impl blocks unchanged past mono. The mono trait-fn
    // resolution pass (still to be implemented) consumes them via the
    // env's impl table and emits concrete `Fn` decls in their place.
    for decl in declarations {
        if matches!(decl, Declaration::Impl(_)) {
            out.push(decl);
        }
    }

    program.types.clear();
    program.traits.clear();
    program.functions.retain(|_, function| {
        function.meta.name_source.generated_kind() == Some(GeneratedKind::Intrinsic)
    });
    program.impls.clear();
    for declaration in out {
        match declaration {
            Declaration::Struct(declaration) => {
                program
                    .types
                    .insert(declaration.meta.name.clone(), TypeDecl::Struct(declaration));
            }
            Declaration::Enum(declaration) => {
                program
                    .types
                    .insert(declaration.meta.name.clone(), TypeDecl::Enum(declaration));
            }
            Declaration::Fn(declaration) => {
                program
                    .functions
                    .insert(declaration.meta.name.clone(), declaration);
            }
            Declaration::Trait(declaration) => {
                program
                    .traits
                    .insert(declaration.meta.name.clone(), declaration);
            }
            Declaration::Impl(declaration) => {
                program.impls.insert(
                    (declaration.trait_path.clone(), declaration.target.clone()),
                    declaration,
                );
            }
        }
    }
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

    fn walk_operand(&mut self, op: &Operand) -> Operand {
        match op {
            Operand::Copy(p) => Operand::Copy(p.clone()),
            Operand::Move(p) => Operand::Move(p.clone()),
            Operand::Take(_) => unreachable!(
                "monomorphization saw unresolved `take` operand; copy relaxation should have resolved it"
            ),
            Operand::Const(c) => Operand::Const(self.walk_const(c)),
        }
    }

    fn walk_const(&mut self, c: &ConstVal) -> ConstVal {
        match c {
            ConstVal::FnName(name, args) => {
                let new_args: Vec<Type> = args.iter().map(|a| self.fold_type(a)).collect();
                // Intrinsics keep their `$name` and type_args intact —
                // codegen inspects the concrete args to lower generic
                // intrinsics like `$sizeof<T>`. Non-intrinsic calls get
                // mangled per-instantiation.
                if crate::mir::intrinsics::is_intrinsic(name) {
                    return ConstVal::FnName(name.clone(), new_args);
                }
                let mangled = self.need(name, &new_args);
                ConstVal::FnName(mangled, Vec::new())
            }
            // Trait-fn callees pass through mono unchanged. The mono
            // trait-resolution pass (still to be implemented) rewrites
            // them into concrete `FnName`s; codegen panics on any
            // surviving `TraitFn`, so a program that reaches LLVM
            // without resolution fails loudly rather than silently.
            ConstVal::TraitFn { .. } => c.clone(),
            ConstVal::Int { .. }
            | ConstVal::Float { .. }
            | ConstVal::Bool(_)
            | ConstVal::Unit
            | ConstVal::ByteStr(_) => c.clone(),
        }
    }

    fn walk_rvalue(&mut self, r: &RValue) -> RValue {
        match r {
            RValue::Use(op) => RValue::Use(self.walk_operand(op)),
            RValue::Ref(k, p) => RValue::Ref(*k, p.clone()),
            RValue::RawRef(p) => RValue::RawRef(p.clone()),
            RValue::EnumConstr(name, args, variant, payload) => {
                let new_args: Vec<Type> = args.iter().map(|a| self.fold_type(a)).collect();
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
            RValue::PtrCast(op, ty) => RValue::PtrCast(self.walk_operand(op), self.fold_type(ty)),
        }
    }

    fn walk_stmt(&mut self, s: &Statement) -> Statement {
        match &s.kind {
            StatementKind::Assign(p, r) => assign_stmt(p.clone(), self.walk_rvalue(r), s.source),
            StatementKind::Call(callee, args) => call_stmt(
                self.walk_operand(callee),
                args.iter().map(|a| self.walk_operand(a)).collect(),
                s.source,
            ),
            StatementKind::Drop(p) => drop_stmt(p.clone(), s.source),
            StatementKind::Unborrow(p) => unborrow_stmt(p.clone(), s.source),
            StatementKind::RequireUninit(p) => require_uninit_stmt(p.clone(), s.source),
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
                t.source,
            ),
            _ => t.clone(),
        }
    }

    fn specialize(&mut self, decl: Declaration, args: &[Type], mangled: String) -> Declaration {
        match decl {
            Declaration::Struct(s) => {
                let type_params = s.meta.params.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let fields = s
                    .fields
                    .iter()
                    .map(|f| StructField {
                        name: f.name.clone(),
                        ty: self.fold_type(&subst(&f.ty)),
                        source: f.source,
                    })
                    .collect();
                Declaration::Struct(StructDecl {
                    meta: DeclMeta {
                        name: mangled,
                        name_source: s.meta.name_source,
                        params: ParamsIntro {
                            lifetime_params: s.meta.params.lifetime_params,
                            outlives: s.meta.params.outlives,
                            type_params: Vec::new(),
                            source: s.meta.params.source,
                        },
                        markers: s.meta.markers,
                    },
                    fields,
                })
            }
            Declaration::Enum(e) => {
                let type_params = e.meta.params.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let variants = e
                    .variants
                    .iter()
                    .map(|v| EnumVariant {
                        name: v.name.clone(),
                        ty: self.fold_type(&subst(&v.ty)),
                        source: v.source,
                    })
                    .collect();
                Declaration::Enum(EnumDecl {
                    meta: DeclMeta {
                        name: mangled,
                        name_source: e.meta.name_source,
                        params: ParamsIntro {
                            lifetime_params: e.meta.params.lifetime_params,
                            outlives: e.meta.params.outlives,
                            type_params: Vec::new(),
                            source: e.meta.params.source,
                        },
                        markers: e.meta.markers,
                    },
                    variants,
                })
            }
            Declaration::Fn(f) => {
                let type_params = f.meta.params.type_params.clone();
                let subst = |ty: &Type| substitute_params(ty, &type_params, args);
                let params = f
                    .params
                    .iter()
                    .map(|p| Param {
                        name: p.name.clone(),
                        ty: self.fold_type(&subst(&p.ty)),
                        source: p.source,
                    })
                    .collect();
                let body = f.body.map(|b| FunctionBody {
                    locals: b
                        .locals
                        .iter()
                        .map(|l| Local {
                            name: l.name.clone(),
                            ty: self.fold_type(&subst(&l.ty)),
                            source: l.source,
                        })
                        .collect(),
                    blocks: b
                        .blocks
                        .iter()
                        .map(|blk| BasicBlock {
                            label: blk.label.clone(),
                            label_source: blk.label_source,
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
                        name_source: f.meta.name_source,
                        params: ParamsIntro {
                            lifetime_params: f.meta.params.lifetime_params,
                            outlives: f.meta.params.outlives,
                            type_params: Vec::new(),
                            source: f.meta.params.source,
                        },
                        markers: trivial_markers(),
                    },
                    is_extern: f.is_extern,
                    abi: f.abi.clone(),
                    params,
                    body,
                })
            }
            // Trait decls carry only signatures, not instantiable
            // code — mono has nothing to specialize. Pass through
            // unchanged so downstream passes still see the decl.
            Declaration::Trait(t) => Declaration::Trait(t),
            // Impl blocks are extracted before mono runs (see
            // `monomorphize`); they never reach specialization.
            Declaration::Impl(_) => unreachable!(
                "impl blocks are extracted from mono's input; specialize should not see one"
            ),
        }
    }
}

impl TypeFolder for MonoCtx {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        match &ty.kind {
            TypeKind::Custom(Instance { name, lifetime_args: lifetimes, type_args: args }) => {
                let concrete_args: Vec<Type> =
                    args.iter().map(|arg| self.fold_type(arg)).collect();
                let mangled = self.need(name, &concrete_args);
                Some(Type::new(
                    TypeKind::Custom(Instance::new(
                        mangled,
                        lifetimes
                            .iter()
                            .map(|lifetime| self.fold_lifetime(lifetime))
                            .collect(),
                        Vec::new(),
                    )),
                    ty.source,
                ))
            }
            TypeKind::Param(name) => panic!(
                "mono: unsubstituted TypeKind::Param '{}' — caller should have substituted it before type folding",
                name
            ),
            // The shared fold owns recursion and metadata preservation for
            // every structural variant that monomorphization does not replace.
            _ => None,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::parser::Parser;

    #[test]
    fn type_rewrite_preserves_outer_and_nested_provenance() {
        let outer_source = SourceInfo::written(Span {
            line: 3,
            col: 5,
            end_line: 3,
            end_col: 17,
        });
        let inner_source = SourceInfo::generated(
            GeneratedKind::LifetimeElision,
            Span {
                line: 3,
                col: 6,
                end_line: 3,
                end_col: 16,
            },
        );
        let ty = Type::new(
            TypeKind::Array(
                Box::new(Type::new(
                    TypeKind::Custom(Instance::new(
                        "Box",
                        vec![Lifetime("box".into())],
                        vec![i64_ty()],
                    )),
                    inner_source,
                )),
                1,
            ),
            outer_source,
        );
        let mut ctx = MonoCtx {
            originals: BTreeMap::new(),
            needed: BTreeMap::new(),
            pending: VecDeque::new(),
        };

        let rewritten = ctx.fold_type(&ty);

        assert_eq!(rewritten.source, outer_source);
        let TypeKind::Array(inner, 1) = rewritten.kind else {
            panic!("expected rewritten array type");
        };
        assert_eq!(inner.source, inner_source);
        let TypeKind::Custom(Instance {
            name,
            lifetime_args: lifetimes,
            type_args: args,
        }) = inner.kind
        else {
            panic!("expected rewritten custom type");
        };
        assert_eq!(name, "Box<i64>");
        assert_eq!(lifetimes, vec![Lifetime("box".into())]);
        assert!(args.is_empty());
    }

    #[test]
    fn monomorphization_preserves_declared_lifetime_metadata() {
        let parsed = Parser::parse_or_panic(
            "
            struct<'a: 'static, T: Copy + Drop> Borrowed: Copy + Drop {
              value: & 'a T
            }

            fn<'caller: 'static> use_borrowed(value: Borrowed<'caller, i64>) {
              entry:
                drop value;
                return
            }
            ",
        );

        let original_struct = parsed
            .declarations
            .iter()
            .find_map(|decl| match decl {
                Declaration::Struct(decl) if decl.meta.name == "Borrowed" => Some(decl.clone()),
                _ => None,
            })
            .expect("generic struct exists");
        let original_function = parsed
            .functions()
            .find(|function| function.meta.name == "use_borrowed")
            .cloned()
            .expect("root function exists");

        let mut program = IndexedProgram::build(&parsed).0;
        monomorphize(&mut program);

        let specialized_struct = match program.types.get("Borrowed<i64>") {
            Some(TypeDecl::Struct(declaration)) => declaration,
            _ => panic!("specialized struct exists"),
        };
        assert_eq!(
            specialized_struct.meta.params.lifetime_params,
            original_struct.meta.params.lifetime_params
        );
        assert_eq!(
            specialized_struct.meta.params.outlives,
            original_struct.meta.params.outlives
        );
        assert_eq!(
            specialized_struct.fields[0].ty.source,
            original_struct.fields[0].ty.source
        );
        let TypeKind::Ref(_, Some(field_lifetime), field_inner) =
            &specialized_struct.fields[0].ty.kind
        else {
            panic!("specialized field remains a named reference");
        };
        assert_eq!(field_lifetime, &Lifetime("a".into()));
        let TypeKind::Custom(Instance {
            type_args: original_type_args,
            ..
        }) = &original_function.params[0].ty.kind
        else {
            panic!("original root parameter is a custom type");
        };
        assert_eq!(field_inner.source, original_type_args[0].source);

        let specialized_function = program
            .functions
            .get("use_borrowed")
            .expect("root function remains");
        assert_eq!(
            specialized_function.meta.params.lifetime_params,
            original_function.meta.params.lifetime_params
        );
        assert_eq!(
            specialized_function.meta.params.outlives,
            original_function.meta.params.outlives
        );
        assert_eq!(
            specialized_function.params[0].ty.source,
            original_function.params[0].ty.source
        );
        let TypeKind::Custom(Instance {
            name,
            lifetime_args: lifetimes,
            type_args: args,
        }) = &specialized_function.params[0].ty.kind
        else {
            panic!("root parameter remains a custom type");
        };
        assert_eq!(name, "Borrowed<i64>");
        assert_eq!(lifetimes, &[Lifetime("caller".into())]);
        assert!(args.is_empty());
    }
}
