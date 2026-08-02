//! Monomorphization pass.
//!
//! Runs after all type-checks and elaboration, immediately before
//! codegen. Takes a MIR [`IndexedProgram`] that may contain generic decls
//! (`struct<T> Box`, `fn<T> id`) and their instantiations
//! (`Box<i32>`, `id<i32>(x)`) and produces an indexed program where:
//!
//!   - Every `Custom(name, args)` has `args = []`; `name` is the
//!     mangled instantiation name (e.g. `Box<i32>`).
//!   - Every `FnName(instance)` has no generic args; its name is the
//!     mangled instantiation name.
//!   - Every `TraitFn` has been resolved to the selected impl method and
//!     rewritten to a concrete `FnName`.
//!   - No `Function.type_params`, `StructDecl.type_params`, or
//!     `EnumDecl.type_params` remain — every decl is a concrete
//!     instantiation.
//!   - Impl blocks are gone; their reachable methods are emitted as ordinary
//!     functions.
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

use crate::common::{GeneratedKind, Marker, Markers};
use crate::mir::env::{
    impl_marker_bounds_satisfied, match_impl_header, match_inherent_impl_header, IndexedProgram,
};
use crate::mir::type_fold::TypeFolder;
use crate::mir::type_util::{
    substitute_params, substitute_stmt_types, substitute_terminator_types,
};
use crate::mir::{ast::*, helpers::*};
use std::collections::{BTreeMap, VecDeque};

/// Consume `program` and return its concrete, monomorphized form.
pub(crate) fn monomorphize(program: IndexedProgram) -> IndexedProgram {
    let IndexedProgram {
        types,
        traits,
        functions,
        impls,
        inherent_impls,
    } = program;

    let type_markers = types
        .iter()
        .map(|(name, declaration)| (name.clone(), declaration.meta().markers))
        .collect();

    let mut declarations = Vec::with_capacity(
        types.len() + traits.len() + functions.len() + impls.len() + inherent_impls.len(),
    );
    declarations.extend(types.into_values().map(|declaration| match declaration {
        TypeDecl::Struct(declaration) => Declaration::Struct(declaration),
        TypeDecl::Enum(declaration) => Declaration::Enum(declaration),
    }));
    declarations.extend(traits.into_values().map(Declaration::Trait));

    let mut intrinsic_functions = indexmap::IndexMap::new();
    for (name, function) in functions {
        if function.meta.name_source.generated_kind() == Some(GeneratedKind::Intrinsic) {
            intrinsic_functions.insert(name, function);
        } else {
            declarations.push(Declaration::Fn(function));
        }
    }
    declarations.extend(impls.into_values().map(Declaration::Impl));
    declarations.extend(inherent_impls.into_iter().map(Declaration::Impl));
    declarations.sort_by_key(|declaration| {
        let source = declaration
            .meta()
            .map(|meta| meta.name_source)
            .unwrap_or(declaration.params().source);
        let span = source.span();
        (span.line, span.col, span.end_line, span.end_col)
    });

    // Index ordinary declarations and impl-method templates by name for
    // lookup during specialization. Impl-header type parameters are prepended
    // to each method's own parameters so both can use the ordinary function
    // specialization path once trait lookup has inferred the header args.
    let is_mono_target = |d: &Declaration| !matches!(d, Declaration::Impl(_));
    let mut originals = BTreeMap::new();
    let mut impl_blocks = Vec::new();
    let mut seeds = Vec::new();
    for declaration in declarations {
        if is_mono_target(&declaration) {
            let meta = declaration.meta().unwrap();
            if meta.params.type_params.is_empty() {
                seeds.push(meta.name.clone());
            }
            originals.insert(meta.name.clone(), declaration);
        } else if let Declaration::Impl(impl_block) = declaration {
            for method in &impl_block.methods {
                let template = impl_method_template(&impl_block, method);
                let template_name = template.meta.name.clone();
                assert!(
                    originals
                        .insert(template_name.clone(), Declaration::Fn(template))
                        .is_none(),
                    "mono: duplicate impl-method template '{}'",
                    template_name,
                );
            }
            impl_blocks.push(impl_block);
        }
    }

    let mut ctx = MonoCtx {
        originals,
        impl_blocks,
        type_markers,
        needed: BTreeMap::new(),
        pending: VecDeque::new(),
    };

    // Seed: every non-generic decl is trivially reachable. Generic
    // decls are only pulled in via instantiations found while walking
    // reachable code.
    for name in seeds {
        ctx.need(&name, &[]);
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
    let mut program = IndexedProgram {
        types: indexmap::IndexMap::new(),
        traits: indexmap::IndexMap::new(),
        functions: intrinsic_functions,
        impls: indexmap::IndexMap::new(),
        inherent_impls: Vec::new(),
    };
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
                if let Some(trait_path) = &declaration.trait_path {
                    program.impls.insert(
                        (trait_path.clone(), declaration.target.clone()),
                        declaration,
                    );
                } else {
                    program.inherent_impls.push(declaration);
                }
            }
        }
    }
    program
}

fn impl_method_template_name(impl_block: &ImplBlock, method: &Function) -> String {
    match &impl_block.trait_path {
        Some(trait_path) => format!(
            "<{} as {}>::{}",
            impl_block.target, trait_path, method.meta.name,
        ),
        None => format!("<{}>::{}", impl_block.target, method.meta.name),
    }
}

fn impl_method_template(impl_block: &ImplBlock, method: &Function) -> Function {
    let mut params = impl_block.params.clone();
    params
        .lifetime_params
        .extend(method.meta.params.lifetime_params.clone());
    params.outlives.extend(method.meta.params.outlives.clone());
    params
        .type_params
        .extend(method.meta.params.type_params.clone());

    let mut method = method.clone();
    method.meta.name = impl_method_template_name(impl_block, &method);
    method.meta.params = params;
    method
}

struct MonoCtx {
    originals: BTreeMap<String, Declaration>,
    impl_blocks: Vec<ImplBlock>,
    type_markers: BTreeMap<String, Markers>,
    /// Map from (original decl name, concrete args) to mangled name.
    /// `pending` separately preserves reachability discovery order.
    needed: BTreeMap<(String, Vec<Type>), String>,
    pending: VecDeque<(String, Vec<Type>)>,
}

impl MonoCtx {
    /// Register a needed instantiation and return its mangled name.
    /// Idempotent — a second call with the same key returns the same
    /// mangled name and does not re-queue.
    fn need(&mut self, name: &str, args: &[Type]) -> String {
        self.need_named(name, args, mangle(name, args))
    }

    fn need_named(&mut self, name: &str, args: &[Type], mangled: String) -> String {
        let key = (name.to_string(), args.to_vec());
        if let Some(existing) = self.needed.get(&key) {
            assert_eq!(
                existing, &mangled,
                "mono: one specialization key produced multiple symbols",
            );
            return existing.clone();
        }
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
            ConstVal::FnName(instance) => {
                let new_args: Vec<Type> = instance
                    .type_args
                    .iter()
                    .map(|a| self.fold_type(a))
                    .collect();
                // Intrinsics keep their `$name` and type_args intact —
                // codegen inspects the concrete args to lower generic
                // intrinsics like `$sizeof<T>`. Non-intrinsic calls get
                // mangled per-instantiation.
                if crate::mir::intrinsics::is_intrinsic(&instance.name) {
                    return ConstVal::FnName(Instance::new(
                        instance.name.clone(),
                        instance.lifetime_args.clone(),
                        new_args,
                    ));
                }
                let mangled = self.need(&instance.name, &new_args);
                ConstVal::FnName(Instance::new(mangled, Vec::new(), Vec::new()))
            }
            ConstVal::InherentFn { self_ty, method } => {
                let (template_name, impl_args) = self.resolve_inherent_fn(self_ty, &method.name);
                let concrete_self = self.fold_type(self_ty);
                let concrete_method = self.fold_instance(method);
                let args = impl_args
                    .into_iter()
                    .chain(method.type_args.iter().cloned())
                    .map(|arg| self.fold_type(&arg))
                    .collect::<Vec<_>>();
                let symbol = format!(
                    "<{}>::{}",
                    erase_type_lifetimes(&concrete_self),
                    erase_instance_lifetimes(&concrete_method),
                );
                let mangled = self.need_named(&template_name, &args, symbol);
                ConstVal::FnName(Instance::new(mangled, Vec::new(), Vec::new()))
            }
            ConstVal::TraitFn {
                trait_path,
                self_ty,
                method,
            } => {
                let (template_name, impl_args) =
                    self.resolve_trait_fn(trait_path, self_ty, &method.name);
                let concrete_self = self.fold_type(self_ty);
                let concrete_trait = self.fold_instance(trait_path);
                let concrete_method = self.fold_instance(method);
                let args = impl_args
                    .into_iter()
                    .chain(method.type_args.iter().cloned())
                    .map(|arg| self.fold_type(&arg))
                    .collect::<Vec<_>>();
                let symbol = format!(
                    "<{} as {}>::{}",
                    erase_type_lifetimes(&concrete_self),
                    erase_instance_lifetimes(&concrete_trait),
                    erase_instance_lifetimes(&concrete_method),
                );
                let mangled = self.need_named(&template_name, &args, symbol);
                ConstVal::FnName(Instance::new(mangled, Vec::new(), Vec::new()))
            }
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

    fn fold_instance(&mut self, instance: &Instance) -> Instance {
        Instance {
            name: instance.name.clone(),
            lifetime_args: instance
                .lifetime_args
                .iter()
                .map(|lifetime| self.fold_lifetime(lifetime))
                .collect(),
            type_args: instance
                .type_args
                .iter()
                .map(|ty| self.fold_type(ty))
                .collect(),
        }
    }

    fn resolve_trait_fn(
        &self,
        trait_path: &Instance,
        self_ty: &Type,
        method_name: &str,
    ) -> (String, Vec<Type>) {
        let mut selected = None;
        for impl_block in &self.impl_blocks {
            let Some(impl_trait_path) = &impl_block.trait_path else {
                continue;
            };
            if impl_trait_path.name != trait_path.name {
                continue;
            }
            let Some(bindings) = match_impl_header(impl_block, trait_path, self_ty) else {
                continue;
            };
            if !impl_marker_bounds_satisfied(impl_block, &bindings, |ty| self.class_of_concrete(ty))
            {
                continue;
            }
            let Some(method) = impl_block
                .methods
                .iter()
                .find(|method| method.meta.name == method_name)
            else {
                continue;
            };
            let candidate = (
                impl_method_template_name(impl_block, method),
                bindings.type_args,
            );
            assert!(
                selected.is_none(),
                "mono: overlapping impls while resolving <{} as {}>::{}",
                self_ty,
                trait_path,
                method_name,
            );
            selected = Some(candidate);
        }
        selected.unwrap_or_else(|| {
            panic!(
                "mono: no impl method found while resolving <{} as {}>::{}; type checking should have rejected the call",
                self_ty, trait_path, method_name,
            )
        })
    }

    fn resolve_inherent_fn(&self, self_ty: &Type, method_name: &str) -> (String, Vec<Type>) {
        let mut selected = None;
        for impl_block in &self.impl_blocks {
            let Some(bindings) = match_inherent_impl_header(impl_block, self_ty) else {
                continue;
            };
            if !impl_marker_bounds_satisfied(impl_block, &bindings, |ty| self.class_of_concrete(ty))
            {
                continue;
            }
            let Some(method) = impl_block
                .methods
                .iter()
                .find(|method| method.meta.name == method_name)
            else {
                continue;
            };
            let candidate = (
                impl_method_template_name(impl_block, method),
                bindings.type_args,
            );
            assert!(
                selected.is_none(),
                "mono: overlapping inherent impls while resolving <{}>::{}",
                self_ty,
                method_name,
            );
            selected = Some(candidate);
        }
        selected.unwrap_or_else(|| {
            panic!(
                "mono: no inherent method found while resolving <{}>::{}; type checking should have rejected the call",
                self_ty, method_name,
            )
        })
    }

    fn class_of_concrete(&self, ty: &Type) -> Markers {
        let all = || Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]);
        match &ty.kind {
            TypeKind::Int(_)
            | TypeKind::Float(_)
            | TypeKind::Bool
            | TypeKind::Unit
            | TypeKind::Never
            | TypeKind::Fn(_)
            | TypeKind::RawPtr(_) => all(),
            TypeKind::Ref(kind, _, _) => match kind {
                RefKind::Shared => all(),
                RefKind::Mut | RefKind::Uninit => Markers::from_iter([Marker::Drop, Marker::Move]),
                RefKind::Out | RefKind::Drop => Markers::from_iter([Marker::Move]),
            },
            TypeKind::Custom(instance) => self
                .type_markers
                .get(&instance.name)
                .copied()
                .unwrap_or_else(Markers::empty),
            TypeKind::Array(element, _) => self.class_of_concrete(element),
            TypeKind::Param(name) => panic!(
                "mono: unresolved type parameter '{}' during impl-bound checking",
                name,
            ),
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
                        params: GenericParams {
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
                        params: GenericParams {
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
                        params: GenericParams {
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

fn erase_instance_lifetimes(instance: &Instance) -> Instance {
    Instance {
        name: instance.name.clone(),
        lifetime_args: Vec::new(),
        type_args: instance
            .type_args
            .iter()
            .map(erase_type_lifetimes)
            .collect(),
    }
}

fn erase_type_lifetimes(ty: &Type) -> Type {
    let kind = match &ty.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_) => return ty.clone(),
        TypeKind::Custom(instance) => TypeKind::Custom(erase_instance_lifetimes(instance)),
        TypeKind::Fn(params) => TypeKind::Fn(params.iter().map(erase_type_lifetimes).collect()),
        TypeKind::Ref(kind, _, inner) => {
            TypeKind::Ref(*kind, None, Box::new(erase_type_lifetimes(inner)))
        }
        TypeKind::RawPtr(inner) => TypeKind::RawPtr(Box::new(erase_type_lifetimes(inner))),
        TypeKind::Array(element, size) => {
            TypeKind::Array(Box::new(erase_type_lifetimes(element)), *size)
        }
    };
    Type::new(kind, ty.source)
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
            impl_blocks: Vec::new(),
            type_markers: BTreeMap::new(),
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

        let program = IndexedProgram::build(&parsed).0;
        let program = monomorphize(program);

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
