//! Lifetime elision desugar. Each `TypeKind::Ref(kind, None, T)` in a
//! decl-position (fn param / return, struct field, enum variant
//! payload) receives a freshly-synthesized `'sN` name, appended to
//! the enclosing decl's `lifetime_params`. After this pass, every
//! decl-position ref carries `Some(Lifetime)` and downstream analyses
//! can assume signature-visible refs are region-named.
//!
//! Elision rule for fns: every synthesized output-position lifetime
//! is constrained by `every_input outlives it` — the returned ref
//! lives no longer than the intersection of all input refs. These
//! constraints are recorded as signature axioms on
//! `Function::signature_outlives`.
//!
//! Position classification for a fn param `p: T`:
//!   - Regular ref-kind (`&T`, `&drop T`, `&uninit T`) — inner
//!     lifetimes are INPUT (callee reads them).
//!   - Exclusive-write kinds (`&mut T`, `&out T`) — outer lifetime
//!     is INPUT (caller's storage), inner lifetimes flip to OUTPUT
//!     (callee writes values with those regions).
//!   - Non-ref: all lifetimes are INPUT.
//!
//! Body-local refs (locals, tmps, borrower vars inside a function
//! body) are NOT desugared here — inference in the region checker
//! fills those in later. Struct and enum decls don't get axioms —
//! there's no notion of "input" vs "output" on a data decl.

use crate::mir::ast::*;
use crate::mir::env::IndexedProgram;
use std::collections::HashMap;

/// Run lifetime elision on every declaration in `program`. Mutates in
/// place. Idempotent — a second run finds no `None` slots to fill.
///
/// Two phases:
///   1. Elide struct and enum decls first. Their `lifetime_params` may
///      grow via synthesis on unannotated ref fields, so downstream
///      Custom uses need the *final* arity to materialize fresh
///      lifetime args.
///   2. Elide fn / trait / impl decls, which reference those Custom
///      types.
pub fn desugar_program(program: &mut IndexedProgram) {
    // Iterate struct/enum elision to a fixpoint. Each pass materializes
    // synthesized lifetime params on the visited decls; a subsequent
    // pass then sees the updated arities and can elide bare Custom
    // mentions elsewhere that reference the just-grown decls. Fixpoint
    // over arity counts converges in one or two iterations in practice.
    let mut arities = HashMap::new();
    loop {
        for decl in program.types.values_mut() {
            match decl {
                TypeDecl::Struct(s) => desugar_struct(s, &arities),
                TypeDecl::Enum(e) => desugar_enum(e, &arities),
            }
        }
        let next = type_arities(program);
        if next == arities {
            break;
        }
        arities = next;
    }
    for function in program.functions.values_mut().filter(|function| {
        function.meta.name_source.generated_kind() != Some(GeneratedKind::Intrinsic)
    }) {
        desugar_fn(function, &arities);
    }
    for trait_decl in program.traits.values_mut() {
        desugar_trait(trait_decl, &arities);
    }
    for impl_block in program
        .impls
        .values_mut()
        .chain(program.inherent_impls.iter_mut())
    {
        desugar_impl(impl_block, &arities);
    }
}

/// Map each named type decl to its lifetime-parameter count. Called
/// after struct/enum elision so the count reflects any synthesized
/// lifetime params.
fn type_arities(program: &IndexedProgram) -> HashMap<String, usize> {
    let mut arities = HashMap::new();
    for decl in program.types.values() {
        match decl {
            TypeDecl::Struct(s) => {
                arities.insert(s.meta.name.clone(), s.meta.params.lifetime_params.len());
            }
            TypeDecl::Enum(e) => {
                arities.insert(e.meta.name.clone(), e.meta.params.lifetime_params.len());
            }
        }
    }
    arities
}

fn desugar_fn(f: &mut Function, arities: &HashMap<String, usize>) {
    desugar_signature(&mut f.meta, &mut f.params, arities);
    // Extend Custom-arg elision to body-locals. A bare `w: Wrap`
    // reuses the fn's lifetime params positionally (same rule as
    // struct-field elision) so two locals of the same bare type
    // share a region — making `y = move x` between them regionally
    // trivial. Bare `Ref` layers in body locals stay `None`: region
    // inference handles those at check time via body-local Free
    // regions.
    if let Some(body) = &mut f.body {
        let mut ctx = DesugarCtx::new(&f.meta.params.lifetime_params, arities);
        let fn_params = f.meta.params.lifetime_params.clone();
        for local in &mut body.locals {
            desugar_body_local_ty(&mut local.ty, &fn_params, &mut ctx);
        }
        f.meta.params.lifetime_params.extend(ctx.synthesized);
    }
}

/// Body-local variant of [`desugar_type_pos`]. Fills bare `Custom`
/// lifetime args by reusing the fn's lifetime params positionally
/// (same rule as struct-field elision). Bare `Ref` layers stay
/// `None` — region inference materializes their regions during
/// checking; synthesizing 'sN here would pollute the fn signature.
fn desugar_body_local_ty(ty: &mut Type, fn_params: &[LifetimeParam], ctx: &mut DesugarCtx) {
    let ty_source = ty.source;
    match &mut ty.kind {
        TypeKind::Ref(_, _, inner) | TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            desugar_body_local_ty(inner, fn_params, ctx);
        }
        TypeKind::Fn(args) => {
            for a in args {
                desugar_body_local_ty(a, fn_params, ctx);
            }
        }
        TypeKind::Custom(Instance {
            name,
            lifetime_args,
            type_args,
        }) => {
            reuse_first_lifetime_args(name, lifetime_args, ty_source, fn_params, ctx);
            for a in type_args {
                desugar_body_local_ty(a, fn_params, ctx);
            }
        }
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_) => {}
    }
}

/// Materialize lifetime args for a bare Custom use by reusing the
/// containing decl's lifetime params positionally, then synthesized
/// params, then fresh ones. Shared by struct-field, enum-variant,
/// and body-local elision walkers — signature-position elision has
/// its own copy since it also tracks input/output axioms for the
/// synthesized args.
fn reuse_first_lifetime_args(
    name: &str,
    lifetime_args: &mut Vec<Lifetime>,
    ty_source: SourceInfo,
    reuse: &[LifetimeParam],
    ctx: &mut DesugarCtx,
) {
    if !lifetime_args.is_empty() {
        return;
    }
    let Some(&arity) = ctx.arities.get(name) else {
        return;
    };
    let available_from_existing = reuse.len();
    let available_synth = ctx.synthesized.len();
    let total_available = available_from_existing + available_synth;
    for i in 0..arity {
        let lt = if i < available_from_existing {
            reuse[i].lifetime.clone()
        } else if i < total_available {
            ctx.synthesized[i - available_from_existing]
                .lifetime
                .clone()
        } else {
            ctx.fresh_at(ty_source)
        };
        lifetime_args.push(lt);
    }
}

/// Trait method sigs and impl method sigs elide by the same rule as free
/// fns: unnamed refs get fresh `'sN` lifetimes appended to the method's
/// own `lifetime_params`, and every synthesized output-position lifetime
/// gets a `every_input outlives it` axiom. The impl-header's `<'a>` and
/// the trait's `<'a>` are separately in scope; elision only introduces
/// method-level synth params, so trait-vs-impl signature conformance
/// after `Self := target` and header-lifetime substitution matches
/// positionally.
fn desugar_trait(t: &mut TraitDecl, arities: &HashMap<String, usize>) {
    for method in &mut t.methods {
        desugar_signature(&mut method.meta, &mut method.params, arities);
    }
}

fn desugar_impl(i: &mut ImplBlock, arities: &HashMap<String, usize>) {
    // Seed the fresh-name skiplist with the impl-header's lifetime
    // params too, because they share a scope with the method-level
    // synthesized lifetimes.
    let header_lts: Vec<LifetimeParam> = i.params.lifetime_params.clone();
    for method in &mut i.methods {
        let mut ctx =
            DesugarCtx::new_with_extra(&method.meta.params.lifetime_params, &header_lts, arities);
        for p in &mut method.params {
            desugar_type_pos(&mut p.ty, Pos::Input, &mut ctx);
        }
        finish_signature_desugar(&mut method.meta, ctx);
    }
}

fn desugar_signature(meta: &mut DeclMeta, params: &mut [Param], arities: &HashMap<String, usize>) {
    let mut ctx = DesugarCtx::new(&meta.params.lifetime_params, arities);
    for p in params {
        desugar_type_pos(&mut p.ty, Pos::Input, &mut ctx);
    }
    finish_signature_desugar(meta, ctx);
}

fn finish_signature_desugar(meta: &mut DeclMeta, ctx: DesugarCtx) {
    meta.params.lifetime_params.extend(ctx.synthesized);
    // Every synthesized output lifetime is outlived by every input
    // lifetime. Explicit output lifetimes are not axiomatized — the
    // user annotated them intentionally.
    for (out_lt, out_source) in &ctx.synth_output {
        for in_lt in &ctx.input {
            meta.params.outlives.push(OutlivesBound::generated(
                in_lt.clone(),
                out_lt.clone(),
                GeneratedKind::LifetimeElision,
                out_source.span(),
            ));
        }
    }
}

fn desugar_struct(s: &mut StructDecl, arities: &HashMap<String, usize>) {
    let mut ctx = DesugarCtx::new(&s.meta.params.lifetime_params, arities);
    for f in &mut s.fields {
        desugar_decl_field_ty(&mut f.ty, &s.meta.params.lifetime_params, &mut ctx);
    }
    s.meta.params.lifetime_params.extend(ctx.synthesized);
}

fn desugar_enum(e: &mut EnumDecl, arities: &HashMap<String, usize>) {
    let mut ctx = DesugarCtx::new(&e.meta.params.lifetime_params, arities);
    for v in &mut e.variants {
        desugar_decl_field_ty(&mut v.ty, &e.meta.params.lifetime_params, &mut ctx);
    }
    e.meta.params.lifetime_params.extend(ctx.synthesized);
}

/// Struct/enum-field variant of [`desugar_type_pos`]. Ref layers still
/// synthesize fresh `'sN` (the usual elision rule), but bare `Custom`
/// mentions inside a field reuse the containing decl's own lifetime
/// params positionally rather than synthesizing more. This is what
/// makes `struct Node { next: &mut Node }` work — the &mut synthesizes
/// `'s0`, and the bare `Node` inside reuses that same `'s0` instead of
/// growing the decl to arity 2. If the containing decl doesn't yet
/// have enough params, synthesize the missing ones (extends the decl).
fn desugar_decl_field_ty(ty: &mut Type, containing_params: &[LifetimeParam], ctx: &mut DesugarCtx) {
    let ty_source = ty.source;
    match &mut ty.kind {
        TypeKind::Ref(_kind, slot, inner) => {
            if slot.is_none() {
                let lt = ctx.fresh_at(ty_source);
                *slot = Some(lt);
            }
            desugar_decl_field_ty(inner, containing_params, ctx);
        }
        TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => {
            desugar_decl_field_ty(inner, containing_params, ctx);
        }
        TypeKind::Fn(args) => {
            for a in args {
                desugar_decl_field_ty(a, containing_params, ctx);
            }
        }
        TypeKind::Custom(Instance {
            name,
            lifetime_args,
            type_args,
        }) => {
            reuse_first_lifetime_args(name, lifetime_args, ty_source, containing_params, ctx);
            for a in type_args {
                desugar_decl_field_ty(a, containing_params, ctx);
            }
        }
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_) => {}
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Pos {
    Input,
    Output,
}

struct DesugarCtx<'a> {
    counter: u32,
    used: Vec<String>,
    synthesized: Vec<LifetimeParam>,
    /// Lifetime params already declared on the enclosing decl (before
    /// synthesis) plus any extras seeded via `new_with_extra`. Used
    /// by bare-Custom elision to reuse an in-scope lifetime rather
    /// than always allocating a fresh one — so a body-local
    /// `y: Linear` can share the fn's Linear-param region.
    pre_existing: Vec<LifetimeParam>,
    /// All lifetimes seen at input position, real or synthesized.
    input: Vec<Lifetime>,
    /// Synthesized lifetimes seen at output position. These get
    /// axioms `in outlives out` for every `in` in `input`.
    synth_output: Vec<(Lifetime, SourceInfo)>,
    /// Type-decl lifetime arities, so bare `Custom` uses materialize
    /// fresh lifetime args of the right count. Empty when running the
    /// struct/enum elision pre-pass — bare Custom mentions inside
    /// struct/enum fields still elide their type_args recursively but
    /// leave their own lifetime_args empty until the second pass.
    arities: &'a HashMap<String, usize>,
}

impl<'a> DesugarCtx<'a> {
    fn new(existing: &[LifetimeParam], arities: &'a HashMap<String, usize>) -> Self {
        Self::new_with_extra(existing, &[], arities)
    }

    /// Seed the fresh-name skiplist with two independent sets of
    /// already-in-scope names. Used by impl-method elision to seed both
    /// the method's own lifetime params and the impl header's — the
    /// header's names are prepended into the effective method scope
    /// downstream, so a collision here would shadow them silently.
    fn new_with_extra(
        existing: &[LifetimeParam],
        extra: &[LifetimeParam],
        arities: &'a HashMap<String, usize>,
    ) -> Self {
        let used = existing
            .iter()
            .chain(extra.iter())
            .map(|l| l.lifetime.0.clone())
            .collect();
        let pre_existing = existing.iter().chain(extra.iter()).cloned().collect();
        Self {
            counter: 0,
            used,
            synthesized: Vec::new(),
            pre_existing,
            input: Vec::new(),
            synth_output: Vec::new(),
            arities,
        }
    }

    fn fresh_at(&mut self, source: SourceInfo) -> Lifetime {
        loop {
            let name = format!("s{}", self.counter);
            self.counter += 1;
            if !self.used.iter().any(|u| u == &name) {
                self.used.push(name.clone());
                let lt = Lifetime(name);
                self.synthesized.push(LifetimeParam::generated(
                    lt.clone(),
                    GeneratedKind::LifetimeElision,
                    source.span(),
                ));
                return lt;
            }
        }
    }
}

fn desugar_type_pos(ty: &mut Type, pos: Pos, ctx: &mut DesugarCtx) {
    let ty_source = ty.source;
    match &mut ty.kind {
        TypeKind::Ref(kind, slot, inner) => {
            let (lt, is_synth) = match slot.take() {
                Some(existing) => (existing, false),
                None => (ctx.fresh_at(ty_source), true),
            };
            match pos {
                Pos::Input => ctx.input.push(lt.clone()),
                Pos::Output => {
                    if is_synth {
                        ctx.synth_output.push((lt.clone(), ty_source));
                    }
                }
            }
            *slot = Some(lt);
            // Exclusive-write kinds flip inner position to output.
            let inner_pos = match kind {
                RefKind::Mut | RefKind::Out => Pos::Output,
                _ => pos,
            };
            desugar_type_pos(inner, inner_pos, ctx);
        }
        TypeKind::RawPtr(inner) => desugar_type_pos(inner, pos, ctx),
        TypeKind::Array(elem, _) => desugar_type_pos(elem, pos, ctx),
        TypeKind::Fn(args) => {
            for a in args {
                desugar_type_pos(a, pos, ctx);
            }
        }
        TypeKind::Custom(Instance {
            name,
            lifetime_args,
            type_args,
        }) => {
            // Materialize lifetime args for a bare use of a Custom
            // type whose decl has lifetime params. Reuse the fn's
            // already-in-scope lifetime params positionally if
            // enough exist — that way two bare `Linear` params share
            // one region, and a body-local `y: Linear` can trivially
            // hold `move x`. Synthesize the missing ones fresh and
            // apply the standard input/output axiom treatment to
            // just the fresh ones.
            if lifetime_args.is_empty() {
                if let Some(&arity) = ctx.arities.get(name) {
                    let available_from_existing = ctx.pre_existing.len();
                    let available_synth = ctx.synthesized.len();
                    let total_available = available_from_existing + available_synth;
                    for i in 0..arity {
                        let (lt, is_new) = if i < available_from_existing {
                            (ctx.pre_existing[i].lifetime.clone(), false)
                        } else if i < total_available {
                            (
                                ctx.synthesized[i - available_from_existing]
                                    .lifetime
                                    .clone(),
                                false,
                            )
                        } else {
                            (ctx.fresh_at(ty_source), true)
                        };
                        if is_new {
                            match pos {
                                Pos::Input => ctx.input.push(lt.clone()),
                                Pos::Output => ctx.synth_output.push((lt.clone(), ty_source)),
                            }
                        } else if matches!(pos, Pos::Input) {
                            // Existing param reused in input position
                            // must appear in the input set so any
                            // output-position synths axiomatize
                            // against it.
                            ctx.input.push(lt.clone());
                        }
                        lifetime_args.push(lt);
                    }
                }
            }
            for a in type_args {
                desugar_type_pos(a, pos, ctx);
            }
        }
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_) => {}
    }
}
