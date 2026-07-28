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

/// Run lifetime elision on every declaration in `program`. Mutates in
/// place. Idempotent — a second run finds no `None` slots to fill.
pub fn desugar_program(program: &mut Program) {
    for decl in &mut program.declarations {
        match decl {
            Declaration::Fn(f) => desugar_fn(f),
            Declaration::Struct(s) => desugar_struct(s),
            Declaration::Enum(e) => desugar_enum(e),
            Declaration::Trait(t) => desugar_trait(t),
            Declaration::Impl(i) => desugar_impl(i),
        }
    }
}

fn desugar_fn(f: &mut Function) {
    desugar_signature(&mut f.meta, &mut f.params);
}

/// Trait method sigs and impl method sigs elide by the same rule as free
/// fns: unnamed refs get fresh `'sN` lifetimes appended to the method's
/// own `lifetime_params`, and every synthesized output-position lifetime
/// gets a `every_input outlives it` axiom. The impl-header's `<'a>` and
/// the trait's `<'a>` are separately in scope; elision only introduces
/// method-level synth params, so trait-vs-impl signature conformance
/// after `Self := target` and header-lifetime substitution matches
/// positionally.
fn desugar_trait(t: &mut TraitDecl) {
    for method in &mut t.methods {
        desugar_signature(&mut method.meta, &mut method.params);
    }
}

fn desugar_impl(i: &mut ImplBlock) {
    // Seed the fresh-name skiplist with the impl-header's lifetime
    // params too — they're in scope for method bodies through
    // `effective_impl_method`, so a synthesized `'sN` colliding with
    // an explicit header name (e.g. `impl<'s0>`) would shadow it once
    // the header is prepended.
    let header_lts: Vec<LifetimeParam> = i.meta.lifetime_params.clone();
    for method in &mut i.methods {
        let mut ctx = ElideCtx::new_with_extra(&method.meta.lifetime_params, &header_lts);
        for p in &mut method.params {
            elide_type_pos(&mut p.ty, Pos::Input, &mut ctx);
        }
        finish_signature_elision(&mut method.meta, ctx);
    }
}

fn desugar_signature(meta: &mut DeclMeta, params: &mut [Param]) {
    let mut ctx = ElideCtx::new(&meta.lifetime_params);
    for p in params {
        elide_type_pos(&mut p.ty, Pos::Input, &mut ctx);
    }
    finish_signature_elision(meta, ctx);
}

fn finish_signature_elision(meta: &mut DeclMeta, ctx: ElideCtx) {
    meta.lifetime_params.extend(ctx.synthesized);
    // Every synthesized output lifetime is outlived by every input
    // lifetime. Explicit output lifetimes are not axiomatized — the
    // user annotated them intentionally.
    for (out_lt, out_source) in &ctx.synth_output {
        for in_lt in &ctx.input {
            meta.outlives.push(OutlivesBound::generated(
                in_lt.clone(),
                out_lt.clone(),
                GeneratedKind::LifetimeElision,
                out_source.span(),
            ));
        }
    }
}

fn desugar_struct(s: &mut StructDecl) {
    let mut ctx = ElideCtx::new(&s.meta.lifetime_params);
    for f in &mut s.fields {
        elide_type_pos(&mut f.ty, Pos::Input, &mut ctx);
    }
    s.meta.lifetime_params.extend(ctx.synthesized);
}

fn desugar_enum(e: &mut EnumDecl) {
    let mut ctx = ElideCtx::new(&e.meta.lifetime_params);
    for v in &mut e.variants {
        elide_type_pos(&mut v.ty, Pos::Input, &mut ctx);
    }
    e.meta.lifetime_params.extend(ctx.synthesized);
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Pos {
    Input,
    Output,
}

struct ElideCtx {
    counter: u32,
    used: Vec<String>,
    synthesized: Vec<LifetimeParam>,
    /// All lifetimes seen at input position, real or synthesized.
    input: Vec<Lifetime>,
    /// Synthesized lifetimes seen at output position. These get
    /// axioms `in outlives out` for every `in` in `input`.
    synth_output: Vec<(Lifetime, SourceInfo)>,
}

impl ElideCtx {
    fn new(existing: &[LifetimeParam]) -> Self {
        Self::new_with_extra(existing, &[])
    }

    /// Seed the fresh-name skiplist with two independent sets of
    /// already-in-scope names. Used by impl-method elision to seed both
    /// the method's own lifetime params and the impl header's — the
    /// header's names are prepended into the effective method scope
    /// downstream, so a collision here would shadow them silently.
    fn new_with_extra(existing: &[LifetimeParam], extra: &[LifetimeParam]) -> Self {
        let used = existing
            .iter()
            .chain(extra.iter())
            .map(|l| l.lifetime.0.clone())
            .collect();
        Self {
            counter: 0,
            used,
            synthesized: Vec::new(),
            input: Vec::new(),
            synth_output: Vec::new(),
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

fn elide_type_pos(ty: &mut Type, pos: Pos, ctx: &mut ElideCtx) {
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
            elide_type_pos(inner, inner_pos, ctx);
        }
        TypeKind::RawPtr(inner) => elide_type_pos(inner, pos, ctx),
        TypeKind::Array(elem, _) => elide_type_pos(elem, pos, ctx),
        TypeKind::Fn(args) => {
            for a in args {
                elide_type_pos(a, pos, ctx);
            }
        }
        TypeKind::Custom(Instance { type_args: args, .. }) => {
            for a in args {
                elide_type_pos(a, pos, ctx);
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

