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
pub fn elide_program(program: &mut Program) {
    for decl in &mut program.declarations {
        match decl {
            Declaration::Fn(f) => elide_function(f),
            Declaration::Struct(s) => elide_struct(s),
            Declaration::Enum(e) => elide_enum(e),
        }
    }
}

fn elide_function(f: &mut Function) {
    let mut ctx = ElideCtx::new(&f.meta.lifetime_params);
    for p in &mut f.params {
        elide_type_pos(&mut p.ty, Pos::Input, &mut ctx);
    }
    f.meta.lifetime_params.extend(ctx.synthesized);
    // Every synthesized output lifetime is outlived by every input
    // lifetime. Explicit output lifetimes are not axiomatized — the
    // user annotated them intentionally.
    for (out_lt, out_source) in &ctx.synth_output {
        for in_lt in &ctx.input {
            f.meta.outlives.push(OutlivesBound::generated(
                in_lt.clone(),
                out_lt.clone(),
                GeneratedKind::LifetimeElision,
                out_source.span(),
            ));
        }
    }
}

fn elide_struct(s: &mut StructDecl) {
    let mut ctx = ElideCtx::new(&s.meta.lifetime_params);
    for f in &mut s.fields {
        elide_type_pos(&mut f.ty, Pos::Input, &mut ctx);
    }
    s.meta.lifetime_params.extend(ctx.synthesized);
}

fn elide_enum(e: &mut EnumDecl) {
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
        Self {
            counter: 0,
            used: existing.iter().map(|l| l.lifetime.0.clone()).collect(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::helpers::*;

    fn explicit_lifetime(name: &str) -> LifetimeParam {
        LifetimeParam::written(Lifetime(name.into()), Span::default())
    }

    fn has_bound(bounds: &[OutlivesBound], longer: &str, shorter: &str) -> bool {
        bounds
            .iter()
            .any(|b| b.longer.0 == longer && b.shorter.0 == shorter)
    }

    #[test]
    fn each_unannotated_ref_gets_fresh_lifetime() {
        let mut ty1 = mut_ref_ty(i64_ty());
        let mut ty2 = shared_ref_ty(i64_ty());
        let mut ctx = ElideCtx::new(&[]);
        elide_type_pos(&mut ty1, Pos::Input, &mut ctx);
        elide_type_pos(&mut ty2, Pos::Input, &mut ctx);
        assert_eq!(
            ctx.synthesized
                .iter()
                .map(|p| p.lifetime.clone())
                .collect::<Vec<_>>(),
            vec![Lifetime("s0".into()), Lifetime("s1".into())]
        );
        assert!(matches!(ty1.kind, TypeKind::Ref(_, Some(_), _)));
        assert!(matches!(ty2.kind, TypeKind::Ref(_, Some(_), _)));
    }

    #[test]
    fn already_annotated_ref_is_untouched() {
        let mut ty = named_ref_ty(RefKind::Shared, Lifetime("a".into()), i64_ty());
        let mut ctx = ElideCtx::new(&[explicit_lifetime("a")]);
        elide_type_pos(&mut ty, Pos::Input, &mut ctx);
        assert!(ctx.synthesized.is_empty());
        if let TypeKind::Ref(_, Some(lt), _) = &ty.kind {
            assert_eq!(lt.0, "a");
        } else {
            panic!("expected annotated ref");
        }
    }

    #[test]
    fn fresh_skips_existing_names() {
        let mut ctx = ElideCtx::new(&[explicit_lifetime("s0"), explicit_lifetime("s2")]);
        let source = SourceInfo::generated(GeneratedKind::TestHelper, Span::default());
        let a = ctx.fresh_at(source);
        let b = ctx.fresh_at(source);
        assert_eq!(a.0, "s1");
        assert_eq!(b.0, "s3");
    }

    #[test]
    fn function_gets_synthesized_params_appended() {
        let mut f = Function {
            meta: DeclMeta {
                name: "f".into(),
                name_source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
                lifetime_params: vec![explicit_lifetime("a")],
                outlives: vec![],
                type_params: vec![],
                markers: trivial_markers(),
            },
            is_extern: false,
            abi: None,
            params: vec![
                Param {
                    name: "x".into(),
                    ty: mut_ref_ty(i64_ty()),
                    source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
                },
                Param {
                    name: "y".into(),
                    ty: named_ref_ty(RefKind::Shared, Lifetime("a".into()), i64_ty()),
                    source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
                },
            ],
            body: None,
        };
        elide_function(&mut f);
        assert_eq!(
            f.meta
                .lifetime_params
                .iter()
                .map(|p| p.lifetime.clone())
                .collect::<Vec<_>>(),
            vec![Lifetime("a".into()), Lifetime("s0".into())]
        );
        assert_eq!(
            f.meta.lifetime_params[1].source.generated_kind(),
            Some(GeneratedKind::LifetimeElision)
        );
    }

    #[test]
    fn idempotent() {
        let mut f = Function {
            meta: basic_meta("f"),
            is_extern: false,
            abi: None,
            params: vec![Param {
                name: "x".into(),
                ty: mut_ref_ty(i64_ty()),
                source: SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
            }],
            body: None,
        };
        elide_function(&mut f);
        let after_first = f.clone();
        elide_function(&mut f);
        assert_eq!(f, after_first);
    }

    fn parse_and_elide(src: &str) -> Function {
        use crate::mir::parser::Parser;
        let mut program = Parser::parse_or_panic(src);
        elide_program(&mut program);
        program
            .declarations
            .into_iter()
            .find_map(|d| match d {
                Declaration::Fn(f) => Some(f),
                _ => None,
            })
            .expect("fn decl")
    }

    #[test]
    fn single_input_output_gets_input_outlives_output_axiom() {
        // fn identity(r: &i64, $return: &out &i64) — elides to
        //   r: &'s0 i64,  $return: &out 's1 &'s2 i64
        // 's0 (input) outlives 's2 (elided output).
        // 's1 (input, outer &out lifetime) outlives 's2 too.
        let f = parse_and_elide(
            "
            fn identity(r: &i64, $return: &out &i64) {
              entry:
                return
            }
        ",
        );
        assert!(has_bound(&f.meta.outlives, "s0", "s2"));
        assert!(has_bound(&f.meta.outlives, "s1", "s2"));
        assert!(f.meta.outlives.iter().all(|bound| {
            bound.source.generated_kind() == Some(GeneratedKind::LifetimeElision)
        }));
    }

    #[test]
    fn multi_input_gives_intersection_axiom() {
        // fn pick(x: &i64, y: &i64, $return: &out &i64) — every
        // input outlives the elided output.
        let f = parse_and_elide(
            "
            fn pick(x: &i64, y: &i64, $return: &out &i64) {
              entry:
                return
            }
        ",
        );
        // Output: 's3 (inner of $return). Inputs: 's0, 's1, 's2.
        for input in ["s0", "s1", "s2"] {
            assert!(
                has_bound(&f.meta.outlives, input, "s3"),
                "expected {} outlives s3",
                input,
            );
        }
    }

    #[test]
    fn explicit_output_lifetime_no_axiom() {
        // Fully-explicit signature: no axioms because nothing was
        // synthesized in output position.
        let f = parse_and_elide(
            "
            fn<'a> identity(r: &'a i64, $return: &out &'a i64) {
              entry:
                return
            }
        ",
        );
        assert!(
            f.meta.outlives.is_empty(),
            "explicit signature should have no axioms, got {:?}",
            f.meta.outlives
        );
    }
}
