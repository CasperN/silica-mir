//! Lifetime elision desugar. Each `Type::Ref(kind, None, T)` in a
//! decl-position (fn param / return, struct field, enum variant
//! payload) receives a freshly-synthesized `'sN` name, appended to
//! the enclosing decl's `lifetime_params`. After this pass, every
//! decl-position ref carries `Some(Lifetime)` and downstream analyses
//! can assume signature-visible refs are region-named.
//!
//! Elision rule for fns (generalized rule 2): every synthesized
//! output-position lifetime is constrained by `every_input outlives
//! it` — the returned ref lives no longer than the intersection of
//! all input refs. These constraints are recorded as signature
//! axioms on `Function::signature_outlives`. Single-input case
//! collapses to Rust's rule 2 (output = input); multi-input case
//! gives output = intersection of inputs.
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
    let mut ctx = ElideCtx::new(&f.lifetime_params);
    for p in &mut f.params {
        elide_type_pos(&mut p.ty, Pos::Input, &mut ctx);
    }
    f.lifetime_params.extend(ctx.synthesized);
    // Rule 2 (generalized): every synthesized output lifetime is
    // outlived by every input lifetime. Explicit output lifetimes
    // are not axiomatized — the user annotated them intentionally.
    for out_lt in &ctx.synth_output {
        for in_lt in &ctx.input {
            f.signature_outlives.push((in_lt.clone(), out_lt.clone()));
        }
    }
}

fn elide_struct(s: &mut StructDecl) {
    let mut ctx = ElideCtx::new(&s.lifetime_params);
    for f in &mut s.fields {
        elide_type_pos(&mut f.ty, Pos::Input, &mut ctx);
    }
    s.lifetime_params.extend(ctx.synthesized);
}

fn elide_enum(e: &mut EnumDecl) {
    let mut ctx = ElideCtx::new(&e.lifetime_params);
    for v in &mut e.variants {
        elide_type_pos(&mut v.ty, Pos::Input, &mut ctx);
    }
    e.lifetime_params.extend(ctx.synthesized);
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Pos {
    Input,
    Output,
}

struct ElideCtx {
    counter: u32,
    used: Vec<String>,
    synthesized: Vec<Lifetime>,
    /// All lifetimes seen at input position, real or synthesized.
    input: Vec<Lifetime>,
    /// Synthesized lifetimes seen at output position. These get
    /// axioms `in outlives out` for every `in` in `input`.
    synth_output: Vec<Lifetime>,
}

impl ElideCtx {
    fn new(existing: &[Lifetime]) -> Self {
        Self {
            counter: 0,
            used: existing.iter().map(|l| l.0.clone()).collect(),
            synthesized: Vec::new(),
            input: Vec::new(),
            synth_output: Vec::new(),
        }
    }

    fn fresh(&mut self) -> Lifetime {
        loop {
            let name = format!("s{}", self.counter);
            self.counter += 1;
            if !self.used.iter().any(|u| u == &name) {
                self.used.push(name.clone());
                let lt = Lifetime(name);
                self.synthesized.push(lt.clone());
                return lt;
            }
        }
    }
}

fn elide_type_pos(ty: &mut Type, pos: Pos, ctx: &mut ElideCtx) {
    match ty {
        Type::Ref(kind, slot, inner) => {
            let (lt, is_synth) = match slot.take() {
                Some(existing) => (existing, false),
                None => (ctx.fresh(), true),
            };
            match pos {
                Pos::Input => ctx.input.push(lt.clone()),
                Pos::Output => {
                    if is_synth {
                        ctx.synth_output.push(lt.clone());
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
        Type::RawPtr(inner) => elide_type_pos(inner, pos, ctx),
        Type::Array(elem, _) => elide_type_pos(elem, pos, ctx),
        Type::Fn(args) => {
            for a in args {
                elide_type_pos(a, pos, ctx);
            }
        }
        Type::Custom(_, _lifetime_args, args) => {
            for a in args {
                elide_type_pos(a, pos, ctx);
            }
        }
        Type::Int(_) | Type::Float(_) | Type::Bool | Type::Unit | Type::Never | Type::Param(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::helpers::*;

    #[test]
    fn each_unannotated_ref_gets_fresh_lifetime() {
        let mut ty1 = mut_ref_ty(i64_ty());
        let mut ty2 = shared_ref_ty(i64_ty());
        let mut ctx = ElideCtx::new(&[]);
        elide_type_pos(&mut ty1, Pos::Input, &mut ctx);
        elide_type_pos(&mut ty2, Pos::Input, &mut ctx);
        assert_eq!(
            ctx.synthesized,
            vec![Lifetime("s0".into()), Lifetime("s1".into())]
        );
        assert!(matches!(ty1, Type::Ref(_, Some(_), _)));
        assert!(matches!(ty2, Type::Ref(_, Some(_), _)));
    }

    #[test]
    fn already_annotated_ref_is_untouched() {
        let mut ty = Type::Ref(
            RefKind::Shared,
            Some(Lifetime("a".into())),
            Box::new(i64_ty()),
        );
        let mut ctx = ElideCtx::new(&[Lifetime("a".into())]);
        elide_type_pos(&mut ty, Pos::Input, &mut ctx);
        assert!(ctx.synthesized.is_empty());
        if let Type::Ref(_, Some(lt), _) = &ty {
            assert_eq!(lt.0, "a");
        } else {
            panic!("expected annotated ref");
        }
    }

    #[test]
    fn fresh_skips_existing_names() {
        let mut ctx = ElideCtx::new(&[Lifetime("s0".into()), Lifetime("s2".into())]);
        let a = ctx.fresh();
        let b = ctx.fresh();
        assert_eq!(a.0, "s1");
        assert_eq!(b.0, "s3");
    }

    #[test]
    fn function_gets_synthesized_params_appended() {
        let mut f = Function {
            name: "f".into(),
            name_span: Span::default(),
            is_extern: false,
            lifetime_params: vec![Lifetime("a".into())],
            signature_outlives: Vec::new(),
            type_params: vec![],
            params: vec![
                Param {
                    name: "x".into(),
                    ty: mut_ref_ty(i64_ty()),
                    span: Span::default(),
                },
                Param {
                    name: "y".into(),
                    ty: Type::Ref(
                        RefKind::Shared,
                        Some(Lifetime("a".into())),
                        Box::new(i64_ty()),
                    ),
                    span: Span::default(),
                },
            ],
            body: None,
        };
        elide_function(&mut f);
        assert_eq!(
            f.lifetime_params,
            vec![Lifetime("a".into()), Lifetime("s0".into())]
        );
    }

    #[test]
    fn idempotent() {
        let mut f = Function {
            name: "f".into(),
            name_span: Span::default(),
            is_extern: false,
            lifetime_params: vec![],
            signature_outlives: Vec::new(),
            type_params: vec![],
            params: vec![Param {
                name: "x".into(),
                ty: mut_ref_ty(i64_ty()),
                span: Span::default(),
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
        let mut program = Parser::new(src.to_string()).parse().expect("parse");
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
        assert!(f
            .signature_outlives
            .contains(&(Lifetime("s0".into()), Lifetime("s2".into()))));
        assert!(f
            .signature_outlives
            .contains(&(Lifetime("s1".into()), Lifetime("s2".into()))));
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
                f.signature_outlives
                    .contains(&(Lifetime(input.into()), Lifetime("s3".into()))),
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
            f.signature_outlives.is_empty(),
            "explicit signature should have no axioms, got {:?}",
            f.signature_outlives
        );
    }
}
