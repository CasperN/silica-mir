//! Lifetime elision desugar. Each `Type::Ref(kind, None, T)` in a
//! decl-position (fn param / return, struct field, enum variant
//! payload) receives a freshly-synthesized `'sN` name, appended to
//! the enclosing decl's `lifetime_params`. After this pass, every
//! decl-position ref carries `Some(Lifetime)` and downstream analyses
//! can assume signature-visible refs are region-named.
//!
//! Elision rule: each unannotated ref gets its OWN fresh lifetime.
//! No unification between inputs and outputs — users annotate
//! explicitly when they want two refs to share a name.
//!
//! Body-local refs (locals, tmps, borrower vars inside a function
//! body) are NOT desugared here — inference in the region checker
//! fills those in later.

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
        elide_type(&mut p.ty, &mut ctx);
    }
    f.lifetime_params.extend(ctx.synthesized);
}

fn elide_struct(s: &mut StructDecl) {
    let mut ctx = ElideCtx::new(&s.lifetime_params);
    for f in &mut s.fields {
        elide_type(&mut f.ty, &mut ctx);
    }
    s.lifetime_params.extend(ctx.synthesized);
}

fn elide_enum(e: &mut EnumDecl) {
    let mut ctx = ElideCtx::new(&e.lifetime_params);
    for v in &mut e.variants {
        elide_type(&mut v.ty, &mut ctx);
    }
    e.lifetime_params.extend(ctx.synthesized);
}

struct ElideCtx {
    counter: u32,
    used: Vec<String>,
    synthesized: Vec<Lifetime>,
}

impl ElideCtx {
    fn new(existing: &[Lifetime]) -> Self {
        Self {
            counter: 0,
            used: existing.iter().map(|l| l.0.clone()).collect(),
            synthesized: Vec::new(),
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

fn elide_type(ty: &mut Type, ctx: &mut ElideCtx) {
    match ty {
        Type::Ref(_, slot @ None, inner) => {
            *slot = Some(ctx.fresh());
            elide_type(inner, ctx);
        }
        Type::Ref(_, Some(_), inner) => elide_type(inner, ctx),
        Type::RawPtr(inner) => elide_type(inner, ctx),
        Type::Array(elem, _) => elide_type(elem, ctx),
        Type::Fn(args) => {
            for a in args {
                elide_type(a, ctx);
            }
        }
        Type::Custom(_, _lifetime_args, args) => {
            for a in args {
                elide_type(a, ctx);
            }
        }
        Type::Int(_)
        | Type::Float(_)
        | Type::Bool
        | Type::Unit
        | Type::Never
        | Type::Param(_) => {}
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
        elide_type(&mut ty1, &mut ctx);
        elide_type(&mut ty2, &mut ctx);
        assert_eq!(ctx.synthesized, vec![Lifetime("s0".into()), Lifetime("s1".into())]);
        assert!(matches!(ty1, Type::Ref(_, Some(_), _)));
        assert!(matches!(ty2, Type::Ref(_, Some(_), _)));
    }

    #[test]
    fn already_annotated_ref_is_untouched() {
        let mut ty = Type::Ref(RefKind::Shared, Some(Lifetime("a".into())), Box::new(i64_ty()));
        let mut ctx = ElideCtx::new(&[Lifetime("a".into())]);
        elide_type(&mut ty, &mut ctx);
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
            type_params: vec![],
            params: vec![
                Param { name: "x".into(), ty: mut_ref_ty(i64_ty()), span: Span::default() },
                Param {
                    name: "y".into(),
                    ty: Type::Ref(RefKind::Shared, Some(Lifetime("a".into())), Box::new(i64_ty())),
                    span: Span::default(),
                },
            ],
            body: None,
        };
        elide_function(&mut f);
        assert_eq!(f.lifetime_params, vec![Lifetime("a".into()), Lifetime("s0".into())]);
    }

    #[test]
    fn idempotent() {
        let mut f = Function {
            name: "f".into(),
            name_span: Span::default(),
            is_extern: false,
            lifetime_params: vec![],
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
}
