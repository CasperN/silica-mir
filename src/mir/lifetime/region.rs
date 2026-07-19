//! Regions: the abstract entities that lifetime constraints range
//! over. Each ref-typed place is assigned exactly one region during
//! preliminary walk.
//!
//! Three flavors:
//! - `Named` — a source-visible name from a fn signature or decl
//!   (e.g., `'a`, `'sN` synthesized by elision). Two refs with the
//!   same named region are constrained to share liveness.
//! - `Free` — an inference variable introduced for a body-local ref
//!   without a signature-declared name. Unifies with whatever
//!   constraints demand.
//! - `Static` — outlives every other region. Reserved for future
//!   `&'static T` support.
//!
//! Regions are per-function: the same `Named("a")` in two different
//! functions denotes different regions. Region identity is scoped
//! to the `RegionCtx` that produced it.

use crate::common::Lifetime;
use crate::mir::ast::*;
use indexmap::IndexMap;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Region {
    Named(Lifetime),
    Free(u32),
    Static,
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Region::Named(lt) => write!(f, "{}", lt),
            Region::Free(n) => write!(f, "'?{}", n),
            Region::Static => write!(f, "'static"),
        }
    }
}

/// Per-function region context. Owns the fresh counter for `Free`
/// regions and the map from every ref-typed owned path to its region.
///
/// Signature refs (params) get `Named(lt)` from their declared type.
/// Body-local refs (fn locals) get `Free(N)` — they have no source
/// name, and constraints will pin them.
#[derive(Debug, Clone, Default)]
pub struct RegionCtx {
    fresh: std::cell::Cell<u32>,
    pub place_region: IndexMap<Place, Region>,
}

impl RegionCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a fresh Free region. Uses interior mutability so the
    /// per-fn `RegionCtx` can hand out fresh regions to call-site
    /// instantiation without requiring `&mut` cascade through every
    /// caller of the check walk.
    pub fn fresh(&self) -> Region {
        let n = self.fresh.get();
        self.fresh.set(n + 1);
        Region::Free(n)
    }

    /// Region for a specific `TypeKind::Ref(_, lt_opt, _)`. `Some(lt)` →
    /// Named; `None` → Free. Callers usually only see `Some` after
    /// elision has run on signature-position types.
    pub fn region_for_ref(&self, lt_opt: &Option<Lifetime>) -> Region {
        match lt_opt {
            Some(lt) => Region::Named(lt.clone()),
            None => self.fresh(),
        }
    }

    pub fn assign(&mut self, place: Place, region: Region) {
        self.place_region.insert(place, region);
    }

    pub fn get(&self, place: &Place) -> Option<&Region> {
        self.place_region.get(place)
    }
}

/// Build the per-function region map. Walks every ref-typed owned
/// path (mirroring `nll::collect_borrowers`) and assigns a region
/// based on the declared type: `Some(lt)` → Named, `None` → Free.
///
/// Recursion through generic type parameters uses the same
/// param-substitution rule as `collect_borrowers`.
pub fn build_region_ctx(func: &Function, env: &crate::mir::type_check::Env) -> RegionCtx {
    use crate::mir::helpers::var_place;
    let mut ctx = RegionCtx::new();
    let locals = func.locals_map();
    for (name, ty) in &locals {
        let mut visited = std::collections::BTreeSet::new();
        walk_regions(&var_place(name.clone()), ty, env, &mut visited, &mut ctx);
    }
    ctx
}

fn walk_regions(
    place: &Place,
    ty: &Type,
    env: &crate::mir::type_check::Env,
    visited: &mut std::collections::BTreeSet<String>,
    ctx: &mut RegionCtx,
) {
    use crate::mir::helpers::{downcast_place, field_place};
    use crate::mir::type_check::TypeDecl;
    use crate::mir::type_util::substitute_all;
    match &ty.kind {
        TypeKind::Ref(_, lt_opt, _) => {
            let region = ctx.region_for_ref(lt_opt);
            ctx.assign(place.clone(), region);
        }
        TypeKind::Custom(name, lifetime_args, args) => {
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    let fields: Vec<_> = s
                        .fields
                        .iter()
                        .map(|f| {
                            (
                                f.name.clone(),
                                substitute_all(
                                    &f.ty,
                                    &s.lifetime_params,
                                    lifetime_args,
                                    &s.type_params,
                                    args,
                                ),
                            )
                        })
                        .collect();
                    for (fname, fty) in fields {
                        let sub = field_place(place.clone(), fname);
                        walk_regions(&sub, &fty, env, visited, ctx);
                    }
                }
                Some(TypeDecl::Enum(e)) => {
                    let variants: Vec<_> = e
                        .variants
                        .iter()
                        .map(|v| {
                            (
                                v.name.clone(),
                                substitute_all(
                                    &v.ty,
                                    &e.lifetime_params,
                                    lifetime_args,
                                    &e.type_params,
                                    args,
                                ),
                            )
                        })
                        .collect();
                    for (vname, vty) in variants {
                        let sub = downcast_place(place.clone(), vname);
                        walk_regions(&sub, &vty, env, visited, ctx);
                    }
                }
                _ => {}
            }
            visited.remove(name);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Lifetime;

    #[test]
    fn named_and_free_regions_display() {
        let n = Region::Named(Lifetime("a".into()));
        let f = Region::Free(3);
        let s = Region::Static;
        assert_eq!(format!("{}", n), "'a");
        assert_eq!(format!("{}", f), "'?3");
        assert_eq!(format!("{}", s), "'static");
    }

    #[test]
    fn fresh_advances_counter() {
        let ctx = RegionCtx::new();
        assert_eq!(ctx.fresh(), Region::Free(0));
        assert_eq!(ctx.fresh(), Region::Free(1));
    }

    #[test]
    fn region_for_ref_named_when_some() {
        let ctx = RegionCtx::new();
        let r = ctx.region_for_ref(&Some(Lifetime("a".into())));
        assert_eq!(r, Region::Named(Lifetime("a".into())));
    }

    #[test]
    fn region_for_ref_free_when_none() {
        let ctx = RegionCtx::new();
        let r = ctx.region_for_ref(&None);
        assert_eq!(r, Region::Free(0));
    }

    #[test]
    fn build_region_ctx_assigns_named_to_signature_free_to_locals() {
        use crate::mir::helpers::var_place;
        use crate::mir::parser::Parser;
        use crate::mir::type_check::Env;
        // Signature refs get Named (from elision or user); body-local
        // refs get Free (elision doesn't run on locals).
        let src = "
            fn<'a> f(x: &'a i64) {
              r: &i64;
              entry:
                r = & x.*;
                return
            }
        ";
        let mut program = Parser::new(src.to_string()).parse().expect("parse");
        crate::mir::elision::elide_program(&mut program);
        let (env, _errs) = Env::build(&program);
        let func = &env.functions["f"];
        let ctx = build_region_ctx(func, &env);
        assert_eq!(
            ctx.get(&var_place("x")),
            Some(&Region::Named(Lifetime("a".into())))
        );
        assert!(matches!(ctx.get(&var_place("r")), Some(Region::Free(_))));
    }
}
