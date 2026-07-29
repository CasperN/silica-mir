//! Regions: the abstract entities that lifetime constraints range
//! over. Each ref-typed place is assigned exactly one region during
//! preliminary walk.
//!
//! Four flavors:
//! - `Named` — a source-visible name from a fn signature or decl
//!   (e.g., `'a`, `'sN` synthesized by elision). Two refs with the
//!   same named region are constrained to share liveness.
//! - `Free` — an inference variable introduced for a body-local ref
//!   without a signature-declared name. A `Free` region flowing into a
//!   caller-visible slot represents a possible escaping local borrow.
//! - `Inference` — an existential variable introduced while instantiating a
//!   callee lifetime parameter at one call site. These are eliminated from
//!   the call constraint graph before failures are classified; unlike
//!   `Free`, they never represent storage owned by the caller body.
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
    Inference(u32),
    Static,
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Region::Named(lt) => write!(f, "{}", lt),
            Region::Free(n) => write!(f, "'?{}", n),
            Region::Inference(n) => write!(f, "'?call{}", n),
            Region::Static => write!(f, "'static"),
        }
    }
}

/// Per-function region context. Owns the counter shared by fresh body-local
/// and call-instantiation regions, the map from every ref-typed owned path
/// to its region, and one storage region per root local.
///
/// Signature refs (params) get `Named(lt)` from their declared type in
/// `place_region`. Body-local refs (fn locals) get `Free(N)`.
///
/// `local_storage` stores an independent `Free(N)` per root local — the
/// region of that local's stack slot. It answers "what region does
/// `&x`, `&x.f`, or `&x[k]` inherit as its outer region?" for any
/// non-reborrow borrow of `x`. Every local (ref-typed or not) needs a
/// storage region, since even a body-local scalar can be borrowed and
/// the resulting ref must not escape.
#[derive(Debug, Clone, Default)]
pub struct RegionCtx {
    fresh: std::cell::Cell<u32>,
    pub place_region: IndexMap<Place, Region>,
    local_storage: IndexMap<String, Region>,
}

impl RegionCtx {
    pub fn new() -> Self {
        Self::default()
    }

    /// Allocate a fresh body-local region. Interior mutability lets later
    /// call-site checking allocate separate `Inference` regions from the same
    /// per-function namespace without an `&mut` cascade through the check walk.
    pub fn fresh(&self) -> Region {
        let n = self.fresh.get();
        self.fresh.set(n + 1);
        Region::Free(n)
    }

    /// Allocate an existential region for a callee lifetime parameter at one
    /// call site. It shares the counter with body-local `Free` regions only to
    /// keep internal debug names distinct; the enum variant carries the
    /// semantic distinction used by constraint normalization.
    pub fn fresh_inference(&self) -> Region {
        let n = self.fresh.get();
        self.fresh.set(n + 1);
        Region::Inference(n)
    }

    /// Region for a specific `TypeKind::Ref(_, lt_opt, _)`. `Some(lt)` →
    /// Named; `None` → Free. Callers usually only see `Some` after
    /// elision has run on signature-position types. The reserved name
    /// `'static` maps to `Region::Static` — the top of the outlives
    /// order — so `&'static T` participates in constraint solving as
    /// the longest-lived region.
    pub fn region_for_ref(&self, lt_opt: &Option<Lifetime>) -> Region {
        match lt_opt {
            Some(lt) if lt.0 == "static" => Region::Static,
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

    /// Region of `place`, treating it as a reference-typed place. First
    /// tries the owned-path map; falls back to reading the `Named`
    /// lifetime slot from `place`'s computed type. The fallback covers
    /// cases like `$return.*` — a `Deref` that isn't an owned path and
    /// so has no entry in `place_region`.
    pub fn region_of_place(
        &self,
        place: &Place,
        locals: &IndexMap<String, Type>,
        env: &crate::mir::type_check::Env,
    ) -> Option<Region> {
        if let Some(owned) = as_owned_path(place) {
            if let Some(r) = self.get(&owned) {
                return Some(r.clone());
            }
        }
        let ty = crate::mir::type_util::place_type(locals, env, place)?;
        if let TypeKind::Ref(_, Some(lt), _) = ty.kind {
            Some(if lt.0 == "static" {
                Region::Static
            } else {
                Region::Named(lt)
            })
        } else {
            None
        }
    }

    /// Storage region for a root local. Populated once per local at
    /// [`build_region_ctx`] time so every borrow of `x`, `x.f`, or
    /// `x[k]` resolves to the same body-local region.
    pub fn storage_region_of_local(&self, name: &str) -> Option<&Region> {
        self.local_storage.get(name)
    }

    fn assign_storage(&mut self, name: String, region: Region) {
        self.local_storage.insert(name, region);
    }

    /// The region that a borrow rvalue `&place` inherits as its outer
    /// region — used to emit the source side of the `source outlives
    /// target` constraint when the target is a ref-typed slot.
    ///
    /// Two shapes reach this helper. A reborrow (`&place.*` or its
    /// nested projection) carries the deref'd reference's own region,
    /// resolved via [`RegionCtx::region_of_place`]. A borrow of a
    /// body-owned place resolves to that place's root local's storage
    /// region — every local has one, so this is total for well-typed
    /// programs.
    pub fn region_of_borrow_source(
        &self,
        place: &Place,
        locals: &IndexMap<String, Type>,
        env: &crate::mir::type_check::Env,
    ) -> Option<Region> {
        let mut cur = place;
        loop {
            match cur {
                Place::Var(name) => return self.storage_region_of_local(name).cloned(),
                Place::Deref(inner) => return self.region_of_place(inner, locals, env),
                Place::Field(inner, _) | Place::Downcast(inner, _) | Place::Index(inner, _) => {
                    cur = inner;
                }
            }
        }
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
        // Every local has a body-local storage region. Borrows of the
        // local's own stack slot (`&x`, `&x.f`, `&x[k]`) resolve here.
        let storage = ctx.fresh();
        ctx.assign_storage(name.clone(), storage);
        let mut visited = std::collections::BTreeSet::new();
        // Cache regions by index-erased path so array slots
        // arr[0]..arr[N-1] that all reach the same ref layer share a
        // single Free — matching the type's single elided lifetime.
        let mut position_regions: IndexMap<Vec<PathStep>, Region> = IndexMap::new();
        walk_ref_places(
            &var_place(name.clone()),
            ty,
            env,
            &mut visited,
            &mut |place, lt_opt| {
                let key = index_erased_key(place);
                let region = position_regions
                    .entry(key)
                    .or_insert_with(|| ctx.region_for_ref(lt_opt))
                    .clone();
                ctx.assign(place.clone(), region);
            },
        );
    }
    ctx
}

/// Path from `place`'s root Var, with all array indices erased. Two
/// places sharing this key hit the same lifetime position in the type
/// (differing only in which array slot they occupy) and therefore
/// share a region.
fn index_erased_key(place: &Place) -> Vec<PathStep> {
    let (_, mut steps) = as_owned_path(place)
        .and_then(|owned| extract_path(&owned))
        .expect("walk_ref_places yields owned paths");
    for step in &mut steps {
        if let PathStep::Index(_) = step {
            *step = PathStep::Index(None);
        }
    }
    steps
}

/// Walk `ty`'s place structure starting at `place`, invoking `on_ref` for
/// every owned-path descendant of ref type. Recurses through struct fields,
/// enum variants, and array slots (substituting the parent's generic
/// arguments for structs and enums), and stops at Ref boundaries — we
/// don't traverse a reference's pointee.
///
/// `visited` is a defensive cycle guard for self-referential Custom types;
/// by-value type recursion is banned upstream by `layout::check_program`,
/// so this can only fire if someone bypasses the standard pipeline.
///
/// Array descent enumerates each constant-index slot as its own owned
/// path. For a large `[T; N]`, this materializes N region entries; the
/// cost is accepted so slot lookups stay uniform with struct-field and
/// enum-variant lookups.
pub(super) fn walk_ref_places(
    place: &Place,
    ty: &Type,
    env: &crate::mir::type_check::Env,
    visited: &mut std::collections::BTreeSet<String>,
    on_ref: &mut dyn FnMut(&Place, &Option<Lifetime>),
) {
    use crate::mir::helpers::{downcast_place, field_place};
    use crate::mir::type_check::TypeDecl;
    match &ty.kind {
        TypeKind::Ref(_, lt_opt, _) => on_ref(place, lt_opt),
        TypeKind::Custom(Instance { name, lifetime_args, type_args: args }) => {
            if !visited.insert(name.clone()) {
                return;
            }
            match env.types.get(name) {
                Some(TypeDecl::Struct(s)) => {
                    let fields: Option<Vec<_>> = s
                        .fields
                        .iter()
                        .map(|f| {
                            s.meta
                                .try_substitute(&f.ty, lifetime_args, args)
                                .map(|ty| (f.name.clone(), ty))
                        })
                        .collect();
                    if let Some(fields) = fields {
                        for (fname, fty) in fields {
                            let sub = field_place(place.clone(), fname);
                            walk_ref_places(&sub, &fty, env, visited, on_ref);
                        }
                    }
                    // Arity-mismatched Instance: skip the walk. typecheck
                    // has reported the mismatch; further recursion here
                    // would consume nonsensical types.
                }
                Some(TypeDecl::Enum(e)) => {
                    let variants: Option<Vec<_>> = e
                        .variants
                        .iter()
                        .map(|v| {
                            e.meta
                                .try_substitute(&v.ty, lifetime_args, args)
                                .map(|ty| (v.name.clone(), ty))
                        })
                        .collect();
                    if let Some(variants) = variants {
                        for (vname, vty) in variants {
                            let sub = downcast_place(place.clone(), vname);
                            walk_ref_places(&sub, &vty, env, visited, on_ref);
                        }
                    }
                }
                // `None` here means the Custom type isn't in the env —
                // a type-check error already reported. Nothing to walk.
                None => {}
            }
            visited.remove(name);
        }
        TypeKind::Array(elem, n) => {
            use crate::mir::helpers::index_place;
            for k in 0..*n {
                let sub = index_place(
                    place.clone(),
                    Operand::Const(ConstVal::Int { bits: k, ty: IntTy::I64 }),
                );
                walk_ref_places(&sub, elem, env, visited, on_ref);
            }
        }
        // Scalars carry no refs. `TypeKind::Fn` erases its ref-carrying
        // parameter types at the type level (fn signatures aren't walked
        // here — they're the callee's problem). `TypeKind::Param` is
        // opaque without substitution. `TypeKind::RawPtr` deliberately
        // has no lifetime bound.
        TypeKind::Unit
        | TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Param(_)
        | TypeKind::Fn(_)
        | TypeKind::RawPtr(_) => {}
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
        let i = Region::Inference(4);
        let s = Region::Static;
        assert_eq!(format!("{}", n), "'a");
        assert_eq!(format!("{}", f), "'?3");
        assert_eq!(format!("{}", i), "'?call4");
        assert_eq!(format!("{}", s), "'static");
    }

    #[test]
    fn fresh_advances_counter() {
        let ctx = RegionCtx::new();
        assert_eq!(ctx.fresh(), Region::Free(0));
        assert_eq!(ctx.fresh_inference(), Region::Inference(1));
        assert_eq!(ctx.fresh(), Region::Free(2));
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
        let mut program = Parser::parse_or_panic(src);
        crate::mir::desugar::lifetime::desugar_program(&mut program);
        let (env, _errs) = Env::build(&program);
        let func = program.find_fn("f").expect("fn f");
        let ctx = build_region_ctx(func, &env);
        assert_eq!(
            ctx.get(&var_place("x")),
            Some(&Region::Named(Lifetime("a".into())))
        );
        assert!(matches!(ctx.get(&var_place("r")), Some(Region::Free(_))));
    }
}
