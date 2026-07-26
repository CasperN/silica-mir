//! Structure-preserving transformations over MIR types.
//!
//! Type transformations override only the nodes or lifetimes they replace.
//! Every other node is rebuilt here, so source attribution, lifetime arguments,
//! and non-child structural data cannot drift between transformations.

use crate::common::Lifetime;
use crate::mir::ast::{Type, TypeKind};

/// Override selected type nodes or lifetimes while using the shared exhaustive
/// rebuild for the rest of the tree.
pub(crate) trait TypeFolder {
    /// Return a replacement for `ty`, or `None` to recursively fold its
    /// children while preserving the node's own source and structural data.
    ///
    /// A replacement is returned as-is. Implementations that need to continue
    /// folding inside it must call [`TypeFolder::fold_type`] on the replacement
    /// before returning.
    fn try_fold_type(&mut self, _ty: &Type) -> Option<Type> {
        None
    }

    /// Transform one lifetime occurrence. The default preserves it exactly.
    /// This hook applies both to reference lifetimes and to lifetime arguments
    /// on custom types.
    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        lifetime.clone()
    }

    fn fold_type(&mut self, ty: &Type) -> Type
    where
        Self: Sized,
    {
        if let Some(replacement) = self.try_fold_type(ty) {
            replacement
        } else {
            fold_type_children(self, ty)
        }
    }
}

/// Rebuild one node after recursively folding each child type and lifetime.
///
/// This match is intentionally exhaustive: adding a MIR type variant must
/// define how its children and non-child metadata survive transformations.
fn fold_type_children<F: TypeFolder>(folder: &mut F, ty: &Type) -> Type {
    let kind = match &ty.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_) => return ty.clone(),
        TypeKind::Custom(name, lifetimes, args) => TypeKind::Custom(
            name.clone(),
            lifetimes
                .iter()
                .map(|lifetime| folder.fold_lifetime(lifetime))
                .collect(),
            args.iter().map(|arg| folder.fold_type(arg)).collect(),
        ),
        TypeKind::Fn(params) => {
            TypeKind::Fn(params.iter().map(|param| folder.fold_type(param)).collect())
        }
        TypeKind::Ref(kind, lifetime, inner) => TypeKind::Ref(
            *kind,
            lifetime
                .as_ref()
                .map(|lifetime| folder.fold_lifetime(lifetime)),
            Box::new(folder.fold_type(inner)),
        ),
        TypeKind::RawPtr(inner) => TypeKind::RawPtr(Box::new(folder.fold_type(inner))),
        TypeKind::Array(element, size) => {
            TypeKind::Array(Box::new(folder.fold_type(element)), *size)
        }
    };
    Type::new(kind, ty.source)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{GeneratedKind, IntTy, RefKind, SourceInfo, Span};

    struct IdentityFolder;

    impl TypeFolder for IdentityFolder {}

    struct RenameLifetime;

    impl TypeFolder for RenameLifetime {
        fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
            Lifetime(format!("{}_folded", lifetime.0))
        }
    }

    fn source(line: u32) -> SourceInfo {
        SourceInfo::generated(
            GeneratedKind::TestHelper,
            Span {
                line,
                col: 1,
                end_line: line,
                end_col: 2,
            },
        )
    }

    #[test]
    fn identity_fold_preserves_nested_structure_and_provenance() {
        let parameter = Type::new(TypeKind::Param("T".into()), source(5));
        let pointer = Type::new(TypeKind::RawPtr(Box::new(parameter)), source(4));
        let custom = Type::new(
            TypeKind::Custom(
                "Wrapper".into(),
                vec![Lifetime("wrapper".into())],
                vec![pointer],
            ),
            source(3),
        );
        let reference = Type::new(
            TypeKind::Ref(
                RefKind::Shared,
                Some(Lifetime("reference".into())),
                Box::new(custom),
            ),
            source(2),
        );
        let function = Type::new(
            TypeKind::Fn(vec![
                reference,
                Type::new(TypeKind::Int(IntTy::I64), source(6)),
            ]),
            source(1),
        );
        let ty = Type::new(TypeKind::Array(Box::new(function), 3), source(0));

        let folded = IdentityFolder.fold_type(&ty);

        assert_eq!(folded.kind, ty.kind);
        assert_eq!(folded.source, source(0));
        let TypeKind::Array(function, 3) = folded.kind else {
            panic!("expected outer array");
        };
        assert_eq!(function.source, source(1));
        let TypeKind::Fn(params) = function.kind else {
            panic!("expected nested function type");
        };
        assert_eq!(params[0].source, source(2));
        let TypeKind::Ref(_, lifetime, custom) = &params[0].kind else {
            panic!("expected nested reference");
        };
        assert_eq!(
            lifetime.as_ref().map(|lifetime| lifetime.0.as_str()),
            Some("reference")
        );
        assert_eq!(custom.source, source(3));
        let TypeKind::Custom(_, lifetimes, args) = &custom.kind else {
            panic!("expected nested custom type");
        };
        assert_eq!(lifetimes[0].0, "wrapper");
        assert_eq!(args[0].source, source(4));
        let TypeKind::RawPtr(parameter) = &args[0].kind else {
            panic!("expected nested raw pointer");
        };
        assert_eq!(parameter.source, source(5));
        assert_eq!(params[1].source, source(6));
    }

    #[test]
    fn lifetime_hook_visits_refs_and_custom_arguments() {
        let ty = Type::new(
            TypeKind::Ref(
                RefKind::Mut,
                Some(Lifetime("reference".into())),
                Box::new(Type::new(
                    TypeKind::Custom(
                        "Wrapper".into(),
                        vec![Lifetime("argument".into())],
                        Vec::new(),
                    ),
                    source(1),
                )),
            ),
            source(0),
        );

        let folded = RenameLifetime.fold_type(&ty);

        let TypeKind::Ref(_, Some(reference), inner) = folded.kind else {
            panic!("expected reference");
        };
        assert_eq!(reference.0, "reference_folded");
        let TypeKind::Custom(_, lifetimes, _) = inner.kind else {
            panic!("expected custom pointee");
        };
        assert_eq!(lifetimes, vec![Lifetime("argument_folded".into())]);
    }
}
