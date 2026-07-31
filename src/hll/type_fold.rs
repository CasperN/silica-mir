//! Structure-preserving transformations over HLL types.
//!
//! Type transformations override only the nodes they replace. Every other
//! node is rebuilt here, so source attribution and non-child metadata such as
//! lifetimes cannot be dropped independently by each transformation.

use crate::hll::ast::{Type, TypeKind};

/// Override selected type nodes while using the shared exhaustive rebuild for
/// the rest of the tree.
pub(crate) trait TypeFolder {
    /// Return a replacement for `ty`, or `None` to recursively fold its
    /// children while preserving the node's own source and structural data.
    fn try_fold_type(&mut self, _ty: &Type) -> Option<Type> {
        None
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

/// Rebuild one node after recursively folding each child type.
///
/// This match is intentionally exhaustive: adding an HLL type variant must
/// define how its children and non-child metadata survive transformations.
fn fold_type_children<F: TypeFolder>(folder: &mut F, ty: &Type) -> Type {
    let kind = match &ty.kind {
        TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Unit
        | TypeKind::Never
        | TypeKind::Param(_)
        | TypeKind::Var(_)
        | TypeKind::IntVar(_)
        | TypeKind::FloatVar(_)
        | TypeKind::Error => return ty.clone(),
        TypeKind::Custom(inst) => TypeKind::Custom(crate::hll::ast::Instance::new(
            inst.name.clone(),
            inst.lifetime_args.clone(),
            inst.type_args
                .iter()
                .map(|arg| folder.fold_type(arg))
                .collect(),
        )),
        TypeKind::Ref(kind, lifetime, inner) => {
            TypeKind::Ref(*kind, lifetime.clone(), Box::new(folder.fold_type(inner)))
        }
        TypeKind::RawPtr(inner) => TypeKind::RawPtr(Box::new(folder.fold_type(inner))),
        TypeKind::Fn(params, ret) => TypeKind::Fn(
            params.iter().map(|param| folder.fold_type(param)).collect(),
            Box::new(folder.fold_type(ret)),
        ),
        TypeKind::Array(element, size) => {
            TypeKind::Array(Box::new(folder.fold_type(element)), *size)
        }
    };
    Type::new(kind, ty.source)
}
