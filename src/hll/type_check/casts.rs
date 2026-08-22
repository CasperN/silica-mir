use crate::hll::ast::{Type, TypeKind};

/// Return true iff `expr as to` is a supported numeric or pointer cast.
pub fn is_cast_supported(from: &Type, to: &Type) -> bool {
    if from == to {
        return true;
    }
    if matches!(&from.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
        && matches!(&to.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
    {
        return true;
    }
    matches!(
        (&from.kind, &to.kind),
        (TypeKind::Int(_), TypeKind::Int(_))
            | (TypeKind::Float(_), TypeKind::Float(_))
            | (TypeKind::Int(_), TypeKind::Float(_))
            | (TypeKind::Float(_), TypeKind::Int(_))
            | (TypeKind::Bool, TypeKind::Int(_))
    )
}

/// Return the intrinsic name that implements `expr as to`, or `None`
/// if `from == to` (no cast needed).
pub fn cast_intrinsic_name(from: &Type, to: &Type) -> Option<String> {
    if from == to {
        return None;
    }
    if matches!(&from.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
        && matches!(&to.kind, TypeKind::Ref(_, _, _) | TypeKind::RawPtr(_))
    {
        return None;
    }
    let ty_name = |ty: &Type| match &ty.kind {
        TypeKind::Int(k) => k.name().to_string(),
        TypeKind::Float(k) => k.name().to_string(),
        TypeKind::Bool => "bool".to_string(),
        _ => panic!("cast_intrinsic_name: unsupported type {:?}", ty),
    };
    Some(format!("${}_to_{}", ty_name(from), ty_name(to)))
}
