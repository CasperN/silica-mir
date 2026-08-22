use std::collections::{BTreeMap, HashMap, HashSet};

use crate::common::{Lifetime, RefKind, SourceInfo};
use crate::diagnostics::Diagnostic;
use crate::hll::ast::{Instance, Type, TypeKind};
use crate::hll::helpers::*;
use crate::hll::type_check::mod_types::{source_diagnostic, HllTypeCheckCode};
use crate::hll::type_fold::TypeFolder;

#[derive(Debug, Clone, PartialEq)]
pub enum UnifyError {
    Mismatch { expected: Type, found: Type },
    ExpectedInteger { found: Type },
    ExpectedFloat { found: Type },
    Infinite,
    ArityMismatch,
}

impl UnifyError {
    pub fn to_diag(self, source: SourceInfo) -> Diagnostic {
        match self {
            UnifyError::Mismatch { expected, found } => {
                let mut diag = source_diagnostic(
                    HllTypeCheckCode::TypeMismatch,
                    source,
                    format!("type mismatch: expected {}, found {}", expected, found),
                );
                if let Some(hint) = mismatch_hint(&expected, &found) {
                    diag = diag.with_hint(hint);
                }
                diag
            }
            UnifyError::ExpectedInteger { found } => {
                let mut diag = source_diagnostic(
                    HllTypeCheckCode::TypeMismatch,
                    source,
                    format!("type mismatch: expected integer type, found {}", found),
                );
                if matches!(found.kind, TypeKind::Float(_)) {
                    diag = diag.with_hint("consider casting with 'as i64'");
                }
                diag
            }
            UnifyError::ExpectedFloat { found } => {
                let mut diag = source_diagnostic(
                    HllTypeCheckCode::TypeMismatch,
                    source,
                    format!("type mismatch: expected float type, found {}", found),
                );
                if matches!(found.kind, TypeKind::Int(_)) {
                    diag = diag.with_hint("consider casting with 'as f64'");
                }
                diag
            }
            UnifyError::Infinite => source_diagnostic(
                HllTypeCheckCode::InfiniteType,
                source,
                "infinite type detected during unification",
            ),
            UnifyError::ArityMismatch => source_diagnostic(
                HllTypeCheckCode::ArityMismatch,
                source,
                "function arity mismatch",
            ),
        }
    }
}

/// Produce actionable hints when unifying `expected` and `found` types fails.
pub fn mismatch_hint(expected: &Type, found: &Type) -> Option<String> {
    match (&expected.kind, &found.kind) {
        (TypeKind::Ref(kind, _, pointee), _) if **pointee == *found => {
            let hint = match kind {
                RefKind::Shared => "consider borrowing with '&'",
                RefKind::Mut => "consider mutably borrowing with '&mut'",
                RefKind::Out => "consider borrowing with '&out'",
                RefKind::Drop => "consider borrowing with '&drop'",
                RefKind::Uninit => "consider borrowing with '&uninit'",
            };
            Some(hint.to_string())
        }
        (_, TypeKind::Ref(_, _, inner)) if **inner == *expected => {
            Some("consider dereferencing with '.*'".to_string())
        }
        (_, TypeKind::RawPtr(inner)) if **inner == *expected => {
            Some("consider dereferencing with '.*'".to_string())
        }
        (TypeKind::Int(_), TypeKind::Int(_))
        | (TypeKind::Float(_), TypeKind::Float(_))
        | (TypeKind::Float(_), TypeKind::Int(_))
        | (TypeKind::Int(_), TypeKind::Float(_)) => {
            Some(format!("consider casting with 'as {}'", expected))
        }
        (TypeKind::Bool, TypeKind::Int(_)) => {
            Some("consider comparing with '!= 0'".to_string())
        }
        (TypeKind::Int(_), TypeKind::Bool) => {
            Some(format!("consider casting with 'as {}'", expected))
        }
        (TypeKind::Tuple(types), _)
            if types.is_empty() && !matches!(&found.kind, TypeKind::Tuple(t) if t.is_empty()) =>
        {
            Some("consider adding a semicolon ';' to discard the value".to_string())
        }
        _ => None,
    }
}

pub struct Subst {
    pub(crate) map: HashMap<usize, Type>,
    pub(crate) next_id: usize,
    pub(crate) lifetime_map: BTreeMap<Lifetime, Lifetime>,
    pub(crate) lifetime_variables: HashSet<Lifetime>,
}

#[derive(Clone, Copy)]
pub(crate) enum ResolveMode {
    PreserveUnresolved,
    DefaultUnresolved,
}

#[derive(Clone, Copy)]
pub(crate) enum SolverVariable {
    General(usize),
    Integer(usize),
    Float(usize),
}

impl SolverVariable {
    fn id(self) -> usize {
        match self {
            Self::General(id) | Self::Integer(id) | Self::Float(id) => id,
        }
    }
}

pub(crate) struct ResolveFolder<'a> {
    pub(crate) subst: &'a Subst,
    pub(crate) mode: ResolveMode,
}

impl TypeFolder for ResolveFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        let variable = match &ty.kind {
            TypeKind::Var(id) => SolverVariable::General(*id),
            TypeKind::IntVar(id) => SolverVariable::Integer(*id),
            TypeKind::FloatVar(id) => SolverVariable::Float(*id),
            _ => return None,
        };

        if let Some(resolved) = self.subst.map.get(&variable.id()).cloned() {
            return Some(self.fold_type(&resolved));
        }

        match (self.mode, variable) {
            (
                ResolveMode::PreserveUnresolved,
                SolverVariable::General(_) | SolverVariable::Integer(_) | SolverVariable::Float(_),
            ) => None,
            (ResolveMode::DefaultUnresolved, SolverVariable::General(_)) => Some(error_ty()),
            (ResolveMode::DefaultUnresolved, SolverVariable::Integer(_)) => Some(i64_ty()),
            (ResolveMode::DefaultUnresolved, SolverVariable::Float(_)) => Some(f64_ty()),
        }
    }

    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        self.subst.resolve_lifetime(lifetime)
    }
}

impl Subst {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            next_id: 0,
            lifetime_map: BTreeMap::new(),
            lifetime_variables: HashSet::new(),
        }
    }

    pub(crate) fn register_lifetime_variable(&mut self, lifetime: Lifetime) {
        self.lifetime_variables.insert(lifetime);
    }

    pub(crate) fn resolve_lifetime(&self, lifetime: &Lifetime) -> Lifetime {
        let mut resolved = lifetime.clone();
        while let Some(next) = self.lifetime_map.get(&resolved) {
            if next == &resolved {
                break;
            }
            resolved = next.clone();
        }
        resolved
    }

    pub(crate) fn unify_lifetimes(&mut self, left: &Lifetime, right: &Lifetime) {
        let left = self.resolve_lifetime(left);
        let right = self.resolve_lifetime(right);
        if left == right {
            return;
        }
        if self.lifetime_variables.contains(&left) {
            self.lifetime_map.insert(left, right);
        } else if self.lifetime_variables.contains(&right) {
            self.lifetime_map.insert(right, left);
        }
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        var_ty(id)
    }

    pub fn fresh_int_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        int_var_ty(id)
    }

    pub fn fresh_float_var(&mut self) -> Type {
        let id = self.next_id;
        self.next_id += 1;
        float_var_ty(id)
    }

    pub fn resolve(&self, ty: &Type) -> Type {
        ResolveFolder {
            subst: self,
            mode: ResolveMode::PreserveUnresolved,
        }
        .fold_type(ty)
    }

    pub fn resolve_default(&self, ty: &Type) -> Type {
        ResolveFolder {
            subst: self,
            mode: ResolveMode::DefaultUnresolved,
        }
        .fold_type(ty)
    }

    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), UnifyError> {
        let r1 = self.resolve(t1);
        let r2 = self.resolve(t2);
        match (&r1.kind, &r2.kind) {
            (TypeKind::Error, _) | (_, TypeKind::Error) => Ok(()),
            (TypeKind::Var(id1), TypeKind::Var(id2)) if id1 == id2 => Ok(()),
            (TypeKind::IntVar(id1), TypeKind::IntVar(id2)) if id1 == id2 => Ok(()),
            (TypeKind::FloatVar(id1), TypeKind::FloatVar(id2)) if id1 == id2 => Ok(()),
            (TypeKind::Var(id), _) => {
                if self.occurs_in(*id, &r2) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, r2);
                Ok(())
            }
            (_, TypeKind::Var(id)) => {
                if self.occurs_in(*id, &r1) {
                    return Err(UnifyError::Infinite);
                }
                self.map.insert(*id, r1);
                Ok(())
            }
            (TypeKind::Never, _) | (_, TypeKind::Never) => Ok(()),
            (TypeKind::IntVar(id), other) => match other {
                TypeKind::IntVar(_) | TypeKind::Int(_) => {
                    self.map.insert(*id, r2);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedInteger { found: r2.clone() }),
            },
            (other, TypeKind::IntVar(id)) => match other {
                TypeKind::IntVar(_) | TypeKind::Int(_) => {
                    self.map.insert(*id, r1);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::Mismatch {
                    expected: r1.clone(),
                    found: int_ty(crate::mir::ast::IntTy::I64),
                }),
            },
            (TypeKind::FloatVar(id), other) => match other {
                TypeKind::FloatVar(_) | TypeKind::Float(_) => {
                    self.map.insert(*id, r2);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::ExpectedFloat { found: r2.clone() }),
            },
            (other, TypeKind::FloatVar(id)) => match other {
                TypeKind::FloatVar(_) | TypeKind::Float(_) => {
                    self.map.insert(*id, r1);
                    Ok(())
                }
                TypeKind::Error => Ok(()),
                _ => Err(UnifyError::Mismatch {
                    expected: r1.clone(),
                    found: float_ty(crate::mir::ast::FloatTy::F64),
                }),
            },
            (TypeKind::Int(i1), TypeKind::Int(i2)) if i1 == i2 => Ok(()),
            (TypeKind::Float(f1), TypeKind::Float(f2)) if f1 == f2 => Ok(()),
            (TypeKind::Bool, TypeKind::Bool) => Ok(()),
            (TypeKind::Tuple(t1), TypeKind::Tuple(t2)) if t1.len() == t2.len() => {
                let t1 = t1.clone();
                let t2 = t2.clone();
                for (x, y) in t1.iter().zip(t2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (
                TypeKind::Custom(Instance {
                    name: n1,
                    lifetime_args: l1,
                    type_args: a1,
                }),
                TypeKind::Custom(Instance {
                    name: n2,
                    lifetime_args: l2,
                    type_args: a2,
                }),
            ) if n1 == n2 && l1.len() == l2.len() && a1.len() == a2.len() => {
                let l1 = l1.clone();
                let l2 = l2.clone();
                let a1 = a1.clone();
                let a2 = a2.clone();
                for (left, right) in l1.iter().zip(l2.iter()) {
                    self.unify_lifetimes(left, right);
                }
                for (x, y) in a1.iter().zip(a2.iter()) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (TypeKind::Param(p1), TypeKind::Param(p2)) if p1 == p2 => Ok(()),
            (TypeKind::Ref(k1, l1, inner1), TypeKind::Ref(k2, l2, inner2)) if k1 == k2 => {
                if let (Some(left), Some(right)) = (l1, l2) {
                    self.unify_lifetimes(left, right);
                }
                self.unify(inner1, inner2)
            }
            (TypeKind::RawPtr(inner1), TypeKind::RawPtr(inner2)) => self.unify(inner1, inner2),
            (TypeKind::Array(inner1, size1), TypeKind::Array(inner2, size2)) if size1 == size2 => {
                self.unify(inner1, inner2)
            }
            (
                TypeKind::Fn {
                    abi: abi1,
                    params: p1,
                    ret: ret1,
                },
                TypeKind::Fn {
                    abi: abi2,
                    params: p2,
                    ret: ret2,
                },
            ) => {
                if abi1 != abi2 {
                    return Err(UnifyError::Mismatch {
                        expected: r1.clone(),
                        found: r2.clone(),
                    });
                }
                if p1.len() != p2.len() {
                    return Err(UnifyError::ArityMismatch);
                }
                for (a1, a2) in p1.iter().zip(p2.iter()) {
                    self.unify(a1, a2)?;
                }
                self.unify(ret1, ret2)
            }
            (_, _) => Err(UnifyError::Mismatch {
                expected: r1,
                found: r2,
            }),
        }
    }

    pub fn can_unify(&self, t1: &Type, t2: &Type) -> bool {
        let mut probe = Self {
            map: self.map.clone(),
            next_id: self.next_id,
            lifetime_map: self.lifetime_map.clone(),
            lifetime_variables: self.lifetime_variables.clone(),
        };
        probe.unify(t1, t2).is_ok()
    }

    pub fn occurs_in(&self, id: usize, ty: &Type) -> bool {
        match &ty.kind {
            TypeKind::Var(v) | TypeKind::IntVar(v) | TypeKind::FloatVar(v) => {
                if *v == id {
                    true
                } else if let Some(resolved) = self.map.get(v) {
                    self.occurs_in(id, resolved)
                } else {
                    false
                }
            }
            TypeKind::Ref(_, _, inner) => self.occurs_in(id, inner),
            TypeKind::RawPtr(inner) => self.occurs_in(id, inner),
            TypeKind::Array(inner, _) => self.occurs_in(id, inner),
            TypeKind::Tuple(types) => types.iter().any(|t| self.occurs_in(id, t)),
            TypeKind::Fn { params, ret, .. } => {
                params.iter().any(|p| self.occurs_in(id, p)) || self.occurs_in(id, ret)
            }
            TypeKind::Custom(Instance {
                type_args: args, ..
            }) => args.iter().any(|a| self.occurs_in(id, a)),
            _ => false,
        }
    }
}

pub fn collect_unresolved_vars(ty: &Type, subst: &Subst, vars: &mut HashSet<usize>) {
    match &ty.kind {
        TypeKind::Var(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            } else {
                vars.insert(*id);
            }
        }
        TypeKind::IntVar(id) | TypeKind::FloatVar(id) => {
            if let Some(resolved) = subst.map.get(id) {
                collect_unresolved_vars(resolved, subst, vars);
            }
        }
        TypeKind::Ref(_, _, inner) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::RawPtr(inner) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::Array(inner, _) => collect_unresolved_vars(inner, subst, vars),
        TypeKind::Fn { params, ret, .. } => {
            for p in params {
                collect_unresolved_vars(p, subst, vars);
            }
            collect_unresolved_vars(ret, subst, vars);
        }
        TypeKind::Custom(Instance {
            type_args: args, ..
        }) => {
            for a in args {
                collect_unresolved_vars(a, subst, vars);
            }
        }
        _ => {}
    }
}
