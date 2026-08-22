use std::collections::{BTreeMap, HashMap, HashSet};

use indexmap::IndexMap;

use crate::common::{Abi, Lifetime, LifetimeParam, Markers, RefKind, SourceInfo};
use crate::diagnostics::Diagnostics;
use crate::hll::ast::*;
use crate::hll::type_check::mod_types::{source_diagnostic, HllTypeCheckCode};
use crate::hll::type_check::subst::Subst;
use crate::hll::type_check::traits;
use crate::hll::type_fold::TypeFolder;

/// Build a `name → bounds` map from a decl's type parameters. Used
/// when computing a type's substructural class or validating uses
/// against bounds — both need the complete bounds for each name.
pub(crate) fn type_params_scope(params: &[TypeParam]) -> HashMap<String, Bounds> {
    params
        .iter()
        .map(|p| (p.name.clone(), p.bounds.clone()))
        .collect()
}

/// Substitute type-parameter references in `ty` using `mapping`.
pub(crate) fn substitute(ty: &Type, mapping: &HashMap<String, Type>) -> Type {
    let lifetime_mapping = BTreeMap::new();
    SubstituteFolder {
        type_mapping: mapping,
        lifetime_mapping: &lifetime_mapping,
    }
    .fold_type(ty)
}

pub(crate) fn substitute_all(
    ty: &Type,
    type_mapping: &HashMap<String, Type>,
    lifetime_mapping: &BTreeMap<Lifetime, Lifetime>,
) -> Type {
    SubstituteFolder {
        type_mapping,
        lifetime_mapping,
    }
    .fold_type(ty)
}

pub(crate) struct SubstituteFolder<'a> {
    pub(crate) type_mapping: &'a HashMap<String, Type>,
    pub(crate) lifetime_mapping: &'a BTreeMap<Lifetime, Lifetime>,
}

impl TypeFolder for SubstituteFolder<'_> {
    fn try_fold_type(&mut self, ty: &Type) -> Option<Type> {
        match &ty.kind {
            TypeKind::Param(name) => self.type_mapping.get(name).cloned(),
            _ => None,
        }
    }

    fn fold_lifetime(&mut self, lifetime: &Lifetime) -> Lifetime {
        self.lifetime_mapping
            .get(lifetime)
            .cloned()
            .unwrap_or_else(|| lifetime.clone())
    }
}

pub(crate) fn substitute_bound(
    bound: &TraitBound,
    type_mapping: &HashMap<String, Type>,
    lifetime_mapping: &BTreeMap<Lifetime, Lifetime>,
) -> Instance {
    Instance::new(
        bound.trait_path.name.clone(),
        bound
            .trait_path
            .lifetime_args
            .iter()
            .map(|lifetime| {
                lifetime_mapping
                    .get(lifetime)
                    .cloned()
                    .unwrap_or_else(|| lifetime.clone())
            })
            .collect(),
        bound
            .trait_path
            .type_args
            .iter()
            .map(|argument| substitute_all(argument, type_mapping, lifetime_mapping))
            .collect(),
    )
}

/// Build a `param_name -> arg_type` substitution map, checking that
/// the number of args matches the number of declared type parameters.
pub(crate) fn build_subst_map(
    decl_name: &str,
    type_params: &[TypeParam],
    args: &[Type],
    source: SourceInfo,
    d: &mut Diagnostics,
) -> Option<HashMap<String, Type>> {
    if args.len() != type_params.len() {
        d.push_error(source_diagnostic(
            HllTypeCheckCode::ArityMismatch,
            source,
            format!(
                "'{}' takes {} type argument(s), found {}",
                decl_name,
                type_params.len(),
                args.len()
            ),
        ));
        return None;
    }
    let mut mapping = HashMap::new();
    for (tp, arg) in type_params.iter().zip(args.iter()) {
        mapping.insert(tp.name.clone(), arg.clone());
    }
    Some(mapping)
}

/// Zip a decl's lifetime parameters with the concrete lifetimes at a use site.
pub(crate) fn build_lifetime_mapping(
    lifetime_params: &[LifetimeParam],
    lifetime_args: &[Lifetime],
) -> Option<BTreeMap<Lifetime, Lifetime>> {
    if lifetime_params.len() != lifetime_args.len() {
        return None;
    }
    Some(
        lifetime_params
            .iter()
            .map(|parameter| parameter.lifetime.clone())
            .zip(lifetime_args.iter().cloned())
            .collect(),
    )
}

pub(crate) fn array_len(len: usize) -> u64 {
    u64::try_from(len).expect("host collection length exceeds Silica's u64 array length")
}

#[derive(Default)]
pub struct TypeEnv {
    pub(crate) variables: Vec<HashMap<String, Type>>,
    pub(crate) structs: HashMap<String, StructDecl>,
    pub(crate) enums: HashMap<String, EnumDecl>,
    pub(crate) traits: HashMap<String, TraitDecl>,
    pub(crate) functions: HashMap<String, FnDecl>,
    pub(crate) impls: Vec<ImplBlock>,
    pub(crate) closures: HashMap<String, ClosureInfo>,
    pub(crate) current_ret_ty: Option<Type>,
    pub(crate) current_type_params: HashMap<String, Bounds>,
    pub(crate) current_generic_params: Vec<TypeParam>,
    pub(crate) current_lifetimes: HashSet<Lifetime>,
    pub(crate) current_function: Option<String>,
    pub(crate) in_unsafe: bool,
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            variables: vec![HashMap::new()],
            structs: HashMap::new(),
            enums: HashMap::new(),
            traits: HashMap::new(),
            functions: HashMap::new(),
            impls: Vec::new(),
            closures: HashMap::new(),
            current_ret_ty: None,
            current_type_params: HashMap::new(),
            current_generic_params: Vec::new(),
            current_lifetimes: HashSet::new(),
            current_function: None,
            in_unsafe: false,
        }
    }

    pub fn push_scope(&mut self) {
        self.variables.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.variables.pop();
    }

    pub fn insert_var(&mut self, name: String, ty: Type) {
        if let Some(scope) = self.variables.last_mut() {
            scope.insert(name, ty);
        }
    }

    pub fn lookup_var(&self, name: &str) -> Option<Type> {
        for scope in self.variables.iter().rev() {
            if let Some(ty) = scope.get(name) {
                return Some(ty.clone());
            }
        }
        None
    }

    pub(crate) fn lookup_struct(&self, name: &str) -> Option<&StructDecl> {
        self.structs.get(name)
    }

    pub(crate) fn field_type(&self, ty: &Type, field_name: &str) -> Option<Type> {
        let TypeKind::Custom(Instance {
            name,
            type_args,
            lifetime_args,
        }) = &ty.kind
        else {
            return None;
        };
        let s = self.lookup_struct(name)?;
        let f = s.fields.iter().find(|f| f.name == field_name)?;
        let type_mapping: HashMap<String, Type> = s
            .type_params
            .iter()
            .zip(type_args)
            .map(|(p, a)| (p.name.clone(), a.clone()))
            .collect();
        let lifetime_mapping: BTreeMap<Lifetime, Lifetime> = s
            .lifetime_params
            .iter()
            .zip(lifetime_args)
            .map(|(p, a)| (p.lifetime.clone(), a.clone()))
            .collect();
        Some(substitute_all(&f.ty, &type_mapping, &lifetime_mapping))
    }

    pub(crate) fn type_satisfies_trait(&self, ty: &Type, trait_path: &Instance) -> bool {
        traits::type_satisfies_trait(self, ty, trait_path)
    }

    pub(crate) fn type_satisfies_trait_with_scope(
        &self,
        ty: &Type,
        trait_path: &Instance,
        scope: &HashMap<String, Bounds>,
    ) -> bool {
        traits::type_satisfies_trait_with_scope(self, ty, trait_path, scope)
    }

    /// Substructural class of a type in this environment.
    pub(crate) fn class_of(&self, ty: &Type, scope: &HashMap<String, Bounds>) -> Markers {
        traits::class_of(self, ty, scope)
    }
}

/// Fully resolved types inferred for HLL expressions, keyed by source provenance.
pub type ExpressionTypes = IndexMap<SourceInfo, Type>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReceiverAdjustment {
    None,
    Borrow(RefKind),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedMethodTarget {
    Inherent {
        self_ty: Type,
        method: Instance,
    },
    Trait {
        trait_path: Instance,
        self_ty: Type,
        method: Instance,
    },
    EnumConstructor {
        enum_instance: Instance,
        variant_name: String,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedReceiverTarget {
    Method(ResolvedMethodTarget),
    Field,
    FreeFunction(Instance),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedReceiverCall {
    pub target: ResolvedReceiverTarget,
    pub adjustment: ReceiverAdjustment,
}

pub(crate) struct PendingInstantiation {
    pub(crate) source: SourceInfo,
    pub(crate) function_name: String,
    pub(crate) caller_type_params: HashMap<String, Bounds>,
    pub(crate) type_params: Vec<TypeParam>,
    pub(crate) type_args: Vec<Type>,
    pub(crate) type_mapping: HashMap<String, Type>,
    pub(crate) lifetime_mapping: BTreeMap<Lifetime, Lifetime>,
}

#[derive(Debug, Clone)]
pub struct ClosureCapture {
    pub name: String,
    pub ty: Type,
    pub is_copy: bool,
    pub is_drop: bool,
    pub source: SourceInfo,
}

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub struct_name: String,
    pub fn_name: String,
    pub params: Vec<Param>,
    pub ret_ty: Type,
    pub captures: Vec<ClosureCapture>,
    pub source: SourceInfo,
    pub body: Expr,
    pub lifetime_params: Vec<LifetimeParam>,
    pub lifetime_args: Vec<Lifetime>,
    pub type_params: Vec<TypeParam>,
    pub type_args: Vec<Type>,
    pub markers: Markers,
    pub is_auto_clone: bool,
    pub is_auto_destroy: bool,
    pub fn_kind: crate::hll::derive::FnKind,
}

impl ClosureInfo {
    pub fn to_struct_decl(&self) -> StructDecl {
        let mut fields = Vec::new();
        let self_custom = Type::synthesized(TypeKind::Custom(Instance::new(
            self.struct_name.clone(),
            self.lifetime_args.clone(),
            self.type_args.clone(),
        )));
        let self_param_ty = match self.fn_kind {
            crate::hll::derive::FnKind::Fn => {
                Type::synthesized(TypeKind::Ref(RefKind::Shared, None, Box::new(self_custom)))
            }
            crate::hll::derive::FnKind::FnMut => {
                Type::synthesized(TypeKind::Ref(RefKind::Mut, None, Box::new(self_custom)))
            }
            crate::hll::derive::FnKind::FnOnce => self_custom,
        };
        let fn_ty = Type::synthesized(TypeKind::Fn {
            abi: Abi::Silica,
            params: {
                let mut p = vec![self_param_ty];
                for param in &self.params {
                    p.push(param.ty.clone());
                }
                p
            },
            ret: Box::new(self.ret_ty.clone()),
        });
        fields.push(StructField {
            name: "$call".to_string(),
            ty: fn_ty,
            source: self.source,
        });
        for c in &self.captures {
            fields.push(StructField {
                name: format!("$cap_{}", c.name),
                ty: c.ty.clone(),
                source: c.source,
            });
        }
        StructDecl {
            name: self.struct_name.clone(),
            lifetime_params: self.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: self.type_params.clone(),
            markers: self.markers,
            fields,
            source: self.source,
        }
    }
}

#[derive(Debug, Clone)]
pub struct GenericClosureCall {
    pub trait_path: Instance,
    pub self_ty: Type,
    pub method: Instance,
    pub adjustment: ReceiverAdjustment,
    pub args_tuple_ty: Type,
}

#[derive(Default)]
pub struct TypeCheckResults {
    pub env: TypeEnv,
    pub expression_types: ExpressionTypes,
    pub function_instantiations: IndexMap<SourceInfo, Instance>,
    pub receiver_calls: IndexMap<SourceInfo, ResolvedReceiverCall>,
    pub generic_closure_calls: IndexMap<SourceInfo, GenericClosureCall>,
    pub qualified_calls: IndexMap<SourceInfo, ResolvedMethodTarget>,
    pub closures: IndexMap<SourceInfo, ClosureInfo>,
    pub closures_by_struct: HashMap<String, ClosureInfo>,
    pub(crate) expression_contexts: IndexMap<SourceInfo, String>,
    pub(crate) pending_instantiations: Vec<PendingInstantiation>,
    pub(crate) synthesized_lifetime_params: IndexMap<String, Vec<LifetimeParam>>,
    pub(crate) reserved_lifetime_names: HashSet<String>,
    pub(crate) next_inferred_lifetime: usize,
    pub next_closure_id: usize,
}

impl std::ops::Deref for TypeCheckResults {
    type Target = ExpressionTypes;

    fn deref(&self) -> &Self::Target {
        &self.expression_types
    }
}

impl std::ops::DerefMut for TypeCheckResults {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.expression_types
    }
}

impl TypeCheckResults {
    pub(crate) fn fresh_inferred_lifetime(
        &mut self,
        env: &TypeEnv,
        subst: &mut Subst,
        source: SourceInfo,
    ) -> Option<Lifetime> {
        let context = env.current_function.as_ref()?;
        let params = self
            .synthesized_lifetime_params
            .entry(context.clone())
            .or_default();
        loop {
            let name = format!("s{}", self.next_inferred_lifetime);
            self.next_inferred_lifetime += 1;
            if self.reserved_lifetime_names.insert(name.clone()) {
                let lifetime = Lifetime(name);
                params.push(LifetimeParam::generated(
                    lifetime.clone(),
                    crate::common::GeneratedKind::LifetimeElision,
                    source.span(),
                ));
                subst.register_lifetime_variable(lifetime.clone());
                return Some(lifetime);
            }
        }
    }

    pub(crate) fn synthesized_lifetimes(&self, context: &str) -> &[LifetimeParam] {
        self.synthesized_lifetime_params
            .get(context)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }
}
