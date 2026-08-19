//! Trait derivation machinery for HLL structs, enums, and closures.
//!
//! Provides capability queries (`can_derive_*`) and MIR synthesizers (`derive_*_mir`)
//! for Silica's compiler-supported auto-traits (`AutoClone`, `AutoDestroy`, etc.).

use crate::common::{Abi, Linkage, Marker, Markers, RefKind, SourceInfo};
use crate::hll::ast::{EnumDecl, StructDecl, StructField, TypeKind};
use crate::hll::lowering::lower_type;
use crate::hll::type_check::TypeEnv;
use crate::mir::ast::{self as mir, BasicBlock, DeclMeta, GenericParams, Place};
use crate::mir::helpers::*;

// ---------------- Capability Queries ----------------

/// Check if any field holds an unfulfilled linear/directional obligation (`&out` or `&drop`).
pub fn has_linear_reference_obligation(fields: &[StructField]) -> bool {
    fields.iter().any(|f| {
        matches!(f.ty.kind, TypeKind::Ref(RefKind::Out | RefKind::Drop, _, _))
    })
}

pub fn can_derive_auto_clone(s: &StructDecl, env: &TypeEnv) -> bool {
    s.fields
        .iter()
        .all(|f| env.type_satisfies_trait(&f.ty, &crate::hll::ast::Instance::bare("AutoClone")))
}

pub fn can_derive_auto_clone_enum(e: &EnumDecl, env: &TypeEnv) -> bool {
    e.variants
        .iter()
        .all(|v| env.type_satisfies_trait(&v.ty, &crate::hll::ast::Instance::bare("AutoClone")))
}

pub fn can_derive_auto_destroy(s: &StructDecl, env: &TypeEnv) -> bool {
    !has_linear_reference_obligation(&s.fields)
        && s.fields.iter().all(|f| {
            env.type_satisfies_trait(&f.ty, &crate::hll::ast::Instance::bare("AutoDestroy"))
        })
}

pub fn can_derive_auto_destroy_enum(e: &EnumDecl, env: &TypeEnv) -> bool {
    e.variants
        .iter()
        .all(|v| env.type_satisfies_trait(&v.ty, &crate::hll::ast::Instance::bare("AutoDestroy")))
}

// ---------------- MIR Derivation Synthesizers ----------------

/// Synthesize `impl<'s0, ...> AutoClone for $closure_N<'s0, ...> { fn clone(recv: &Self, $return: &out Self) { ... } }`.
pub fn derive_auto_clone_mir(closure: &crate::hll::type_check::ClosureInfo) -> mir::Declaration {
    let source = SourceInfo::generated(mir::GeneratedKind::HllDesugaring, closure.source.span());
    let target_ty = mir::Type::new(
        mir::TypeKind::Custom(mir::Instance::new(
            closure.struct_name.clone(),
            closure.lifetime_args.clone(),
            Vec::new(),
        )),
        source,
    );

    let recv_param = mir::Param {
        name: "recv".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Shared, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };
    let return_param = mir::Param {
        name: "$return".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Out, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };

    let mut stmts = Vec::new();
    let mut locals = Vec::new();

    let recv_place = Place::Var("recv".to_string());
    let return_place = Place::Var("$return".to_string());

    // 1. $call field is always Copy:
    let call_dest = field_place(deref_place(return_place.clone()), "$call".to_string());
    let call_src = field_place(deref_place(recv_place.clone()), "$call".to_string());
    stmts.push(assign_stmt(call_dest, use_rv(copy_op(call_src)), source));

    // 2. Capture fields:
    for c in &closure.captures {
        let field_name = format!("$cap_{}", c.name);
        let field_dest = field_place(deref_place(return_place.clone()), field_name.clone());
        let field_src = field_place(deref_place(recv_place.clone()), field_name.clone());
        let mir_field_ty = lower_type(&c.ty);

        if c.is_copy {
            stmts.push(assign_stmt(field_dest, use_rv(copy_op(field_src)), source));
        } else {
            let tmp_recv_name = format!("$tmp_recv_{}", c.name);
            let tmp_recv_place = Place::Var(tmp_recv_name.clone());
            let tmp_recv_ty = shared_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_recv_name,
                ty: tmp_recv_ty,
                source,
            });

            let tmp_out_name = format!("$tmp_out_{}", c.name);
            let tmp_out_place = Place::Var(tmp_out_name.clone());
            let tmp_out_ty = out_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_out_name,
                ty: tmp_out_ty,
                source,
            });

            stmts.push(assign_stmt(
                tmp_recv_place.clone(),
                ref_rv(RefKind::Shared, field_src),
                source,
            ));
            stmts.push(assign_stmt(
                tmp_out_place.clone(),
                ref_rv(RefKind::Out, field_dest),
                source,
            ));
            let callee = trait_fn_op(
                mir::Instance::bare("AutoClone"),
                mir_field_ty,
                mir::Instance::bare("clone"),
            );
            stmts.push(call_stmt(
                callee,
                vec![move_op(tmp_recv_place), move_op(tmp_out_place)],
                source,
            ));
        }
    }

    stmts.push(unborrow_stmt(return_place.clone(), source));
    stmts.push(drop_stmt(recv_place.clone(), source));
    stmts.push(require_uninit_stmt(recv_place, source));

    let entry_block = BasicBlock {
        label: "entry".to_string(),
        label_source: source,
        statements: stmts,
        terminator: return_term(source),
    };

    let clone_fn = mir::Function {
        meta: DeclMeta {
            name: "clone".to_string(),
            name_source: source,
            params: GenericParams {
                lifetime_params: Vec::new(),
                outlives: Vec::new(),
                type_params: Vec::new(),
                source,
            },
            markers: Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]),
        },
        linkage: Linkage::Local,
        abi: Abi::Silica,
        params: vec![recv_param, return_param],
        body: Some(mir::FunctionBody {
            locals,
            blocks: vec![entry_block],
        }),
    };

    mir::Declaration::Impl(mir::ImplBlock {
        params: GenericParams {
            lifetime_params: closure.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            source,
        },
        trait_path: Some(mir::Instance::bare("AutoClone")),
        target: target_ty,
        methods: vec![clone_fn],
    })
}

/// Synthesize `impl<'s0, ...> AutoDestroy for $closure_N<'s0, ...> { fn destroy(recv: &drop Self) { ... } }`.
pub fn derive_auto_destroy_mir(closure: &crate::hll::type_check::ClosureInfo) -> mir::Declaration {
    let source = SourceInfo::generated(mir::GeneratedKind::HllDesugaring, closure.source.span());
    let target_ty = mir::Type::new(
        mir::TypeKind::Custom(mir::Instance::new(
            closure.struct_name.clone(),
            closure.lifetime_args.clone(),
            Vec::new(),
        )),
        source,
    );

    let recv_param = mir::Param {
        name: "recv".to_string(),
        ty: mir::Type::new(
            mir::TypeKind::Ref(RefKind::Drop, None, Box::new(target_ty.clone())),
            source,
        ),
        source,
    };

    let mut stmts = Vec::new();
    let mut locals = Vec::new();

    let recv_place = Place::Var("recv".to_string());

    // 1. $call field is always Drop:
    let call_src = field_place(deref_place(recv_place.clone()), "$call".to_string());
    stmts.push(drop_stmt(call_src, source));

    // 2. Capture fields:
    for c in &closure.captures {
        let field_name = format!("$cap_{}", c.name);
        let field_src = field_place(deref_place(recv_place.clone()), field_name.clone());
        let mir_field_ty = lower_type(&c.ty);

        if c.is_drop {
            stmts.push(drop_stmt(field_src, source));
        } else {
            let tmp_recv_name = format!("$tmp_drop_{}", c.name);
            let tmp_recv_place = Place::Var(tmp_recv_name.clone());
            let tmp_recv_ty = drop_ref_ty(mir_field_ty.clone());
            locals.push(mir::Local {
                name: tmp_recv_name,
                ty: tmp_recv_ty,
                source,
            });

            stmts.push(assign_stmt(
                tmp_recv_place.clone(),
                ref_rv(RefKind::Drop, field_src),
                source,
            ));
            let callee = trait_fn_op(
                mir::Instance::bare("AutoDestroy"),
                mir_field_ty,
                mir::Instance::bare("destroy"),
            );
            stmts.push(call_stmt(callee, vec![move_op(tmp_recv_place)], source));
        }
    }

    let entry_block = BasicBlock {
        label: "entry".to_string(),
        label_source: source,
        statements: stmts,
        terminator: return_term(source),
    };

    let destroy_fn = mir::Function {
        meta: DeclMeta {
            name: "destroy".to_string(),
            name_source: source,
            params: GenericParams {
                lifetime_params: Vec::new(),
                outlives: Vec::new(),
                type_params: Vec::new(),
                source,
            },
            markers: Markers::from_iter([Marker::Copy, Marker::Drop, Marker::Move]),
        },
        linkage: Linkage::Local,
        abi: Abi::Silica,
        params: vec![recv_param],
        body: Some(mir::FunctionBody {
            locals,
            blocks: vec![entry_block],
        }),
    };

    mir::Declaration::Impl(mir::ImplBlock {
        params: GenericParams {
            lifetime_params: closure.lifetime_params.clone(),
            outlives: Vec::new(),
            type_params: Vec::new(),
            source,
        },
        trait_path: Some(mir::Instance::bare("AutoDestroy")),
        target: target_ty,
        methods: vec![destroy_fn],
    })
}
