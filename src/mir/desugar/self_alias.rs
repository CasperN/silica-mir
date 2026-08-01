//! `Self`-alias desugaring: replace `Self` in impl-method signatures,
//! locals, and bodies with the impl's target type.

use crate::mir::ast::*;
use crate::mir::env::IndexedProgram;
use crate::mir::type_util::{
    substitute_params, substitute_stmt_types, substitute_terminator_types,
};

/// Replace every `Self` reference in each impl-method with the impl's
/// target type. `Self` is parsed as `TypeKind::Param("Self")` inside
/// impls; after this pass, no impl-method carries that param, so
/// type-check, elaboration, mono, and codegen only ever see the
/// concrete target.
///
/// The parser binds `Self` for the whole impl-method scope (sigs,
/// locals, and body operands), so this pass has to walk everywhere the
/// method carries a `Type`: param types, local types, statement Type
/// slots (fn-name type args, trait-fn `self_ty`, `PtrCast` targets,
/// enum construction type args), and terminator Type slots.
///
/// Trait method sigs still mention `Self` after this pass — traits are
/// templates. Trait-impl checking substitutes `Self := target` on the
/// trait side at conformance-check time.
pub fn desugar_self_alias(program: &mut IndexedProgram) {
    for imp in program
        .impls
        .values_mut()
        .chain(program.inherent_impls.iter_mut())
    {
        let self_param = [TypeParam {
            name: "Self".to_string(),
            bounds: Bounds::default(),
            source: imp.target.source,
        }];
        let self_arg = [imp.target.clone()];
        for method in &mut imp.methods {
            for p in &mut method.params {
                p.ty = substitute_params(&p.ty, &self_param, &self_arg);
            }
            if let Some(body) = method.body.as_mut() {
                for local in &mut body.locals {
                    local.ty = substitute_params(&local.ty, &self_param, &self_arg);
                }
                for block in &mut body.blocks {
                    for stmt in &mut block.statements {
                        *stmt = substitute_stmt_types(stmt, &self_param, &self_arg);
                    }
                    block.terminator =
                        substitute_terminator_types(&block.terminator, &self_param, &self_arg);
                }
            }
        }
    }
}
