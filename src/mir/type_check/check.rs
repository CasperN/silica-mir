//! MIR type-checking pass.
//!
//! Verifies that every declaration, statement, and terminator in the
//! program is well-typed against the `Env`. No inference: types come
//! from the environment (parameters, locals) and from the structural
//! `type_of_*` queries; this pass only checks that they line up.

use super::Env;
use super::TypeCheckCode;
use super::TypeCheckCode::*;
use super::TypeDecl;
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::helpers::*;
use crate::mir::substructural::composition::scope_from;
use indexmap::IndexMap;
use std::collections::HashSet;

impl Env {
    pub fn typecheck(&self, d: &mut Diagnostics) {
        // Validate struct fields and enum variants
        for type_decl in self.types.values() {
            match type_decl {
                TypeDecl::Struct(s) => {
                    let scope = scope_from(&s.type_params);
                    let mut seen: HashSet<&str> = HashSet::new();
                    for f in &s.fields {
                        if !seen.insert(f.name.as_str()) {
                            d.push_error(
                                Diagnostic::new(DuplicateStructField, f.span, format!(
                                        "In struct '{}', field '{}' is declared more than once",
                                        s.name, f.name
                                    )),
                            );
                        }
                        if let Err(e) = self.validate_type(&f.ty, &scope) {
                            d.push_error(
                                Diagnostic::new(InvalidDeclaredType, f.span, format!("In struct '{}', field '{}': {}", s.name, f.name, e)),
                            );
                        }
                    }
                }
                TypeDecl::Enum(e) => {
                    let scope = scope_from(&e.type_params);
                    let mut seen: HashSet<&str> = HashSet::new();
                    for v in &e.variants {
                        if !seen.insert(v.name.as_str()) {
                            d.push_error(
                                Diagnostic::new(DuplicateEnumVariant, v.span, format!(
                                        "In enum '{}', variant '{}' is declared more than once",
                                        e.name, v.name
                                    )),
                            );
                        }
                        if let Err(err) = self.validate_type(&v.ty, &scope) {
                            d.push_error(
                                Diagnostic::new(InvalidDeclaredType, v.span, format!("In enum '{}', variant '{}': {}", e.name, v.name, err)),
                            );
                        }
                    }
                }
            }
        }

        // Validate all functions
        for f in self.functions.values() {
            self.typecheck_function(f, d);
        }
    }

    fn typecheck_function(&self, f: &Function, d: &mut Diagnostics) {
        let scope = scope_from(&f.type_params);
        for (i, p) in f.params.iter().enumerate() {
            if p.name == "$return" {
                if i != f.params.len() - 1 {
                    d.push_error(
                        Diagnostic::new(InvalidDeclaredType, p.span, format!("In function '{}', parameter '$return' must be in the final position", f.name)),
                    );
                }
                match &p.ty {
                    Type::Ref(RefKind::Out, _, _) => {}
                    _ => {
                        d.push_error(
                            Diagnostic::new(InvalidDeclaredType, p.span, format!("In function '{}', parameter '$return' must be of type '&out ReturnType', found {}", f.name, p.ty)),
                        );
                    }
                }
            }
            if let Err(e) = self.validate_type(&p.ty, &scope) {
                d.push_error(
                    Diagnostic::new(InvalidDeclaredType, p.span, format!("In function '{}', parameter '{}': {}", f.name, p.name, e)),
                );
            }
        }

        // `main` has a fixed signature convention — codegen synthesizes
        // an `i32 @main()` wrapper that calls it. Reject any other
        // shape here so bad programs fail at check time instead of
        // producing invalid IR.
        if f.name == "main" {
            check_main_signature(f, d);
        }

        let Some(body) = &f.body else {
            return;
        };

        if body.blocks.is_empty() {
            d.push_error(
                Diagnostic::new(NoEntryBlock, f.name_span, format!(
                        "Function '{}' has no entry block: body must contain at least one basic block",
                        f.name
                    )),
            );
            return;
        }

        // Build the locals map. On name conflict, keep the first binding and
        // record an error — later checks still see a consistent scope.
        let mut locals_map: IndexMap<String, Type> = IndexMap::new();
        for p in &f.params {
            if locals_map.contains_key(&p.name) {
                d.push_error(
                    Diagnostic::new(DuplicateLocalName, p.span, format!(
                            "Duplicate variable name '{}' in parameters of function '{}'",
                            p.name, f.name
                        )),
                );
            } else {
                locals_map.insert(p.name.clone(), p.ty.clone());
            }
        }
        for l in &body.locals {
            if let Err(e) = self.validate_type(&l.ty, &scope) {
                d.push_error(
                    Diagnostic::new(InvalidDeclaredType, l.span, format!("In function '{}', local '{}': {}", f.name, l.name, e)),
                );
            }
            if locals_map.contains_key(&l.name) {
                d.push_error(
                    Diagnostic::new(DuplicateLocalName, l.span, format!(
                            "Duplicate variable name '{}' in locals/parameters of function '{}'",
                            l.name, f.name
                        )),
                );
            } else {
                locals_map.insert(l.name.clone(), l.ty.clone());
            }
        }

        let block_labels: HashSet<String> = body.blocks.iter().map(|b| b.label.clone()).collect();

        for block in &body.blocks {
            self.typecheck_block(f, block, &locals_map, &block_labels, d);
        }
    }

    fn typecheck_block(
        &self,
        func: &Function,
        block: &BasicBlock,
        locals: &IndexMap<String, Type>,
        block_labels: &HashSet<String>,
        d: &mut Diagnostics,
    ) {
        for (stmt, span) in &block.statements {
            if let Err(e) = self.typecheck_statement(func, block, stmt, *span, locals) {
                d.push_error(e);
            }
        }
        self.typecheck_terminator(func, block, locals, block_labels, d);
    }

    fn typecheck_statement(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        stmt_span: Span,
        locals: &IndexMap<String, Type>,
    ) -> Result<(), Diagnostic> {
        // Local helper: build a Diagnostic with statement context.
        let stmt_diag = |code, msg: String| -> Diagnostic {
            Diagnostic::new(code, stmt_span, msg)
                .in_function(&func.name)
                .in_block(&block.label)
        };
        // Attach the current function/block to a Diagnostic produced
        // by an inner helper (which knows its code + span but not the
        // enclosing context).
        let with_context = |d: Diagnostic| -> Diagnostic {
            d.in_function(&func.name).in_block(&block.label)
        };
        match stmt {
            Statement::Assign(place, rvalue) => {
                let lhs_ty = self
                    .type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
                let rhs_ty = self
                    .type_of_rvalue(rvalue, stmt_span, locals)
                    .map_err(with_context)?;
                if !self.types_match(&lhs_ty, &rhs_ty) {
                    return Err(stmt_diag(
                        AssignmentTypeMismatch,
                        format!(
                            "Type mismatch in assignment. LHS is {}, RHS is {}",
                            lhs_ty, rhs_ty
                        ),
                    ));
                }
                Ok(())
            }
            Statement::Call(target, args) => {
                let target_ty = self
                    .type_of_operand(target, stmt_span, locals)
                    .map_err(with_context)?;

                let Type::Fn(param_tys) = target_ty else {
                    return Err(stmt_diag(
                        CallTargetNotFunction,
                        format!("Call target is not a function type: {}", target_ty),
                    ));
                };

                if args.len() != param_tys.len() {
                    return Err(stmt_diag(
                        CallWrongArity,
                        format!(
                            "Wrong i64 of arguments for call. Expected {}, found {}",
                            param_tys.len(),
                            args.len()
                        ),
                    ));
                }
                for (i, (arg, param_ty)) in args.iter().zip(param_tys.iter()).enumerate() {
                    let arg_ty = self
                        .type_of_operand(arg, stmt_span, locals)
                        .map_err(with_context)?;
                    if !self.types_match(param_ty, &arg_ty) {
                        return Err(stmt_diag(
                            CallArgTypeMismatch,
                            format!(
                                "Call argument {} type mismatch. Expected {}, found {}",
                                i, param_ty, arg_ty
                            ),
                        ));
                    }
                }
                Ok(())
            }
            Statement::Drop(place) => {
                // Just resolve the place — any legality (Drop,
                // currently init) is enforced by the substructural checker.
                self.type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
                Ok(())
            }
            Statement::Unborrow(place) => {
                let ty = self
                    .type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
                if !matches!(ty, Type::Ref(_, _, _)) {
                    return Err(stmt_diag(
                        UnborrowNonReference,
                        format!("unborrow requires a reference-typed place, found {}", ty),
                    ));
                }
                Ok(())
            }
        }
    }

    fn typecheck_terminator(
        &self,
        func: &Function,
        block: &BasicBlock,
        locals: &IndexMap<String, Type>,
        block_labels: &HashSet<String>,
        d: &mut Diagnostics,
    ) {
        let ts = block.terminator_span;
        // Local helper: build a Diagnostic with terminator context.
        let terminator_diag = |code, msg: String| -> Diagnostic {
            Diagnostic::new(code, ts, msg)
                .in_function(&func.name)
                .in_block(&block.label)
        };
        match &block.terminator {
            Terminator::Goto(label) => {
                if !block_labels.contains(label) {
                    d.push_error(terminator_diag(
                        TypeCheckCode::TerminatorUndefinedTarget,
                        format!("goto targets undefined block '{}'", label),
                    ));
                }
            }
            Terminator::Return => {}
            Terminator::Branch {
                cond,
                true_label,
                false_label,
            } => {
                match self.type_of_operand(cond, ts, locals) {
                    Ok(cond_ty) if cond_ty != Type::Bool => d.push_error(terminator_diag(
                        TypeCheckCode::BranchConditionNotBool,
                        format!("branch condition must be bool, found {}", cond_ty),
                    )),
                    Ok(_) => {}
                    Err(inner_diag) => d.push_error(
                        inner_diag
                            .in_function(&func.name)
                            .in_block(&block.label),
                    ),
                }
                if !block_labels.contains(true_label) {
                    d.push_error(terminator_diag(
                        TypeCheckCode::TerminatorUndefinedTarget,
                        format!("branch true target undefined block '{}'", true_label),
                    ));
                }
                if !block_labels.contains(false_label) {
                    d.push_error(terminator_diag(
                        TypeCheckCode::TerminatorUndefinedTarget,
                        format!("branch false target undefined block '{}'", false_label),
                    ));
                }
            }
            Terminator::SwitchEnum { place, cases } => {
                // Resolve the place to (enum_name, decl) or record an error.
                // Variant-membership checks are skipped if this fails, but
                // label-existence checks still run on every case.
                let enum_decl: Option<&EnumDecl> = match self.type_of_place(place, ts, locals) {
                    Ok(Type::Custom(name, _, _)) => match self.types.get(&name) {
                        Some(TypeDecl::Enum(e)) => Some(e),
                        Some(TypeDecl::Struct(_)) => {
                            d.push_error(terminator_diag(
                                TypeCheckCode::SwitchOnNonEnum,
                                format!(
                                    "switchEnum place must be an enum type, found struct '{}'",
                                    name
                                ),
                            ));
                            None
                        }
                        None => {
                            d.push_error(terminator_diag(
                                TypeCheckCode::SwitchOnNonEnum,
                                format!("Undeclared enum '{}' in switchEnum", name),
                            ));
                            None
                        }
                    },
                    Ok(other) => {
                        d.push_error(terminator_diag(
                            TypeCheckCode::SwitchOnNonEnum,
                            format!("switchEnum place must be an enum type, found {}", other),
                        ));
                        None
                    }
                    Err(inner_diag) => {
                        d.push_error(
                            inner_diag
                                .in_function(&func.name)
                                .in_block(&block.label),
                        );
                        None
                    }
                };

                for (variant, label) in cases {
                    if let Some(e_decl) = enum_decl {
                        if !e_decl.variants.iter().any(|v| v.name == *variant) {
                            d.push_error(terminator_diag(
                                TypeCheckCode::SwitchArmUnknownVariant,
                                format!(
                                    "variant '{}' is not part of enum '{}'",
                                    variant, e_decl.name
                                ),
                            ));
                        }
                    }
                    if !block_labels.contains(label) {
                        d.push_error(terminator_diag(
                            TypeCheckCode::TerminatorUndefinedTarget,
                            format!(
                                "switchEnum variant '{}' targets undefined block '{}'",
                                variant, label
                            ),
                        ));
                    }
                }
            }
            Terminator::Abort => {}
            Terminator::Unreachable => {}
        }
    }
}

/// Verify `fn main`'s signature is one of the two accepted shapes:
///
/// - `fn main()` — the wrapper always returns 0.
/// - `fn main(exit: &out i32)` — the wrapper returns the value
///   written through `exit`.
///
/// Anything else is a check error. Externs (no body) are ignored;
/// this only fires on definitions.
fn check_main_signature(f: &Function, d: &mut Diagnostics) {
    if f.is_extern {
        return;
    }
    let is_out_i32 = |ty: &Type| matches!(
        ty,
        Type::Ref(RefKind::Out, _, inner) if **inner == i32_ty()
    );
    match f.params.as_slice() {
        [] => {}
        [p] if is_out_i32(&p.ty) => {}
        [p] => {
            d.push_error(
                Diagnostic::new(MainBadSignature, p.span, format!(
                        "In function 'main': single parameter must be '&out i32', found {}",
                        p.ty
                    )),
            );
        }
        _ => {
            d.push_error(Diagnostic::new(
                MainBadSignature,
                f.name_span,
                format!(
                    "In function 'main': takes at most one parameter (an optional '&out i32'), found {} parameters",
                    f.params.len()
                ),
            ));
        }
    }
}
