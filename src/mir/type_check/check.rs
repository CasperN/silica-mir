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
use crate::common::Lifetime;
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::helpers::*;
use indexmap::IndexMap;
use std::collections::{BTreeSet, HashSet};

/// Build the set of lifetime names in scope for a decl.
fn lifetime_scope(params: &[Lifetime]) -> BTreeSet<Lifetime> {
    params.iter().cloned().collect()
}

/// Collect all Named lifetimes referenced in `ty` that aren't in
/// `scope`. Duplicates are preserved so each occurrence gets a
/// diagnostic at its enclosing decl's span.
fn undeclared_lifetimes(ty: &Type, scope: &BTreeSet<Lifetime>) -> Vec<Lifetime> {
    let mut out = Vec::new();
    walk_lifetimes(ty, scope, &mut out);
    out
}

fn walk_lifetimes(ty: &Type, scope: &BTreeSet<Lifetime>, out: &mut Vec<Lifetime>) {
    match &ty.kind {
        TypeKind::Ref(_, Some(lt), inner) => {
            if !scope.contains(lt) {
                out.push(lt.clone());
            }
            walk_lifetimes(inner, scope, out);
        }
        TypeKind::Ref(_, None, inner) => walk_lifetimes(inner, scope, out),
        TypeKind::Custom(_, lts, args) => {
            for lt in lts {
                if !scope.contains(lt) {
                    out.push(lt.clone());
                }
            }
            for a in args {
                walk_lifetimes(a, scope, out);
            }
        }
        TypeKind::RawPtr(inner) | TypeKind::Array(inner, _) => walk_lifetimes(inner, scope, out),
        TypeKind::Fn(args) => {
            for a in args {
                walk_lifetimes(a, scope, out);
            }
        }
        _ => {}
    }
}

impl Env {
    pub fn typecheck(&self, program: &Program, d: &mut Diagnostics) {
        // Validate struct fields and enum variants
        for type_decl in self.types.values() {
            let (container_kind, item_kind, duplicate_code, items) = match type_decl {
                TypeDecl::Struct(s) => (
                    "struct",
                    "field",
                    DuplicateStructField,
                    s.fields
                        .iter()
                        .map(|f| (f.name.as_str(), &f.ty, f.span))
                        .collect::<Vec<_>>(),
                ),
                TypeDecl::Enum(e) => (
                    "enum",
                    "variant",
                    DuplicateEnumVariant,
                    e.variants
                        .iter()
                        .map(|v| (v.name.as_str(), &v.ty, v.span))
                        .collect::<Vec<_>>(),
                ),
            };
            let meta = type_decl.meta();
            let scope = meta.param_scope();
            let lt_scope = lifetime_scope(&meta.lifetime_params);
            let mut seen: HashSet<&str> = HashSet::new();
            for (name, ty, span) in items {
                if !seen.insert(name) {
                    d.push_error(Diagnostic::new(
                        duplicate_code,
                        span,
                        format!(
                            "In {} '{}', {} '{}' is declared more than once",
                            container_kind, meta.name, item_kind, name
                        ),
                    ));
                }
                if let Err(e) = self.validate_type(ty, &scope) {
                    d.push_error(Diagnostic::new(
                        InvalidDeclaredType,
                        ty.span,
                        format!(
                            "In {} '{}', {} '{}': {}",
                            container_kind, meta.name, item_kind, name, e
                        ),
                    ));
                }
                for lt in undeclared_lifetimes(ty, &lt_scope) {
                    d.push_error(Diagnostic::new(
                        UndeclaredLifetime,
                        ty.span,
                        format!(
                            "In {} '{}', {} '{}': undeclared lifetime {}",
                            container_kind, meta.name, item_kind, name, lt,
                        ),
                    ));
                }
            }
        }

        // Validate all functions
        for f in program.functions() {
            self.typecheck_function(f, d);
        }
    }

    fn typecheck_function(&self, f: &Function, d: &mut Diagnostics) {
        let scope = f.meta.param_scope();
        let lt_scope = lifetime_scope(&f.meta.lifetime_params);
        for (i, p) in f.params.iter().enumerate() {
            if p.name == "$return" {
                if i != f.params.len() - 1 {
                    d.push_error(Diagnostic::new(
                        InvalidDeclaredType,
                        p.span,
                        format!(
                            "In function '{}', parameter '$return' must be in the final position",
                            f.meta.name
                        ),
                    ));
                }
                match &p.ty.kind {
                    TypeKind::Ref(RefKind::Out, _, _) => {}
                    _ => {
                        d.push_error(
                            Diagnostic::new(InvalidDeclaredType, p.ty.span,
                                format!(
                                    "In function '{}', parameter '$return' must be of type '&out ReturnType', found {}", 
                                    f.meta.name,
                                    p.ty)),
                        );
                    }
                }
            }
            if let Err(e) = self.validate_type(&p.ty, &scope) {
                d.push_error(Diagnostic::new(
                    InvalidDeclaredType,
                    p.ty.span,
                    format!(
                        "In function '{}', parameter '{}': {}",
                        f.meta.name, p.name, e
                    ),
                ));
            }
            for lt in undeclared_lifetimes(&p.ty, &lt_scope) {
                d.push_error(Diagnostic::new(
                    UndeclaredLifetime,
                    p.ty.span,
                    format!(
                        "In function '{}', parameter '{}': undeclared lifetime {}",
                        f.meta.name, p.name, lt,
                    ),
                ));
            }
        }

        // `main` has a fixed signature convention — codegen synthesizes
        // an `i32 @main()` wrapper that calls it. Reject any other
        // shape here so bad programs fail at check time instead of
        // producing invalid IR.
        if f.meta.name == "main" {
            check_main_signature(f, d);
        }

        let Some(body) = &f.body else {
            return;
        };

        if body.blocks.is_empty() {
            d.push_error(Diagnostic::new(
                NoEntryBlock,
                f.meta.name_span,
                format!(
                    "Function '{}' has no entry block: body must contain at least one basic block",
                    f.meta.name
                ),
            ));
            return;
        }

        // Build the locals map. On name conflict, keep the first binding and
        // record an error — later checks still see a consistent scope.
        let mut locals_map: IndexMap<String, Type> = IndexMap::new();
        for p in &f.params {
            if locals_map.contains_key(&p.name) {
                d.push_error(Diagnostic::new(
                    DuplicateLocalName,
                    p.span,
                    format!(
                        "Duplicate variable name '{}' in parameters of function '{}'",
                        p.name, f.meta.name
                    ),
                ));
            } else {
                locals_map.insert(p.name.clone(), p.ty.clone());
            }
        }
        for l in &body.locals {
            if let Err(e) = self.validate_type(&l.ty, &scope) {
                d.push_error(Diagnostic::new(
                    InvalidDeclaredType,
                    l.ty.span,
                    format!("In function '{}', local '{}': {}", f.meta.name, l.name, e),
                ));
            }
            for lt in undeclared_lifetimes(&l.ty, &lt_scope) {
                d.push_error(Diagnostic::new(
                    UndeclaredLifetime,
                    l.ty.span,
                    format!(
                        "In function '{}', local '{}': undeclared lifetime {}",
                        f.meta.name, l.name, lt,
                    ),
                ));
            }
            if locals_map.contains_key(&l.name) {
                d.push_error(Diagnostic::new(
                    DuplicateLocalName,
                    l.span,
                    format!(
                        "Duplicate variable name '{}' in locals/parameters of function '{}'",
                        l.name, f.meta.name
                    ),
                ));
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
        for stmt in &block.statements {
            if let Err(e) = self.typecheck_statement(func, block, stmt, stmt.span, locals) {
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
                .in_function(&func.meta.name)
                .in_block(&block.label)
        };
        // Attach the current function/block to a Diagnostic produced
        // by an inner helper (which knows its code + span but not the
        // enclosing context).
        let with_context =
            |d: Diagnostic| -> Diagnostic { d.in_function(&func.meta.name).in_block(&block.label) };
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
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
            StatementKind::Call(target, args) => {
                let target_ty = self
                    .type_of_operand(target, stmt_span, locals)
                    .map_err(with_context)?;

                let target_ty_str = format!("{}", target_ty);
                let TypeKind::Fn(param_tys) = target_ty.kind else {
                    return Err(stmt_diag(
                        CallTargetNotFunction,
                        format!("Call target is not a function type: {}", target_ty_str),
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
            StatementKind::Drop(place) => {
                // Just resolve the place — any legality (Drop,
                // currently init) is enforced by the substructural checker.
                self.type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
                Ok(())
            }
            StatementKind::Unborrow(place) => {
                let ty = self
                    .type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
                if !matches!(&ty.kind, TypeKind::Ref(_, _, _)) {
                    return Err(stmt_diag(
                        UnborrowNonReference,
                        format!("unborrow requires a reference-typed place, found {}", ty),
                    ));
                }
                Ok(())
            }
            StatementKind::RequireUninit(place) => {
                self.type_of_place(place, stmt_span, locals)
                    .map_err(with_context)?;
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
        let ts = block.terminator.span;
        // Local helper: build a Diagnostic with terminator context.
        let terminator_diag = |code, msg: String| -> Diagnostic {
            Diagnostic::new(code, ts, msg)
                .in_function(&func.meta.name)
                .in_block(&block.label)
        };
        match &block.terminator.kind {
            TerminatorKind::Goto(label) => {
                if !block_labels.contains(label) {
                    d.push_error(terminator_diag(
                        TypeCheckCode::TerminatorUndefinedTarget,
                        format!("goto targets undefined block '{}'", label),
                    ));
                }
            }
            TerminatorKind::Return => {}
            TerminatorKind::Branch {
                cond,
                true_label,
                false_label,
            } => {
                match self.type_of_operand(cond, ts, locals) {
                    Ok(cond_ty) if cond_ty.kind != TypeKind::Bool => d.push_error(terminator_diag(
                        TypeCheckCode::BranchConditionNotBool,
                        format!("branch condition must be bool, found {}", cond_ty),
                    )),
                    Ok(_) => {}
                    Err(inner_diag) => d.push_error(
                        inner_diag
                            .in_function(&func.meta.name)
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
            TerminatorKind::SwitchEnum { place, cases } => {
                // Resolve the place to (enum_name, decl) or record an error.
                // Variant-membership checks are skipped if this fails, but
                // label-existence checks still run on every case.
                let enum_decl: Option<&EnumDecl> = match self.type_of_place(place, ts, locals) {
                    Ok(ty) => match ty.kind {
                        TypeKind::Custom(name, _, _) => match self.types.get(&name) {
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
                        _ => {
                            d.push_error(terminator_diag(
                                TypeCheckCode::SwitchOnNonEnum,
                                format!("switchEnum place must be an enum type, found {}", ty),
                            ));
                            None
                        }
                    },
                    Err(inner_diag) => {
                        d.push_error(
                            inner_diag
                                .in_function(&func.meta.name)
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
                                    variant, e_decl.meta.name
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
            TerminatorKind::Abort => {}
            TerminatorKind::Unreachable => {}
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
    let is_out_i32 = |ty: &Type| {
        matches!(
            &ty.kind,
            TypeKind::Ref(RefKind::Out, _, inner) if **inner == i32_ty()
        )
    };
    match f.params.as_slice() {
        [] => {}
        [p] if is_out_i32(&p.ty) => {}
        [p] => {
            d.push_error(Diagnostic::new(
                MainBadSignature,
                p.span,
                format!(
                    "In function 'main': single parameter must be '&out i32', found {}",
                    p.ty
                ),
            ));
        }
        _ => {
            d.push_error(Diagnostic::new(
                MainBadSignature,
                f.meta.name_span,
                format!(
                    "In function 'main': takes at most one parameter (an optional '&out i32'), found {} parameters",
                    f.params.len()
                ),
            ));
        }
    }
}
