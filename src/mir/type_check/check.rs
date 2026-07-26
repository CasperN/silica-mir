//! MIR type-checking pass.
//!
//! Verifies that every declaration, statement, and terminator in the
//! program is well-typed against the `Env`. No inference: types come
//! from the environment (parameters, locals) and from the structural
//! `type_of_*` queries; this pass only checks that they line up.

use super::env::{TypeResolutionError, TypeValidationError};
use super::Env;
use super::TypeCheckCode;
use super::TypeCheckCode::*;
use super::TypeDecl;
use crate::common::{Lifetime, LifetimeParam};
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::diagnostic_format::{format_type_diagnostic, DiagnosticFormat};
use crate::mir::helpers::*;
use indexmap::IndexMap;
use std::collections::{BTreeSet, HashSet};

fn resolution_diagnostic(
    error: TypeResolutionError,
    source: SourceInfo,
    meta: &DeclMeta,
    env: &Env,
) -> Diagnostic {
    let mut format = DiagnosticFormat::new();
    let scope = format.scope(meta);
    let message = error.message(&mut format, &scope, env);
    format.finish(Diagnostic::new(error.code(), source, message))
}

fn validation_diagnostic(
    error: TypeValidationError,
    source: SourceInfo,
    meta: &DeclMeta,
    context: String,
) -> Diagnostic {
    let mut format = DiagnosticFormat::new();
    let scope = format.scope(meta);
    let reason = error.message(&mut format, &scope);
    format.finish(Diagnostic::new(
        InvalidDeclaredType,
        source,
        format!("{}: {}", context, reason),
    ))
}

/// Build the set of lifetime names in scope for a decl. `'static` is
/// always in scope — it's the reserved top-of-outlives-order region,
/// available to every decl without being declared as a parameter.
fn lifetime_scope(params: &[LifetimeParam]) -> BTreeSet<Lifetime> {
    let mut s: BTreeSet<Lifetime> = params.iter().map(|p| p.lifetime.clone()).collect();
    s.insert(Lifetime("static".to_string()));
    s
}

/// Reject shape errors on a decl's declared lifetime params:
/// - `'static` is reserved and cannot be a user param.
/// - Duplicates are rejected (any subsequent occurrence).
/// - Outlives clauses must reference in-scope lifetimes on both sides.
fn validate_lifetime_decls(
    meta: &crate::mir::ast::DeclMeta,
    container_kind: &str,
    d: &mut Diagnostics,
) {
    let mut seen: BTreeSet<&Lifetime> = BTreeSet::new();
    for lt in &meta.lifetime_params {
        if lt.lifetime.0 == "static" {
            d.push_error(Diagnostic::new(
                ReservedLifetimeName,
                lt.source,
                format!(
                    "In {} '{}': 'static is a reserved lifetime and cannot be declared as a parameter",
                    container_kind, meta.name,
                ),
            ));
        }
        if !seen.insert(&lt.lifetime) {
            d.push_error(Diagnostic::new(
                DuplicateLifetimeParam,
                lt.source,
                format!(
                    "In {} '{}': lifetime parameter {} is declared more than once",
                    container_kind, meta.name, lt,
                ),
            ));
        }
    }
    let lt_scope = lifetime_scope(&meta.lifetime_params);
    for bound in &meta.outlives {
        for lt in [&bound.longer, &bound.shorter] {
            if !lt_scope.contains(lt) {
                d.push_error(Diagnostic::new(
                    UndeclaredLifetime,
                    bound.source,
                    format!(
                        "In {} '{}': outlives clause references undeclared lifetime {}",
                        container_kind, meta.name, lt,
                    ),
                ));
            }
        }
    }
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
        // Scalars (Unit, Int, Float, Bool, Never) and Param carry no
        // lifetimes to collect. New TypeKind variants that CAN carry
        // lifetimes must add a case above.
        TypeKind::Unit
        | TypeKind::Int(_)
        | TypeKind::Float(_)
        | TypeKind::Bool
        | TypeKind::Never
        | TypeKind::Param(_) => {}
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
                        .map(|f| (f.name.as_str(), &f.ty, f.source))
                        .collect::<Vec<_>>(),
                ),
                TypeDecl::Enum(e) => (
                    "enum",
                    "variant",
                    DuplicateEnumVariant,
                    e.variants
                        .iter()
                        .map(|v| (v.name.as_str(), &v.ty, v.source))
                        .collect::<Vec<_>>(),
                ),
            };
            let meta = type_decl.meta();
            let scope = meta.param_scope();
            let lt_scope = lifetime_scope(&meta.lifetime_params);
            let mut seen: HashSet<&str> = HashSet::new();
            for (name, ty, source) in items {
                if !seen.insert(name) {
                    d.push_error(Diagnostic::new(
                        duplicate_code,
                        source,
                        format!(
                            "In {} '{}', {} '{}' is declared more than once",
                            container_kind, meta.name, item_kind, name
                        ),
                    ));
                }
                if let Err(e) = self.validate_type(ty, &scope) {
                    d.push_error(validation_diagnostic(
                        e,
                        ty.source,
                        meta,
                        format!(
                            "In {} '{}', {} '{}'",
                            container_kind, meta.name, item_kind, name,
                        ),
                    ));
                }
                for lt in undeclared_lifetimes(ty, &lt_scope) {
                    d.push_error(Diagnostic::new(
                        UndeclaredLifetime,
                        ty.source,
                        format!(
                            "In {} '{}', {} '{}': undeclared lifetime {}",
                            container_kind, meta.name, item_kind, name, lt,
                        ),
                    ));
                }
            }
            validate_lifetime_decls(meta, container_kind, d);
        }

        // Validate all functions
        for f in program.functions() {
            self.typecheck_function(f, d);
        }
    }

    fn typecheck_function(&self, f: &Function, d: &mut Diagnostics) {
        let scope = f.meta.param_scope();
        let lt_scope = lifetime_scope(&f.meta.lifetime_params);
        validate_lifetime_decls(&f.meta, "function", d);
        for (i, p) in f.params.iter().enumerate() {
            if p.name == "$return" {
                if i != f.params.len() - 1 {
                    d.push_error(Diagnostic::new(
                        InvalidDeclaredType,
                        p.source,
                        format!(
                            "In function '{}', parameter '$return' must be in the final position",
                            f.meta.name
                        ),
                    ));
                }
                match &p.ty.kind {
                    TypeKind::Ref(RefKind::Out, _, _) => {}
                    _ => {
                        d.push_error(format_type_diagnostic(&f.meta, &p.ty, |ty| {
                            Diagnostic::new(
                                InvalidDeclaredType,
                                p.ty.source,
                                format!(
                                    "In function '{}', parameter '$return' must be of type '&out ReturnType', found {}",
                                    f.meta.name, ty,
                                ),
                            )
                        }));
                    }
                }
            }
            if let Err(e) = self.validate_type(&p.ty, &scope) {
                d.push_error(validation_diagnostic(
                    e,
                    p.ty.source,
                    &f.meta,
                    format!("In function '{}', parameter '{}'", f.meta.name, p.name),
                ));
            }
            for lt in undeclared_lifetimes(&p.ty, &lt_scope) {
                d.push_error(Diagnostic::new(
                    UndeclaredLifetime,
                    p.ty.source,
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
                f.meta.name_source,
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
                    p.source,
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
                d.push_error(validation_diagnostic(
                    e,
                    l.ty.source,
                    &f.meta,
                    format!("In function '{}', local '{}'", f.meta.name, l.name),
                ));
            }
            for lt in undeclared_lifetimes(&l.ty, &lt_scope) {
                d.push_error(Diagnostic::new(
                    UndeclaredLifetime,
                    l.ty.source,
                    format!(
                        "In function '{}', local '{}': undeclared lifetime {}",
                        f.meta.name, l.name, lt,
                    ),
                ));
            }
            if locals_map.contains_key(&l.name) {
                d.push_error(Diagnostic::new(
                    DuplicateLocalName,
                    l.source,
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
        let scope = func.meta.param_scope();
        let lt_scope = lifetime_scope(&func.meta.lifetime_params);
        for stmt in &block.statements {
            self.validate_stmt_embedded_types(func, block, stmt, &scope, &lt_scope, d);
            if let Err(e) = self.typecheck_statement(func, block, stmt, locals) {
                d.push_error(e);
            }
        }
        self.typecheck_terminator(func, block, locals, block_labels, d);
    }

    /// Validate every `Type` mentioned inside a statement's rvalues and
    /// operands — cast targets, enum-constr type args, fn-name type args
    /// — against the enclosing function's parameter scope. Decl-position
    /// types (params, locals) are already validated in `typecheck_function`;
    /// this closes the analogous gap for expression-embedded types.
    fn validate_stmt_embedded_types(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        scope: crate::mir::substructural::composition::ParamScope,
        lt_scope: &BTreeSet<Lifetime>,
        d: &mut Diagnostics,
    ) {
        let record = |ty: &Type, d: &mut Diagnostics| {
            if let Err(e) = self.validate_type(ty, scope) {
                d.push_error(
                    validation_diagnostic(
                        e,
                        ty.source,
                        &func.meta,
                        format!("In function '{}'", func.meta.name),
                    )
                    .in_block(&block.label),
                );
            }
            for lt in undeclared_lifetimes(ty, lt_scope) {
                d.push_error(
                    Diagnostic::new(
                        UndeclaredLifetime,
                        ty.source,
                        format!(
                            "In function '{}': undeclared lifetime {}",
                            func.meta.name, lt
                        ),
                    )
                    .in_block(&block.label),
                );
            }
        };
        let record_op = |op: &Operand, d: &mut Diagnostics| {
            if let Operand::Const(ConstVal::FnName(_, type_args)) = op {
                for ty in type_args {
                    record(ty, d);
                }
            }
        };
        match &stmt.kind {
            StatementKind::Assign(_, rvalue) => match rvalue {
                RValue::PtrCast(op, ty) => {
                    record_op(op, d);
                    record(ty, d);
                }
                RValue::EnumConstr(_, type_args, _, op) => {
                    for ty in type_args {
                        record(ty, d);
                    }
                    record_op(op, d);
                }
                RValue::Use(op) => record_op(op, d),
                RValue::ArrayLit(ops) => {
                    for op in ops {
                        record_op(op, d);
                    }
                }
                RValue::Ref(_, _) | RValue::RawRef(_) => {}
            },
            StatementKind::Call(target, args) => {
                record_op(target, d);
                for op in args {
                    record_op(op, d);
                }
            }
            StatementKind::Drop(_)
            | StatementKind::Unborrow(_)
            | StatementKind::RequireUninit(_) => {}
        }
    }

    fn typecheck_statement(
        &self,
        func: &Function,
        block: &BasicBlock,
        stmt: &Statement,
        locals: &IndexMap<String, Type>,
    ) -> Result<(), Diagnostic> {
        // Local helper: build a Diagnostic with statement context.
        let stmt_diag = |code, msg: String| -> Diagnostic {
            Diagnostic::new(code, stmt.source, msg)
                .in_function(&func.meta.name)
                .in_block(&block.label)
        };
        // Attach the current function/block to a Diagnostic produced
        // by an inner helper (which knows its code + span but not the
        // enclosing context).
        let with_context = |error: TypeResolutionError| -> Diagnostic {
            resolution_diagnostic(error, stmt.source, &func.meta, self)
                .in_function(&func.meta.name)
                .in_block(&block.label)
        };
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                let lhs_ty = self.type_of_place(place, locals).map_err(with_context)?;
                let rhs_ty = self
                    .type_of_rvalue(rvalue, stmt.source, locals)
                    .map_err(with_context)?;
                if !self.types_match(&lhs_ty, &rhs_ty) {
                    let mut format = DiagnosticFormat::new();
                    let scope = format.scope(&func.meta);
                    let lhs = format.ty(&scope, &lhs_ty);
                    let rhs = format.ty(&scope, &rhs_ty);
                    return Err(format.finish(stmt_diag(
                        AssignmentTypeMismatch,
                        format!(
                            "Type mismatch in assignment. LHS is {}, RHS is {}",
                            lhs, rhs
                        ),
                    )));
                }
                Ok(())
            }
            StatementKind::Call(target, args) => {
                let target_ty = self.type_of_operand(target, locals).map_err(with_context)?;

                if !matches!(&target_ty.kind, TypeKind::Fn(_)) {
                    return Err(format_type_diagnostic(&func.meta, &target_ty, |ty| {
                        stmt_diag(
                            CallTargetNotFunction,
                            format!("Call target is not a function type: {}", ty),
                        )
                    }));
                }
                let TypeKind::Fn(param_tys) = target_ty.kind else {
                    unreachable!("function type checked above")
                };

                if args.len() != param_tys.len() {
                    return Err(stmt_diag(
                        CallWrongArity,
                        format!(
                            "Wrong number of arguments for call. Expected {}, found {}",
                            param_tys.len(),
                            args.len()
                        ),
                    ));
                }
                for (i, (arg, param_ty)) in args.iter().zip(param_tys.iter()).enumerate() {
                    let arg_ty = self.type_of_operand(arg, locals).map_err(with_context)?;
                    if !self.types_match(param_ty, &arg_ty) {
                        let mut format = DiagnosticFormat::new();
                        let caller_scope = format.scope(&func.meta);
                        let expected = match target {
                            Operand::Const(ConstVal::FnName(name, _)) => {
                                if let Some(callee) = self.functions.get(name) {
                                    let callee_scope = format.scope(&callee.meta);
                                    format.ty(&callee_scope, param_ty)
                                } else {
                                    format.ty(&caller_scope, param_ty)
                                }
                            }
                            _ => format.ty(&caller_scope, param_ty),
                        };
                        let found = format.ty(&caller_scope, &arg_ty);
                        return Err(format.finish(stmt_diag(
                            CallArgTypeMismatch,
                            format!(
                                "Call argument {} type mismatch. Expected {}, found {}",
                                i, expected, found
                            ),
                        )));
                    }
                }
                Ok(())
            }
            StatementKind::Drop(place) => {
                // Just resolve the place — any legality (Drop,
                // currently init) is enforced by the substructural checker.
                self.type_of_place(place, locals).map_err(with_context)?;
                Ok(())
            }
            StatementKind::Unborrow(place) => {
                let ty = self.type_of_place(place, locals).map_err(with_context)?;
                if !matches!(&ty.kind, TypeKind::Ref(_, _, _)) {
                    return Err(format_type_diagnostic(&func.meta, &ty, |ty| {
                        stmt_diag(
                            UnborrowNonReference,
                            format!("unborrow requires a reference-typed place, found {}", ty),
                        )
                    }));
                }
                Ok(())
            }
            StatementKind::RequireUninit(place) => {
                self.type_of_place(place, locals).map_err(with_context)?;
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
        // Local helper: build a Diagnostic with terminator context.
        let terminator_diag = |code, msg: String| -> Diagnostic {
            Diagnostic::new(code, block.terminator.source, msg)
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
                match self.type_of_operand(cond, locals) {
                    Ok(cond_ty) if cond_ty.kind != TypeKind::Bool => {
                        d.push_error(format_type_diagnostic(&func.meta, &cond_ty, |ty| {
                            terminator_diag(
                                TypeCheckCode::BranchConditionNotBool,
                                format!("branch condition must be bool, found {}", ty),
                            )
                        }))
                    }
                    Ok(_) => {}
                    Err(error) => d.push_error(
                        resolution_diagnostic(error, block.terminator.source, &func.meta, self)
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
                let enum_decl: Option<&EnumDecl> = match self.type_of_place(place, locals) {
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
                            d.push_error(format_type_diagnostic(&func.meta, &ty, |ty| {
                                terminator_diag(
                                    TypeCheckCode::SwitchOnNonEnum,
                                    format!("switchEnum place must be an enum type, found {}", ty,),
                                )
                            }));
                            None
                        }
                    },
                    Err(error) => {
                        d.push_error(
                            resolution_diagnostic(error, block.terminator.source, &func.meta, self)
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
            d.push_error(format_type_diagnostic(&f.meta, &p.ty, |ty| {
                Diagnostic::new(
                    MainBadSignature,
                    p.source,
                    format!(
                        "In function 'main': single parameter must be '&out i32', found {}",
                        ty,
                    ),
                )
            }));
        }
        _ => {
            d.push_error(Diagnostic::new(
                MainBadSignature,
                f.meta.name_source,
                format!(
                    "In function 'main': takes at most one parameter (an optional '&out i32'), found {} parameters",
                    f.params.len()
                ),
            ));
        }
    }
}
