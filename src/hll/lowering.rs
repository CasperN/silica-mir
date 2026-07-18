use std::collections::HashMap;
use indexmap::IndexMap;
use crate::mir::ast as mir;
use crate::mir::helpers::*;
use crate::hll::ast as hll;
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};

/// Machine-readable code for each HLL → MIR lowering error kind.
///
/// All lowering-time errors are internal compiler errors — the well-
/// formed shape of the AST is a type_check post-condition, so anything
/// that lowering rejects is a bug in an earlier pass or in lowering
/// itself, not in user code. Diagnostics still carry the originating
/// `expr.span` so ICE reports point at the source that surfaced the
/// invariant violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HllLoweringCode {
    /// No entry in the per-expression type map. Type-check should have
    /// populated one for every expression it visited.
    MissingType,
    /// Binary op emitted on a non-numeric type. Type-check should have
    /// rejected this before lowering ran.
    BinaryOpNonNumeric,
    /// `match` scrutinee has a non-enum type.
    MatchTargetNotEnum,
    /// Match arm references an enum name with no declaration.
    EnumDeclMissing,
    /// Match arm references a variant not declared on the enum.
    EnumVariantMissing,
    /// `break` outside of any enclosing loop.
    BreakOutsideLoop,
    /// `continue` outside of any enclosing loop.
    ContinueOutsideLoop,
    /// Scope stack empty when a scope-relative operation ran (`defer`
    /// registration, `pop_and_emit_defers`). Internal invariant.
    ScopeStackUnderflow,
}

impl From<HllLoweringCode> for DiagCode {
    fn from(code: HllLoweringCode) -> DiagCode {
        DiagCode::HllLowering(code)
    }
}

fn diag(code: HllLoweringCode, span: mir::Span, msg: impl Into<String>) -> Diagnostic {
    Diagnostic::new(code, span, msg)
}

fn lookup_type<'a>(
    expr: &hll::Expr,
    types: &'a IndexMap<mir::Span, hll::Type>,
) -> Option<&'a hll::Type> {
    types.get(&expr.span)
}

/// Run HLL → MIR lowering. Any error is treated as an internal compiler
/// error and pushed into `d.internal_errors`; the caller decides
/// whether to continue.
pub fn run_lowering(
    program: &hll::Program,
    types: &IndexMap<mir::Span, hll::Type>,
    d: &mut Diagnostics,
) -> Option<mir::Program> {
    match lower_program(program, types) {
        Ok(p) => Some(p),
        Err(diag) => {
            d.push_internal_error(diag);
            None
        }
    }
}

struct Scope {
    defers: Vec<hll::Expr>,
    is_loop: bool,
}

struct LowerCtx {
    locals: Vec<mir::Local>,
    blocks: Vec<mir::BasicBlock>,
    current_block_label: Option<String>,
    current_statements: Vec<(mir::Statement, mir::Span)>,
    temp_counter: usize,
    block_counter: usize,
    loop_stack: Vec<(String, String, mir::Place)>, // (start_label, end_label, dest_place)
    scopes: Vec<Scope>,
    functions: HashMap<String, hll::FnDecl>,
    enums: HashMap<String, hll::EnumDecl>,
}

impl LowerCtx {
    fn new(program: &hll::Program) -> Self {
        let mut functions = HashMap::new();
        let mut enums = HashMap::new();
        for decl in &program.declarations {
            match decl {
                hll::Declaration::Fn(f) => {
                    functions.insert(f.name.clone(), f.clone());
                }
                hll::Declaration::Enum(e) => {
                    enums.insert(e.name.clone(), e.clone());
                }
                _ => {}
            }
        }
        Self {
            locals: Vec::new(),
            blocks: Vec::new(),
            current_block_label: None,
            current_statements: Vec::new(),
            temp_counter: 0,
            block_counter: 0,
            loop_stack: Vec::new(),
            scopes: Vec::new(),
            functions,
            enums,
        }
    }

    fn push_scope(&mut self, is_loop: bool) {
        self.scopes.push(Scope {
            defers: Vec::new(),
            is_loop,
        });
    }

    fn pop_and_emit_defers(&mut self, types: &IndexMap<mir::Span, hll::Type>) -> Result<(), Diagnostic> {
        let scope = self.scopes.pop().ok_or_else(|| {
            diag(
                HllLoweringCode::ScopeStackUnderflow,
                mir::Span::default(),
                "pop_and_emit_defers called with empty scope stack",
            )
        })?;
        for defer_expr in scope.defers.into_iter().rev() {
            let unit_temp = self.fresh_temp(unit_ty(), defer_expr.span);
            lower_expr_into(self, &defer_expr, &unit_temp, types)?;
        }
        Ok(())
    }

    fn emit_defers_to_depth(&mut self, depth: usize, types: &IndexMap<mir::Span, hll::Type>) -> Result<(), Diagnostic> {
        let mut defers = Vec::new();
        for i in (depth..self.scopes.len()).rev() {
            for defer_expr in self.scopes[i].defers.iter().rev() {
                defers.push(defer_expr.clone());
            }
        }
        for defer_expr in defers {
            let unit_temp = self.fresh_temp(unit_ty(), defer_expr.span);
            lower_expr_into(self, &defer_expr, &unit_temp, types)?;
        }
        Ok(())
    }

    fn fresh_temp(&mut self, ty: mir::Type, span: mir::Span) -> mir::Place {
        let name = format!("_temp_{}", self.temp_counter);
        self.temp_counter += 1;
        self.locals.push(mir::Local {
            name: name.clone(),
            ty,
            span,
        });
        var_place(name)
    }

    fn fresh_label(&mut self, prefix: &str) -> String {
        let label = format!("{}_{}", prefix, self.block_counter);
        self.block_counter += 1;
        label
    }

    fn start_block(&mut self, label: String) {
        assert!(self.current_block_label.is_none());
        self.current_block_label = Some(label);
        self.current_statements.clear();
    }

    fn terminate_block(&mut self, term: mir::Terminator, span: mir::Span) {
        if let Some(label) = self.current_block_label.take() {
            self.blocks.push(mir::BasicBlock {
                label,
                label_span: span,
                statements: std::mem::take(&mut self.current_statements),
                terminator: term,
                terminator_span: span,
            });
        }
    }

    fn emit_statement(&mut self, stmt: mir::Statement, span: mir::Span) {
        if self.current_block_label.is_some() {
            self.current_statements.push((stmt, span));
        }
    }
}

/// HLL and MIR `TypeParam` have identical shape; this is a
/// straight per-field copy.
fn lower_type_params(params: &[hll::TypeParam]) -> Vec<mir::TypeParam> {
    params
        .iter()
        .map(|p| mir::TypeParam {
            name: p.name.clone(),
            bounds: p.bounds.clone(),
            span: p.span,
        })
        .collect()
}

/// Recover the inferred type arguments at a generic-fn call site by
/// diffing the callee's freshened signature (recorded in `types` at
/// `fn_expr_span` by HLL type_check) against the fn's declared
/// signature.
///
/// For each declared type parameter T, find the first position where
/// T appears in the declared signature (params or return type), then
/// read the corresponding fresh type at the same position. Non-generic
/// fns yield an empty vec.
fn infer_fn_type_args(
    f_decl: &hll::FnDecl,
    fn_expr_span: mir::Span,
    types: &IndexMap<mir::Span, hll::Type>,
) -> Vec<mir::Type> {
    if f_decl.type_params.is_empty() {
        return Vec::new();
    }
    let Some(hll::Type::Fn(fresh_params, fresh_ret)) = types.get(&fn_expr_span) else {
        return Vec::new();
    };
    f_decl
        .type_params
        .iter()
        .map(|tp| {
            for (decl, fresh) in f_decl.params.iter().map(|p| &p.ty).zip(fresh_params.iter()) {
                if let Some(t) = find_param_at(&tp.name, decl, fresh) {
                    return lower_type(&t);
                }
            }
            if let Some(t) = find_param_at(&tp.name, &f_decl.ret_ty, fresh_ret) {
                return lower_type(&t);
            }
            // Type param doesn't appear anywhere in the signature —
            // HLL type_check would have left it as an unresolved Var,
            // which resolve_default pins to i64. Fall back to unit
            // here rather than panicking; codegen doesn't handle Param
            // yet either, so this only matters once monomorphization
            // lands.
            mir::Type::Unit
        })
        .collect()
}

/// Walk `decl` and `fresh` in lockstep looking for `Type::Param(name)`
/// in `decl`. Returns the corresponding `fresh` subtype at the first
/// occurrence.
fn find_param_at(name: &str, decl: &hll::Type, fresh: &hll::Type) -> Option<hll::Type> {
    match (decl, fresh) {
        (hll::Type::Param(n), _) if n == name => Some(fresh.clone()),
        (hll::Type::Ref(_, a), hll::Type::Ref(_, b))
        | (hll::Type::RawPtr(a), hll::Type::RawPtr(b))
        | (hll::Type::Array(a, _), hll::Type::Array(b, _)) => find_param_at(name, a, b),
        (hll::Type::Fn(a_ps, a_r), hll::Type::Fn(b_ps, b_r)) => {
            for (a, b) in a_ps.iter().zip(b_ps.iter()) {
                if let Some(t) = find_param_at(name, a, b) {
                    return Some(t);
                }
            }
            find_param_at(name, a_r, b_r)
        }
        (hll::Type::Custom(_, a_args), hll::Type::Custom(_, b_args)) => {
            for (a, b) in a_args.iter().zip(b_args.iter()) {
                if let Some(t) = find_param_at(name, a, b) {
                    return Some(t);
                }
            }
            None
        }
        _ => None,
    }
}

fn lower_type(ty: &hll::Type) -> mir::Type {
    match ty {
        hll::Type::Int(t) => int_ty(*t),
        hll::Type::Float(t) => float_ty(*t),
        hll::Type::Bool => bool_ty(),
        hll::Type::Unit => unit_ty(),
        hll::Type::Never => never_ty(),
        hll::Type::Custom(name, args) => {
            let lowered_args: Vec<mir::Type> = args.iter().map(lower_type).collect();
            custom_ty_with_args(name.clone(), lowered_args)
        }
        hll::Type::Param(name) => param_ty(name.clone()),
        hll::Type::Ref(kind, inner) => ref_ty(*kind, lower_type(inner)),
        hll::Type::RawPtr(inner) => raw_ptr_ty(lower_type(inner)),
        hll::Type::Fn(params, ret) => {
            let mut mir_params: Vec<mir::Type> = params.iter().map(lower_type).collect();
            if **ret != hll::Type::Unit {
                mir_params.push(out_ref_ty(lower_type(ret)));
            }
            fn_ty(mir_params)
        }
        hll::Type::Array(inner, size) => array_ty(lower_type(inner), *size as u64),
        hll::Type::Var(_) | hll::Type::IntVar(_) | hll::Type::FloatVar(_) => unreachable!("type variables must be resolved before lowering"),
        hll::Type::Error => unreachable!("cannot lower program with type errors"),
    }
}

fn is_copy_type(ty: &mir::Type) -> bool {
    match ty {
        mir::Type::Int(_)
        | mir::Type::Float(_)
        | mir::Type::Bool
        | mir::Type::Unit
        | mir::Type::Never
        | mir::Type::Ref(_, _)
        | mir::Type::RawPtr(_) => true,
        mir::Type::Array(inner, _) => is_copy_type(inner),
        _ => false,
    }
}

fn lower_expr_to_place(
    ctx: &mut LowerCtx,
    expr: &hll::Expr,
    types: &IndexMap<mir::Span, hll::Type>,
) -> Result<mir::Place, Diagnostic> {
    match &expr.kind {
        hll::ExprKind::Variable(name) => Ok(mir::Place::Var(name.clone())),
        hll::ExprKind::FieldAccess(target, field) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(field_place(target_place, field.clone()))
        }
        hll::ExprKind::Downcast(target, variant) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(downcast_place(target_place, variant.clone()))
        }
        hll::ExprKind::Deref(target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(deref_place(target_place))
        }
        hll::ExprKind::ArrayIndex(target, index) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            let index_op = lower_expr_to_operand(ctx, index, types)?;
            Ok(index_place(target_place, index_op))
        }
        _ => {
            // Allocate a temporary and evaluate the expression into it
            let hll_ty = lookup_type(expr, types).ok_or_else(|| {
                diag(
                    HllLoweringCode::MissingType,
                    expr.span,
                    "missing type annotation for expression",
                )
            })?;
            let mir_ty = lower_type(hll_ty);
            let temp = ctx.fresh_temp(mir_ty, expr.span);
            lower_expr_into(ctx, expr, &temp, types)?;
            Ok(temp)
        }
    }
}

fn lower_expr_to_operand(
    ctx: &mut LowerCtx,
    expr: &hll::Expr,
    types: &IndexMap<mir::Span, hll::Type>,
) -> Result<mir::Operand, Diagnostic> {
    match &expr.kind {
        hll::ExprKind::Literal(lit) => {
            let const_val = match lit {
                hll::Literal::Int(val, suffix) => {
                    let ty = if let Some(s) = suffix {
                        *s
                    } else {
                        match lookup_type(expr, types) {
                            Some(hll::Type::Int(int_ty)) => *int_ty,
                            _ => mir::IntTy::I64,
                        }
                    };
                    int_const(*val as u64, ty)
                }
                hll::Literal::Float(val, suffix) => {
                    let ty = if let Some(s) = suffix {
                        *s
                    } else {
                        match lookup_type(expr, types) {
                            Some(hll::Type::Float(float_ty)) => *float_ty,
                            _ => mir::FloatTy::F64,
                        }
                    };
                    float_const(val.to_bits(), ty)
                }
                hll::Literal::Bool(val) => bool_const(*val),
                hll::Literal::Unit => unit_const(),
            };
            Ok(const_op(const_val))
        }
        hll::ExprKind::Variable(_)
        | hll::ExprKind::FieldAccess(_, _)
        | hll::ExprKind::Downcast(_, _)
        | hll::ExprKind::Deref(_)
        | hll::ExprKind::ArrayIndex(_, _) => {
            let place = lower_expr_to_place(ctx, expr, types)?;
            let hll_ty = lookup_type(expr, types).ok_or_else(|| {
                diag(
                    HllLoweringCode::MissingType,
                    expr.span,
                    "missing type annotation for variable/projection",
                )
            })?;
            let mir_ty = lower_type(hll_ty);
            if is_copy_type(&mir_ty) {
                Ok(copy_op(place))
            } else {
                Ok(move_op(place))
            }
        }
        _ => {
            // Evaluate into a temporary first, then move the temporary
            let place = lower_expr_to_place(ctx, expr, types)?;
            Ok(move_op(place))
        }
    }
}

fn lower_expr_into(
    ctx: &mut LowerCtx,
    expr: &hll::Expr,
    dest: &mir::Place,
    types: &IndexMap<mir::Span, hll::Type>,
) -> Result<(), Diagnostic> {
    match &expr.kind {
        hll::ExprKind::Literal(_)
        | hll::ExprKind::Variable(_)
        | hll::ExprKind::FieldAccess(_, _)
        | hll::ExprKind::Downcast(_, _)
        | hll::ExprKind::Deref(_)
        | hll::ExprKind::ArrayIndex(_, _) => {
            let op = lower_expr_to_operand(ctx, expr, types)?;
            ctx.emit_statement(
                assign_stmt(dest.clone(), use_rv(op)),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Borrow(kind, target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            ctx.emit_statement(
                assign_stmt(dest.clone(), ref_rv(*kind, target_place)),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::RawBorrow(target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            ctx.emit_statement(
                assign_stmt(dest.clone(), raw_ref_rv(target_place)),
                expr.span,
            );
            Ok(())
        }

        hll::ExprKind::Assign(lhs, rhs) => {
            let lhs_place = lower_expr_to_place(ctx, lhs, types)?;
            let rhs_op = lower_expr_to_operand(ctx, rhs, types)?;
            ctx.emit_statement(
                assign_stmt(lhs_place, use_rv(rhs_op)),
                expr.span,
            );
            // Assignment expression itself evaluates to Unit
            ctx.emit_statement(
                assign_stmt(dest.clone(), use_rv(const_op(unit_const()))),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Binary(lhs, op, rhs) => {
            let lhs_hll_ty = lookup_type(lhs, types).ok_or_else(|| {
                diag(
                    HllLoweringCode::MissingType,
                    lhs.span,
                    "missing type annotation for binary lhs",
                )
            })?;
            let mir_ty = lower_type(lhs_hll_ty);
            
            // Map BinOp to string name
            let op_name = match op {
                hll::BinOp::Add => "add",
                hll::BinOp::Sub => "sub",
                hll::BinOp::Mul => "mul",
                hll::BinOp::Div => "div",
                hll::BinOp::Rem => "rem",
                hll::BinOp::Eq => "eq",
                hll::BinOp::Ne => "ne",
                hll::BinOp::Lt => "lt",
                hll::BinOp::Le => "le",
                hll::BinOp::Gt => "gt",
                hll::BinOp::Ge => "ge",
            };
            
            let type_name = match &mir_ty {
                mir::Type::Int(int_ty) => int_ty.name(),
                mir::Type::Float(float_ty) => float_ty.name(),
                _ => return Err(diag(
                    HllLoweringCode::BinaryOpNonNumeric,
                    expr.span,
                    format!("binary op on non-numeric type {:?}", mir_ty),
                )),
            };
            
            let intrinsic_name = format!("${}_{}", type_name, op_name);
            let fn_op = const_op(fn_name_const(intrinsic_name));
            
            let lhs_op = lower_expr_to_operand(ctx, lhs, types)?;
            let rhs_op = lower_expr_to_operand(ctx, rhs, types)?;
            let mut arg_ops = vec![lhs_op, rhs_op];
            
            let hll_ret_ty = lookup_type(expr, types).ok_or_else(|| {
                diag(
                    HllLoweringCode::MissingType,
                    expr.span,
                    "missing type annotation for binary expression",
                )
            })?;
            
            let out_ref = out_ref_ty(lower_type(hll_ret_ty));
            let out_ref_place = ctx.fresh_temp(out_ref, expr.span);
            ctx.emit_statement(
                assign_stmt(out_ref_place.clone(), ref_rv(mir::RefKind::Out, dest.clone())),
                expr.span,
            );
            arg_ops.push(move_op(out_ref_place));
            ctx.emit_statement(call_stmt(fn_op, arg_ops), expr.span);
            Ok(())
        }
        hll::ExprKind::Call(fn_expr, args) => {
            let mut arg_ops = Vec::new();
            for arg in args {
                arg_ops.push(lower_expr_to_operand(ctx, arg, types)?);
            }

            // Lower fn_expr to operand. Direct function names lower to
            // a FnName const; for a generic fn, extract the inferred
            // type args by comparing the callee's typed signature
            // (`types[fn_expr.span]`, freshened by HLL type_check) to
            // the fn's declared signature.
            let fn_op = if let hll::ExprKind::Variable(ref name) = fn_expr.kind {
                if let Some(f_decl) = ctx.functions.get(name).cloned() {
                    let mir_type_args = infer_fn_type_args(&f_decl, fn_expr.span, types);
                    const_op(fn_name_const_with_args(name.clone(), mir_type_args))
                } else {
                    lower_expr_to_operand(ctx, fn_expr, types)?
                }
            } else {
                lower_expr_to_operand(ctx, fn_expr, types)?
            };

            // Check if call has return value (if dest type is not Unit)
            let hll_ret_ty = lookup_type(expr, types).ok_or_else(|| {
                diag(
                    HllLoweringCode::MissingType,
                    expr.span,
                    "missing type annotation for call",
                )
            })?;

            if *hll_ret_ty != hll::Type::Unit {
                // Return value is written to dest. In MIR, we pass &out dest as final argument.
                // The codegen expects Statement::Call(fn_op, args) where the last argument is evaluated.
                // Wait, in checkpoint 1:
                // "Translated Statement::Call to omit the last argument from the LLVM call arguments list, capture the return value register, and emit a store to the target address."
                // In LLVM codegen:
                // `let (_, ret_ptr_val) = arg_pairs.pop().expect(...)`
                // This means the last argument is indeed a pointer to the destination!
                // How is that reference created in MIR call?
                // It is created as a mutable/out borrow: `&out dest`!
                // So in MIR Statement::Call, we must pass a temporary reference to the destination!
                // Wait, how do we pass a reference as an operand?
                // An operand can only be Copy(Place), Move(Place), or Const.
                // It CANNOT be RValue::Ref!
                // So in MIR, we must allocate a temporary local `_temp_out_ref` of type `&out T`,
                // assign `_temp_out_ref = &out dest`,
                // and pass `Operand::Move(_temp_out_ref)` as the final argument in Statement::Call!
                // Yes! That is absolutely correct and matches MIR semantics perfectly!
                let out_ref = out_ref_ty(lower_type(hll_ret_ty));
                let out_ref_place = ctx.fresh_temp(out_ref, expr.span);
                ctx.emit_statement(
                    assign_stmt(out_ref_place.clone(), ref_rv(mir::RefKind::Out, dest.clone())),
                    expr.span,
                );
                arg_ops.push(move_op(out_ref_place));
                ctx.emit_statement(call_stmt(fn_op, arg_ops), expr.span);
            } else {
                ctx.emit_statement(call_stmt(fn_op, arg_ops), expr.span);
                // Function returns unit, assign Unit to dest
                ctx.emit_statement(
                    assign_stmt(dest.clone(), use_rv(const_op(unit_const()))),
                    expr.span,
                );
            }
            Ok(())
        }
        hll::ExprKind::Block(stmts, last_expr, _) => {
            ctx.push_scope(false);
            for stmt in stmts {
                match stmt {
                    hll::Stmt::Let { is_mut: _, name, ty: annot_ty, init, span } => {
                        // Type source: initializer's typed-slot when present,
                        // else the required annotation. type-check has already
                        // rejected the "no init and no annotation" case.
                        let hll_ty = match (init, annot_ty) {
                            (Some(init), _) => lookup_type(init, types),
                            (None, Some(annot)) => Some(annot),
                            (None, None) => None,
                        }
                        .ok_or_else(|| {
                            diag(
                                HllLoweringCode::MissingType,
                                *span,
                                "missing type for let binding",
                            )
                        })?;
                        let mir_ty = lower_type(hll_ty);
                        ctx.locals.push(mir::Local {
                            name: name.clone(),
                            ty: mir_ty,
                            span: *span,
                        });
                        if let Some(init) = init {
                            let dest = var_place(name.clone());
                            lower_expr_into(ctx, init, &dest, types)?;
                        }
                        // No init: the local exists as NeverInit — the caller
                        // must initialize it before use (init-state enforces).
                    }
                    hll::Stmt::Defer { body, span } => {
                        let scope = ctx.scopes.last_mut().ok_or_else(|| {
                            diag(
                                HllLoweringCode::ScopeStackUnderflow,
                                *span,
                                "defer registered with empty scope stack",
                            )
                        })?;
                        scope.defers.push(body.clone());
                    }
                    hll::Stmt::Expr(e) => {
                        // Value is ignored, lower into a dummy temporary matching the expr type
                        let hll_ty = lookup_type(e, types).cloned().unwrap_or(hll::Type::Unit);
                        let mir_ty = if hll_ty == hll::Type::Never {
                            mir::Type::Unit
                        } else {
                            lower_type(&hll_ty)
                        };
                        let dummy = ctx.fresh_temp(mir_ty, e.span);
                        lower_expr_into(ctx, e, &dummy, types)?;
                    }
                }
            }
            if let Some(last) = last_expr {
                lower_expr_into(ctx, last, dest, types)?;
            } else {
                ctx.emit_statement(
                    assign_stmt(dest.clone(), use_rv(const_op(unit_const()))),
                    expr.span,
                );
            }
            ctx.pop_and_emit_defers(types)?;
            Ok(())
        }
        hll::ExprKind::If(cond, true_block, false_block) => {
            let cond_op = lower_expr_to_operand(ctx, cond, types)?;
            let true_label = ctx.fresh_label("if_true");
            let false_label = ctx.fresh_label("if_false");
            let merge_label = ctx.fresh_label("if_merge");

            ctx.terminate_block(
                branch_term(cond_op, true_label.clone(), false_label.clone()),
                expr.span,
            );

            // True branch
            ctx.start_block(true_label);
            lower_expr_into(ctx, true_block, dest, types)?;
            ctx.terminate_block(goto_term(merge_label.clone()), expr.span);

            // False branch
            ctx.start_block(false_label);
            lower_expr_into(ctx, false_block, dest, types)?;
            ctx.terminate_block(goto_term(merge_label.clone()), expr.span);

            // Merge block
            ctx.start_block(merge_label);
            Ok(())
        }
        hll::ExprKind::Loop(body) => {
            let start_label = ctx.fresh_label("loop_start");
            let end_label = ctx.fresh_label("loop_end");

            ctx.terminate_block(goto_term(start_label.clone()), expr.span);

            ctx.loop_stack.push((start_label.clone(), end_label.clone(), dest.clone()));
            ctx.push_scope(true);
            ctx.start_block(start_label.clone());

            // Loop body value is discarded
            let dummy = ctx.fresh_temp(unit_ty(), body.span);
            lower_expr_into(ctx, body, &dummy, types)?;
            ctx.scopes.pop();
            ctx.terminate_block(goto_term(start_label), expr.span);

            ctx.loop_stack.pop();

            ctx.start_block(end_label);
            Ok(())
        }
        hll::ExprKind::Break(val_expr) => {
            let break_err = || diag(
                HllLoweringCode::BreakOutsideLoop,
                expr.span,
                "break outside of loop",
            );
            let (_, end_label, dest_place) = ctx.loop_stack.last().ok_or_else(break_err)?.clone();

            if let Some(val) = val_expr {
                lower_expr_into(ctx, val, &dest_place, types)?;
            }

            let loop_depth = ctx.scopes.iter().rposition(|s| s.is_loop).ok_or_else(break_err)?;
            ctx.emit_defers_to_depth(loop_depth, types)?;

            ctx.terminate_block(goto_term(end_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Continue => {
            let continue_err = || diag(
                HllLoweringCode::ContinueOutsideLoop,
                expr.span,
                "continue outside of loop",
            );
            let (start_label, _, _) = ctx.loop_stack.last().ok_or_else(continue_err)?.clone();

            let loop_depth = ctx.scopes.iter().rposition(|s| s.is_loop).ok_or_else(continue_err)?;
            ctx.emit_defers_to_depth(loop_depth, types)?;

            ctx.terminate_block(goto_term(start_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Return(val_expr) => {
            if let Some(val) = val_expr {
                // Return value is written to $return.*
                let ret_place = deref_place(var_place("$return"));
                lower_expr_into(ctx, val, &ret_place, types)?;
            }
            ctx.emit_defers_to_depth(0, types)?;
            ctx.terminate_block(return_term(), expr.span);
            Ok(())
        }
        hll::ExprKind::Match(target, arms) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            
            let mut cases = Vec::new();
            let mut case_labels = Vec::new();
            for (pattern, _) in arms {
                let hll::Pattern::Variant(variant, _) = pattern;
                let label = ctx.fresh_label(&format!("switch_{}", variant));
                cases.push((variant.clone(), label.clone()));
                case_labels.push(label);
            }
            
            let merge_label = ctx.fresh_label("switch_merge");
            
            ctx.terminate_block(
                switch_enum_term(target_place.clone(), cases),
                expr.span,
            );
            
            // Lower each arm block
            for ((pattern, body), label) in arms.iter().zip(case_labels.iter()) {
                let hll::Pattern::Variant(variant, bound_var) = pattern;
                ctx.start_block(label.clone());
                
                if let Some(var_name) = bound_var {
                    let target_hll_ty = lookup_type(target, types).ok_or_else(|| {
                        diag(
                            HllLoweringCode::MissingType,
                            target.span,
                            "missing type annotation for match target",
                        )
                    })?;
                    let (enum_is_copy, bound_var_mir_ty) = if let hll::Type::Custom(
                        ref enum_name,
                        ref args,
                    ) = target_hll_ty
                    {
                        let enum_decl = ctx.enums.get(enum_name).ok_or_else(|| {
                            diag(
                                HllLoweringCode::EnumDeclMissing,
                                target.span,
                                format!("undeclared enum '{}' in lowering", enum_name),
                            )
                        })?;
                        let variant_decl = enum_decl.variants.iter().find(|v| v.name == *variant).ok_or_else(|| {
                            diag(
                                HllLoweringCode::EnumVariantMissing,
                                body.span,
                                format!("enum '{}' has no variant '{}' in lowering", enum_name, variant),
                            )
                        })?;
                        // Substitute the enum's type params with the args
                        // at this use site (e.g. `Option<i64>` binds T := i64).
                        let mir_variant_ty = lower_type(&variant_decl.ty);
                        let mir_type_params = lower_type_params(&enum_decl.type_params);
                        let mir_args: Vec<mir::Type> = args.iter().map(lower_type).collect();
                        let payload_ty = crate::mir::type_util::substitute_params(
                            &mir_variant_ty,
                            &mir_type_params,
                            &mir_args,
                        );
                        let is_copy = enum_decl.markers.implies(mir::Marker::Copy);
                        (is_copy, payload_ty)
                    } else {
                        return Err(diag(
                            HllLoweringCode::MatchTargetNotEnum,
                            target.span,
                            format!("expected enum type for match target, found {:?}", target_hll_ty),
                        ));
                    };

                    ctx.locals.push(mir::Local {
                        name: var_name.clone(),
                        ty: bound_var_mir_ty.clone(),
                        span: body.span,
                    });

                    // Match arm payload extraction. Dispatch table (today):
                    //
                    //   scrutinee class   access mode        extraction
                    //   ---------------   ---------------   -------------------
                    //   Copy              owned/borrowed    copy scrut as V
                    //   Move (not Copy)   owned             move scrut as V
                    //   Move (not Copy)   borrowed          copy scrut as V
                    //
                    // The owned Move-only case uses `move` so init-state's
                    // enum-atomicity rule cascades the whole scrutinee to
                    // `Moved`; without it the scrutinee stays Init at the
                    // merge and (since Move-only is not Drop) trips
                    // SUB-ReturnValueLeak at return.
                    //
                    // Borrowed scrutinees can't be moved through (that
                    // would consume the pointee behind someone else's
                    // borrow), so those still copy — the payload copies
                    // out and the scrutinee stays live via its borrow.
                    //
                    // Future: when AutoClone / AutoTransfer (pure, non-
                    // trivial) and CoClone / CoTransfer (effectful)
                    // markers land, this switch grows arms that emit
                    // `call Clone::clone(&scrut as V, &out binding)` and
                    // `call Transfer::transfer(&drop scrut as V, &out
                    // binding)` in place of the bitwise ops. MIR stays
                    // mechanical (only `copy`/`move` primitives); HLL
                    // owns the class-marker dispatch.
                    let downcast = downcast_place(target_place.clone(), variant.clone());
                    let scrutinee_is_owned = mir::extract_path(&target_place).is_some();
                    let op = if enum_is_copy || !scrutinee_is_owned {
                        copy_op(downcast)
                    } else {
                        move_op(downcast)
                    };
                    ctx.emit_statement(
                        assign_stmt(var_place(var_name.clone()), use_rv(op)),
                        body.span,
                    );
                }
                
                lower_expr_into(ctx, body, dest, types)?;
                ctx.terminate_block(goto_term(merge_label.clone()), expr.span);
            }
            
            ctx.start_block(merge_label);
            Ok(())
        }
        hll::ExprKind::StructConstr(_, fields) => {
            for (field_name, value_expr) in fields {
                let field_dest = field_place(dest.clone(), field_name.clone());
                lower_expr_into(ctx, value_expr, &field_dest, types)?;
            }
            Ok(())
        }
        hll::ExprKind::EnumConstr(enum_name, variant_name, payload) => {
            let payload_op = lower_expr_to_operand(ctx, payload, types)?;
            // Extract inferred type args from the constructor's own
            // typed slot — HM already pinned them from the payload /
            // context. For a non-generic enum this is empty.
            let type_args = match types.get(&expr.span) {
                Some(hll::Type::Custom(_, args)) => args.iter().map(lower_type).collect(),
                _ => Vec::new(),
            };
            ctx.emit_statement(
                assign_stmt(
                    dest.clone(),
                    enum_constr_rv_with_args(
                        enum_name.clone(),
                        type_args,
                        variant_name.clone(),
                        payload_op,
                    ),
                ),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Array(elements) => {
            let mut ops = Vec::new();
            for el in elements {
                ops.push(lower_expr_to_operand(ctx, el, types)?);
            }
            ctx.emit_statement(
                assign_stmt(dest.clone(), array_lit_rv(ops)),
                expr.span,
            );
            Ok(())
        }
    }
}

pub fn lower_program(
    program: &hll::Program,
    types: &IndexMap<mir::Span, hll::Type>,
) -> Result<mir::Program, Diagnostic> {
    let mut declarations = Vec::new();
    
    for decl in &program.declarations {
        match decl {
            hll::Declaration::Struct(s) => {
                let fields = s.fields.iter().map(|f| mir::StructField {
                    name: f.name.clone(),
                    ty: lower_type(&f.ty),
                    span: f.span,
                }).collect();
                declarations.push(mir::Declaration::Struct(mir::StructDecl {
                    name: s.name.clone(),
                    name_span: s.span,
                    type_params: lower_type_params(&s.type_params),
                    markers: s.markers.clone(),
                    fields,
                }));
            }
            hll::Declaration::Enum(e) => {
                let variants = e.variants.iter().map(|v| mir::EnumVariant {
                    name: v.name.clone(),
                    ty: lower_type(&v.ty),
                    span: v.span,
                }).collect();
                declarations.push(mir::Declaration::Enum(mir::EnumDecl {
                    name: e.name.clone(),
                    name_span: e.span,
                    type_params: lower_type_params(&e.type_params),
                    markers: e.markers.clone(),
                    variants,
                }));
            }
            hll::Declaration::Fn(f) => {
                let mut params: Vec<mir::Param> = f.params.iter().map(|p| mir::Param {
                    name: p.name.clone(),
                    ty: lower_type(&p.ty),
                    span: p.span,
                }).collect();

                // If return type is not Unit, append $return parameter
                if f.ret_ty != hll::Type::Unit {
                    params.push(mir::Param {
                        name: "$return".to_string(),
                        ty: out_ref_ty(lower_type(&f.ret_ty)),
                        span: f.span,
                    });
                }

                // Extern declarations: no body to lower; MIR carries
                // extern-ness via `is_extern: true` and `body: None`.
                // The ABI string (`f.abi`) is preserved in HLL but
                // dropped here — MIR codegen currently ignores it (see
                // punchlist). When codegen wires the ABI through,
                // Function will grow an `abi: Option<String>` field
                // and this call site will pass `f.abi.clone()`.
                let Some(body_expr) = &f.body else {
                    declarations.push(mir::Declaration::Fn(mir::Function {
                        name: f.name.clone(),
                        name_span: f.span,
                        is_extern: true,
                        type_params: lower_type_params(&f.type_params),
                        params,
                        body: None,
                    }));
                    continue;
                };

                let mut ctx = LowerCtx::new(program);

                let start_label = "entry".to_string();
                ctx.start_block(start_label);

                // Lower body block into ctx
                // Since body is a block/expression, we lower it.
                // If return type is not Unit, we write the result to $return.*.
                // Otherwise we write it to a dummy Unit place.
                if f.ret_ty != hll::Type::Unit {
                    let ret_place = deref_place(var_place("$return"));
                    lower_expr_into(&mut ctx, body_expr, &ret_place, types)?;
                } else {
                    let dummy = ctx.fresh_temp(unit_ty(), body_expr.span);
                    lower_expr_into(&mut ctx, body_expr, &dummy, types)?;
                }

                // If the entry block or last block hasn't been terminated, terminate it with Return
                if ctx.current_block_label.is_some() {
                    ctx.terminate_block(return_term(), f.span);
                }

                declarations.push(mir::Declaration::Fn(mir::Function {
                    name: f.name.clone(),
                    name_span: f.span,
                    is_extern: false,
                    type_params: lower_type_params(&f.type_params),
                    params,
                    body: Some(mir::FunctionBody {
                        locals: ctx.locals,
                        blocks: ctx.blocks,
                    }),
                }));
            }
        }
    }

    Ok(mir::Program { declarations, source: program.source.clone() })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::parser::Parser;
    use crate::hll::type_check::typecheck_program_collect;
    use crate::diagnostics::Diagnostics;
    use crate::mir::pretty_print::pretty_print;

    fn lower_source(source: &str) -> String {
        let hll_prog = Parser::new(source).parse().unwrap_or_else(|d| {
            panic!(
                "parse error:\n{}\n--- source ---\n{}",
                d.errors_str().join("\n"),
                source
            )
        });
        let mut tc_d = Diagnostics::default();
        let types = typecheck_program_collect(&hll_prog, &mut tc_d);
        if tc_d.has_errors() {
            panic!("typecheck error:\n{}\n--- source ---\n{}", tc_d.errors_str().join("\n"), source);
        }
        let mir_prog = lower_program(&hll_prog, &types).unwrap();

        // Run MIR typecheck sanity check on the lowered program
        let (env, env_errs) = crate::mir::type_check::Env::build(&mir_prog);
        if !env_errs.is_empty() {
            panic!("MIR Env build failed on lowered program: {:?}", env_errs);
        }
        let mut d = crate::Diagnostics::default();
        env.typecheck(&mut d);
        if d.has_errors() {
            panic!("MIR typecheck failed on lowered program: {:?}", d.errors_str());
        }

        pretty_print(&mir_prog)
    }

    fn assert_lower_eq(source: &str, expected_mir: &str) {
        let actual = lower_source(source);
        let actual_clean: Vec<&str> = actual.lines().map(|l| l.trim()).filter(|l| !l.is_empty()).collect();
        let expected_clean: Vec<&str> = expected_mir.lines().map(|l| l.trim()).filter(|l| !l.is_empty()).collect();
        assert_eq!(actual_clean, expected_clean);
    }

    #[test]
    fn test_lower_fn_decl() {
        let source = "
            fn add(a: i64, b: i64) -> i64 {
                let mut sum = a;
                sum = b;
                sum
            }
        ";
        assert_lower_eq(
            source,
            "
            fn add(a: i64, b: i64, $return: &out i64) {
              sum: i64;
              _temp_0: unit;
              entry:
                sum = copy a;
                sum = copy b;
                _temp_0 = unit;
                $return.* = copy sum;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_struct_and_field_access() {
        let source = "
            struct Point: Copy + Drop { x: i64, y: i64 }
            fn get_x(p: Point) -> i64 {
                let x = p.x;
                x
            }
        ";
        assert_lower_eq(
            source,
            "
            struct Point: Copy + Drop {
              x: i64
              y: i64
            }

            fn get_x(p: Point, $return: &out i64) {
              x: i64;
              entry:
                x = copy p.x;
                $return.* = copy x;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_match() {
        let source = "
            enum Option: Copy + Drop { None: unit, Some: i64 }
            fn match_val(v: Option) -> i64 {
                v match {
                    Some(val) => val,
                    None => 0
                }
            }
        ";
        assert_lower_eq(
            source,
            "
            enum Option: Copy + Drop {
              None: unit
              Some: i64
            }

            fn match_val(v: Option, $return: &out i64) {
              val: i64;
              entry:
                switchEnum(v) [Some: switch_Some_0, None: switch_None_1]
              switch_Some_0:
                val = copy v as Some;
                $return.* = copy val;
                goto switch_merge_2
              switch_None_1:
                $return.* = 0;
                goto switch_merge_2
              switch_merge_2:
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_loop_break_value() {
        let source = "
            fn check() -> i64 {
                let mut x = 0;
                loop {
                    x = 42;
                    break x;
                }
            }
        ";
        assert_lower_eq(
            source,
            "
            fn check($return: &out i64) {
              x: i64;
              _temp_0: unit;
              _temp_1: unit;
              _temp_2: unit;
              entry:
                x = 0;
                goto loop_start_0
              loop_start_0:
                x = 42;
                _temp_1 = unit;
                $return.* = copy x;
                goto loop_end_1
              loop_end_1:
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_if_without_else() {
        let source = "
            fn check(cond: bool) {
                if cond {
                    let a = 1;
                }
            }
        ";
        assert_lower_eq(
            source,
            "
            fn check(cond: bool) {
              _temp_0: unit;
              a: i64;
              entry:
                branch(copy cond) [true: if_true_0, false: if_false_1]
              if_true_0:
                a = 1;
                _temp_0 = unit;
                goto if_merge_2
              if_false_1:
                _temp_0 = unit;
                goto if_merge_2
              if_merge_2:
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_constructors_and_arrays() {
        let source = "
            struct Point: Copy + Drop { x: i64, y: i64 }
            enum Option: Copy + Drop { None: unit, Some: i64 }
            fn check(arr: [i64; 3]) -> i64 {
                let p = Point { x: 1, y: 2 };
                let o = Option::Some(42);
                let a = [1, 2, 3];
                let val = arr[0];
                val
            }
        ";
        assert_lower_eq(
            source,
            "
            struct Point: Copy + Drop {
              x: i64
              y: i64
            }

            enum Option: Copy + Drop {
              None: unit
              Some: i64
            }

            fn check(arr: [i64; 3], $return: &out i64) {
              p: Point;
              o: Option;
              a: [i64; 3];
              val: i64;
              entry:
                p.x = 1;
                p.y = 2;
                o = Option::Some(42);
                a = [1, 2, 3];
                val = copy arr[0];
                $return.* = copy val;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_recursive_tree_search() {
        let source = "
            struct Node: Copy + Drop {
                value: i64,
                left: Tree,
                right: Tree
            }
            enum Tree: Copy + Drop {
                Empty: unit,
                Node: *Node
            }
            fn search_tree(tree: Tree, target: i64) -> bool {
                tree match {
                    Empty(u) => false,
                    Node(n) => unsafe {
                        let val = n.*.value;
                        if is_equal(val, target) {
                            true
                        } else {
                            if is_greater(val, target) {
                                search_tree(n.*.left, target)
                            } else {
                                search_tree(n.*.right, target)
                            }
                        }
                    }
                }
            }
            fn is_equal(x: i64, y: i64) -> bool {
                true
            }
            fn is_greater(x: i64, y: i64) -> bool {
                true
            }
        ";
        assert_lower_eq(
            source,
            "
            struct Node: Copy + Drop {
              value: i64
              left: Tree
              right: Tree
            }

            enum Tree: Copy + Drop {
              Empty: unit
              Node: *Node
            }

            fn search_tree(tree: Tree, target: i64, $return: &out bool) {
              u: unit;
              n: *Node;
              val: i64;
              _temp_0: bool;
              _temp_1: &out bool;
              _temp_2: bool;
              _temp_3: &out bool;
              _temp_4: &out bool;
              _temp_5: &out bool;
              entry:
                switchEnum(tree) [Empty: switch_Empty_0, Node: switch_Node_1]
              switch_Empty_0:
                u = copy tree as Empty;
                $return.* = false;
                goto switch_merge_2
              switch_Node_1:
                n = copy tree as Node;
                val = copy n.*.value;
                _temp_1 = &out _temp_0;
                call is_equal(copy val, copy target, move _temp_1);
                branch(move _temp_0) [true: if_true_3, false: if_false_4]
              if_true_3:
                $return.* = true;
                goto if_merge_5
              if_false_4:
                _temp_3 = &out _temp_2;
                call is_greater(copy val, copy target, move _temp_3);
                branch(move _temp_2) [true: if_true_6, false: if_false_7]
              if_true_6:
                _temp_4 = &out $return.*;
                call search_tree(move n.*.left, copy target, move _temp_4);
                goto if_merge_8
              if_false_7:
                _temp_5 = &out $return.*;
                call search_tree(move n.*.right, copy target, move _temp_5);
                goto if_merge_8
              if_merge_8:
                goto if_merge_5
              if_merge_5:
                goto switch_merge_2
              switch_merge_2:
                return
            }

            fn is_equal(x: i64, y: i64, $return: &out bool) {
              entry:
                $return.* = true;
                return
            }

            fn is_greater(x: i64, y: i64, $return: &out bool) {
              entry:
                $return.* = true;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_binary_expression() {
        let source = "
            fn check(a: i64, b: i64) -> bool {
                let x = a + b * 2;
                x < 10
            }
        ";
        assert_lower_eq(
            source,
            "
            fn check(a: i64, b: i64, $return: &out bool) {
              x: i64;
              _temp_0: i64;
              _temp_1: &out i64;
              _temp_2: &out i64;
              _temp_3: &out bool;
              entry:
                _temp_1 = &out _temp_0;
                call $i64_mul(copy b, 2, move _temp_1);
                _temp_2 = &out x;
                call $i64_add(copy a, move _temp_0, move _temp_2);
                _temp_3 = &out $return.*;
                call $i64_lt(copy x, 10, move _temp_3);
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_binary_expression_with_untyped_literals() {
        let source = "
            fn check(a: u32) -> u32 {
                a + 1
            }
        ";
        assert_lower_eq(
            source,
            "
            fn check(a: u32, $return: &out u32) {
              _temp_0: &out u32;
              entry:
                _temp_0 = &out $return.*;
                call $u32_add(copy a, 1u32, move _temp_0);
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_binary_expression_with_never() {
        let source = "
            fn check(a: i64) -> i64 {
                a + return 1
            }
        ";
        assert_lower_eq(
            source,
            "
            fn check(a: i64, $return: &out i64) {
              _temp_0: never;
              _temp_1: &out i64;
              entry:
                $return.* = 1;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_struct_marker_combinations() {
        // No markers (linear)
        assert_lower_eq(
            "
            struct Foo { x: i64 }
            ",
            "
            struct Foo {
              x: i64
            }
            "
        );

        // Copy marker only
        assert_lower_eq(
            "
            struct Foo: Copy { x: i64 }
            ",
            "
            struct Foo: Copy {
              x: i64
            }
            "
        );

        // Drop marker only
        assert_lower_eq(
            "
            struct Foo: Drop { x: i64 }
            ",
            "
            struct Foo: Drop {
              x: i64
            }
            "
        );
        // Two markers, Drop + Move
        assert_lower_eq(
            "
            struct Foo: Drop + Move { x: i64 }
            ",
            "
            struct Foo: Drop + Move {
              x: i64
            }
            "
        );

        // Move marker only.
        assert_lower_eq(
            "
            struct Foo: Move { x: i64 }
            ",
            "
            struct Foo: Move {
              x: i64
            }
            "
        );
    }

    #[test]
    fn test_lower_defer_lifo() {
        let source = "
            fn f(res: &out i64) {
                let mut x = 1;
                {
                    defer x = 10;
                    defer x = 20;
                };
                res.* = x;
            }
        ";
        assert_lower_eq(
            source,
            "
            fn f(res: &out i64) {
              _temp_0: unit;
              x: i64;
              _temp_1: unit;
              _temp_2: unit;
              _temp_3: unit;
              _temp_4: unit;
              entry:
                x = 1;
                _temp_1 = unit;
                x = 20;
                _temp_2 = unit;
                x = 10;
                _temp_3 = unit;
                res.* = copy x;
                _temp_4 = unit;
                _temp_0 = unit;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_defer_return() {
        let source = "
            fn f(x: &mut i64) -> i64 {
                defer x.* = 100;
                x.*
            }
        ";
        assert_lower_eq(
            source,
            "
            fn f(x: &mut i64, $return: &out i64) {
              _temp_0: unit;
              entry:
                $return.* = copy x.*;
                x.* = 100;
                _temp_0 = unit;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_defer_nested() {
        let source = "
            fn f(res: &out i64) {
                let mut x = 1;
                defer {
                    x = 10;
                    defer x = 20;
                    x = 30;
                };
                res.* = x;
            }
        ";
        assert_lower_eq(
            source,
            "
            fn f(res: &out i64) {
              _temp_0: unit;
              x: i64;
              _temp_1: unit;
              _temp_2: unit;
              _temp_3: unit;
              _temp_4: unit;
              _temp_5: unit;
              entry:
                x = 1;
                res.* = copy x;
                _temp_1 = unit;
                _temp_0 = unit;
                x = 10;
                _temp_3 = unit;
                x = 30;
                _temp_4 = unit;
                _temp_2 = unit;
                x = 20;
                _temp_5 = unit;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_defer_loop_break_continue() {
        let source = "
            fn f(res: &out i64) {
                let mut x = 0;
                loop {
                    defer x = (x + 1);
                    if true {
                        break;
                    }
                };
                res.* = x;
            }
        ";
        assert_lower_eq(
            source,
            "
            fn f(res: &out i64) {
              _temp_0: unit;
              x: i64;
              _temp_1: unit;
              _temp_2: unit;
              _temp_3: unit;
              _temp_4: unit;
              _temp_5: i64;
              _temp_6: &out i64;
              _temp_7: unit;
              _temp_8: i64;
              _temp_9: &out i64;
              _temp_10: unit;
              entry:
                x = 0;
                goto loop_start_0
              loop_start_0:
                branch(true) [true: if_true_2, false: if_false_3]
              if_true_2:
                _temp_6 = &out _temp_5;
                call $i64_add(copy x, 1, move _temp_6);
                x = move _temp_5;
                _temp_4 = unit;
                goto loop_end_1
              if_false_3:
                _temp_2 = unit;
                goto if_merge_4
              if_merge_4:
                _temp_9 = &out _temp_8;
                call $i64_add(copy x, 1, move _temp_9);
                x = move _temp_8;
                _temp_7 = unit;
                goto loop_start_0
              loop_end_1:
                res.* = copy x;
                _temp_10 = unit;
                _temp_0 = unit;
                return
            }
            "
        );
    }
}









