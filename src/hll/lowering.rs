use std::collections::HashMap;
use crate::mir::ast as mir;
use crate::hll::ast as hll;
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};

/// Machine-readable code for each HLL → MIR lowering error kind.
///
/// All lowering-time errors are internal compiler errors — the well-
/// formed shape of the AST is a type_check post-condition, so anything
/// that lowering rejects is a bug in an earlier pass or in lowering
/// itself, not in user code. Currently one code covers all of them; a
/// finer taxonomy can be introduced when the underlying error sites
/// grow richer context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HllLoweringCode {
    /// Catch-all for internal invariants that lowering enforces
    /// (missing type-map entry, missing decl, redundant safety-net
    /// pattern-match arm, etc.).
    Generic,
}

impl From<HllLoweringCode> for DiagCode {
    fn from(code: HllLoweringCode) -> DiagCode {
        DiagCode::HllLowering(code)
    }
}

/// Run HLL → MIR lowering. Any error is treated as an internal compiler
/// error and pushed into `d.internal_errors`; the caller decides
/// whether to continue.
pub fn run_lowering(
    program: &hll::Program,
    types: &HashMap<*const hll::Expr, hll::Type>,
    d: &mut Diagnostics,
) -> Option<mir::Program> {
    match lower_program(program, types) {
        Ok(p) => Some(p),
        Err(msg) => {
            d.push_internal_error(Diagnostic::new(
                HllLoweringCode::Generic,
                mir::Span::default(),
                msg,
            ));
            None
        }
    }
}

struct LowerCtx {
    locals: Vec<mir::Local>,
    blocks: Vec<mir::BasicBlock>,
    current_block_label: Option<String>,
    current_statements: Vec<(mir::Statement, mir::Span)>,
    temp_counter: usize,
    block_counter: usize,
    loop_stack: Vec<(String, String, mir::Place)>, // (start_label, end_label, dest_place)
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
            functions,
            enums,
        }
    }

    fn fresh_temp(&mut self, ty: mir::Type, span: mir::Span) -> mir::Place {
        let name = format!("_temp_{}", self.temp_counter);
        self.temp_counter += 1;
        self.locals.push(mir::Local {
            name: name.clone(),
            ty,
            span,
        });
        mir::Place::Var(name)
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

fn lower_type(ty: &hll::Type) -> mir::Type {
    match ty {
        hll::Type::Int(t) => mir::Type::Int(*t),
        hll::Type::Float(t) => mir::Type::Float(*t),
        hll::Type::Bool => mir::Type::Bool,
        hll::Type::Unit => mir::Type::Unit,
        hll::Type::Never => mir::Type::Never,
        hll::Type::Custom(name) => mir::Type::Custom(name.clone()),
        hll::Type::Ref(kind, inner) => mir::Type::Ref(*kind, Box::new(lower_type(inner))),
        hll::Type::RawPtr(inner) => mir::Type::RawPtr(Box::new(lower_type(inner))),
        hll::Type::Fn(params, ret) => {
            let mut mir_params: Vec<mir::Type> = params.iter().map(lower_type).collect();
            if **ret != hll::Type::Unit {
                mir_params.push(mir::Type::Ref(mir::RefKind::Out, Box::new(lower_type(ret))));
            }
            mir::Type::Fn(mir_params)
        }
        hll::Type::Array(inner, size) => mir::Type::Array(Box::new(lower_type(inner)), *size as u64),
        hll::Type::Var(_) => unreachable!("type variables must be resolved before lowering"),
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
    types: &HashMap<*const hll::Expr, hll::Type>,
) -> Result<mir::Place, String> {
    match &expr.kind {
        hll::ExprKind::Variable(name) => Ok(mir::Place::Var(name.clone())),
        hll::ExprKind::FieldAccess(target, field) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(mir::Place::Field(Box::new(target_place), field.clone()))
        }
        hll::ExprKind::Downcast(target, variant) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(mir::Place::Downcast(Box::new(target_place), variant.clone()))
        }
        hll::ExprKind::Deref(target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            Ok(mir::Place::Deref(Box::new(target_place)))
        }
        hll::ExprKind::ArrayIndex(target, index) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            let index_op = lower_expr_to_operand(ctx, index, types)?;
            Ok(mir::Place::Index(Box::new(target_place), Box::new(index_op)))
        }
        _ => {
            // Allocate a temporary and evaluate the expression into it
            let hll_ty = types.get(&(expr as *const hll::Expr)).ok_or_else(|| {
                format!("missing type annotation for expression at {:?}", expr.span)
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
    types: &HashMap<*const hll::Expr, hll::Type>,
) -> Result<mir::Operand, String> {
    match &expr.kind {
        hll::ExprKind::Literal(lit) => {
            let const_val = match lit {
                hll::Literal::Int(val, suffix) => {
                    let ty = if let Some(s) = suffix {
                        *s
                    } else {
                        match types.get(&(expr as *const hll::Expr)) {
                            Some(hll::Type::Int(int_ty)) => *int_ty,
                            _ => mir::IntTy::I64,
                        }
                    };
                    mir::ConstVal::Int {
                        bits: *val as u64,
                        ty,
                    }
                }
                hll::Literal::Float(val, suffix) => {
                    let ty = if let Some(s) = suffix {
                        *s
                    } else {
                        match types.get(&(expr as *const hll::Expr)) {
                            Some(hll::Type::Float(float_ty)) => *float_ty,
                            _ => mir::FloatTy::F64,
                        }
                    };
                    mir::ConstVal::Float {
                        bits: val.to_bits(),
                        ty,
                    }
                }
                hll::Literal::Bool(val) => mir::ConstVal::Bool(*val),
                hll::Literal::Unit => mir::ConstVal::Unit,
            };
            Ok(mir::Operand::Const(const_val))
        }
        hll::ExprKind::Variable(_)
        | hll::ExprKind::FieldAccess(_, _)
        | hll::ExprKind::Downcast(_, _)
        | hll::ExprKind::Deref(_)
        | hll::ExprKind::ArrayIndex(_, _) => {
            let place = lower_expr_to_place(ctx, expr, types)?;
            let hll_ty = types.get(&(expr as *const hll::Expr)).ok_or_else(|| {
                format!("missing type annotation for variable/projection at {:?}", expr.span)
            })?;
            let mir_ty = lower_type(hll_ty);
            if is_copy_type(&mir_ty) {
                Ok(mir::Operand::Copy(place))
            } else {
                Ok(mir::Operand::Move(place))
            }
        }
        _ => {
            // Evaluate into a temporary first, then move the temporary
            let place = lower_expr_to_place(ctx, expr, types)?;
            Ok(mir::Operand::Move(place))
        }
    }
}

fn lower_expr_into(
    ctx: &mut LowerCtx,
    expr: &hll::Expr,
    dest: &mir::Place,
    types: &HashMap<*const hll::Expr, hll::Type>,
) -> Result<(), String> {
    match &expr.kind {
        hll::ExprKind::Literal(_)
        | hll::ExprKind::Variable(_)
        | hll::ExprKind::FieldAccess(_, _)
        | hll::ExprKind::Downcast(_, _)
        | hll::ExprKind::Deref(_)
        | hll::ExprKind::ArrayIndex(_, _) => {
            let op = lower_expr_to_operand(ctx, expr, types)?;
            ctx.emit_statement(
                mir::Statement::Assign(dest.clone(), mir::RValue::Use(op)),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Borrow(kind, target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            ctx.emit_statement(
                mir::Statement::Assign(dest.clone(), mir::RValue::Ref(*kind, target_place)),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::RawBorrow(target) => {
            let target_place = lower_expr_to_place(ctx, target, types)?;
            ctx.emit_statement(
                mir::Statement::Assign(dest.clone(), mir::RValue::RawRef(target_place)),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Assign(lhs, rhs) => {
            let lhs_place = lower_expr_to_place(ctx, lhs, types)?;
            let rhs_op = lower_expr_to_operand(ctx, rhs, types)?;
            ctx.emit_statement(
                mir::Statement::Assign(lhs_place, mir::RValue::Use(rhs_op)),
                expr.span,
            );
            // Assignment expression itself evaluates to Unit
            ctx.emit_statement(
                mir::Statement::Assign(dest.clone(), mir::RValue::Use(mir::Operand::Const(mir::ConstVal::Unit))),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Binary(lhs, op, rhs) => {
            let lhs_hll_ty = types.get(&(lhs.as_ref() as *const hll::Expr)).ok_or_else(|| {
                format!("missing type annotation for binary LHS at {:?}", lhs.span)
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
                _ => return Err(format!("at {}: binary operations only supported on numeric types, found {:?}", expr.span, mir_ty)),
            };
            
            let intrinsic_name = format!("${}_{}", type_name, op_name);
            let fn_op = mir::Operand::Const(mir::ConstVal::FnName(intrinsic_name));
            
            let lhs_op = lower_expr_to_operand(ctx, lhs, types)?;
            let rhs_op = lower_expr_to_operand(ctx, rhs, types)?;
            let mut arg_ops = vec![lhs_op, rhs_op];
            
            let hll_ret_ty = types.get(&(expr as *const hll::Expr)).ok_or_else(|| {
                format!("missing type annotation for binary expression at {:?}", expr.span)
            })?;
            
            let ref_ty = mir::Type::Ref(mir::RefKind::Out, Box::new(lower_type(hll_ret_ty)));
            let out_ref_place = ctx.fresh_temp(ref_ty, expr.span);
            ctx.emit_statement(
                mir::Statement::Assign(out_ref_place.clone(), mir::RValue::Ref(mir::RefKind::Out, dest.clone())),
                expr.span,
            );
            arg_ops.push(mir::Operand::Move(out_ref_place));
            ctx.emit_statement(mir::Statement::Call(fn_op, arg_ops), expr.span);
            Ok(())
        }
        hll::ExprKind::Call(fn_expr, args) => {
            let mut arg_ops = Vec::new();
            for arg in args {
                arg_ops.push(lower_expr_to_operand(ctx, arg, types)?);
            }

            // Lower fn_expr to operand.
            // If it is a direct function name, we match it.
            let fn_op = if let hll::ExprKind::Variable(ref name) = fn_expr.kind {
                if ctx.functions.contains_key(name) {
                    mir::Operand::Const(mir::ConstVal::FnName(name.clone()))
                } else {
                    lower_expr_to_operand(ctx, fn_expr, types)?
                }
            } else {
                lower_expr_to_operand(ctx, fn_expr, types)?
            };

            // Check if call has return value (if dest type is not Unit)
            let hll_ret_ty = types.get(&(expr as *const hll::Expr)).ok_or_else(|| {
                format!("missing type annotation for call at {:?}", expr.span)
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
                let ref_ty = mir::Type::Ref(mir::RefKind::Out, Box::new(lower_type(hll_ret_ty)));
                let out_ref_place = ctx.fresh_temp(ref_ty, expr.span);
                ctx.emit_statement(
                    mir::Statement::Assign(out_ref_place.clone(), mir::RValue::Ref(mir::RefKind::Out, dest.clone())),
                    expr.span,
                );
                arg_ops.push(mir::Operand::Move(out_ref_place));
                ctx.emit_statement(mir::Statement::Call(fn_op, arg_ops), expr.span);
            } else {
                ctx.emit_statement(mir::Statement::Call(fn_op, arg_ops), expr.span);
                // Function returns unit, assign Unit to dest
                ctx.emit_statement(
                    mir::Statement::Assign(dest.clone(), mir::RValue::Use(mir::Operand::Const(mir::ConstVal::Unit))),
                    expr.span,
                );
            }
            Ok(())
        }
        hll::ExprKind::Block(stmts, last_expr) => {
            for stmt in stmts {
                match stmt {
                    hll::Stmt::Let { is_mut: _, name, ty: _, init, span } => {
                        let hll_ty = types.get(&(init as *const hll::Expr)).ok_or_else(|| {
                            format!("missing type annotation for let init at {:?}", init.span)
                        })?;
                        let mir_ty = lower_type(hll_ty);
                        ctx.locals.push(mir::Local {
                            name: name.clone(),
                            ty: mir_ty,
                            span: *span,
                        });
                        let var_place = mir::Place::Var(name.clone());
                        lower_expr_into(ctx, init, &var_place, types)?;
                    }
                    hll::Stmt::Expr(e) => {
                        // Value is ignored, lower into a dummy unit temporary
                        let dummy = ctx.fresh_temp(mir::Type::Unit, e.span);
                        lower_expr_into(ctx, e, &dummy, types)?;
                    }
                }
            }
            if let Some(last) = last_expr {
                lower_expr_into(ctx, last, dest, types)?;
            } else {
                ctx.emit_statement(
                    mir::Statement::Assign(dest.clone(), mir::RValue::Use(mir::Operand::Const(mir::ConstVal::Unit))),
                    expr.span,
                );
            }
            Ok(())
        }
        hll::ExprKind::If(cond, true_block, false_block) => {
            let cond_op = lower_expr_to_operand(ctx, cond, types)?;
            let true_label = ctx.fresh_label("if_true");
            let false_label = ctx.fresh_label("if_false");
            let merge_label = ctx.fresh_label("if_merge");

            ctx.terminate_block(
                mir::Terminator::Branch {
                    cond: cond_op,
                    true_label: true_label.clone(),
                    false_label: false_label.clone(),
                },
                expr.span,
            );

            // True branch
            ctx.start_block(true_label);
            lower_expr_into(ctx, true_block, dest, types)?;
            ctx.terminate_block(mir::Terminator::Goto(merge_label.clone()), expr.span);

            // False branch
            ctx.start_block(false_label);
            lower_expr_into(ctx, false_block, dest, types)?;
            ctx.terminate_block(mir::Terminator::Goto(merge_label.clone()), expr.span);

            // Merge block
            ctx.start_block(merge_label);
            Ok(())
        }
        hll::ExprKind::Loop(body) => {
            let start_label = ctx.fresh_label("loop_start");
            let end_label = ctx.fresh_label("loop_end");

            ctx.terminate_block(mir::Terminator::Goto(start_label.clone()), expr.span);

            ctx.loop_stack.push((start_label.clone(), end_label.clone(), dest.clone()));
            ctx.start_block(start_label);
            
            // Loop body value is discarded
            let dummy = ctx.fresh_temp(mir::Type::Unit, body.span);
            lower_expr_into(ctx, body, &dummy, types)?;
            ctx.terminate_block(mir::Terminator::Goto(ctx.loop_stack.last().unwrap().0.clone()), expr.span);

            ctx.loop_stack.pop();

            ctx.start_block(end_label);
            Ok(())
        }
        hll::ExprKind::Break(val_expr) => {
            let (_, end_label, dest_place) = ctx.loop_stack.last().ok_or_else(|| {
                format!("at {}: break outside of loop", expr.span)
            })?.clone();

            if let Some(val) = val_expr {
                lower_expr_into(ctx, val, &dest_place, types)?;
            }

            ctx.terminate_block(mir::Terminator::Goto(end_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Continue => {
            let (start_label, _, _) = ctx.loop_stack.last().ok_or_else(|| {
                format!("at {}: continue outside of loop", expr.span)
            })?.clone();

            ctx.terminate_block(mir::Terminator::Goto(start_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Return(val_expr) => {
            if let Some(val) = val_expr {
                // Return value is written to $return.*
                let ret_place = mir::Place::Deref(Box::new(mir::Place::Var("$return".to_string())));
                lower_expr_into(ctx, val, &ret_place, types)?;
            }
            ctx.terminate_block(mir::Terminator::Return, expr.span);
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
                mir::Terminator::SwitchEnum {
                    place: target_place.clone(),
                    cases,
                },
                expr.span,
            );
            
            // Lower each arm block
            for ((pattern, body), label) in arms.iter().zip(case_labels.iter()) {
                let hll::Pattern::Variant(variant, bound_var) = pattern;
                ctx.start_block(label.clone());
                
                if let Some(var_name) = bound_var {
                    let target_hll_ty = types.get(&(&**target as *const hll::Expr)).ok_or_else(|| {
                        format!("missing type annotation for match target")
                    })?;
                    let bound_var_mir_ty = if let hll::Type::Custom(ref enum_name) = target_hll_ty {
                        let enum_decl = ctx.enums.get(enum_name).ok_or_else(|| {
                            format!("undeclared enum '{}' in lowering", enum_name)
                        })?;
                        let variant_decl = enum_decl.variants.iter().find(|v| v.name == *variant).ok_or_else(|| {
                            format!("enum '{}' has no variant '{}' in lowering", enum_name, variant)
                        })?;
                        lower_type(&variant_decl.ty)
                    } else {
                        return Err(format!("expected enum type for match target, found {:?}", target_hll_ty));
                    };
                    
                    ctx.locals.push(mir::Local {
                        name: var_name.clone(),
                        ty: bound_var_mir_ty.clone(),
                        span: body.span,
                    });
                    
                    let downcast_place = mir::Place::Downcast(Box::new(target_place.clone()), variant.clone());
                    let op = if is_copy_type(&bound_var_mir_ty) {
                        mir::Operand::Copy(downcast_place)
                    } else {
                        mir::Operand::Move(downcast_place)
                    };
                    ctx.emit_statement(
                        mir::Statement::Assign(mir::Place::Var(var_name.clone()), mir::RValue::Use(op)),
                        body.span,
                    );
                }
                
                lower_expr_into(ctx, body, dest, types)?;
                ctx.terminate_block(mir::Terminator::Goto(merge_label.clone()), expr.span);
            }
            
            ctx.start_block(merge_label);
            Ok(())
        }
        hll::ExprKind::StructConstr(_, fields) => {
            for (field_name, value_expr) in fields {
                let field_dest = mir::Place::Field(Box::new(dest.clone()), field_name.clone());
                lower_expr_into(ctx, value_expr, &field_dest, types)?;
            }
            Ok(())
        }
        hll::ExprKind::EnumConstr(enum_name, variant_name, payload) => {
            let payload_op = lower_expr_to_operand(ctx, payload, types)?;
            ctx.emit_statement(
                mir::Statement::Assign(
                    dest.clone(),
                    mir::RValue::EnumConstr(enum_name.clone(), variant_name.clone(), payload_op),
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
                mir::Statement::Assign(dest.clone(), mir::RValue::ArrayLit(ops)),
                expr.span,
            );
            Ok(())
        }
    }
}

pub fn lower_program(
    program: &hll::Program,
    types: &HashMap<*const hll::Expr, hll::Type>,
) -> Result<mir::Program, String> {
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
                    markers: e.markers.clone(),
                    variants,
                }));
            }
            hll::Declaration::Fn(f) => {
                let mut ctx = LowerCtx::new(program);
                
                let mut params: Vec<mir::Param> = f.params.iter().map(|p| mir::Param {
                    name: p.name.clone(),
                    ty: lower_type(&p.ty),
                    span: p.span,
                }).collect();

                // If return type is not Unit, append $return parameter
                if f.ret_ty != hll::Type::Unit {
                    params.push(mir::Param {
                        name: "$return".to_string(),
                        ty: mir::Type::Ref(mir::RefKind::Out, Box::new(lower_type(&f.ret_ty))),
                        span: f.span,
                    });
                }

                let start_label = "entry".to_string();
                ctx.start_block(start_label);

                // Lower body block into ctx
                // Since body is a block/expression, we lower it.
                // If return type is not Unit, we write the result to $return.*.
                // Otherwise we write it to a dummy Unit place.
                if f.ret_ty != hll::Type::Unit {
                    let ret_place = mir::Place::Deref(Box::new(mir::Place::Var("$return".to_string())));
                    lower_expr_into(&mut ctx, &f.body, &ret_place, types)?;
                } else {
                    let dummy = ctx.fresh_temp(mir::Type::Unit, f.body.span);
                    lower_expr_into(&mut ctx, &f.body, &dummy, types)?;
                }

                // If the entry block or last block hasn't been terminated, terminate it with Return
                if ctx.current_block_label.is_some() {
                    ctx.terminate_block(mir::Terminator::Return, f.span);
                }

                declarations.push(mir::Declaration::Fn(mir::Function {
                    name: f.name.clone(),
                    name_span: f.span,
                    is_extern: false,
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
    use crate::mir::pretty_print::pretty_print;

    fn lower_source(source: &str) -> String {
        let hll_prog = Parser::new(source).parse().unwrap_or_else(|d| {
            panic!(
                "parse error:\n{}\n--- source ---\n{}",
                d.errors_str().join("\n"),
                source
            )
        });
        let types = typecheck_program_collect(&hll_prog).unwrap();
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
                    Node(n) => {
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
}









