use std::collections::HashMap;
use crate::mir::ast as mir;
use crate::hll::ast as hll;

struct LowerCtx {
    locals: Vec<mir::Local>,
    blocks: Vec<mir::BasicBlock>,
    current_block_label: Option<String>,
    current_statements: Vec<(mir::Statement, mir::Span)>,
    temp_counter: usize,
    block_counter: usize,
    loop_stack: Vec<(String, String)>, // (start_label, end_label)
    functions: HashMap<String, hll::FnDecl>,
}

impl LowerCtx {
    fn new(program: &hll::Program) -> Self {
        let mut functions = HashMap::new();
        for decl in &program.declarations {
            if let hll::Declaration::Fn(f) = decl {
                functions.insert(f.name.clone(), f.clone());
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
        hll::Type::Boolean => mir::Type::Boolean,
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
        hll::Type::Var(_) => unreachable!("type variables must be resolved before lowering"),
    }
}

fn is_copy_type(ty: &mir::Type) -> bool {
    // Scalar values, references, and pointers are Copy
    matches!(
        ty,
        mir::Type::Int(_)
            | mir::Type::Float(_)
            | mir::Type::Boolean
            | mir::Type::Unit
            | mir::Type::Never
            | mir::Type::Ref(_, _)
            | mir::Type::RawPtr(_)
    )
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
                hll::Literal::Int(val, suffix) => mir::ConstVal::Int {
                    bits: *val as u64,
                    ty: suffix.unwrap_or(mir::IntTy::I64),
                },
                hll::Literal::Float(val, suffix) => mir::ConstVal::Float {
                    bits: val.to_bits(),
                    ty: suffix.unwrap_or(mir::FloatTy::F64),
                },
                hll::Literal::Boolean(val) => mir::ConstVal::Boolean(*val),
                hll::Literal::Unit => mir::ConstVal::Unit,
            };
            Ok(mir::Operand::Const(const_val))
        }
        hll::ExprKind::Variable(_)
        | hll::ExprKind::FieldAccess(_, _)
        | hll::ExprKind::Downcast(_, _)
        | hll::ExprKind::Deref(_) => {
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
        | hll::ExprKind::Deref(_) => {
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
                ctx.emit_statement(
                    mir::Statement::Assign(dest.clone(), mir::RValue::Use(mir::Operand::Const(mir::ConstVal::Unit))),
                    expr.span,
                ); // Pre-init to unit or keep assignment separate. Actually we just append `&out dest` to args:
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

            ctx.loop_stack.push((start_label.clone(), end_label.clone()));
            ctx.start_block(start_label);
            
            // Loop body value is discarded
            let dummy = ctx.fresh_temp(mir::Type::Unit, body.span);
            lower_expr_into(ctx, body, &dummy, types)?;
            ctx.terminate_block(mir::Terminator::Goto(ctx.loop_stack.last().unwrap().0.clone()), expr.span);

            ctx.loop_stack.pop();

            ctx.start_block(end_label);
            // Loop expression evaluates to Unit (or Never if infinite, but Unit is fine as fallback)
            ctx.emit_statement(
                mir::Statement::Assign(dest.clone(), mir::RValue::Use(mir::Operand::Const(mir::ConstVal::Unit))),
                expr.span,
            );
            Ok(())
        }
        hll::ExprKind::Break(val_expr) => {
            let (_, end_label) = ctx.loop_stack.last().ok_or_else(|| {
                format!("at {}: break outside of loop", expr.span)
            })?.clone();

            if let Some(val) = val_expr {
                // If break has a value, we can discard or handle it. Since HLL loops return Unit in this subset,
                // we just evaluate it to a dummy place.
                let dummy = ctx.fresh_temp(mir::Type::Unit, val.span);
                lower_expr_into(ctx, val, &dummy, types)?;
            }

            ctx.terminate_block(mir::Terminator::Goto(end_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Continue => {
            let (start_label, _) = ctx.loop_stack.last().ok_or_else(|| {
                format!("at {}: continue outside of loop", expr.span)
            })?.clone();

            ctx.terminate_block(mir::Terminator::Goto(start_label), expr.span);
            Ok(())
        }
        hll::ExprKind::Return(val_expr) => {
            if let Some(val) = val_expr {
                // Return value is written to *$return
                let ret_place = mir::Place::Deref(Box::new(mir::Place::Var("$return".to_string())));
                lower_expr_into(ctx, val, &ret_place, types)?;
            }
            ctx.terminate_block(mir::Terminator::Return, expr.span);
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
                    markers: mir::Markers {
                        copy: true,
                        drop: true,
                        mov: true,
                    },
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
                    markers: mir::Markers {
                        copy: true,
                        drop: true,
                        mov: true,
                    },
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
                // If return type is not Unit, we write the result to *$return.
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

    Ok(mir::Program { declarations })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::parser::Parser;
    use crate::hll::type_check::typecheck_program_collect;
    use crate::mir::pretty_print::pretty_print;

    fn lower_source(source: &str) -> String {
        let mut p = Parser::new(source).unwrap();
        let hll_prog = p.parse_program().unwrap();
        let types = typecheck_program_collect(&hll_prog).unwrap();
        let mir_prog = lower_program(&hll_prog, &types).unwrap();
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
                *$return = copy sum;
                return
            }
            "
        );
    }

    #[test]
    fn test_lower_struct_and_field_access() {
        let source = "
            struct Point { x: i64, y: i64 }
            fn get_x(p: Point) -> i64 {
                let x = p.x;
                x
            }
        ";
        assert_lower_eq(
            source,
            "
            struct Copy Drop Move Point {
              x: i64
              y: i64
            }

            fn get_x(p: Point, $return: &out i64) {
              x: i64;
              entry:
                x = copy p.x;
                *$return = copy x;
                return
            }
            "
        );
    }
}
