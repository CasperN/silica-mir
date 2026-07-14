/// HLL mutability check.
///
/// Walks the HLL AST after type-checking and before lowering.  Tracks
/// which local bindings were declared `let mut` and rejects assignments
/// whose place-expression root is a non-`mut` binding.
///
/// Mutations *through* a reference (`x.* = ...`) do **not** require the
/// reference variable itself to be `mut` — only direct reassignment or
/// field/index writes on owned places need it.

use crate::hll::ast::*;
use crate::mir::ast::Span;
use std::collections::HashMap;

// ── scope tracker ────────────────────────────────────────────────────

struct Scope {
    /// Stack of frames; each frame maps binding name → is_mut.
    frames: Vec<HashMap<String, bool>>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            frames: vec![HashMap::new()],
        }
    }

    fn push(&mut self) {
        self.frames.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }

    fn declare(&mut self, name: &str, is_mut: bool) {
        self.frames
            .last_mut()
            .expect("scope stack must be non-empty")
            .insert(name.to_string(), is_mut);
    }

    /// Look up whether `name` is mutable.  Returns `None` if the name
    /// is not in scope (which is a type-check error, not ours).
    fn is_mut(&self, name: &str) -> Option<bool> {
        for frame in self.frames.iter().rev() {
            if let Some(&m) = frame.get(name) {
                return Some(m);
            }
        }
        None
    }
}

// ── public entry ─────────────────────────────────────────────────────

/// Check that non-`mut` bindings are never reassigned.
pub fn check_mutability(program: &Program) -> Result<(), String> {
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            check_fn(f).map_err(|e| format!("in function '{}': {}", f.name, e))?;
        }
    }
    Ok(())
}

fn check_fn(f: &FnDecl) -> Result<(), String> {
    let mut scope = Scope::new();
    // Parameters are immutable (Param has no is_mut field).
    for p in &f.params {
        scope.declare(&p.name, false);
    }
    check_expr(&f.body, &mut scope)
}

// ── place-root resolution ────────────────────────────────────────────

/// The root of a place expression, if it's a variable not behind a deref.
enum PlaceRoot<'a> {
    /// Direct variable (possibly through field / index projections).
    Var(&'a str, Span),
    /// Behind a deref — mutation goes through the reference, so
    /// we don't need to check the variable's mutability.
    ThroughDeref,
    /// Not a place expression we can resolve (e.g. a call result).
    Unknown,
}

/// Walk the LHS of an assignment to find the root variable, stopping
/// if we cross a deref (which means the mutation targets the referent,
/// not the binding).
fn place_root(expr: &Expr) -> PlaceRoot<'_> {
    match &expr.kind {
        ExprKind::Variable(name) => PlaceRoot::Var(name, expr.span),
        ExprKind::FieldAccess(inner, _) => place_root(inner),
        ExprKind::ArrayIndex(inner, _) => place_root(inner),
        ExprKind::Downcast(inner, _) => place_root(inner),
        ExprKind::Deref(_) => PlaceRoot::ThroughDeref,
        _ => PlaceRoot::Unknown,
    }
}

// ── expression / statement walk ──────────────────────────────────────

fn check_expr(expr: &Expr, scope: &mut Scope) -> Result<(), String> {
    match &expr.kind {
        // ── leaf / simple ────────────────────────────────────────
        ExprKind::Literal(_)
        | ExprKind::Variable(_)
        | ExprKind::Continue => Ok(()),

        // ── unary wrappers ───────────────────────────────────────
        ExprKind::Borrow(_, inner)
        | ExprKind::RawBorrow(inner)
        | ExprKind::Deref(inner)
        | ExprKind::FieldAccess(inner, _)
        | ExprKind::Downcast(inner, _) => check_expr(inner, scope),

        ExprKind::ArrayIndex(arr, idx) => {
            check_expr(arr, scope)?;
            check_expr(idx, scope)
        }

        ExprKind::Binary(lhs, _, rhs) => {
            check_expr(lhs, scope)?;
            check_expr(rhs, scope)
        }

        // ── assignment — the core check ──────────────────────────
        ExprKind::Assign(lhs, rhs) => {
            check_expr(rhs, scope)?;
            // Walk the lhs for nested sub-expressions (index exprs etc.)
            check_assign_subexprs(lhs, scope)?;
            match place_root(lhs) {
                PlaceRoot::Var(name, span) => {
                    if let Some(false) = scope.is_mut(name) {
                        return Err(format!(
                            "at {}: cannot assign to immutable binding '{}'",
                            span, name,
                        ));
                    }
                    // `None` means the name wasn't in scope — the type
                    // checker already rejects this, so we silently pass.
                    Ok(())
                }
                PlaceRoot::ThroughDeref | PlaceRoot::Unknown => Ok(()),
            }
        }

        // ── blocks ───────────────────────────────────────────────
        ExprKind::Block(stmts, trailing) => {
            scope.push();
            for stmt in stmts {
                check_stmt(stmt, scope)?;
            }
            if let Some(tail) = trailing {
                check_expr(tail, scope)?;
            }
            scope.pop();
            Ok(())
        }

        // ── control flow ─────────────────────────────────────────
        ExprKind::If(cond, then_arm, else_arm) => {
            check_expr(cond, scope)?;
            check_expr(then_arm, scope)?;
            check_expr(else_arm, scope)
        }

        ExprKind::Loop(body) => check_expr(body, scope),

        ExprKind::Break(val) | ExprKind::Return(val) => {
            if let Some(v) = val {
                check_expr(v, scope)?;
            }
            Ok(())
        }

        // ── calls ────────────────────────────────────────────────
        ExprKind::Call(callee, args) => {
            check_expr(callee, scope)?;
            for arg in args {
                check_expr(arg, scope)?;
            }
            Ok(())
        }

        // ── match ────────────────────────────────────────────────
        ExprKind::Match(target, arms) => {
            check_expr(target, scope)?;
            for (pattern, body) in arms {
                scope.push();
                // Pattern bindings are immutable.
                if let Pattern::Variant(_, Some(bound)) = pattern {
                    scope.declare(bound, false);
                }
                check_expr(body, scope)?;
                scope.pop();
            }
            Ok(())
        }

        // ── constructors / aggregates ────────────────────────────
        ExprKind::StructConstr(_, fields) => {
            for (_, val) in fields {
                check_expr(val, scope)?;
            }
            Ok(())
        }

        ExprKind::EnumConstr(_, _, payload) => check_expr(payload, scope),

        ExprKind::Array(elems) => {
            for e in elems {
                check_expr(e, scope)?;
            }
            Ok(())
        }
    }
}

/// Check sub-expressions inside the LHS of an assignment that are
/// not part of the "place path" but are arbitrary expressions (e.g.
/// the index expression in `a[expr]`).
fn check_assign_subexprs(expr: &Expr, scope: &mut Scope) -> Result<(), String> {
    match &expr.kind {
        ExprKind::ArrayIndex(arr, idx) => {
            check_assign_subexprs(arr, scope)?;
            check_expr(idx, scope)
        }
        ExprKind::FieldAccess(inner, _)
        | ExprKind::Downcast(inner, _)
        | ExprKind::Deref(inner) => check_assign_subexprs(inner, scope),
        // The root variable itself — no sub-expressions to check.
        ExprKind::Variable(_) => Ok(()),
        // Anything else is an arbitrary expression; fully check it.
        _ => check_expr(expr, scope),
    }
}

fn check_stmt(stmt: &Stmt, scope: &mut Scope) -> Result<(), String> {
    match stmt {
        Stmt::Let {
            is_mut,
            name,
            ty: _,
            init,
            span: _,
        } => {
            check_expr(init, scope)?;
            scope.declare(name, *is_mut);
            Ok(())
        }
        Stmt::Expr(e) => check_expr(e, scope),
    }
}

// ── tests ────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::parser::Parser;
    use crate::hll::type_check;

    /// Parse + typecheck + mut-check.
    fn check(source: &str) -> Result<(), String> {
        let program = Parser::new(source)
            .parse()
            .map_err(|d| d.errors_str().join("\n"))?;
        type_check::typecheck_program(&program)?;
        check_mutability(&program)
    }

    // ── should pass ──────────────────────────────────────────────

    #[test]
    fn let_mut_reassign_ok() {
        let src = "
            fn f() -> i64 {
                let mut x: i64 = 1;
                x = 2;
                x
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn immutable_binding_no_reassign_ok() {
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                x
            }
        ";
        assert!(check(src).is_ok());
    }

    #[test]
    fn deref_write_through_immutable_binding_ok() {
        // Writing through a reference doesn't require the reference
        // variable itself to be mut.
        let src = "
            fn f(r: &mut i64) {
                r.* = 42;
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn mut_field_assign_ok() {
        let src = "
            struct Point { x: i64, y: i64 }
            fn f() -> i64 {
                let mut p = Point { x: 1, y: 2 };
                p.x = 10;
                p.x
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn mut_array_index_assign_ok() {
        let src = "
            fn f() -> i64 {
                let mut a = [1, 2, 3];
                a[0] = 99;
                a[0]
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn shadowing_mut_over_immutable_ok() {
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                let mut x: i64 = 2;
                x = 3;
                x
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn inner_scope_mut_outer_immutable_ok() {
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                {
                    let mut x: i64 = 2;
                    x = 3;
                    x
                }
            }
        ";
        assert!(check(src).is_ok(), "expected ok, got: {:?}", check(src));
    }

    // ── should fail ──────────────────────────────────────────────

    #[test]
    fn reassign_immutable_binding_errors() {
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                x = 2;
                x
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'x'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn reassign_param_errors() {
        let src = "
            fn f(x: i64) -> i64 {
                x = 2;
                x
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'x'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn field_assign_on_immutable_errors() {
        let src = "
            struct Point { x: i64, y: i64 }
            fn f() -> i64 {
                let p = Point { x: 1, y: 2 };
                p.x = 10;
                p.x
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'p'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn array_index_assign_on_immutable_errors() {
        let src = "
            fn f() -> i64 {
                let a = [1, 2, 3];
                a[0] = 99;
                a[0]
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'a'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn match_binding_reassign_errors() {
        let src = "
            enum Opt { None: unit, Some: i64 }
            fn f(o: Opt) -> i64 {
                o match {
                    Some(v) => {
                        v = 99;
                        v
                    },
                    None(u) => 0,
                }
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'v'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn outer_immutable_survives_inner_shadow() {
        // After the inner scope where `x` was shadowed as mut,
        // assigning to the outer immutable `x` should still be an error.
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                {
                    let mut x: i64 = 2;
                    x = 3;
                };
                x = 4;
                x
            }
        ";
        let res = check(src);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(
            err.contains("cannot assign to immutable binding 'x'"),
            "unexpected error: {}",
            err,
        );
    }
}
