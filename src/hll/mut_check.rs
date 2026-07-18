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
use crate::mir::ast::{Span, RefKind};
use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use std::collections::HashMap;

/// Machine-readable code for each HLL mutability-check error kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HllMutCheckCode {
    /// `x = ...` or `x.field = ...` where `x` was declared without `mut`.
    AssignToImmutable,
    /// `&mut x` (or another mutable-borrow kind) where `x` was declared
    /// without `mut`.
    BorrowImmutableAsMut,
}

impl From<HllMutCheckCode> for DiagCode {
    fn from(code: HllMutCheckCode) -> DiagCode {
        DiagCode::HllMutCheck(code)
    }
}

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
pub fn check_mutability(program: &Program, d: &mut Diagnostics) {
    for decl in &program.declarations {
        if let Declaration::Fn(f) = decl {
            check_fn(f, d);
        }
    }
}

fn check_fn(f: &FnDecl, d: &mut Diagnostics) {
    let mut scope = Scope::new();
    // Parameters are immutable (Param has no is_mut field).
    for p in &f.params {
        scope.declare(&p.name, false);
    }
    check_expr(&f.body, &mut scope, &f.name, d);
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

fn check_expr(expr: &Expr, scope: &mut Scope, func: &str, d: &mut Diagnostics) {
    match &expr.kind {
        // ── leaf / simple ────────────────────────────────────────
        ExprKind::Literal(_)
        | ExprKind::Variable(_)
        | ExprKind::Continue => {}

        // ── unary wrappers ───────────────────────────────────────
        ExprKind::Borrow(kind, inner) => {
            check_expr(inner, scope, func, d);
            if *kind != RefKind::Shared {
                if let PlaceRoot::Var(name, span) = place_root(inner) {
                    if let Some(false) = scope.is_mut(name) {
                        d.push_error(
                            Diagnostic::new(
                                HllMutCheckCode::BorrowImmutableAsMut,
                                span,
                                format!("cannot borrow immutable binding '{}' as mutable", name),
                            )
                            .in_function(func),
                        );
                    }
                }
            }
        }
        ExprKind::RawBorrow(inner)
        | ExprKind::Deref(inner)
        | ExprKind::FieldAccess(inner, _)
        | ExprKind::Downcast(inner, _) => check_expr(inner, scope, func, d),

        ExprKind::ArrayIndex(arr, idx) => {
            check_expr(arr, scope, func, d);
            check_expr(idx, scope, func, d);
        }

        ExprKind::Binary(lhs, _, rhs) => {
            check_expr(lhs, scope, func, d);
            check_expr(rhs, scope, func, d);
        }

        // ── assignment — the core check ──────────────────────────
        ExprKind::Assign(lhs, rhs) => {
            check_expr(rhs, scope, func, d);
            // Walk the lhs for nested sub-expressions (index exprs etc.)
            check_assign_subexprs(lhs, scope, func, d);
            if let PlaceRoot::Var(name, span) = place_root(lhs) {
                if let Some(false) = scope.is_mut(name) {
                    d.push_error(
                        Diagnostic::new(
                            HllMutCheckCode::AssignToImmutable,
                            span,
                            format!("cannot assign to immutable binding '{}'", name),
                        )
                        .in_function(func),
                    );
                }
                // `None` means the name wasn't in scope — type_check
                // already rejects this, so we silently pass.
            }
        }

        ExprKind::Block(stmts, trailing, _) => {
            scope.push();
            for stmt in stmts {
                check_stmt(stmt, scope, func, d);
            }
            if let Some(tail) = trailing {
                check_expr(tail, scope, func, d);
            }
            scope.pop();
        }

        // ── control flow ─────────────────────────────────────────
        ExprKind::If(cond, then_arm, else_arm) => {
            check_expr(cond, scope, func, d);
            check_expr(then_arm, scope, func, d);
            check_expr(else_arm, scope, func, d);
        }

        ExprKind::Loop(body) => check_expr(body, scope, func, d),

        ExprKind::Break(val) | ExprKind::Return(val) => {
            if let Some(v) = val {
                check_expr(v, scope, func, d);
            }
        }

        // ── calls ────────────────────────────────────────────────
        ExprKind::Call(callee, args) => {
            check_expr(callee, scope, func, d);
            for arg in args {
                check_expr(arg, scope, func, d);
            }
        }

        // ── match ────────────────────────────────────────────────
        ExprKind::Match(target, arms) => {
            check_expr(target, scope, func, d);
            for (pattern, body) in arms {
                scope.push();
                // Pattern bindings are immutable.
                if let Pattern::Variant(_, Some(bound)) = pattern {
                    scope.declare(bound, false);
                }
                check_expr(body, scope, func, d);
                scope.pop();
            }
        }

        // ── constructors / aggregates ────────────────────────────
        ExprKind::StructConstr(_, fields) => {
            for (_, val) in fields {
                check_expr(val, scope, func, d);
            }
        }

        ExprKind::EnumConstr(_, _, payload) => check_expr(payload, scope, func, d),

        ExprKind::Array(elems) => {
            for e in elems {
                check_expr(e, scope, func, d);
            }
        }
    }
}

/// Check sub-expressions inside the LHS of an assignment that are
/// not part of the "place path" but are arbitrary expressions (e.g.
/// the index expression in `a[expr]`).
fn check_assign_subexprs(expr: &Expr, scope: &mut Scope, func: &str, d: &mut Diagnostics) {
    match &expr.kind {
        ExprKind::ArrayIndex(arr, idx) => {
            check_assign_subexprs(arr, scope, func, d);
            check_expr(idx, scope, func, d);
        }
        ExprKind::FieldAccess(inner, _)
        | ExprKind::Downcast(inner, _)
        | ExprKind::Deref(inner) => check_assign_subexprs(inner, scope, func, d),
        // The root variable itself — no sub-expressions to check.
        ExprKind::Variable(_) => {}
        // Anything else is an arbitrary expression; fully check it.
        _ => check_expr(expr, scope, func, d),
    }
}

fn check_stmt(stmt: &Stmt, scope: &mut Scope, func: &str, d: &mut Diagnostics) {
    match stmt {
        Stmt::Let {
            is_mut,
            name,
            ty: _,
            init,
            span: _,
        } => {
            if let Some(init) = init {
                check_expr(init, scope, func, d);
            }
            scope.declare(name, *is_mut);
        }
        Stmt::Defer { body, span: _ } => {
            check_expr(body, scope, func, d);
        }
        Stmt::Expr(e) => check_expr(e, scope, func, d),
    }
}

// ── tests ────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::parser::Parser;
    use crate::hll::type_check;

    /// Parse + typecheck + mut-check. Returns the mut-check errors as
    /// strings (empty on success).
    fn check(source: &str) -> Vec<String> {
        let program = Parser::new(source).parse().expect("parse ok");
        let tc_d = type_check::typecheck_program(&program);
        assert!(!tc_d.has_errors(), "typecheck ok: {:?}", tc_d.errors_str());
        let mut d = Diagnostics::default().with_source(program.source.clone());
        check_mutability(&program, &mut d);
        d.errors_str()
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
    }

    #[test]
    fn immutable_binding_no_reassign_ok() {
        let src = "
            fn f() -> i64 {
                let x: i64 = 1;
                x
            }
        ";
        assert!(check(src).is_empty());
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
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
        assert!(check(src).is_empty(), "expected ok, got: {:?}", check(src));
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
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
        let errs = check(src);
        assert!(!errs.is_empty());
        let err = errs.join("\n");
        assert!(
            err.contains("cannot assign to immutable binding 'x'"),
            "unexpected error: {}",
            err,
        );
    }

    #[test]
    fn borrow_mut_on_immutable_errors() {
        let src = "
            fn f() {
                let x = 1;
                let r = &mut x;
            }
        ";
        let errs = check(src);
        assert!(!errs.is_empty());
    }
}
