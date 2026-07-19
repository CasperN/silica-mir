//! Tree-sitter-driven HLL parser.
//!
//! Consumes `.si` source through the tree-sitter grammar at
//! `tree-sitter-silica/hll/grammar.js` and produces the typed
//! HLL AST defined in `hll::ast`. Emits structured `Diagnostics`
//! for syntax errors (multi-error output) and CST-to-AST invariant
//! failures — same error-code shape as the MIR parser.

use crate::common::{FloatTy, IntTy, Lifetime, Marker, Markers, RefKind, Span};
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::hll::ast::*;
use crate::hll::helpers::*;
use crate::mir::parser::ParserCode;
use std::collections::BTreeSet;
use tree_sitter::{Node, Parser as TSParser};

/// Names of type parameters in scope for the enclosing decl. Threaded
/// explicitly through `map_type`; identifiers in scope resolve to
/// `Type::Param`, otherwise to `Type::Custom`.
type TypeScope = BTreeSet<String>;

extern "C" {
    fn tree_sitter_silica() -> *const std::ffi::c_void;
}

pub fn language() -> tree_sitter::Language {
    unsafe { tree_sitter::Language::from_raw(tree_sitter_silica() as *const _) }
}

fn span_of(node: Node) -> Span {
    let p = node.start_position();
    let ep = node.end_position();
    Span {
        line: (p.row as u32).saturating_add(1),
        col: (p.column as u32).saturating_add(1),
        end_line: (ep.row as u32).saturating_add(1),
        end_col: (ep.column as u32).saturating_add(1),
    }
}

/// Map a scalar type keyword to `Type`. Same table as MIR — the
/// keywords are defined once in `common/grammar.js`.
fn scalar_kind_to_type(kind: &str) -> Option<Type> {
    Some(match kind {
        "i8" => i8_ty(),
        "i16" => i16_ty(),
        "i32" => i32_ty(),
        "i64" => i64_ty(),
        "u8" => u8_ty(),
        "u16" => u16_ty(),
        "u32" => u32_ty(),
        "u64" => u64_ty(),
        "f32" => f32_ty(),
        "f64" => f64_ty(),
        _ => return None,
    })
}

fn split_int_suffix(text: &str) -> (&str, Option<IntTy>) {
    for (suf, ty) in [
        ("i16", IntTy::I16),
        ("i32", IntTy::I32),
        ("i64", IntTy::I64),
        ("u16", IntTy::U16),
        ("u32", IntTy::U32),
        ("u64", IntTy::U64),
        ("i8", IntTy::I8),
        ("u8", IntTy::U8),
    ] {
        if let Some(rest) = text.strip_suffix(suf) {
            return (rest, Some(ty));
        }
    }
    (text, None)
}

fn parse_int_literal(text: &str) -> Result<(i64, Option<IntTy>), String> {
    let (digits_and_prefix, ty) = split_int_suffix(text);
    let (radix, digits) = if let Some(rest) = digits_and_prefix.strip_prefix("0x") {
        (16u32, rest)
    } else if let Some(rest) = digits_and_prefix.strip_prefix("0b") {
        (2u32, rest)
    } else {
        (10u32, digits_and_prefix)
    };
    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    if cleaned.is_empty() {
        return Err(format!("integer literal has no digits: {:?}", text));
    }
    let val = i64::from_str_radix(&cleaned, radix)
        .map_err(|e| format!("invalid integer literal {:?}: {}", text, e))?;
    Ok((val, ty))
}

fn parse_float_literal(text: &str) -> Result<(f64, Option<FloatTy>), String> {
    let (digits, ty) = if let Some(rest) = text.strip_suffix("f32") {
        (rest, Some(FloatTy::F32))
    } else if let Some(rest) = text.strip_suffix("f64") {
        (rest, Some(FloatTy::F64))
    } else {
        (text, None)
    };
    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    let val: f64 = cleaned
        .parse()
        .map_err(|e| format!("invalid float literal {:?}: {}", text, e))?;
    Ok((val, ty))
}

pub struct Parser {
    source: std::sync::Arc<String>,
}

impl Parser {
    pub fn new(source: impl Into<String>) -> Self {
        Self {
            source: std::sync::Arc::new(source.into()),
        }
    }

    pub fn parse(&self) -> Result<Program, Diagnostics> {
        let mut ts_parser = TSParser::new();
        if let Err(e) = ts_parser.set_language(&language()) {
            let mut d = Diagnostics::default().with_source(self.source.clone());
            d.push_error(Diagnostic::new(
                ParserCode::MalformedCst,
                Span::default(),
                format!("failed to load tree-sitter grammar: {}", e),
            ));
            return Err(d);
        }

        let Some(tree) = ts_parser.parse(&*self.source, None) else {
            let mut d = Diagnostics::default().with_source(self.source.clone());
            d.push_error(Diagnostic::new(
                ParserCode::MalformedCst,
                Span::default(),
                "tree-sitter failed to produce a parse tree",
            ));
            return Err(d);
        };
        let root = tree.root_node();

        if root.has_error() {
            let mut diags = Diagnostics::default().with_source(self.source.clone());
            self.walk_syntax_errors(root, None, &mut diags);
            return Err(diags);
        }

        self.map_program(root).map_err(|d| {
            let mut diags = Diagnostics::default().with_source(self.source.clone());
            diags.push_error(d);
            diags
        })
    }

    fn get_text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    fn diag(&self, node: Node, code: ParserCode, msg: impl Into<String>) -> Diagnostic {
        Diagnostic::new(code, span_of(node), msg)
    }

    fn lit_diag<T>(&self, res: Result<T, String>, node: Node) -> Result<T, Diagnostic> {
        res.map_err(|s| self.diag(node, ParserCode::InvalidLiteral, s))
    }

    /// Walk the CST emitting one diagnostic per ERROR/MISSING node.
    /// Attaches `in_function` context when the error is inside a
    /// `fn_decl` subtree.
    fn walk_syntax_errors<'a>(
        &'a self,
        node: Node<'a>,
        ctx_fn: Option<&'a str>,
        diags: &mut Diagnostics,
    ) {
        let ctx_fn = match node.kind() {
            "fn_decl" => node
                .child_by_field_name("name")
                .map(|n| self.get_text(n))
                .or(ctx_fn),
            _ => ctx_fn,
        };

        if node.is_missing() {
            let mut d = Diagnostic::new(
                ParserCode::MissingToken,
                span_of(node),
                format!("missing '{}'", node.kind()),
            );
            if let Some(f) = ctx_fn {
                d = d.in_function(f);
            }
            diags.push_error(d);
        } else if node.is_error() {
            let text = self.get_text(node);
            let msg = if text.is_empty() {
                "syntax error".to_string()
            } else {
                format!("unexpected: {}", text)
            };
            let mut d = Diagnostic::new(ParserCode::UnexpectedToken, span_of(node), msg);
            if let Some(f) = ctx_fn {
                d = d.in_function(f);
            }
            diags.push_error(d);
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_syntax_errors(child, ctx_fn, diags);
        }
    }

    fn map_program(&self, node: Node) -> Result<Program, Diagnostic> {
        let mut declarations = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "declaration" {
                declarations.push(self.map_declaration(child)?);
            }
        }
        Ok(Program {
            declarations,
            source: self.source.clone(),
        })
    }

    fn map_declaration(&self, node: Node) -> Result<Declaration, Diagnostic> {
        let child = node
            .child(0)
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "empty declaration"))?;
        match child.kind() {
            "struct_decl" => Ok(Declaration::Struct(self.map_struct_decl(child)?)),
            "enum_decl" => Ok(Declaration::Enum(self.map_enum_decl(child)?)),
            "fn_decl" => Ok(Declaration::Fn(self.map_fn_decl(child)?)),
            _ => Err(self.diag(
                child,
                ParserCode::MalformedCst,
                format!("unknown declaration kind: {}", child.kind()),
            )),
        }
    }

    fn map_struct_decl(&self, node: Node) -> Result<StructDecl, Diagnostic> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "struct decl missing name"))?;
        let name = self.get_text(name_node).to_string();
        let span = span_of(node);

        let mut scope: TypeScope = BTreeSet::new();
        let mut cursor = node.walk();
        let (lifetime_params, type_params) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope)?
        } else {
            (Vec::new(), Vec::new())
        };

        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            self.map_markers(markers_node)?
        } else {
            Markers::empty()
        };

        let mut fields = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "struct_field" {
                let f_name_node = child.child_by_field_name("name").ok_or_else(|| {
                    self.diag(child, ParserCode::MalformedCst, "struct field missing name")
                })?;
                let f_type_node = child.child_by_field_name("type").ok_or_else(|| {
                    self.diag(child, ParserCode::MalformedCst, "struct field missing type")
                })?;
                fields.push(StructField {
                    name: self.get_text(f_name_node).to_string(),
                    ty: self.map_type(f_type_node, &scope)?,
                    span: span_of(child),
                });
            }
        }

        Ok(StructDecl {
            name,
            lifetime_params,
            type_params,
            markers,
            fields,
            span,
        })
    }

    fn map_enum_decl(&self, node: Node) -> Result<EnumDecl, Diagnostic> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "enum decl missing name"))?;
        let name = self.get_text(name_node).to_string();
        let span = span_of(node);

        let mut scope: TypeScope = BTreeSet::new();
        let mut cursor = node.walk();
        let (lifetime_params, type_params) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope)?
        } else {
            (Vec::new(), Vec::new())
        };

        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            self.map_markers(markers_node)?
        } else {
            Markers::empty()
        };

        let mut variants = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "enum_variant" {
                let v_name_node = child.child_by_field_name("name").ok_or_else(|| {
                    self.diag(child, ParserCode::MalformedCst, "enum variant missing name")
                })?;
                let v_type_node = child.child_by_field_name("type").ok_or_else(|| {
                    self.diag(child, ParserCode::MalformedCst, "enum variant missing type")
                })?;
                variants.push(EnumVariant {
                    name: self.get_text(v_name_node).to_string(),
                    ty: self.map_type(v_type_node, &scope)?,
                    span: span_of(child),
                });
            }
        }

        Ok(EnumDecl {
            name,
            lifetime_params,
            type_params,
            markers,
            variants,
            span,
        })
    }

    fn map_fn_decl(&self, node: Node) -> Result<FnDecl, Diagnostic> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "fn decl missing name"))?;
        let name = self.get_text(name_node).to_string();
        let span = span_of(node);

        let mut temp_cursor = node.walk();
        let is_unsafe = node.children(&mut temp_cursor).any(|c| c.kind() == "unsafe");

        let (abi, abi_span) = if let Some(abi_node) = node.child_by_field_name("abi") {
            // Strip surrounding quotes; the string_lit rule matches `"..."`.
            let raw = self.get_text(abi_node);
            (
                Some(raw.trim_matches('"').to_string()),
                Some(span_of(abi_node)),
            )
        } else {
            (None, None)
        };

        let with_fn = |d: Diagnostic| d.in_function(name.clone());

        let mut scope: TypeScope = BTreeSet::new();
        let mut cursor = node.walk();
        let (lifetime_params, type_params) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope).map_err(with_fn)?
        } else {
            (Vec::new(), Vec::new())
        };

        let mut params = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "param_decl" {
                let p_name_node = child.child_by_field_name("name").ok_or_else(|| {
                    with_fn(self.diag(child, ParserCode::MalformedCst, "param missing name"))
                })?;
                let p_type_node = child.child_by_field_name("type").ok_or_else(|| {
                    with_fn(self.diag(child, ParserCode::MalformedCst, "param missing type"))
                })?;
                params.push(Param {
                    name: self.get_text(p_name_node).to_string(),
                    ty: self.map_type(p_type_node, &scope).map_err(with_fn)?,
                    span: span_of(child),
                });
            }
        }

        let (ret_ty, ret_ty_span) = if let Some(rt_node) = node.child_by_field_name("return_type") {
            (
                self.map_type(rt_node, &scope).map_err(with_fn)?,
                span_of(rt_node),
            )
        } else {
            // No `-> R` in source: fall back to the whole-fn span so
            // diagnostics still land somewhere sensible even though
            // there's no explicit annotation.
            (unit_ty(), span)
        };

        let body = if let Some(body_node) = node.child_by_field_name("body") {
            Some(self.map_expr(body_node, &scope).map_err(with_fn)?)
        } else {
            None
        };

        Ok(FnDecl {
            name,
            is_unsafe,
            abi,
            abi_span,
            lifetime_params,
            type_params,
            params,
            ret_ty,
            ret_ty_span,
            body,
            span,
        })
    }

    /// Map a `type` (or scalar/keyword token) CST node to `Type`.
    /// `scope` is the set of in-scope type-parameter names for the
    /// enclosing decl; a bare identifier that matches becomes
    /// `Type::Param`, otherwise `Type::Custom` (possibly with args).
    fn map_type(&self, node: Node, scope: &TypeScope) -> Result<Type, Diagnostic> {
        // Shared type rule with MIR; the shape is identical.
        if let Some(ty) = scalar_kind_to_type(node.kind()) {
            return Ok(ty);
        }
        match node.kind() {
            "bool" => return Ok(bool_ty()),
            "unit" => return Ok(unit_ty()),
            "never" => return Ok(never_ty()),
            "identifier" => {
                return Ok(self.identifier_to_type(
                    self.get_text(node),
                    Vec::new(),
                    Vec::new(),
                    scope,
                ))
            }
            "type" => {}
            _ => {
                return Err(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("unexpected node kind in type: {}", node.kind()),
                ));
            }
        }

        let first = node.child(0).ok_or_else(|| {
            self.diag(node, ParserCode::MalformedCst, "type node has no children")
        })?;
        if let Some(ty) = scalar_kind_to_type(first.kind()) {
            return Ok(ty);
        }
        match first.kind() {
            "bool" => return Ok(bool_ty()),
            "unit" => return Ok(unit_ty()),
            "never" => return Ok(never_ty()),
            "identifier" => {
                // Identifier alt with optional `type_args` as sibling:
                // `Foo`, `Foo<T, U>`, `Foo<'a, T>`.
                let text = self.get_text(first);
                let (lifetimes, args) = if let Some(ta) = node.child(1) {
                    if ta.kind() == "type_args" {
                        self.map_type_args(ta, scope)?
                    } else {
                        (Vec::new(), Vec::new())
                    }
                } else {
                    (Vec::new(), Vec::new())
                };
                return Ok(self.identifier_to_type(text, lifetimes, args, scope));
            }
            _ => {}
        }

        let text = self.get_text(first);
        let ref_kind = match text {
            "&" => Some(RefKind::Shared),
            "&mut" => Some(RefKind::Mut),
            "&out" => Some(RefKind::Out),
            "&drop" => Some(RefKind::Drop),
            "&uninit" => Some(RefKind::Uninit),
            _ => None,
        };
        if let Some(kind) = ref_kind {
            let lt = node
                .child(1)
                .filter(|c| c.kind() == "lifetime")
                .map(|c| Lifetime(self.get_text(c).trim_start_matches('\'').to_string()));
            let inner_idx = if lt.is_some() { 2 } else { 1 };
            let inner = node.child(inner_idx).ok_or_else(|| {
                self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("missing inner type for {}", text),
                )
            })?;
            return Ok(Type::Ref(kind, lt, Box::new(self.map_type(inner, scope)?)));
        }
        if text == "*" {
            let inner = node.child(1).ok_or_else(|| {
                self.diag(
                    node,
                    ParserCode::MalformedCst,
                    "missing inner type for raw pointer",
                )
            })?;
            return Ok(raw_ptr_ty(self.map_type(inner, scope)?));
        }
        if text == "[" {
            let elem = node.child_by_field_name("element").ok_or_else(|| {
                self.diag(node, ParserCode::MalformedCst, "array type missing element")
            })?;
            let len_node = node.child_by_field_name("length").ok_or_else(|| {
                self.diag(node, ParserCode::MalformedCst, "array type missing length")
            })?;
            let (len, _) = self.lit_diag(parse_int_literal(self.get_text(len_node)), len_node)?;
            return Ok(array_ty(self.map_type(elem, scope)?, len as usize));
        }
        if text == "fn" {
            // `fn(T,...) [-> R]`. The optional `return_type` field
            // sits outside the paren-delimited params. Iterate all
            // `type` children for params, skipping the return-type
            // node when present; default to unit if the arrow was
            // omitted.
            let ret_node = node.child_by_field_name("return_type");
            let mut params = Vec::new();
            let mut cursor = node.walk();
            for child in node.children(&mut cursor) {
                if child.kind() == "type" && Some(child) != ret_node {
                    params.push(self.map_type(child, scope)?);
                }
            }
            let ret = if let Some(rt) = ret_node {
                self.map_type(rt, scope)?
            } else {
                unit_ty()
            };
            return Ok(fn_ty(params, ret));
        }
        Err(self.diag(
            first,
            ParserCode::MalformedCst,
            format!("unexpected token in type: {}", text),
        ))
    }

    /// Resolve a bare identifier that appeared in type position. If
    /// `name` is in the current scope, produce `Type::Param(name)` —
    /// but only when there are no type arguments, since a type
    /// parameter can't be instantiated. Otherwise produce
    /// `Type::Custom(name, args)`.
    fn identifier_to_type(
        &self,
        name: &str,
        lifetimes: Vec<Lifetime>,
        args: Vec<Type>,
        scope: &TypeScope,
    ) -> Type {
        if lifetimes.is_empty() && args.is_empty() && scope.contains(name) {
            param_ty(name)
        } else {
            Type::Custom(name.to_string(), lifetimes, args)
        }
    }

    /// Parse a `type_params` node (`<'a, T, U: Copy + Drop>`) into
    /// (lifetime_params, type_params). Populates `scope` with each
    /// type-param name so subsequent `map_type` calls see them as
    /// `Param`s.
    fn map_type_params(
        &self,
        node: Node,
        scope: &mut TypeScope,
    ) -> Result<(Vec<Lifetime>, Vec<TypeParam>), Diagnostic> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "lifetime" => {
                    let name = self.get_text(child).trim_start_matches('\'').to_string();
                    lifetimes.push(Lifetime(name));
                }
                "type_param" => {
                    let name_node = child.child_by_field_name("name").ok_or_else(|| {
                        self.diag(child, ParserCode::MalformedCst, "type param missing name")
                    })?;
                    let pname = self.get_text(name_node).to_string();
                    if scope.contains(&pname) {
                        return Err(self.diag(
                            name_node,
                            ParserCode::MalformedCst,
                            format!("Duplicate type parameter '{}'", pname),
                        ));
                    }
                    let bounds = if let Some(m) = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "markers")
                    {
                        self.map_markers(m)?
                    } else {
                        Markers::empty()
                    };
                    scope.insert(pname.clone());
                    types.push(TypeParam {
                        name: pname,
                        bounds,
                        span: span_of(child),
                    });
                }
                _ => {}
            }
        }
        Ok((lifetimes, types))
    }

    /// Parse a `type_args` node (`<'a, T, U>`) into (lifetime_args, type_args).
    fn map_type_args(
        &self,
        node: Node,
        scope: &TypeScope,
    ) -> Result<(Vec<Lifetime>, Vec<Type>), Diagnostic> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "lifetime" {
                let name = self.get_text(child).trim_start_matches('\'').to_string();
                lifetimes.push(Lifetime(name));
            } else if child.kind() == "type" || scalar_kind_to_type(child.kind()).is_some() {
                types.push(self.map_type(child, scope)?);
            }
        }
        Ok((lifetimes, types))
    }

    /// Walk any expression-carrying node into a typed `Expr`. All
    /// operator forms (assign, borrow, field access, deref, downcast,
    /// call, index, match) are named rules in the grammar, so
    /// dispatch is straight by `node.kind()`. The `expr` node itself
    /// is a thin wrapper containing exactly one child — recurse into
    /// it.
    fn map_expr(&self, node: Node, scope: &TypeScope) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        match node.kind() {
            "expr" => {
                let child = node.child(0).ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "expr wrapper empty")
                })?;
                self.map_expr(child, scope)
            }

            // ---- Literals + identifier ----
            "int_lit" => {
                let (val, ty) = self.lit_diag(parse_int_literal(self.get_text(node)), node)?;
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Int(val, ty)),
                    span,
                })
            }
            "float_lit" => {
                let (val, ty) = self.lit_diag(parse_float_literal(self.get_text(node)), node)?;
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Float(val, ty)),
                    span,
                })
            }
            "bool_lit" => Ok(Expr {
                kind: ExprKind::Literal(Literal::Bool(self.get_text(node) == "true")),
                span,
            }),
            "unit_lit" => Ok(Expr {
                kind: ExprKind::Literal(Literal::Unit),
                span,
            }),
            "identifier" => Ok(Expr {
                kind: ExprKind::Variable(self.get_text(node).to_string()),
                span,
            }),

            // ---- Compound primaries ----
            "paren_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| c.kind() == "expr");
                if let Some(e) = inner {
                    self.map_expr(e, scope)
                } else {
                    Ok(Expr {
                        kind: ExprKind::Literal(Literal::Unit),
                        span,
                    })
                }
            }
            "block_expr" => self.map_block(node, scope),
            "if_expr" => self.map_if(node, scope),
            "loop_expr" => {
                let body = node.child_by_field_name("body").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "loop missing body")
                })?;
                Ok(Expr {
                    kind: ExprKind::Loop(Box::new(self.map_expr(body, scope)?)),
                    span,
                })
            }
            "break_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| self.is_expr_kind(c));
                let val = inner
                    .map(|n| self.map_expr(n, scope))
                    .transpose()?
                    .map(Box::new);
                Ok(Expr {
                    kind: ExprKind::Break(val),
                    span,
                })
            }
            "continue_expr" => Ok(Expr {
                kind: ExprKind::Continue,
                span,
            }),
            "return_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| self.is_expr_kind(c));
                let val = inner
                    .map(|n| self.map_expr(n, scope))
                    .transpose()?
                    .map(Box::new);
                Ok(Expr {
                    kind: ExprKind::Return(val),
                    span,
                })
            }
            "struct_constr" => self.map_struct_constr(node, scope),
            "enum_constr" => self.map_enum_constr(node, scope),
            "array_lit" => {
                let mut cursor = node.walk();
                let mut elems = Vec::new();
                for c in node.children(&mut cursor) {
                    if self.is_expr_kind(&c) {
                        elems.push(self.map_expr(c, scope)?);
                    }
                }
                Ok(Expr {
                    kind: ExprKind::Array(elems),
                    span,
                })
            }

            // ---- Operators (named for nested CST structure) ----
            "assign_expr" => {
                let lhs = node.child_by_field_name("lhs").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "assign missing lhs")
                })?;
                let rhs = node.child_by_field_name("rhs").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "assign missing rhs")
                })?;
                Ok(Expr {
                    kind: ExprKind::Assign(
                        Box::new(self.map_expr(lhs, scope)?),
                        Box::new(self.map_expr(rhs, scope)?),
                    ),
                    span,
                })
            }
            "borrow_expr" => {
                let kind_node = node.child_by_field_name("kind").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "borrow missing kind")
                })?;
                let ref_kind = match self.get_text(kind_node) {
                    "&" => RefKind::Shared,
                    "&mut" => RefKind::Mut,
                    "&out" => RefKind::Out,
                    "&deinit" => RefKind::Drop,
                    "&uninit" => RefKind::Uninit,
                    other => {
                        return Err(self.diag(
                            kind_node,
                            ParserCode::MalformedCst,
                            format!("unknown borrow kind: {}", other),
                        ));
                    }
                };
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "borrow missing target")
                })?;
                Ok(Expr {
                    kind: ExprKind::Borrow(ref_kind, Box::new(self.map_expr(target, scope)?)),
                    span,
                })
            }
            "raw_borrow_expr" => {
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "&raw missing target")
                })?;
                Ok(Expr {
                    kind: ExprKind::RawBorrow(Box::new(self.map_expr(target, scope)?)),
                    span,
                })
            }
            "unary_expr" => {
                let operand = node.child_by_field_name("operand").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "unary expression missing operand",
                    )
                })?;
                let op_node = node.child_by_field_name("op").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "unary expression missing op",
                    )
                })?;
                let op = match self.get_text(op_node) {
                    "-" => UnOp::Neg,
                    other => {
                        return Err(self.diag(
                            op_node,
                            ParserCode::MalformedCst,
                            format!("unknown unary operator: {}", other),
                        ));
                    }
                };
                Ok(Expr {
                    kind: ExprKind::Unary(op, Box::new(self.map_expr(operand, scope)?)),
                    span,
                })
            }
            "binary_expr" => {
                let lhs = node.child_by_field_name("lhs").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing lhs",
                    )
                })?;
                let op_node = node.child_by_field_name("op").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing op",
                    )
                })?;
                let rhs = node.child_by_field_name("rhs").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing rhs",
                    )
                })?;
                let op = match self.get_text(op_node) {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "*" => BinOp::Mul,
                    "/" => BinOp::Div,
                    "%" => BinOp::Rem,
                    "==" => BinOp::Eq,
                    "!=" => BinOp::Ne,
                    "<" => BinOp::Lt,
                    "<=" => BinOp::Le,
                    ">" => BinOp::Gt,
                    ">=" => BinOp::Ge,
                    other => {
                        return Err(self.diag(
                            op_node,
                            ParserCode::MalformedCst,
                            format!("unknown binary operator: {}", other),
                        ));
                    }
                };
                Ok(Expr {
                    kind: ExprKind::Binary(
                        Box::new(self.map_expr(lhs, scope)?),
                        op,
                        Box::new(self.map_expr(rhs, scope)?),
                    ),
                    span,
                })
            }
            "field_access" => {
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "field access missing target",
                    )
                })?;
                let field = node.child_by_field_name("field").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "field access missing field")
                })?;
                Ok(Expr {
                    kind: ExprKind::FieldAccess(
                        Box::new(self.map_expr(target, scope)?),
                        self.get_text(field).to_string(),
                    ),
                    span,
                })
            }
            "deref_expr" => {
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "deref missing target")
                })?;
                Ok(Expr {
                    kind: ExprKind::Deref(Box::new(self.map_expr(target, scope)?)),
                    span,
                })
            }
            "cast_expr" => {
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "cast missing target")
                })?;
                let ty_node = node.child_by_field_name("ty").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "cast missing type")
                })?;
                Ok(Expr {
                    kind: ExprKind::Cast(
                        Box::new(self.map_expr(target, scope)?),
                        self.map_type(ty_node, scope)?,
                    ),
                    span,
                })
            }
            "call_expr" => {
                let func = node.child_by_field_name("function").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "call missing function")
                })?;
                let mut cursor = node.walk();
                let mut args = Vec::new();
                for c in node.children(&mut cursor) {
                    if c != func && self.is_expr_kind(&c) {
                        args.push(self.map_expr(c, scope)?);
                    }
                }
                Ok(Expr {
                    kind: ExprKind::Call(Box::new(self.map_expr(func, scope)?), args),
                    span,
                })
            }
            "index_expr" => {
                let target = node.child_by_field_name("target").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "index missing target")
                })?;
                let idx = node.child_by_field_name("index").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "index missing index")
                })?;
                Ok(Expr {
                    kind: ExprKind::ArrayIndex(
                        Box::new(self.map_expr(target, scope)?),
                        Box::new(self.map_expr(idx, scope)?),
                    ),
                    span,
                })
            }
            "match_expr" => {
                let scrut = node.child_by_field_name("scrutinee").ok_or_else(|| {
                    self.diag(node, ParserCode::MalformedCst, "match missing scrutinee")
                })?;
                self.map_match(node, scrut, scope)
            }

            other => Err(self.diag(
                node,
                ParserCode::MalformedCst,
                format!("unrecognized expression node kind: {}", other),
            )),
        }
    }

    fn map_block(&self, node: Node, scope: &TypeScope) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        let is_unsafe = self.get_text(node).starts_with("unsafe");
        let mut stmts = Vec::new();
        let mut tail = None;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "stmt" {
                stmts.push(self.map_stmt(child, scope)?);
            } else if self.is_expr_kind(&child) {
                // Trailing expression (has field name "tail" in grammar).
                tail = Some(Box::new(self.map_expr(child, scope)?));
            }
        }
        Ok(Expr {
            kind: ExprKind::Block(stmts, tail, is_unsafe),
            span,
        })
    }

    fn map_stmt(&self, node: Node, scope: &TypeScope) -> Result<Stmt, Diagnostic> {
        // stmt is a choice: let_stmt | defer_stmt | (expr ';').
        let child = node
            .child(0)
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "empty statement"))?;
        match child.kind() {
            "let_stmt" => self.map_let_stmt(child, scope),
            "defer_stmt" => {
                let body_node = child.child_by_field_name("body").ok_or_else(|| {
                    self.diag(child, ParserCode::MalformedCst, "defer missing body")
                })?;
                let body = self.map_expr(body_node, scope)?;
                Ok(Stmt::Defer {
                    body,
                    span: span_of(node),
                })
            }
            _ => {
                let e = self.map_expr(child, scope)?;
                Ok(Stmt::Expr(e))
            }
        }
    }

    fn map_let_stmt(&self, node: Node, scope: &TypeScope) -> Result<Stmt, Diagnostic> {
        let span = span_of(node);
        let name_node = node
            .child_by_field_name("name")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "let missing name"))?;
        let name = self.get_text(name_node).to_string();
        // `mut` is an anonymous token, detect via child text.
        let mut is_mut = false;
        let mut cursor = node.walk();
        for c in node.children(&mut cursor) {
            if self.get_text(c) == "mut" {
                is_mut = true;
                break;
            }
        }
        let ty = if let Some(t) = node.child_by_field_name("type") {
            Some(self.map_type(t, scope)?)
        } else {
            None
        };
        let init = match node.child_by_field_name("init") {
            Some(n) => Some(self.map_expr(n, scope)?),
            None => None,
        };
        Ok(Stmt::Let {
            is_mut,
            name,
            ty,
            init,
            span,
        })
    }

    fn map_if(&self, node: Node, scope: &TypeScope) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        let cond_node = node
            .child_by_field_name("cond")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "if missing cond"))?;
        let then_node = node
            .child_by_field_name("then")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "if missing then"))?;
        let else_expr = if let Some(else_node) = node.child_by_field_name("else") {
            self.map_expr(else_node, scope)?
        } else {
            // Implicit-else's span is a point at the position where
            // an `else` keyword would appear, so diagnostics on the
            // implicit-else path don't collide with the whole if.
            let then_end = then_node.end_position();
            let line = (then_end.row as u32).saturating_add(1);
            let col = (then_end.column as u32).saturating_add(1);
            Expr {
                kind: ExprKind::Block(Vec::new(), None, false),
                span: Span {
                    line,
                    col,
                    end_line: line,
                    end_col: col,
                },
            }
        };
        Ok(Expr {
            kind: ExprKind::If(
                Box::new(self.map_expr(cond_node, scope)?),
                Box::new(self.map_expr(then_node, scope)?),
                Box::new(else_expr),
            ),
            span,
        })
    }

    fn map_match(
        &self,
        node: Node,
        scrutinee_node: Node,
        scope: &TypeScope,
    ) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        let mut arms = Vec::new();
        let mut cursor = node.walk();
        for c in node.children(&mut cursor) {
            if c.kind() == "match_arm" {
                let pat_node = c.child_by_field_name("pattern").ok_or_else(|| {
                    self.diag(c, ParserCode::MalformedCst, "match arm missing pattern")
                })?;
                let body_node = c.child_by_field_name("body").ok_or_else(|| {
                    self.diag(c, ParserCode::MalformedCst, "match arm missing body")
                })?;
                arms.push((
                    self.map_pattern(pat_node)?,
                    self.map_expr(body_node, scope)?,
                ));
            }
        }
        Ok(Expr {
            kind: ExprKind::Match(Box::new(self.map_expr(scrutinee_node, scope)?), arms),
            span,
        })
    }

    fn map_pattern(&self, node: Node) -> Result<Pattern, Diagnostic> {
        let variant_node = node
            .child_by_field_name("variant")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "pattern missing variant"))?;
        let variant = self.get_text(variant_node).to_string();
        let bound = node
            .child_by_field_name("bound")
            .map(|b| self.get_text(b).to_string());
        Ok(Pattern::Variant(variant, bound))
    }

    fn map_struct_constr(&self, node: Node, scope: &TypeScope) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        let name_node = node.child_by_field_name("name").ok_or_else(|| {
            self.diag(node, ParserCode::MalformedCst, "struct constr missing name")
        })?;
        let name = self.get_text(name_node).to_string();
        let mut fields = Vec::new();
        let mut cursor = node.walk();
        for c in node.children(&mut cursor) {
            if c.kind() == "field_init" {
                let fn_name = c.child_by_field_name("name").ok_or_else(|| {
                    self.diag(c, ParserCode::MalformedCst, "field init missing name")
                })?;
                let fn_val = c.child_by_field_name("value").ok_or_else(|| {
                    self.diag(c, ParserCode::MalformedCst, "field init missing value")
                })?;
                fields.push((
                    self.get_text(fn_name).to_string(),
                    self.map_expr(fn_val, scope)?,
                ));
            }
        }
        Ok(Expr {
            kind: ExprKind::StructConstr(name, fields),
            span,
        })
    }

    fn map_enum_constr(&self, node: Node, scope: &TypeScope) -> Result<Expr, Diagnostic> {
        let span = span_of(node);
        let name_node = node
            .child_by_field_name("name")
            .ok_or_else(|| self.diag(node, ParserCode::MalformedCst, "enum constr missing name"))?;
        let variant_node = node.child_by_field_name("variant").ok_or_else(|| {
            self.diag(
                node,
                ParserCode::MalformedCst,
                "enum constr missing variant",
            )
        })?;
        let payload_node = node.child_by_field_name("payload").ok_or_else(|| {
            self.diag(
                node,
                ParserCode::MalformedCst,
                "enum constr missing payload",
            )
        })?;
        Ok(Expr {
            kind: ExprKind::EnumConstr(
                self.get_text(name_node).to_string(),
                self.get_text(variant_node).to_string(),
                Box::new(self.map_expr(payload_node, scope)?),
            ),
            span,
        })
    }

    /// True if `node` is any expression-carrying node kind that
    /// `map_expr` handles. Used to skip anonymous keyword/punctuation
    /// children when iterating for the "trailing expression" of a
    /// block or the "value" of `break`/`return`.
    fn is_expr_kind(&self, node: &Node) -> bool {
        node.kind() == "expr"
    }

    /// Parse a `markers` node (one or more `Copy`/`Drop`/`Move` in any
    /// order). Errors on duplicates.
    fn map_markers(&self, node: Node) -> Result<Markers, Diagnostic> {
        let mut seen: Vec<Marker> = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() != "marker" {
                continue;
            }
            let text = self.get_text(child);
            let m = match text {
                "Copy" => Marker::Copy,
                "Drop" => Marker::Drop,
                "Move" => Marker::Move,
                other => {
                    return Err(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        format!("unknown marker: {}", other),
                    ));
                }
            };
            if seen.contains(&m) {
                return Err(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("Duplicate marker '{}'", text),
                ));
            }
            seen.push(m);
        }
        Ok(Markers::from_iter(seen))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_struct_decl_test() {
        let source = "struct Point { x: i64, y: i64 }";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(ref s) = program.declarations[0] {
            assert_eq!(s.name, "Point");
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].name, "x");
            assert_eq!(s.fields[0].ty, i64_ty());
            assert_eq!(s.fields[1].name, "y");
            assert_eq!(s.fields[1].ty, i64_ty());
            assert!(!s.markers.declared(Marker::Copy));
            assert!(!s.markers.declared(Marker::Drop));
            assert!(!s.markers.declared(Marker::Move));
        } else {
            panic!("Expected struct declaration");
        }
    }

    #[test]
    fn parse_enum_decl_test() {
        let source = "enum Option { None: unit, Some: i64 }";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(ref e) = program.declarations[0] {
            assert_eq!(e.name, "Option");
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].name, "None");
            assert_eq!(e.variants[0].ty, unit_ty());
            assert_eq!(e.variants[1].name, "Some");
            assert_eq!(e.variants[1].ty, i64_ty());
            assert!(!e.markers.declared(Marker::Copy));
            assert!(!e.markers.declared(Marker::Drop));
            assert!(!e.markers.declared(Marker::Move));
        } else {
            panic!("Expected enum declaration");
        }
    }

    #[test]
    fn parse_struct_decl_with_markers() {
        let source = "struct Point: Copy + Drop { x: i64, y: i64 }";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(ref s) = program.declarations[0] {
            assert_eq!(s.name, "Point");
            assert!(s.markers.declared(Marker::Copy));
            assert!(s.markers.declared(Marker::Drop));
            assert!(!s.markers.declared(Marker::Move));
        } else {
            panic!("Expected struct declaration");
        }
    }

    #[test]
    fn parse_enum_decl_with_markers() {
        let source = "enum Option: Move + Drop { None: unit, Some: i64 }";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(ref e) = program.declarations[0] {
            assert_eq!(e.name, "Option");
            assert!(!e.markers.declared(Marker::Copy));
            assert!(e.markers.declared(Marker::Drop));
            assert!(e.markers.declared(Marker::Move));
        } else {
            panic!("Expected enum declaration");
        }
    }

    #[test]
    fn parse_fn_decl_test() {
        let source = "
            fn add(a: i64, b: i64) -> i64 {
                let mut sum = a;
                sum = b;
                return sum;
            }
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(ref f) = program.declarations[0] {
            assert_eq!(f.name, "add");
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.ret_ty, i64_ty());
            if let ExprKind::Block(ref stmts, ref last, _) = f.body.as_ref().unwrap().kind {
                assert_eq!(stmts.len(), 3);
                assert!(last.is_none());
            } else {
                panic!("Expected block body");
            }
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn parse_borrows_and_pointers() {
        let source = "
            fn check(ptr: *i64, r: &mut i64) {
                let a = ptr.*;
                let b = &raw a;
                let c = &out a;
                let d = &deinit a;
                let e = &uninit a;
            }
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(ref f) = program.declarations[0] {
            assert_eq!(f.params[0].ty, raw_ptr_ty(i64_ty()));
            assert_eq!(f.params[1].ty, mut_ref_ty(i64_ty()));
        } else {
            panic!("Expected function");
        }
    }

    #[test]
    fn parse_match_expression() {
        let source = "
            fn match_val(v: Option) -> i64 {
                v match {
                    Some(val) => val,
                    None => 0
                }
            }
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn parse_if_without_else() {
        let source = "
            fn check(cond: bool) {
                if cond {
                    let a = 1;
                }
            }
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn parse_constructors_and_arrays() {
        let source = "
            fn check(arr: [i64; 3]) {
                let p = Point { x: 1, y: 2 };
                let o = Option::Some(42);
                let a = [1, 2, 3];
                let val = arr[0];
            }
        ";
        let program = Parser::new(source).parse().unwrap();
    }

    #[test]
    fn parse_extern_fn() {
        let source = "
            extern fn add_impl(a: i64, b: i64) -> i64;
            extern \"C\" fn c_fn(a: f64) -> f64;
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 2);
        
        let Declaration::Fn(f1) = &program.declarations[0] else { panic!() };
        assert_eq!(f1.name, "add_impl");
        assert_eq!(f1.abi, None);
        assert!(f1.body.is_none());

        let Declaration::Fn(f2) = &program.declarations[1] else { panic!() };
        assert_eq!(f2.name, "c_fn");
        assert_eq!(f2.abi.as_deref(), Some("C"));
        assert!(f2.body.is_none());
    }

    #[test]
    fn parse_generic_extern_fn() {
        let source = "
            extern fn<'a, T: Move> add_impl(a: &mut i64, b: T);
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        let Declaration::Fn(f) = &program.declarations[0] else { panic!() };
        assert_eq!(f.name, "add_impl");
        assert_eq!(f.lifetime_params.len(), 1);
        assert_eq!(f.lifetime_params[0].0, "a");
        assert_eq!(f.type_params.len(), 1);
        assert_eq!(f.type_params[0].name, "T");
        assert!(f.body.is_none());
    }

    // Helper: extract the initializer of the first `let` statement
    // in the first function's block body. Used by the postfix/prefix
    // precedence tests to pull out an `Expr` without repeated
    // pattern-match boilerplate.
    fn first_let_init(program: &Program) -> Expr {
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        let ExprKind::Block(stmts, _, _) = &f.body.as_ref().unwrap().kind else {
            panic!("expected block body");
        };
        let Stmt::Let {
            init: Some(init), ..
        } = &stmts[0]
        else {
            panic!("expected let stmt with initializer");
        };
        init.clone()
    }

    #[test]
    fn postfix_deref_then_field_nests_correctly() {
        // Regression: `n.*.value` must parse as
        // FieldAccess(Deref(n), "value"), not something that skips
        // the deref. When _expr_postfix was a hidden rule and the
        // walker walked the flat inlined children, this got the
        // deref/field ordering wrong.
        let source = "fn f(n: *Point) { let v = n.*.value; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::FieldAccess(inner, field) = init.kind else {
            panic!("expected FieldAccess, got {:?}", init.kind);
        };
        assert_eq!(field, "value");
        assert!(
            matches!(inner.kind, ExprKind::Deref(_)),
            "expected deref inside field access, got {:?}",
            inner.kind
        );
    }

    #[test]
    fn chained_field_access() {
        // `a.b.c` → FieldAccess(FieldAccess(a, b), c).
        let source = "fn f(a: Point) { let x = a.b.c; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::FieldAccess(outer, c) = init.kind else {
            panic!("expected FieldAccess outer");
        };
        assert_eq!(c, "c");
        let ExprKind::FieldAccess(_, b) = &outer.kind else {
            panic!("expected FieldAccess inner");
        };
        assert_eq!(b, "b");
    }

    #[test]
    fn chained_array_index() {
        // `a[0][1]` → Index(Index(a, 0), 1).
        let source = "fn f(a: [[i64; 2]; 2]) { let x = a[0][1]; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::ArrayIndex(outer, _) = init.kind else {
            panic!("expected ArrayIndex outer");
        };
        assert!(matches!(outer.kind, ExprKind::ArrayIndex(_, _)));
    }

    #[test]
    fn call_then_field() {
        // `f().x` → FieldAccess(Call(f), "x"). Verifies postfix
        // chains work across mixed operator kinds.
        let source = "fn f() { let v = g().x; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::FieldAccess(target, x) = init.kind else {
            panic!("expected FieldAccess");
        };
        assert_eq!(x, "x");
        assert!(matches!(target.kind, ExprKind::Call(_, _)));
    }

    #[test]
    fn borrow_binds_looser_than_field_access() {
        // `&x.y` must parse as `&(x.y)`, not `(&x).y` — prefix
        // borrows are prec 10, postfix operators are prec 20.
        let source = "fn f(x: Point) { let r = &x.y; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::Borrow(_, inner) = init.kind else {
            panic!("expected Borrow, got {:?}", init.kind);
        };
        assert!(
            matches!(inner.kind, ExprKind::FieldAccess(_, _)),
            "expected FieldAccess inside Borrow, got {:?}",
            inner.kind
        );
    }

    #[test]
    fn assignment_is_right_associative() {
        // `a = b = c` → Assign(a, Assign(b, c)). The rhs recursion
        // in the grammar uses `_expr_assignment` (not `_expr_prefix`)
        // to make the chain right-associative.
        let source = "fn f() { a = b = c; }";
        let program = Parser::new(source).parse().unwrap();
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        let ExprKind::Block(stmts, _, _) = &f.body.as_ref().unwrap().kind else {
            panic!("expected block");
        };
        let Stmt::Expr(e) = &stmts[0] else {
            panic!("expected expr stmt");
        };
        let ExprKind::Assign(_lhs, rhs) = &e.kind else {
            panic!("expected outer assign");
        };
        assert!(
            matches!(rhs.kind, ExprKind::Assign(_, _)),
            "expected inner assign as rhs (right-assoc), got {:?}",
            rhs.kind
        );
    }

    #[test]
    fn trailing_comma_in_struct_decl() {
        // `commaSep` in the common grammar accepts an optional
        // trailing comma. Verify both with and without trailing.
        let with = Parser::new("struct P { x: i64, y: i64, }").parse().unwrap();
        let without = Parser::new("struct P { x: i64, y: i64 }").parse().unwrap();
        let Declaration::Struct(a) = &with.declarations[0] else {
            panic!()
        };
        let Declaration::Struct(b) = &without.declarations[0] else {
            panic!()
        };
        assert_eq!(a.fields.len(), 2);
        assert_eq!(b.fields.len(), 2);
    }

    #[test]
    fn trailing_comma_in_enum_decl() {
        let src = "enum E { A: unit, B: i64, }";
        let program = Parser::new(src).parse().unwrap();
        let Declaration::Enum(e) = &program.declarations[0] else {
            panic!()
        };
        assert_eq!(e.variants.len(), 2);
    }

    #[test]
    fn empty_function_body() {
        // `fn f() {}` — empty block, no trailing expression, unit
        // return.
        let program = Parser::new("fn f() {}").parse().unwrap();
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!()
        };
        let ExprKind::Block(stmts, tail, _) = &f.body.as_ref().unwrap().kind else {
            panic!("expected block body")
        };
        assert!(stmts.is_empty());
        assert!(tail.is_none());
    }

    #[test]
    fn return_and_break_without_value() {
        // `return` and `break` with no expression carry `None`.
        let program = Parser::new(
            "fn f() {
                loop {
                    break;
                };
                return;
            }",
        )
        .parse()
        .unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn line_comments_are_ignored() {
        // `# ...` line comments are declared as tree-sitter `extras`
        // and skipped by the lexer. Same source with and without
        // comments should produce equivalent AST.
        let with = "\
            # a header comment\n\
            fn f(a: i64) -> i64 {\n\
              # inline comment\n\
              a\n\
            }\n";
        let program = Parser::new(with).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }

    /// Helper: extract the parameter list of the first function in
    /// `source`. Used by the fn-type tests below.
    fn first_fn_params(source: &str) -> Vec<Param> {
        let program = Parser::new(source)
            .parse()
            .unwrap_or_else(|d| panic!("parse error:\n{}", d.errors_str().join("\n")));
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn declaration");
        };
        f.params.clone()
    }

    #[test]
    fn fn_type_with_return_arrow() {
        // `fn(i64) -> i64` → Type::Fn([i64], i64).
        let params = first_fn_params("fn caller(f: fn(i64) -> i64) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!("expected Fn type, got {:?}", params[0].ty);
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        assert_eq!(**r, i64_ty());
    }

    #[test]
    fn fn_type_without_arrow_defaults_to_unit() {
        // `fn(i64)` → Type::Fn([i64], unit). The arrow is optional;
        // absence means the callee returns `unit`.
        let params = first_fn_params("fn caller(f: fn(i64)) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!("expected Fn type, got {:?}", params[0].ty);
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        assert_eq!(**r, unit_ty());
    }

    #[test]
    fn fn_type_zero_params_no_arrow() {
        // `fn()` — nullary, no arrow → Fn([], unit).
        let params = first_fn_params("fn caller(f: fn()) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!()
        };
        assert!(p.is_empty(), "expected empty param list, got {:?}", p);
        assert_eq!(**r, unit_ty());
    }

    #[test]
    fn fn_type_zero_params_with_arrow() {
        // `fn() -> i64` — nullary with arrow → Fn([], i64).
        let params = first_fn_params("fn caller(f: fn() -> i64) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!()
        };
        assert!(p.is_empty());
        assert_eq!(**r, i64_ty());
    }

    #[test]
    fn fn_type_multi_param() {
        // `fn(i64, bool) -> bool` — verifies that all params in a
        // multi-arg list are collected, and the arrow'd return type
        // isn't accidentally included in the param list (my earlier
        // walker bug would have added it as a param).
        let params = first_fn_params("fn caller(f: fn(i64, bool) -> bool) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!()
        };
        assert_eq!(p.as_slice(), &[i64_ty(), Type::Bool]);
        assert_eq!(**r, Type::Bool);
    }

    #[test]
    fn fn_type_nested_as_param() {
        // `fn(fn(i64)) -> bool` — the fn-typed param is itself a
        // fn type. Exercises the walker's recursion.
        let params = first_fn_params("fn caller(f: fn(fn(i64)) -> bool) {}");
        let Type::Fn(outer_p, outer_r) = &params[0].ty else {
            panic!()
        };
        assert_eq!(outer_p.len(), 1);
        let Type::Fn(inner_p, inner_r) = &outer_p[0] else {
            panic!("expected nested Fn type, got {:?}", outer_p[0]);
        };
        assert_eq!(inner_p.as_slice(), &[i64_ty()]);
        assert_eq!(**inner_r, unit_ty());
        assert_eq!(**outer_r, Type::Bool);
    }

    #[test]
    fn fn_type_returns_fn_type() {
        // `fn(i64) -> fn()` — the arrow's return type is itself a
        // fn type. Verifies the walker doesn't confuse where the
        // return type ends.
        let params = first_fn_params("fn caller(f: fn(i64) -> fn()) {}");
        let Type::Fn(p, r) = &params[0].ty else {
            panic!()
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        let Type::Fn(ret_p, ret_r) = &**r else {
            panic!("expected Fn as return, got {:?}", r);
        };
        assert!(ret_p.is_empty());
        assert_eq!(**ret_r, unit_ty());
    }

    #[test]
    fn fn_type_trailing_comma_in_params() {
        // `fn(i64, bool,)` — trailing comma tolerated by commaSep.
        let params = first_fn_params("fn caller(f: fn(i64, bool,) -> bool) {}");
        let Type::Fn(p, _) = &params[0].ty else {
            panic!()
        };
        assert_eq!(p.len(), 2);
    }

    #[test]
    fn syntax_errors_emit_multiple_diagnostics() {
        // Regression against the pre-hoist single-error fallback.
        // Two otherwise-valid functions each containing an invalid
        // statement — tree-sitter's error recovery should treat the
        // two errors as independent and emit a diagnostic for each.
        let src = "\
            fn a() { @@; }\n\
            fn b() { @@; }\n";
        let diags = Parser::new(src).parse().expect_err("two broken functions");
        assert!(
            diags.error_count() >= 2,
            "expected ≥2 errors, got {}: {:?}",
            diags.error_count(),
            diags.errors_str()
        );
    }

    #[test]
    fn parse_binary_expressions_precedence() {
        // Test that binary expressions parse correctly with expected associativity/precedence.
        // e.g. `a + b * c` -> Add(a, Mul(b, c))
        let source = "fn f(a: i64, b: i64, c: i64) { let x = a + b * c; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::Binary(lhs, op, rhs) = init.kind else {
            panic!("expected Binary outer");
        };
        assert_eq!(op, BinOp::Add);
        assert!(matches!(lhs.kind, ExprKind::Variable(ref name) if name == "a"));
        let ExprKind::Binary(rlhs, rop, rrhs) = rhs.kind else {
            panic!("expected Binary inner");
        };
        assert_eq!(rop, BinOp::Mul);
        assert!(matches!(rlhs.kind, ExprKind::Variable(ref name) if name == "b"));
        assert!(matches!(rrhs.kind, ExprKind::Variable(ref name) if name == "c"));
    }

    #[test]
    fn parse_binary_expressions_with_parentheses() {
        // Test that parentheses correctly override default precedence:
        // `(a + b) * c` -> Mul(Add(a, b), c)
        let source = "fn f(a: i64, b: i64, c: i64) { let x = (a + b) * c; }";
        let init = first_let_init(&Parser::new(source).parse().unwrap());
        let ExprKind::Binary(lhs, op, rhs) = init.kind else {
            panic!("expected Binary outer");
        };
        assert_eq!(op, BinOp::Mul);
        let ExprKind::Binary(llhs, lop, lrhs) = lhs.kind else {
            panic!("expected Binary inner");
        };
        assert_eq!(lop, BinOp::Add);
        assert!(matches!(llhs.kind, ExprKind::Variable(ref name) if name == "a"));
        assert!(matches!(lrhs.kind, ExprKind::Variable(ref name) if name == "b"));
        assert!(matches!(rhs.kind, ExprKind::Variable(ref name) if name == "c"));
    }

    #[test]
    fn parse_defer_stmt() {
        let source = "
            fn f() {
                defer x = 2;
                defer {
                    let y = 1;
                };
            }
        ";
        let program = Parser::new(source).parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(ref f) = program.declarations[0] {
            if let ExprKind::Block(ref stmts, _, _) = f.body.as_ref().unwrap().kind {
                assert_eq!(stmts.len(), 2);
                assert!(matches!(stmts[0], Stmt::Defer { .. }));
                assert!(matches!(stmts[1], Stmt::Defer { .. }));
            } else {
                panic!("Expected block body");
            }
        } else {
            panic!("Expected function declaration");
        }
    }

    // Helper: parse `fn f(...) { <stmts> <tail_source> }` and return the
    // block's trailing expression, panicking if the tail is absent.
    fn block_tail(source: &str) -> Expr {
        let program = Parser::new(source).parse().unwrap();
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        let ExprKind::Block(_, tail, _) = &f.body.as_ref().unwrap().kind else {
            panic!("expected block body");
        };
        *tail
            .clone()
            .expect("expected block trailing expression, got unit tail")
    }

    #[test]
    fn block_tail_binary_expr() {
        // `{ a + b }` — trailing binary op must be captured as tail.
        let e = block_tail("fn f(a: i64, b: i64) -> i64 { a + b }");
        assert!(
            matches!(e.kind, ExprKind::Binary(_, _, _)),
            "got {:?}",
            e.kind
        );
    }

    #[test]
    fn block_tail_call_expr() {
        let e = block_tail("fn f() -> i64 { g() }");
        assert!(matches!(e.kind, ExprKind::Call(_, _)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_field_access() {
        let e = block_tail("fn f(p: Point) -> i64 { p.x }");
        assert!(
            matches!(e.kind, ExprKind::FieldAccess(_, _)),
            "got {:?}",
            e.kind
        );
    }

    #[test]
    fn block_tail_deref_expr() {
        let e = block_tail("fn f(p: *i64) -> i64 { p.* }");
        assert!(matches!(e.kind, ExprKind::Deref(_)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_cast_expr() {
        let e = block_tail("fn f(x: i64) -> i32 { x as i32 }");
        assert!(matches!(e.kind, ExprKind::Cast(_, _)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_index_expr() {
        let e = block_tail("fn f(a: [i64; 4]) -> i64 { a[0] }");
        assert!(
            matches!(e.kind, ExprKind::ArrayIndex(_, _)),
            "got {:?}",
            e.kind
        );
    }

    #[test]
    fn block_tail_match_expr() {
        let e = block_tail("fn f(o: Option) -> i64 { o match { Some(x) => 1, None => 0 } }");
        assert!(matches!(e.kind, ExprKind::Match(_, _)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_borrow_expr() {
        let e = block_tail("fn f(x: i64) -> &i64 { &x }");
        assert!(matches!(e.kind, ExprKind::Borrow(_, _)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_raw_borrow_expr() {
        let e = block_tail("fn f(x: i64) -> *i64 { &raw x }");
        assert!(matches!(e.kind, ExprKind::RawBorrow(_)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_assign_expr() {
        // `{ x = 1 }` — assignment evaluates to unit but must still be
        // captured as the tail expression, not silently dropped.
        let e = block_tail("fn f(x: i64) { let mut y = x; y = 1 }");
        assert!(matches!(e.kind, ExprKind::Assign(_, _)), "got {:?}", e.kind);
    }

    #[test]
    fn block_tail_int_literal() {
        let e = block_tail("fn f() -> i64 { 42 }");
        assert!(
            matches!(e.kind, ExprKind::Literal(Literal::Int(_, _))),
            "got {:?}",
            e.kind
        );
    }

    #[test]
    fn block_tail_identifier() {
        let e = block_tail("fn f(x: i64) -> i64 { x }");
        assert!(matches!(e.kind, ExprKind::Variable(_)), "got {:?}", e.kind);
    }
}
