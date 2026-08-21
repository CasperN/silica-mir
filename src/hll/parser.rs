//! Tree-sitter-driven HLL parser.
//!
//! Consumes `.si` source through the tree-sitter grammar at
//! `tree-sitter-silica/hll/grammar.js` and produces the typed
//! HLL AST defined in `hll::ast`. Emits structured `Diagnostics`
//! for syntax errors (multi-error output) and CST-to-AST invariant
//! failures — same error-code shape as the MIR parser.

use crate::common::{
    FloatTy, GeneratedKind, IntTy, Lifetime, LifetimeParam, Marker, Markers, OutlivesBound,
    RefKind, SourceInfo, Span,
};
use crate::diagnostics::{Diagnostic, Diagnostics};
use crate::hll::ast::*;
use crate::mir::parser::ParserCode;
use std::collections::{BTreeSet, HashSet};
use tree_sitter::{Node, Parser as TSParser};

#[derive(Clone, Default)]
struct TypeScope {
    params: BTreeSet<String>,
    self_ty: Option<Type>,
}

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

/// Map a scalar type keyword to `TypeKind`. Same table as MIR — the
/// keywords are defined once in `common/grammar.js`.
fn scalar_kind_to_type_kind(kind: &str) -> Option<TypeKind> {
    Some(match kind {
        "i8" => TypeKind::Int(IntTy::I8),
        "i16" => TypeKind::Int(IntTy::I16),
        "i32" => TypeKind::Int(IntTy::I32),
        "i64" => TypeKind::Int(IntTy::I64),
        "u8" => TypeKind::Int(IntTy::U8),
        "u16" => TypeKind::Int(IntTy::U16),
        "u32" => TypeKind::Int(IntTy::U32),
        "u64" => TypeKind::Int(IntTy::U64),
        "f32" => TypeKind::Float(FloatTy::F32),
        "f64" => TypeKind::Float(FloatTy::F64),
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

fn parse_int_literal(text: &str) -> Result<(u64, Option<IntTy>), String> {
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
    let val = u64::from_str_radix(&cleaned, radix)
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

    /// Test-only: parse `src` and panic on any parse-level failure.
    /// Panics carry the collected error text so failures are diagnosable
    /// without additional test boilerplate.
    #[cfg(test)]
    pub fn parse_or_panic(src: impl Into<String>) -> Program {
        let mut d = Diagnostics::default();
        Self::new(src)
            .parse(&mut d)
            .unwrap_or_else(|| panic!("HLL parse failed:\n{}", d.errors_str().join("\n")))
    }

    pub fn parse(&self, d: &mut Diagnostics) -> Option<Program> {
        let mut ts_parser = TSParser::new();
        if let Err(e) = ts_parser.set_language(&language()) {
            d.push_error(Diagnostic::new(
                ParserCode::MalformedCst,
                SourceInfo::generated(GeneratedKind::ParserInfrastructure, Span::default()),
                format!("failed to load tree-sitter grammar: {}", e),
            ));
            return None;
        }

        let Some(tree) = ts_parser.parse(&*self.source, None) else {
            d.push_error(Diagnostic::new(
                ParserCode::MalformedCst,
                SourceInfo::generated(GeneratedKind::ParserInfrastructure, Span::default()),
                "tree-sitter failed to produce a parse tree",
            ));
            return None;
        };
        let root = tree.root_node();

        if root.has_error() {
            self.walk_syntax_errors(root, None, None, d);
            return None;
        }

        let program = self.map_program(root, d);
        if d.has_errors() {
            None
        } else {
            program
        }
    }

    fn get_text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    fn diag(&self, node: Node, code: ParserCode, msg: impl Into<String>) -> Diagnostic {
        Diagnostic::new(code, SourceInfo::written(span_of(node)), msg)
    }

    fn reject_self_ident(
        &self,
        name: &str,
        node: Node,
        position: &str,
        d: &mut Diagnostics,
    ) -> bool {
        if name != "Self" {
            return false;
        }
        d.push_error(self.diag(
            node,
            ParserCode::ReservedIdent,
            format!("'Self' is reserved and cannot be used as {}", position),
        ));
        true
    }

    fn lit_diag<T>(&self, res: Result<T, String>, node: Node, d: &mut Diagnostics) -> Option<T> {
        match res {
            Ok(v) => Some(v),
            Err(s) => {
                d.push_error(self.diag(node, ParserCode::InvalidLiteral, s));
                None
            }
        }
    }

    /// Walk the CST emitting one diagnostic per ERROR/MISSING node. Function
    /// context retains the enclosing trait or impl identity so equally named
    /// methods remain distinguishable even when parsing fails before an AST
    /// can be built.
    fn walk_syntax_errors<'a>(
        &'a self,
        node: Node<'a>,
        owner: Option<&str>,
        ctx_fn: Option<&str>,
        diags: &mut Diagnostics,
    ) {
        let next_owner = match node.kind() {
            "trait_decl" => node
                .child_by_field_name("name")
                .map(|name| self.get_text(name).to_string()),
            "impl_decl" => node.child_by_field_name("target").map(|target| {
                let target = self.get_text(target);
                if let Some(trait_name) = node.child_by_field_name("trait_name") {
                    let mut trait_path = self.get_text(trait_name).to_string();
                    let mut cursor = node.walk();
                    if let Some(args) = node
                        .children(&mut cursor)
                        .find(|child| child.kind() == "type_args")
                    {
                        trait_path.push_str(self.get_text(args));
                    }
                    format!("<{} as {}>", target, trait_path)
                } else {
                    format!("<{}>", target)
                }
            }),
            _ => owner.map(str::to_string),
        };
        let next_owner = next_owner.as_deref();

        let next_ctx_fn = if node.kind() == "fn_decl" {
            node.child_by_field_name("name").map(|name| {
                let name = self.get_text(name);
                match next_owner {
                    Some(owner) => format!("{}::{}", owner, name),
                    None => name.to_string(),
                }
            })
        } else {
            ctx_fn.map(str::to_string)
        };
        let next_ctx_fn = next_ctx_fn.as_deref();

        if node.is_missing() {
            let mut d = Diagnostic::new(
                ParserCode::MissingToken,
                SourceInfo::written(span_of(node)),
                format!("missing '{}'", node.kind()),
            );
            if let Some(f) = next_ctx_fn {
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
            let mut d = Diagnostic::new(
                ParserCode::UnexpectedToken,
                SourceInfo::written(span_of(node)),
                msg,
            );
            if let Some(f) = next_ctx_fn {
                d = d.in_function(f);
            }
            diags.push_error(d);
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_syntax_errors(child, next_owner, next_ctx_fn, diags);
        }
    }

    fn map_program(&self, node: Node, d: &mut Diagnostics) -> Option<Program> {
        let mut declarations = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "declaration" {
                if let Some(decl) = self.map_declaration(child, d) {
                    declarations.push(decl);
                }
            }
        }
        Some(Program {
            declarations,
            source: self.source.clone(),
        })
    }

    fn map_declaration(&self, node: Node, d: &mut Diagnostics) -> Option<Declaration> {
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "empty declaration"));
            return None;
        };
        match child.kind() {
            "struct_decl" => Some(Declaration::Struct(self.map_struct_decl(child, d)?)),
            "enum_decl" => Some(Declaration::Enum(self.map_enum_decl(child, d)?)),
            "fn_decl" => Some(Declaration::Fn(self.map_fn_decl(child, d)?)),
            "trait_decl" => Some(Declaration::Trait(self.map_trait_decl(child, d)?)),
            "impl_decl" => Some(Declaration::Impl(self.map_impl_decl(child, d)?)),
            _ => {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("unknown declaration kind: {}", child.kind()),
                ));
                None
            }
        }
    }

    fn map_struct_decl(&self, node: Node, d: &mut Diagnostics) -> Option<StructDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "struct decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        if self.reject_self_ident(&name, name_node, "a struct name", d) {
            return None;
        }
        let name_span = span_of(name_node);
        let span = span_of(node);

        let mut scope = TypeScope::default();
        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            let (markers, redundant_move) =
                Markers::from_declared(self.map_marker_tokens(markers_node, d)?);
            if redundant_move {
                d.push_info(Diagnostic::new(
                    ParserCode::MoveMarkerRedundant,
                    SourceInfo::written(name_span),
                    Markers::redundant_move_message(&name),
                ));
            }
            markers
        } else {
            Markers::empty()
        };

        let mut fields = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "struct_field" {
                let Some(f_name_node) = child.child_by_field_name("name") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "struct field missing name",
                    ));
                    continue;
                };
                let Some(f_type_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "struct field missing type",
                    ));
                    continue;
                };
                let Some(ty) = self.map_type(f_type_node, &scope, d) else {
                    continue;
                };
                fields.push(StructField {
                    name: self.get_text(f_name_node).to_string(),
                    ty,
                    source: SourceInfo::written(span_of(child)),
                });
            }
        }

        Some(StructDecl {
            name,
            lifetime_params,
            outlives,
            type_params,
            markers,
            fields,
            source: SourceInfo::written(span),
        })
    }

    fn map_enum_decl(&self, node: Node, d: &mut Diagnostics) -> Option<EnumDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "enum decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        if self.reject_self_ident(&name, name_node, "an enum name", d) {
            return None;
        }
        let name_span = span_of(name_node);
        let span = span_of(node);

        let mut scope = TypeScope::default();
        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            let (markers, redundant_move) =
                Markers::from_declared(self.map_marker_tokens(markers_node, d)?);
            if redundant_move {
                d.push_info(Diagnostic::new(
                    ParserCode::MoveMarkerRedundant,
                    SourceInfo::written(name_span),
                    Markers::redundant_move_message(&name),
                ));
            }
            markers
        } else {
            Markers::empty()
        };

        let mut variants = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "enum_variant" {
                let Some(v_name_node) = child.child_by_field_name("name") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "enum variant missing name",
                    ));
                    continue;
                };
                let Some(v_type_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "enum variant missing type",
                    ));
                    continue;
                };
                let Some(ty) = self.map_type(v_type_node, &scope, d) else {
                    continue;
                };
                variants.push(EnumVariant {
                    name: self.get_text(v_name_node).to_string(),
                    ty,
                    source: SourceInfo::written(span_of(child)),
                });
            }
        }

        Some(EnumDecl {
            name,
            lifetime_params,
            outlives,
            type_params,
            markers,
            variants,
            source: SourceInfo::written(span),
        })
    }

    fn map_fn_decl(&self, node: Node, d: &mut Diagnostics) -> Option<FnDecl> {
        self.map_fn_decl_in_scope(node, &TypeScope::default(), None, d)
    }

    /// Resolve the optional `abi` clause on a fn decl or fn type. Emits
    /// `PARSE-UnknownAbi` and recovers as `Abi::Silica` when the clause
    /// text isn't a supported ABI or spells the default redundantly.
    fn parse_abi_clause(&self, node: Node, d: &mut Diagnostics) -> Abi {
        let Some(abi_node) = node.child_by_field_name("abi") else {
            return Abi::Silica;
        };
        let raw = self.get_text(abi_node);
        if let Some(abi) = Abi::from_str(raw) {
            return abi;
        }
        let msg = if raw == "\"Silica\"" {
            "the Silica ABI is the default; omit the ABI string".to_string()
        } else {
            format!("unknown extern ABI {} — expected \"C\" or bare extern", raw)
        };
        d.push_error(self.diag(abi_node, ParserCode::UnknownAbi, msg));
        Abi::Silica
    }

    fn map_fn_decl_in_scope(
        &self,
        node: Node,
        enclosing_scope: &TypeScope,
        enclosing_context: Option<&str>,
        d: &mut Diagnostics,
    ) -> Option<FnDecl> {
        let errors_before = d.error_count();
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "fn decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        let span = span_of(node);

        let is_unsafe = node.child_by_field_name("unsafe").is_some();
        let linkage = if node.child_by_field_name("extern").is_some() {
            Linkage::Foreign
        } else {
            Linkage::Local
        };
        let abi = self.parse_abi_clause(node, d);

        let mut scope = enclosing_scope.clone();
        let mut cursor = node.walk();
        let type_params_result = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, &mut scope, d)
        } else {
            Some((Vec::new(), Vec::new(), Vec::new()))
        };

        let mut params = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "param_decl" {
                let Some(p_name_node) = child.child_by_field_name("name") else {
                    d.push_error(self.diag(child, ParserCode::MalformedCst, "param missing name"));
                    continue;
                };
                let Some(p_type_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(child, ParserCode::MalformedCst, "param missing type"));
                    continue;
                };
                let Some(ty) = self.map_type(p_type_node, &scope, d) else {
                    continue;
                };
                params.push(Param {
                    name: self.get_text(p_name_node).to_string(),
                    ty,
                    source: SourceInfo::written(span_of(child)),
                });
            } else if child.kind() == "self_param" {
                if let Some(param) = self.map_self_param(child, &scope, d) {
                    params.push(param);
                }
            }
        }

        let ret_ty = if let Some(rt_node) = node.child_by_field_name("return_type") {
            self.map_type(rt_node, &scope, d)
        } else {
            Some(Type::new(
                TypeKind::Tuple(Vec::new()),
                SourceInfo::generated(GeneratedKind::HllDesugaring, span),
            ))
        };

        let body = if let Some(body_node) = node.child_by_field_name("body") {
            self.map_expr(body_node, &scope, d).map(Some)
        } else {
            Some(None)
        };

        d.annotate_errors_in_function(errors_before, enclosing_context.unwrap_or(&name));

        let (lifetime_params, type_params, outlives) = type_params_result?;
        let ret_ty = ret_ty?;
        let body = body?;

        Some(FnDecl {
            name,
            linkage,
            abi,
            is_unsafe,
            lifetime_params,
            outlives,
            type_params,
            params,
            ret_ty,
            body,
            source: SourceInfo::written(span),
        })
    }

    fn map_self_param(
        &self,
        node: Node,
        scope: &TypeScope,
        _d: &mut Diagnostics,
    ) -> Option<Param> {
        let span = span_of(node);
        let self_target = if let Some(st) = &scope.self_ty {
            st.clone()
        } else if scope.params.contains("Self") {
            Type::new(
                TypeKind::Param("Self".to_string()),
                SourceInfo::written(span),
            )
        } else {
            Type::new(
                TypeKind::Custom(Instance::new("Self", Vec::new(), Vec::new())),
                SourceInfo::written(span),
            )
        };

        let mut cursor = node.walk();
        let has_amp = node.children(&mut cursor).any(|c| c.kind() == "&");
        let ty = if has_amp {
            let mut ref_kind = RefKind::Shared;
            let mut lifetime = None;
            for child in node.children(&mut cursor) {
                match child.kind() {
                    "mut" => ref_kind = RefKind::Mut,
                    "drop" => ref_kind = RefKind::Drop,
                    "out" => ref_kind = RefKind::Out,
                    "uninit" => ref_kind = RefKind::Uninit,
                    "lifetime" => {
                        let text = self.get_text(child);
                        lifetime = Some(Lifetime(text.trim_start_matches('\'').to_string()));
                    }
                    _ => {}
                }
            }
            Type::new(
                TypeKind::Ref(ref_kind, lifetime, Box::new(self_target)),
                SourceInfo::written(span),
            )
        } else {
            self_target
        };

        Some(Param {
            name: "self".to_string(),
            ty,
            source: SourceInfo::written(span),
        })
    }

    fn map_trait_decl(&self, node: Node, d: &mut Diagnostics) -> Option<TraitDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "trait decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        if self.reject_self_ident(&name, name_node, "a trait name", d) {
            return None;
        }
        let mut scope = TypeScope::default();
        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(params) = node
            .children(&mut cursor)
            .find(|child| child.kind() == "type_params")
        {
            self.map_type_params(params, &mut scope, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };
        scope.params.insert("Self".to_string());
        let mut bounds_cursor = node.walk();
        let self_bounds = if let Some(bounds) = node
            .children(&mut bounds_cursor)
            .find(|child| child.kind() == "trait_bounds")
        {
            self.map_trait_bounds(bounds, &scope, d)?
        } else {
            Bounds::default()
        };
        let mut methods = Vec::new();
        let mut names = HashSet::new();
        for child in node.children(&mut cursor) {
            if child.kind() != "fn_decl" {
                continue;
            }
            let method_name = child
                .child_by_field_name("name")
                .map(|node| self.get_text(node))
                .unwrap_or("<missing>");
            let context = trait_method_context(&name, method_name);
            let mut method = self.map_fn_decl_in_scope(child, &scope, Some(&context), d)?;
            if method.linkage == Linkage::Foreign {
                if child.child_by_field_name("abi").is_none() {
                    d.push_error(
                        self.diag(
                            child,
                            ParserCode::InvalidFnModifiers,
                            format!("trait method '{}' cannot be extern without an ABI clause; trait methods have no foreign symbol", method.name),
                        )
                        .in_function(&context),
                    );
                    continue;
                }
                method.linkage = Linkage::Local;
            }
            if !names.insert(method.name.clone()) {
                d.push_error(
                    self.diag(
                        child,
                        ParserCode::MalformedCst,
                        format!("duplicate trait method '{}'", method.name),
                    )
                    .in_function(&context),
                );
                continue;
            }
            methods.push(method);
        }

        Some(TraitDecl {
            name,
            lifetime_params,
            outlives,
            type_params,
            self_bounds,
            methods,
            source: SourceInfo::written(span_of(node)),
        })
    }

    fn map_impl_decl(&self, node: Node, d: &mut Diagnostics) -> Option<ImplBlock> {
        let trait_name_node = node.child_by_field_name("trait_name");
        if let Some(trait_name_node) = trait_name_node {
            if self.reject_self_ident(
                self.get_text(trait_name_node),
                trait_name_node,
                "a trait reference",
                d,
            ) {
                return None;
            }
        }
        let mut scope = TypeScope::default();
        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(params) = node
            .children(&mut cursor)
            .find(|child| child.kind() == "type_params")
        {
            self.map_type_params(params, &mut scope, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };
        let trait_path = if let Some(trait_name_node) = trait_name_node {
            let (trait_lifetimes, trait_types) = if let Some(args) = node
                .children(&mut cursor)
                .find(|child| child.kind() == "type_args")
            {
                self.map_type_args(args, &scope, d)?
            } else {
                (Vec::new(), Vec::new())
            };
            Some(Instance::new(
                self.get_text(trait_name_node),
                trait_lifetimes,
                trait_types,
            ))
        } else {
            None
        };
        let Some(target_node) = node.child_by_field_name("target") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "impl decl missing target"));
            return None;
        };
        let target = self.map_type(target_node, &scope, d)?;
        scope.self_ty = Some(target.clone());

        let mut methods = Vec::new();
        let mut names = HashSet::new();
        for child in node.children(&mut cursor) {
            if child.kind() != "fn_decl" {
                continue;
            }
            let method_name = child
                .child_by_field_name("name")
                .map(|node| self.get_text(node))
                .unwrap_or("<missing>");
            let context = impl_method_context(&target, trait_path.as_ref(), method_name);
            let mut method = self.map_fn_decl_in_scope(child, &scope, Some(&context), d)?;
            if method.linkage == Linkage::Foreign {
                if child.child_by_field_name("abi").is_none() {
                    d.push_error(
                        self.diag(
                            child,
                            ParserCode::InvalidFnModifiers,
                            format!("impl method '{}' cannot be extern without an ABI clause; impl methods have no foreign symbol", method.name),
                        )
                        .in_function(&context),
                    );
                    continue;
                }
                method.linkage = Linkage::Local;
            }
            if !names.insert(method.name.clone()) {
                d.push_error(
                    self.diag(
                        child,
                        ParserCode::MalformedCst,
                        format!("duplicate impl method '{}'", method.name),
                    )
                    .in_function(&context),
                );
                continue;
            }
            methods.push(method);
        }

        Some(ImplBlock {
            lifetime_params,
            outlives,
            type_params,
            trait_path,
            target,
            methods,
            source: SourceInfo::written(span_of(node)),
        })
    }

    /// Map a `type` (or scalar/keyword token) CST node to `Type`.
    /// `scope` is the set of in-scope type-parameter names for the
    /// enclosing decl; a bare identifier that matches becomes
    /// `TypeKind::Param`, otherwise `TypeKind::Custom` (possibly with args).
    fn map_type(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Type> {
        let kind = self.map_type_kind(node, scope, d)?;
        Some(Type::new(kind, SourceInfo::written(span_of(node))))
    }

    /// Parse a type's structural kind. [`Self::map_type`] owns construction of
    /// the source-bearing outer node; recursive calls construct source-bearing
    /// child types from their own CST nodes.
    fn map_type_kind(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<TypeKind> {
        // Shared type rule with MIR; the shape is identical.
        if let Some(ty) = scalar_kind_to_type_kind(node.kind()) {
            return Some(ty);
        }
        match node.kind() {
            "bool" => return Some(TypeKind::Bool),
            "tuple_type" => {
                let mut elem_types = Vec::new();
                for i in 0..node.named_child_count() {
                    if let Some(child) = node.named_child(i as u32) {
                        elem_types.push(self.map_type(child, scope, d)?);
                    }
                }
                return Some(TypeKind::Tuple(elem_types));
            }
            "never" => return Some(TypeKind::Never),
            "identifier" => {
                return Some(self.identifier_to_type_kind(
                    self.get_text(node),
                    Vec::new(),
                    Vec::new(),
                    scope,
                ))
            }
            "type" => {}
            _ => {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("unexpected node kind in type: {}", node.kind()),
                ));
                return None;
            }
        }

        let Some(first) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "type node has no children"));
            return None;
        };
        if let Some(ty) = scalar_kind_to_type_kind(first.kind()) {
            return Some(ty);
        }
        match first.kind() {
            "bool" => return Some(TypeKind::Bool),
            "tuple_type" => {
                let mut elem_types = Vec::new();
                for i in 0..first.named_child_count() {
                    if let Some(child) = first.named_child(i as u32) {
                        elem_types.push(self.map_type(child, scope, d)?);
                    }
                }
                return Some(TypeKind::Tuple(elem_types));
            }
            "never" => return Some(TypeKind::Never),
            "identifier" => {
                // Identifier alt with optional `type_args` as sibling:
                // `Foo`, `Foo<T, U>`, `Foo<'a, T>`.
                let text = self.get_text(first);
                let (lifetimes, args) = if let Some(ta) = node.child(1) {
                    if ta.kind() == "type_args" {
                        self.map_type_args(ta, scope, d)?
                    } else {
                        (Vec::new(), Vec::new())
                    }
                } else {
                    (Vec::new(), Vec::new())
                };
                return Some(self.identifier_to_type_kind(text, lifetimes, args, scope));
            }
            _ => {}
        }

        let text = self.get_text(first);
        if text == "&" {
            let mut cursor = node.walk();
            let children: Vec<Node> = node.children(&mut cursor).collect();
            let mut idx = 1;
            let lt = if idx < children.len() && children[idx].kind() == "lifetime" {
                let lt = Lifetime(self.get_text(children[idx]).trim_start_matches('\'').to_string());
                idx += 1;
                Some(lt)
            } else {
                None
            };
            let kind = if idx < children.len() {
                match self.get_text(children[idx]) {
                    "mut" => {
                        idx += 1;
                        RefKind::Mut
                    }
                    "out" => {
                        idx += 1;
                        RefKind::Out
                    }
                    "drop" => {
                        idx += 1;
                        RefKind::Drop
                    }
                    "uninit" => {
                        idx += 1;
                        RefKind::Uninit
                    }
                    _ => RefKind::Shared,
                }
            } else {
                RefKind::Shared
            };
            let Some(&inner) = children.get(idx) else {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    "missing inner type for reference",
                ));
                return None;
            };
            return Some(TypeKind::Ref(
                kind,
                lt,
                Box::new(self.map_type(inner, scope, d)?),
            ));
        }
        if text == "*" {
            let Some(inner) = node.child(1) else {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    "missing inner type for raw pointer",
                ));
                return None;
            };
            return Some(TypeKind::RawPtr(Box::new(self.map_type(inner, scope, d)?)));
        }
        if text == "[" {
            let Some(elem) = node.child_by_field_name("element") else {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    "array type missing element",
                ));
                return None;
            };
            let Some(len_node) = node.child_by_field_name("length") else {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    "array type missing length",
                ));
                return None;
            };
            let (len, _) =
                self.lit_diag(parse_int_literal(self.get_text(len_node)), len_node, d)?;
            return Some(TypeKind::Array(
                Box::new(self.map_type(elem, scope, d)?),
                len,
            ));
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
                    params.push(self.map_type(child, scope, d)?);
                }
            }
            let ret = if let Some(rt) = ret_node {
                self.map_type(rt, scope, d)?
            } else {
                Type::new(
                    TypeKind::Tuple(Vec::new()),
                    SourceInfo::generated(GeneratedKind::HllDesugaring, span_of(node)),
                )
            };
            let abi = self.parse_abi_clause(node, d);
            return Some(TypeKind::Fn {
                abi,
                params,
                ret: Box::new(ret),
            });
        }
        d.push_error(self.diag(
            first,
            ParserCode::MalformedCst,
            format!("unexpected token in type: {}", text),
        ));
        None
    }

    /// Resolve a bare identifier that appeared in type position. If
    /// `name` is in the current scope, produce `TypeKind::Param(name)` —
    /// but only when there are no type arguments, since a type
    /// parameter can't be instantiated. Otherwise produce
    /// `TypeKind::Custom(name, args)`.
    fn identifier_to_type_kind(
        &self,
        name: &str,
        lifetimes: Vec<Lifetime>,
        args: Vec<Type>,
        scope: &TypeScope,
    ) -> TypeKind {
        if name == "Self" && lifetimes.is_empty() && args.is_empty() {
            if let Some(self_ty) = &scope.self_ty {
                return self_ty.kind.clone();
            }
        }
        if lifetimes.is_empty() && args.is_empty() && scope.params.contains(name) {
            TypeKind::Param(name.to_string())
        } else {
            TypeKind::Custom(Instance::new(name.to_string(), lifetimes, args))
        }
    }

    /// Parse a `type_params` node (`<'a, 'b: 'a, T, U: Copy + Drop>`)
    /// into (lifetime_params, type_params, outlives). Populates
    /// `scope` with each type-param name so subsequent `map_type`
    /// calls see them as `Param`s. Outlives pairs
    /// `(subject, must_outlive)` are collected from the `'a: 'b + 'c`
    /// inline bounds; the tuple convention matches
    /// `DeclMeta::outlives` at the MIR side.
    fn map_type_params(
        &self,
        node: Node,
        scope: &mut TypeScope,
        d: &mut Diagnostics,
    ) -> Option<(Vec<LifetimeParam>, Vec<TypeParam>, Vec<OutlivesBound>)> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut outlives = Vec::new();
        let mut declared_here = HashSet::new();
        let mut pre_cursor = node.walk();
        for child in node
            .children(&mut pre_cursor)
            .filter(|c| c.kind() == "type_param")
        {
            let Some(name_node) = child.child_by_field_name("name") else {
                d.push_error(self.diag(child, ParserCode::MalformedCst, "type param missing name"));
                return None;
            };
            let name = self.get_text(name_node).to_string();
            if self.reject_self_ident(&name, name_node, "a type parameter", d) {
                return None;
            }
            if scope.params.contains(&name) || !declared_here.insert(name.clone()) {
                d.push_error(self.diag(
                    name_node,
                    ParserCode::MalformedCst,
                    format!("Duplicate type parameter '{}'", name),
                ));
                return None;
            }
            scope.params.insert(name);
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "lifetime_param" => {
                    let Some(name_node) = child.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "lifetime param missing name",
                        ));
                        continue;
                    };
                    let subject = Lifetime(
                        self.get_text(name_node)
                            .trim_start_matches('\'')
                            .to_string(),
                    );
                    lifetimes.push(LifetimeParam::written(subject.clone(), span_of(child)));
                    let mut bcursor = child.walk();
                    for bound_node in child.children_by_field_name("bound", &mut bcursor) {
                        let bound = Lifetime(
                            self.get_text(bound_node)
                                .trim_start_matches('\'')
                                .to_string(),
                        );
                        outlives.push(OutlivesBound::written(
                            subject.clone(),
                            bound,
                            span_of(bound_node),
                        ));
                    }
                }
                "type_param" => {
                    let Some(name_node) = child.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "type param missing name",
                        ));
                        continue;
                    };
                    let pname = self.get_text(name_node).to_string();
                    let mut child_cursor = child.walk();
                    let bounds = if let Some(bounds) = child
                        .children(&mut child_cursor)
                        .find(|node| node.kind() == "trait_bounds")
                    {
                        self.map_trait_bounds(bounds, scope, d)?
                    } else {
                        Bounds::default()
                    };
                    types.push(TypeParam {
                        name: pname,
                        bounds,
                        source: SourceInfo::written(span_of(child)),
                    });
                }
                // Other CST children (`<`, `>`, `,`) are literal
                // punctuation — nothing to map.
                _ => {}
            }
        }
        Some((lifetimes, types, outlives))
    }

    fn map_trait_bounds(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<Bounds> {
        let mut marker_bounds = Vec::new();
        let mut trait_bounds = Vec::new();
        let mut cursor = node.walk();
        for bound in node.children_by_field_name("bound", &mut cursor) {
            let Some(trait_name) = bound.child_by_field_name("name") else {
                d.push_error(self.diag(
                    bound,
                    ParserCode::MalformedCst,
                    "trait bound missing name",
                ));
                return None;
            };
            let name = self.get_text(trait_name).to_string();
            if self.reject_self_ident(&name, trait_name, "a trait bound", d) {
                return None;
            }
            let mut args_cursor = bound.walk();
            let (lifetime_args, type_args) = if let Some(args) = bound
                .children(&mut args_cursor)
                .find(|node| node.kind() == "type_args")
            {
                self.map_type_args(args, scope, d)?
            } else {
                (Vec::new(), Vec::new())
            };
            let marker = (lifetime_args.is_empty() && type_args.is_empty())
                .then(|| match name.as_str() {
                    "Copy" => Some(Marker::Copy),
                    "Drop" => Some(Marker::Drop),
                    "Move" => Some(Marker::Move),
                    _ => None,
                })
                .flatten();
            if let Some(marker) = marker {
                if marker_bounds.contains(&marker) {
                    d.push_error(self.diag(
                        bound,
                        ParserCode::MalformedCst,
                        format!("Duplicate marker '{}'", name),
                    ));
                    return None;
                }
                marker_bounds.push(marker);
                continue;
            }
            let trait_bound = TraitBound {
                trait_path: Instance::new(name, lifetime_args, type_args),
                source: SourceInfo::written(span_of(bound)),
            };
            if trait_bounds.contains(&trait_bound) {
                d.push_error(self.diag(
                    bound,
                    ParserCode::MalformedCst,
                    format!("Duplicate trait bound '{}'", trait_bound.trait_path),
                ));
                return None;
            }
            trait_bounds.push(trait_bound);
        }
        Some(Bounds {
            markers: Markers::from_iter(marker_bounds),
            traits: trait_bounds,
        })
    }

    /// Parse a `type_args` node (`<'a, T, U>`) into (lifetime_args, type_args).
    fn map_type_args(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<(Vec<Lifetime>, Vec<Type>)> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "lifetime" {
                let name = self.get_text(child).trim_start_matches('\'').to_string();
                lifetimes.push(Lifetime(name));
            } else if child.kind() == "type" || scalar_kind_to_type_kind(child.kind()).is_some() {
                types.push(self.map_type(child, scope, d)?);
            }
        }
        Some((lifetimes, types))
    }

    /// Walk any expression-carrying node into a typed `Expr`. All
    /// operator forms (assign, borrow, field access, deref, downcast,
    /// call, index, match) are named rules in the grammar, so
    /// dispatch is straight by `node.kind()`. The `expr` node itself
    /// is a thin wrapper containing exactly one child — recurse into
    /// it.
    fn map_expr(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Expr> {
        let span = span_of(node);
        match node.kind() {
            "expr" => {
                let Some(child) = node.child(0) else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "expr wrapper empty"));
                    return None;
                };
                self.map_expr(child, scope, d)
            }

            // ---- Literals + identifier ----
            "int_lit" => {
                let (val, ty) = self.lit_diag(parse_int_literal(self.get_text(node)), node, d)?;
                Some(Expr {
                    kind: ExprKind::Literal(Literal::Int(val, ty)),
                    source: SourceInfo::written(span),
                })
            }
            "float_lit" => {
                let (val, ty) = self.lit_diag(parse_float_literal(self.get_text(node)), node, d)?;
                Some(Expr {
                    kind: ExprKind::Literal(Literal::Float(val, ty)),
                    source: SourceInfo::written(span),
                })
            }
            "bool_lit" => Some(Expr {
                kind: ExprKind::Literal(Literal::Bool(self.get_text(node) == "true")),
                source: SourceInfo::written(span),
            }),
            "tuple_expr" => {
                let mut elems = Vec::new();
                for i in 0..node.named_child_count() {
                    if let Some(child) = node.named_child(i as u32) {
                        elems.push(self.map_expr(child, scope, d)?);
                    }
                }
                Some(Expr {
                    kind: ExprKind::Tuple(elems),
                    source: SourceInfo::written(span),
                })
            }
            "byte_str_lit" => {
                let raw = self.get_text(node);
                let Some(inner) = raw.strip_prefix("b\"").and_then(|s| s.strip_suffix('"')) else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "malformed byte string literal",
                    ));
                    return None;
                };
                let bytes =
                    self.lit_diag(crate::mir::parser::decode_byte_escapes(inner), node, d)?;
                Some(Expr {
                    kind: ExprKind::Literal(Literal::ByteStr(bytes)),
                    source: SourceInfo::written(span),
                })
            }
            "byte_char_lit" => {
                let raw = self.get_text(node);
                let Some(inner) = raw.strip_prefix("b'").and_then(|s| s.strip_suffix('\'')) else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "malformed byte character literal",
                    ));
                    return None;
                };
                let bytes =
                    self.lit_diag(crate::mir::parser::decode_byte_escapes(inner), node, d)?;
                if bytes.len() != 1 {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "byte character literal must be exactly one byte",
                    ));
                    return None;
                }
                Some(Expr {
                    kind: ExprKind::Literal(Literal::Int(u64::from(bytes[0]), Some(IntTy::U8))),
                    source: SourceInfo::written(span),
                })
            }
            "identifier" => Some(Expr {
                kind: ExprKind::Variable(self.get_text(node).to_string()),
                source: SourceInfo::written(span),
            }),

            // ---- Compound primaries ----
            "paren_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| c.kind() == "expr");
                if let Some(e) = inner {
                    self.map_expr(e, scope, d)
                } else {
                    Some(Expr {
                        kind: ExprKind::Tuple(Vec::new()),
                        source: SourceInfo::written(span),
                    })
                }
            }
            "block_expr" => self.map_block(node, scope, d),
            "if_expr" => self.map_if(node, scope, d),
            "loop_expr" => {
                let Some(body) = node.child_by_field_name("body") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "loop missing body"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Loop(Box::new(self.map_expr(body, scope, d)?)),
                    source: SourceInfo::written(span),
                })
            }
            "break_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| self.is_expr_kind(c));
                let val = match inner {
                    Some(n) => Some(Box::new(self.map_expr(n, scope, d)?)),
                    None => None,
                };
                Some(Expr {
                    kind: ExprKind::Break(val),
                    source: SourceInfo::written(span),
                })
            }
            "continue_expr" => Some(Expr {
                kind: ExprKind::Continue,
                source: SourceInfo::written(span),
            }),
            "return_expr" => {
                let mut cursor = node.walk();
                let inner = node.children(&mut cursor).find(|c| self.is_expr_kind(c));
                let val = match inner {
                    Some(n) => Some(Box::new(self.map_expr(n, scope, d)?)),
                    None => None,
                };
                Some(Expr {
                    kind: ExprKind::Return(val),
                    source: SourceInfo::written(span),
                })
            }
            "struct_constr" => self.map_struct_constr(node, scope, d),
            "scoped_identifier" => self.map_scoped_identifier(node, scope, d),
            "array_lit" => {
                let mut cursor = node.walk();
                let mut elems = Vec::new();
                for c in node.children(&mut cursor) {
                    if self.is_expr_kind(&c) {
                        elems.push(self.map_expr(c, scope, d)?);
                    }
                }
                Some(Expr {
                    kind: ExprKind::Array(elems),
                    source: SourceInfo::written(span),
                })
            }

            // ---- Operators (named for nested CST structure) ----
            "assign_expr" => {
                let Some(lhs) = node.child_by_field_name("lhs") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "assign missing lhs"));
                    return None;
                };
                let Some(rhs) = node.child_by_field_name("rhs") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "assign missing rhs"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Assign(
                        Box::new(self.map_expr(lhs, scope, d)?),
                        Box::new(self.map_expr(rhs, scope, d)?),
                    ),
                    source: SourceInfo::written(span),
                })
            }
            "borrow_expr" => {
                let Some(kind_node) = node.child_by_field_name("kind") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "borrow missing kind"));
                    return None;
                };
                let ref_kind = match self.get_text(kind_node) {
                    "&" => RefKind::Shared,
                    "&mut" => RefKind::Mut,
                    "&out" => RefKind::Out,
                    "&drop" => RefKind::Drop,
                    "&uninit" => RefKind::Uninit,
                    other => {
                        d.push_error(self.diag(
                            kind_node,
                            ParserCode::MalformedCst,
                            format!("unknown borrow kind: {}", other),
                        ));
                        return None;
                    }
                };
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "borrow missing target",
                    ));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Borrow(ref_kind, Box::new(self.map_expr(target, scope, d)?)),
                    source: SourceInfo::written(span),
                })
            }
            "raw_borrow_expr" => {
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "&raw missing target"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::RawBorrow(Box::new(self.map_expr(target, scope, d)?)),
                    source: SourceInfo::written(span),
                })
            }
            "unary_expr" => {
                let Some(operand) = node.child_by_field_name("operand") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "unary expression missing operand",
                    ));
                    return None;
                };
                let Some(op_node) = node.child_by_field_name("op") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "unary expression missing op",
                    ));
                    return None;
                };
                let op = match self.get_text(op_node) {
                    "-" => UnOp::Neg,
                    other => {
                        d.push_error(self.diag(
                            op_node,
                            ParserCode::MalformedCst,
                            format!("unknown unary operator: {}", other),
                        ));
                        return None;
                    }
                };
                Some(Expr {
                    kind: ExprKind::Unary(op, Box::new(self.map_expr(operand, scope, d)?)),
                    source: SourceInfo::written(span),
                })
            }
            "binary_expr" => {
                let Some(lhs) = node.child_by_field_name("lhs") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing lhs",
                    ));
                    return None;
                };
                let Some(op_node) = node.child_by_field_name("op") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing op",
                    ));
                    return None;
                };
                let Some(rhs) = node.child_by_field_name("rhs") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "binary expression missing rhs",
                    ));
                    return None;
                };
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
                        d.push_error(self.diag(
                            op_node,
                            ParserCode::MalformedCst,
                            format!("unknown binary operator: {}", other),
                        ));
                        return None;
                    }
                };
                Some(Expr {
                    kind: ExprKind::Binary(
                        Box::new(self.map_expr(lhs, scope, d)?),
                        op,
                        Box::new(self.map_expr(rhs, scope, d)?),
                    ),
                    source: SourceInfo::written(span),
                })
            }
            "field_access" => {
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "field access missing target",
                    ));
                    return None;
                };
                let Some(field) = node.child_by_field_name("field") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "field access missing field",
                    ));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::FieldAccess(
                        Box::new(self.map_expr(target, scope, d)?),
                        self.get_text(field).to_string(),
                    ),
                    source: SourceInfo::written(span),
                })
            }
            "deref_expr" => {
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "deref missing target"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Deref(Box::new(self.map_expr(target, scope, d)?)),
                    source: SourceInfo::written(span),
                })
            }
            "cast_expr" => {
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "cast missing target"));
                    return None;
                };
                let Some(ty_node) = node.child_by_field_name("ty") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "cast missing type"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::Cast(
                        Box::new(self.map_expr(target, scope, d)?),
                        self.map_type(ty_node, scope, d)?,
                    ),
                    source: SourceInfo::written(span),
                })
            }
            "call_expr" => {
                let Some(func) = node.child_by_field_name("function") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "call missing function",
                    ));
                    return None;
                };
                // Generic calls parse as `call_expr(instantiation_expr(f, <T>), args)`
                // — unwrap the inner instantiation_expr to lift the type args
                // onto the call's generics slot.
                let (func_node, generics) = if func.kind() == "instantiation_expr" {
                    let Some(inner_fn) = func.child_by_field_name("function") else {
                        d.push_error(self.diag(
                            func,
                            ParserCode::MalformedCst,
                            "instantiation missing function",
                        ));
                        return None;
                    };
                    let Some(type_args_node) = func.child_by_field_name("type_args") else {
                        d.push_error(self.diag(
                            func,
                            ParserCode::MalformedCst,
                            "instantiation missing type_args",
                        ));
                        return None;
                    };
                    let (lifetimes, types) = self.map_type_args(type_args_node, scope, d)?;
                    (inner_fn, GenericArgs { lifetimes, types })
                } else {
                    (func, GenericArgs::empty())
                };
                let target = if func_node.kind() == "field_access" {
                    let Some(receiver) = func_node.child_by_field_name("target") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "receiver call missing receiver",
                        ));
                        return None;
                    };
                    let Some(method) = func_node.child_by_field_name("field") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "receiver call missing method",
                        ));
                        return None;
                    };
                    CallTarget::Receiver {
                        receiver: Box::new(self.map_expr(receiver, scope, d)?),
                        method: self.get_text(method).to_string(),
                        method_source: SourceInfo::written(span_of(method)),
                        selector_source: SourceInfo::written(span_of(func_node)),
                    }
                } else if func_node.kind() == "qualified_method" {
                    let Some(self_ty) = func_node.child_by_field_name("self_ty") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "qualified method missing self type",
                        ));
                        return None;
                    };
                    let Some(method) = func_node.child_by_field_name("method_name") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "qualified method missing method name",
                        ));
                        return None;
                    };
                    let trait_path = if let Some(trait_name) =
                        func_node.child_by_field_name("trait_name")
                    {
                        let (lifetimes, types) =
                            if let Some(trait_args) = func_node.child_by_field_name("trait_args") {
                                self.map_type_args(trait_args, scope, d)?
                            } else {
                                (Vec::new(), Vec::new())
                            };
                        Some(Instance::new(self.get_text(trait_name), lifetimes, types))
                    } else {
                        None
                    };
                    CallTarget::Qualified {
                        self_ty: self.map_type(self_ty, scope, d)?,
                        trait_path,
                        method: self.get_text(method).to_string(),
                        method_source: SourceInfo::written(span_of(method)),
                        selector_source: SourceInfo::written(span_of(func_node)),
                    }
                } else if func_node.kind() == "scoped_identifier" {
                    let Some(target_name) = func_node.child_by_field_name("target_name") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "scoped identifier missing target name",
                        ));
                        return None;
                    };
                    let target_text = self.get_text(target_name);
                    let resolved_target_name = self.resolve_constructor_name(target_text, scope);
                    let target_ty = Type::new(
                        TypeKind::Custom(Instance::new(resolved_target_name, Vec::new(), Vec::new())),
                        SourceInfo::written(span_of(target_name)),
                    );
                    let Some(member) = func_node.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            func_node,
                            ParserCode::MalformedCst,
                            "scoped identifier missing member name",
                        ));
                        return None;
                    };
                    CallTarget::Path {
                        target: target_ty,
                        member: self.get_text(member).to_string(),
                        member_source: SourceInfo::written(span_of(member)),
                        selector_source: SourceInfo::written(span_of(func_node)),
                    }
                } else {
                    CallTarget::Expr(Box::new(self.map_expr(func_node, scope, d)?))
                };
                let mut cursor = node.walk();
                let mut args = Vec::new();
                for c in node.children(&mut cursor) {
                    if c != func && self.is_expr_kind(&c) {
                        args.push(self.map_expr(c, scope, d)?);
                    }
                }
                Some(Expr {
                    kind: ExprKind::Call(target, generics, args),
                    source: SourceInfo::written(span),
                })
            }
            // Bare `foo<T>` without a call. Silica doesn't use this shape
            // as a value; it exists only to make tree-sitter's LR
            // generator disambiguate `foo<T>(x)` from `a < b > c`. Reject
            // as ill-formed at parse time.
            "instantiation_expr" => {
                d.push_error(self.diag(
                    node,
                    ParserCode::UnexpectedToken,
                    "type arguments without a call are not a valid expression",
                ));
                None
            }
            "qualified_method" => {
                d.push_error(self.diag(
                    node,
                    ParserCode::UnexpectedToken,
                    "a qualified method must be called",
                ));
                None
            }
            "index_expr" => {
                let Some(target) = node.child_by_field_name("target") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "index missing target"));
                    return None;
                };
                let Some(idx) = node.child_by_field_name("index") else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "index missing index"));
                    return None;
                };
                Some(Expr {
                    kind: ExprKind::ArrayIndex(
                        Box::new(self.map_expr(target, scope, d)?),
                        Box::new(self.map_expr(idx, scope, d)?),
                    ),
                    source: SourceInfo::written(span),
                })
            }
            "match_expr" => {
                let Some(scrut) = node.child_by_field_name("scrutinee") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "match missing scrutinee",
                    ));
                    return None;
                };
                self.map_match(node, scrut, scope, d)
            }
            "lambda_expr" => {
                let mut params = Vec::new();
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    if child.kind() == "lambda_param" {
                        if let Some(param) = self.map_lambda_param(child, scope, d) {
                            params.push(param);
                        }
                    }
                }
                let ret_ty = if let Some(ret_node) = node.child_by_field_name("return_type") {
                    self.map_type(ret_node, scope, d)
                } else {
                    None
                };
                let Some(body_node) = node.child_by_field_name("body") else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "lambda missing body expression",
                    ));
                    return None;
                };
                let body = self.map_expr(body_node, scope, d)?;
                Some(Expr {
                    kind: ExprKind::Lambda {
                        params,
                        ret_ty,
                        body: Box::new(body),
                    },
                    source: SourceInfo::written(span),
                })
            }

            other => {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("unrecognized expression node kind: {}", other),
                ));
                None
            }
        }
    }

    fn map_block(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Expr> {
        let span = span_of(node);
        let is_unsafe = self.get_text(node).starts_with("unsafe");
        let mut stmts = Vec::new();
        let mut tail = None;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "stmt" {
                if let Some(stmt) = self.map_stmt(child, scope, d) {
                    stmts.push(stmt);
                }
            } else if self.is_expr_kind(&child) {
                // Trailing expression (has field name "tail" in grammar).
                if let Some(expr) = self.map_expr(child, scope, d) {
                    tail = Some(Box::new(expr));
                }
            }
        }
        Some(Expr {
            kind: ExprKind::Block(stmts, tail, is_unsafe),
            source: SourceInfo::written(span),
        })
    }

    fn map_stmt(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Stmt> {
        // stmt is a choice: let_stmt | defer_stmt | (expr ';').
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "empty statement"));
            return None;
        };
        match child.kind() {
            "let_stmt" => self.map_let_stmt(child, scope, d),
            "defer_stmt" => {
                let Some(body_node) = child.child_by_field_name("body") else {
                    d.push_error(self.diag(child, ParserCode::MalformedCst, "defer missing body"));
                    return None;
                };
                let body = self.map_expr(body_node, scope, d)?;
                Some(Stmt::Defer {
                    body,
                    source: SourceInfo::written(span_of(node)),
                })
            }
            _ => {
                let e = self.map_expr(child, scope, d)?;
                Some(Stmt::Expr(e))
            }
        }
    }

    fn map_let_stmt(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Stmt> {
        let span = span_of(node);
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "let missing name"));
            return None;
        };
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
            Some(self.map_type(t, scope, d)?)
        } else {
            None
        };
        let init = match node.child_by_field_name("init") {
            Some(n) => Some(self.map_expr(n, scope, d)?),
            None => None,
        };
        Some(Stmt::Let {
            is_mut,
            name,
            ty,
            init,
            source: SourceInfo::written(span),
        })
    }

    fn map_if(&self, node: Node, scope: &TypeScope, d: &mut Diagnostics) -> Option<Expr> {
        let span = span_of(node);
        let Some(cond_node) = node.child_by_field_name("cond") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "if missing cond"));
            return None;
        };
        let Some(then_node) = node.child_by_field_name("then") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "if missing then"));
            return None;
        };
        let else_expr = if let Some(else_node) = node.child_by_field_name("else") {
            self.map_expr(else_node, scope, d)?
        } else {
            // Implicit-else's span is a point at the position where
            // an `else` keyword would appear, so diagnostics on the
            // implicit-else path don't collide with the whole if.
            let then_end = then_node.end_position();
            let line = (then_end.row as u32).saturating_add(1);
            let col = (then_end.column as u32).saturating_add(1);
            Expr {
                kind: ExprKind::Block(Vec::new(), None, false),
                source: SourceInfo::generated(
                    GeneratedKind::HllDesugaring,
                    Span {
                        line,
                        col,
                        end_line: line,
                        end_col: col,
                    },
                ),
            }
        };
        Some(Expr {
            kind: ExprKind::If(
                Box::new(self.map_expr(cond_node, scope, d)?),
                Box::new(self.map_expr(then_node, scope, d)?),
                Box::new(else_expr),
            ),
            source: SourceInfo::written(span),
        })
    }

    fn map_match(
        &self,
        node: Node,
        scrutinee_node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<Expr> {
        let span = span_of(node);
        let mut arms = Vec::new();
        let mut cursor = node.walk();
        for c in node.children(&mut cursor) {
            if c.kind() == "match_arm" {
                let Some(pat_node) = c.child_by_field_name("pattern") else {
                    d.push_error(self.diag(
                        c,
                        ParserCode::MalformedCst,
                        "match arm missing pattern",
                    ));
                    continue;
                };
                let Some(body_node) = c.child_by_field_name("body") else {
                    d.push_error(self.diag(c, ParserCode::MalformedCst, "match arm missing body"));
                    continue;
                };
                let Some(pat) = self.map_pattern(pat_node, d) else {
                    continue;
                };
                let Some(body) = self.map_expr(body_node, scope, d) else {
                    continue;
                };
                arms.push((pat, body));
            }
        }
        Some(Expr {
            kind: ExprKind::Match(Box::new(self.map_expr(scrutinee_node, scope, d)?), arms),
            source: SourceInfo::written(span),
        })
    }

    fn map_pattern(&self, node: Node, d: &mut Diagnostics) -> Option<Pattern> {
        let Some(variant_node) = node.child_by_field_name("variant") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "pattern missing variant"));
            return None;
        };
        let variant = self.get_text(variant_node).to_string();
        let bound = node
            .child_by_field_name("bound")
            .map(|b| self.get_text(b).to_string());
        Some(Pattern::Variant(variant, bound))
    }

    fn map_struct_constr(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<Expr> {
        let span = span_of(node);
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "struct constr missing name"));
            return None;
        };
        let name = self.resolve_constructor_name(self.get_text(name_node), scope);
        let mut fields = Vec::new();
        let mut cursor = node.walk();
        for c in node.children(&mut cursor) {
            if c.kind() == "field_init" {
                let Some(fn_name) = c.child_by_field_name("name") else {
                    d.push_error(self.diag(c, ParserCode::MalformedCst, "field init missing name"));
                    continue;
                };
                let Some(fn_val) = c.child_by_field_name("value") else {
                    d.push_error(self.diag(
                        c,
                        ParserCode::MalformedCst,
                        "field init missing value",
                    ));
                    continue;
                };
                let Some(val) = self.map_expr(fn_val, scope, d) else {
                    continue;
                };
                fields.push((self.get_text(fn_name).to_string(), val));
            }
        }
        Some(Expr {
            kind: ExprKind::StructConstr(name, fields),
            source: SourceInfo::written(span),
        })
    }

    fn map_scoped_identifier(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<Expr> {
        let span = span_of(node);
        let Some(target_name) = node.child_by_field_name("target_name") else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                "scoped identifier missing target name",
            ));
            return None;
        };
        let target_text = self.get_text(target_name);
        let resolved_target_name = self.resolve_constructor_name(target_text, scope);
        let target_ty = Type::new(
            TypeKind::Custom(Instance::new(resolved_target_name, Vec::new(), Vec::new())),
            SourceInfo::written(span_of(target_name)),
        );
        let Some(member) = node.child_by_field_name("name") else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                "scoped identifier missing member name",
            ));
            return None;
        };
        Some(Expr {
            kind: ExprKind::Path(target_ty, self.get_text(member).to_string()),
            source: SourceInfo::written(span),
        })
    }

    fn map_lambda_param(
        &self,
        node: Node,
        scope: &TypeScope,
        d: &mut Diagnostics,
    ) -> Option<LambdaParam> {
        let name_node = node.child_by_field_name("name")?;
        let name = self.get_text(name_node).to_string();
        let is_mut = node
            .children(&mut node.walk())
            .any(|c| self.get_text(c) == "mut");
        let ty = if let Some(ty_node) = node.child_by_field_name("type") {
            self.map_type(ty_node, scope, d)
        } else {
            None
        };
        Some(LambdaParam {
            is_mut,
            name,
            ty,
            source: SourceInfo::written(span_of(node)),
        })
    }

    fn resolve_constructor_name(&self, name: &str, scope: &TypeScope) -> String {
        if name == "Self" {
            if let Some(Type {
                kind: TypeKind::Custom(instance),
                ..
            }) = &scope.self_ty
            {
                return instance.name.clone();
            }
        }
        name.to_string()
    }

    /// True if `node` is any expression-carrying node kind that
    /// `map_expr` handles. Used to skip anonymous keyword/punctuation
    /// children when iterating for the "trailing expression" of a
    /// block or the "value" of `break`/`return`.
    fn is_expr_kind(&self, node: &Node) -> bool {
        node.kind() == "expr"
    }

    /// Parse a `markers` node (one or more `Copy`/`Drop`/`Move` in any
    /// order) into the raw sequence the user wrote. Errors on duplicates.
    /// Callers canonicalize via `Markers::from_iter` or `Markers::from_declared`
    /// (the latter also flags redundant Move for an info diagnostic).
    fn map_marker_tokens(&self, node: Node, d: &mut Diagnostics) -> Option<Vec<Marker>> {
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
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        format!("unknown marker: {}", other),
                    ));
                    return None;
                }
            };
            if seen.contains(&m) {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("Duplicate marker '{}'", text),
                ));
                return None;
            }
            seen.push(m);
        }
        Some(seen)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hll::helpers::*;

    #[test]
    fn parse_struct_decl_test() {
        let source = "struct Point { x: i64, y: i64 }";
        let program = Parser::parse_or_panic(source);
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
        let source = "enum Option { None: (), Some: i64 }";
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
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
        let source = "enum Option: Move + Drop { None: (), Some: i64 }";
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
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
                let d = &drop a;
                let e = &uninit a;
            }
        ";
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
    }

    #[test]
    fn array_length_uses_full_u64_range() {
        let source = "extern fn inspect(a: [u8; 9223372036854775808]);";
        let program = Parser::parse_or_panic(source);
        let Declaration::Fn(function) = &program.declarations[0] else {
            panic!("expected function declaration");
        };
        let TypeKind::Array(element, length) = &function.params[0].ty.kind else {
            panic!("expected array parameter");
        };
        assert_eq!(element.kind, TypeKind::Int(IntTy::U8));
        assert_eq!(*length, 9_223_372_036_854_775_808);
    }

    #[test]
    fn parse_extern_fn() {
        let source = "
            extern fn add_impl(a: i64, b: i64) -> i64;
            extern \"C\" unsafe fn c_fn(a: f64) -> f64;
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 2);

        let Declaration::Fn(f1) = &program.declarations[0] else {
            panic!()
        };
        assert_eq!(f1.name, "add_impl");
        assert_eq!(f1.linkage, Linkage::Foreign);
        assert_eq!(f1.abi, Abi::Silica);
        assert!(!f1.is_unsafe);
        assert!(f1.body.is_none());

        let Declaration::Fn(f2) = &program.declarations[1] else {
            panic!()
        };
        assert_eq!(f2.name, "c_fn");
        assert_eq!(f2.linkage, Linkage::Foreign);
        assert_eq!(f2.abi, Abi::C);
        assert!(f2.is_unsafe);
        assert!(f2.body.is_none());
    }

    #[test]
    fn parse_generic_extern_fn() {
        let source = "
            extern fn add_impl<'a, T: Move>(a: &mut i64, b: T);
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!()
        };
        assert_eq!(f.name, "add_impl");
        assert_eq!(f.lifetime_params.len(), 1);
        assert_eq!(f.lifetime_params[0].0, "a");
        assert_eq!(f.type_params.len(), 1);
        assert_eq!(f.type_params[0].name, "T");
        assert!(f.body.is_none());
    }

    #[test]
    fn parse_byte_str_and_byte_char() {
        let source = "
            fn check() {
                let s = b\"hello\\nworld\";
                let c = b'A';
            }
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!()
        };
        let ExprKind::Block(stmts, _, _) = &f.body.as_ref().unwrap().kind else {
            panic!()
        };

        let Stmt::Let {
            init: Some(init_s), ..
        } = &stmts[0]
        else {
            panic!()
        };
        assert_eq!(
            init_s.kind,
            ExprKind::Literal(Literal::ByteStr(b"hello\nworld".to_vec()))
        );

        let Stmt::Let {
            init: Some(init_c), ..
        } = &stmts[1]
        else {
            panic!()
        };
        assert_eq!(
            init_c.kind,
            ExprKind::Literal(Literal::Int(65, Some(IntTy::U8)))
        );
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
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let init = first_let_init(&Parser::parse_or_panic(source));
        let ExprKind::FieldAccess(target, x) = init.kind else {
            panic!("expected FieldAccess");
        };
        assert_eq!(x, "x");
        assert!(matches!(target.kind, ExprKind::Call(_, _, _)));
    }

    #[test]
    fn borrow_binds_looser_than_field_access() {
        // `&x.y` must parse as `&(x.y)`, not `(&x).y` — prefix
        // borrows are prec 10, postfix operators are prec 20.
        let source = "fn f(x: Point) { let r = &x.y; }";
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let program = Parser::parse_or_panic(source);
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
        let with = Parser::parse_or_panic("struct P { x: i64, y: i64, }");
        let without = Parser::parse_or_panic("struct P { x: i64, y: i64 }");
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
        let src = "enum E { A: (), B: i64, }";
        let program = Parser::parse_or_panic(src);
        let Declaration::Enum(e) = &program.declarations[0] else {
            panic!()
        };
        assert_eq!(e.variants.len(), 2);
    }

    #[test]
    fn empty_function_body() {
        // `fn f() {}` — empty block, no trailing expression, unit
        // return.
        let program = Parser::parse_or_panic("fn f() {}");
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
        let program = Parser::parse_or_panic(
            "fn f() {
                loop {
                    break;
                };
                return;
            }",
        );
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
        let program = Parser::parse_or_panic(with);
        assert_eq!(program.declarations.len(), 1);
    }

    /// Helper: extract the parameter list of the first function in
    /// `source`. Used by the fn-type tests below.
    fn first_fn_params(source: &str) -> Vec<Param> {
        let program = Parser::parse_or_panic(source);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn declaration");
        };
        f.params.clone()
    }

    #[test]
    fn parameter_and_nested_type_nodes_keep_distinct_source_spans() {
        let params = first_fn_params("fn main(exit: &out i64) {}");
        let param = &params[0];
        assert_eq!(
            param.span(),
            Span {
                line: 1,
                col: 9,
                end_line: 1,
                end_col: 23,
            }
        );
        assert_eq!(
            param.ty.span(),
            Span {
                line: 1,
                col: 15,
                end_line: 1,
                end_col: 23,
            }
        );
        let TypeKind::Ref(_, _, pointee) = &param.ty.kind else {
            panic!("expected reference type, got {:?}", param.ty);
        };
        assert_eq!(
            pointee.span(),
            Span {
                line: 1,
                col: 20,
                end_line: 1,
                end_col: 23,
            }
        );
    }

    #[test]
    fn fn_type_with_return_arrow() {
        // `fn(i64) -> i64` → TypeKind::Fn { params: [i64], ret: i64, .. }.
        let params = first_fn_params("fn caller(f: fn(i64) -> i64) {}");
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
            panic!("expected Fn type, got {:?}", params[0].ty);
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        assert_eq!(**r, i64_ty());
    }

    #[test]
    fn fn_type_without_arrow_defaults_to_unit() {
        // `fn(i64)` → TypeKind::Fn { params: [i64], ret: (), .. }. The arrow is optional;
        // absence means the callee returns `unit`.
        let params = first_fn_params("fn caller(f: fn(i64)) {}");
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
            panic!("expected Fn type, got {:?}", params[0].ty);
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        assert_eq!(**r, unit_ty());
    }

    #[test]
    fn fn_type_zero_params_no_arrow() {
        // `fn()` — nullary, no arrow → Fn([], unit).
        let params = first_fn_params("fn caller(f: fn()) {}");
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert!(p.is_empty(), "expected empty param list, got {:?}", p);
        assert_eq!(**r, unit_ty());
    }

    #[test]
    fn fn_type_zero_params_with_arrow() {
        // `fn() -> i64` — nullary with arrow → Fn([], i64).
        let params = first_fn_params("fn caller(f: fn() -> i64) {}");
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
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
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert_eq!(p.as_slice(), &[i64_ty(), bool_ty()]);
        assert_eq!(**r, bool_ty());
    }

    #[test]
    fn fn_type_nested_as_param() {
        // `fn(fn(i64)) -> bool` — the fn-typed param is itself a
        // fn type. Exercises the walker's recursion.
        let params = first_fn_params("fn caller(f: fn(fn(i64)) -> bool) {}");
        let TypeKind::Fn { params: outer_p, ret: outer_r, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert_eq!(outer_p.len(), 1);
        let TypeKind::Fn { params: inner_p, ret: inner_r, .. } = &outer_p[0].kind else {
            panic!("expected nested Fn type, got {:?}", outer_p[0]);
        };
        assert_eq!(inner_p.as_slice(), &[i64_ty()]);
        assert_eq!(**inner_r, unit_ty());
        assert_eq!(**outer_r, bool_ty());
    }

    #[test]
    fn fn_type_returns_fn_type() {
        // `fn(i64) -> fn()` — the arrow's return type is itself a
        // fn type. Verifies the walker doesn't confuse where the
        // return type ends.
        let params = first_fn_params("fn caller(f: fn(i64) -> fn()) {}");
        let TypeKind::Fn { params: p, ret: r, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert_eq!(p.as_slice(), &[i64_ty()]);
        let TypeKind::Fn { params: ret_p, ret: ret_r, .. } = &r.kind else {
            panic!("expected Fn as return, got {:?}", r);
        };
        assert!(ret_p.is_empty());
        assert_eq!(**ret_r, unit_ty());
    }

    #[test]
    fn fn_type_trailing_comma_in_params() {
        let params = first_fn_params("fn caller(f: fn(i64, bool,) -> bool) {}");
        let TypeKind::Fn { params: p, ret: _, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert_eq!(p.len(), 2);
    }

    #[test]
    fn fn_type_default_abi_is_silica() {
        let params = first_fn_params("fn caller(f: fn(i64) -> i64) {}");
        let TypeKind::Fn { abi, .. } = &params[0].ty.kind else {
            panic!()
        };
        assert_eq!(*abi, Abi::Silica);
    }

    #[test]
    fn fn_type_with_c_abi() {
        let params = first_fn_params("fn caller(f: fn \"C\"(i64) -> i64) {}");
        let TypeKind::Fn { abi, params: p, ret } = &params[0].ty.kind else {
            panic!("expected Fn type")
        };
        assert_eq!(*abi, Abi::C);
        assert_eq!(p.as_slice(), &[i64_ty()]);
        assert_eq!(**ret, i64_ty());
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
        let mut diags = Diagnostics::default();
        let prog = Parser::new(src).parse(&mut diags);
        assert!(
            prog.is_none(),
            "expected parse failure for two broken functions"
        );
        assert!(
            diags.error_count() >= 2,
            "expected ≥2 errors, got {}: {:?}",
            diags.error_count(),
            diags.errors_str()
        );
    }

    #[test]
    fn syntax_errors_distinguish_trait_and_impl_methods() {
        let src = "\
            struct S: Copy + Drop {}\n\
            trait Tr { fn broken(recv: &Self) { @@; } }\n\
            impl Tr for S { fn broken(recv: &Self) { @@; } }\n";
        let mut diags = Diagnostics::default();
        assert!(Parser::new(src).parse(&mut diags).is_none());
        let rendered = diags.errors_str().join("\n");
        assert!(
            rendered.contains("In function 'Tr::broken'"),
            "missing qualified trait context: {rendered}"
        );
        assert!(
            rendered.contains("In function '<S as Tr>::broken'"),
            "missing qualified impl context: {rendered}"
        );
    }

    #[test]
    fn parse_binary_expressions_precedence() {
        // Test that binary expressions parse correctly with expected associativity/precedence.
        // e.g. `a + b * c` -> Add(a, Mul(b, c))
        let source = "fn f(a: i64, b: i64, c: i64) { let x = a + b * c; }";
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let init = first_let_init(&Parser::parse_or_panic(source));
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
        let program = Parser::parse_or_panic(source);
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
        let program = Parser::parse_or_panic(source);
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
        assert!(
            matches!(e.kind, ExprKind::Call(_, _, _)),
            "got {:?}",
            e.kind
        );
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
