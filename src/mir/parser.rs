use crate::diagnostics::{DiagCode, Diagnostic, Diagnostics};
use crate::mir::ast::*;
use crate::mir::helpers::*;
use tree_sitter::{Node, Parser as TSParser};

/// Machine-readable error codes emitted by the MIR parser.
///
/// Emitted from two places:
/// - The tree-sitter ERROR/MISSING walker (surface syntax errors).
/// - The CST-to-AST conversion layer (invariant failures + literal
///   decode errors that tree-sitter accepts token-wise but our
///   downstream code rejects).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParserCode {
    /// A tree-sitter ERROR node — a token region the parser couldn't
    /// fit into any grammar rule. Emitted once per error region.
    UnexpectedToken,
    /// A tree-sitter MISSING node — a token the parser expected but
    /// didn't see, synthesized into the CST for error recovery. Kept
    /// distinct from `UnexpectedToken` because MISSING errors often
    /// have an obvious fix (insert the token) while `UnexpectedToken`
    /// needs reader judgment.
    MissingToken,
    /// A literal token that tree-sitter accepted as syntactically
    /// well-formed but the value decoder rejected (e.g., an unknown
    /// `\q` byte-string escape, a length-3 hex escape).
    InvalidLiteral,
    /// The CST-to-AST walker encountered a node shape it can't
    /// handle. In principle unreachable given the grammar; kept as
    /// a reportable diagnostic rather than a panic so grammar drift
    /// surfaces as an error rather than crashing the compiler.
    MalformedCst,
    /// User wrote all three of `Copy`, `Drop`, `Move` on a decl — the
    /// `Move` is redundant under the horizontal closure. Info-level
    /// lint on the parsed marker list.
    MoveMarkerRedundant,
    /// A binder or type-reference position used a name the language
    /// reserves. The grammar accepts any identifier here; the parser
    /// rejects reserved names (currently `Self`) on the way to the
    /// AST. Reserving `Self` at the parser boundary prevents a
    /// user-declared struct/enum/trait/param/field/local named `Self`
    /// from colliding with the implicit `Self` alias in trait and
    /// impl bodies, and prevents an out-of-scope `Self` type
    /// reference from silently resolving as a `Custom("Self")`.
    ReservedIdent,
}

impl From<ParserCode> for DiagCode {
    fn from(code: ParserCode) -> DiagCode {
        DiagCode::Parser(code)
    }
}

extern "C" {
    fn tree_sitter_silica_mir() -> *const std::ffi::c_void;
}

pub fn language() -> tree_sitter::Language {
    unsafe { tree_sitter::Language::from_raw(tree_sitter_silica_mir() as *const _) }
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

fn written_source(span: Span) -> SourceInfo {
    SourceInfo::written(span)
}

// CST conversion is the boundary at which written MIR syntax acquires source
// provenance. These wrappers keep that classification explicit while allowing
// the parser below to continue passing the spans it extracts from tree-sitter.
fn assign_stmt(dst: Place, src: RValue, span: Span) -> Statement {
    crate::mir::helpers::assign_stmt(dst, src, written_source(span))
}

fn call_stmt(callee: Operand, args: Vec<Operand>, span: Span) -> Statement {
    crate::mir::helpers::call_stmt(callee, args, written_source(span))
}

fn drop_stmt(place: Place, span: Span) -> Statement {
    crate::mir::helpers::drop_stmt(place, written_source(span))
}

fn unborrow_stmt(place: Place, span: Span) -> Statement {
    crate::mir::helpers::unborrow_stmt(place, written_source(span))
}

fn require_uninit_stmt(place: Place, span: Span) -> Statement {
    crate::mir::helpers::require_uninit_stmt(place, written_source(span))
}

fn goto_term(label: impl Into<String>, span: Span) -> Terminator {
    crate::mir::helpers::goto_term(label, written_source(span))
}

fn return_term(span: Span) -> Terminator {
    crate::mir::helpers::return_term(written_source(span))
}

fn branch_term(
    cond: Operand,
    true_label: impl Into<String>,
    false_label: impl Into<String>,
    span: Span,
) -> Terminator {
    crate::mir::helpers::branch_term(cond, true_label, false_label, written_source(span))
}

fn switch_enum_term(place: Place, cases: Vec<(String, String)>, span: Span) -> Terminator {
    crate::mir::helpers::switch_enum_term(place, cases, written_source(span))
}

fn abort_term(span: Span) -> Terminator {
    crate::mir::helpers::abort_term(written_source(span))
}

fn unreachable_term(span: Span) -> Terminator {
    crate::mir::helpers::unreachable_term(written_source(span))
}

/// Map a scalar type keyword's tree-sitter node kind to `Type`.
/// Returns `None` if the kind isn't one of the ten scalar keywords.
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

/// Parse an integer literal token (`"42"`, `"0xFF"`, `"0b1010_1100"`,
/// `"100u32"`, `"1_000_000i16"`, ...). Unsuffixed → `IntTy::I64`.
fn parse_int_literal(text: &str) -> Result<ConstVal, String> {
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
    let bits = u64::from_str_radix(&cleaned, radix)
        .map_err(|e| format!("invalid integer literal {:?}: {}", text, e))?;
    Ok(int_const(bits, ty))
}

fn split_int_suffix(text: &str) -> (&str, IntTy) {
    // Check longer suffixes first so `i16`/`u16` don't lose to `i1`/`u1`.
    // (No `i1`/`u1` today but the ordering is defensive.)
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
            return (rest, ty);
        }
    }
    (text, IntTy::I64) // unsuffixed default
}

/// Parse a float literal token (`"3.14"`, `"3.14f32"`, `"1_000.5"`, ...).
/// Unsuffixed → `FloatTy::F64`.
fn parse_float_literal(text: &str) -> Result<ConstVal, String> {
    let (digits, ty) = if let Some(rest) = text.strip_suffix("f32") {
        (rest, FloatTy::F32)
    } else if let Some(rest) = text.strip_suffix("f64") {
        (rest, FloatTy::F64)
    } else {
        (text, FloatTy::F64)
    };
    let cleaned: String = digits.chars().filter(|c| *c != '_').collect();
    match ty {
        FloatTy::F32 => {
            let v: f32 = cleaned
                .parse()
                .map_err(|e| format!("invalid f32 literal {:?}: {}", text, e))?;
            Ok(float_const(v.to_bits() as u64, ty))
        }
        FloatTy::F64 => {
            let v: f64 = cleaned
                .parse()
                .map_err(|e| format!("invalid f64 literal {:?}: {}", text, e))?;
            Ok(float_const(v.to_bits(), ty))
        }
    }
}

/// Parse a byte string literal token `b"..."`. Supports these escape
/// sequences: `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\'`, and `\xNN`
/// (two hex digits, case-insensitive). Non-ASCII source bytes are
/// rejected — use `\xNN` escapes to embed arbitrary bytes.
fn parse_byte_str_literal(text: &str) -> Result<ConstVal, String> {
    let inner = text
        .strip_prefix("b\"")
        .and_then(|s| s.strip_suffix('"'))
        .ok_or_else(|| format!("byte string literal missing quotes: {:?}", text))?;
    Ok(byte_str_const(decode_byte_escapes(inner)?))
}

/// Parse a byte character literal token `b'X'`. Value type is `u8`,
/// carrying the single decoded byte. Accepts the same escape set as
/// [`parse_byte_str_literal`].
fn parse_byte_char_literal(text: &str) -> Result<ConstVal, String> {
    let inner = text
        .strip_prefix("b'")
        .and_then(|s| s.strip_suffix('\''))
        .ok_or_else(|| format!("byte char literal missing quotes: {:?}", text))?;
    let bytes = decode_byte_escapes(inner)?;
    if bytes.len() != 1 {
        return Err(format!(
            "byte char literal must be exactly one byte, got {} ({:?})",
            bytes.len(),
            text
        ));
    }
    Ok(int_const(bytes[0] as u64, IntTy::U8))
}

/// Decode the escape sequences in a `b"..."` / `b'...'` literal body
/// (quote delimiters already stripped). Shared by both parsers so the
/// escape set stays consistent.
pub(crate) fn decode_byte_escapes(inner: &str) -> Result<Vec<u8>, String> {
    let mut out: Vec<u8> = Vec::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => out.push(b'\n'),
                Some('t') => out.push(b'\t'),
                Some('r') => out.push(b'\r'),
                Some('0') => out.push(b'\0'),
                Some('\\') => out.push(b'\\'),
                Some('"') => out.push(b'"'),
                Some('\'') => out.push(b'\''),
                Some('x') => {
                    let h1 = chars.next().ok_or("truncated \\x escape")?;
                    let h2 = chars.next().ok_or("truncated \\x escape")?;
                    let hex = format!("{}{}", h1, h2);
                    let val = u8::from_str_radix(&hex, 16)
                        .map_err(|_| format!("invalid \\x escape: \\x{}", hex))?;
                    out.push(val);
                }
                Some(other) => {
                    return Err(format!("unknown escape sequence: \\{}", other));
                }
                None => return Err("truncated backslash at end of literal".to_string()),
            }
        } else if c.is_ascii() {
            out.push(c as u8);
        } else {
            return Err(format!(
                "non-ASCII char {:?} in byte literal; use \\xNN escapes",
                c
            ));
        }
    }
    Ok(out)
}

pub struct Parser {
    source: std::sync::Arc<String>,
    /// Names of type parameters currently in scope. Populated on entry
    /// to a struct/enum/fn decl mapping (before its field/param/local
    /// types are visited) and cleared on exit. `map_type` reads this
    /// when it sees an identifier: a match means `Param`, otherwise
    /// `Custom`. Decls don't nest, so a single set suffices.
    type_scope: std::cell::RefCell<std::collections::BTreeSet<String>>,
}

impl Parser {
    pub fn new(source: impl Into<String>) -> Self {
        Self {
            source: std::sync::Arc::new(source.into()),
            type_scope: std::cell::RefCell::new(std::collections::BTreeSet::new()),
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
            .unwrap_or_else(|| panic!("MIR parse failed:\n{}", d.errors_str().join("\n")))
    }

    /// Parse `self.source` into a `Program`, emitting all diagnostics
    /// into `d`. Tree-sitter ERROR regions become `UnexpectedToken`
    /// diagnostics and MISSING nodes become `MissingToken` diagnostics
    /// (multi-error output); CST-to-AST failures become `MalformedCst`
    /// or `InvalidLiteral` diagnostics with the span of the offending
    /// node. Returns `None` if a program couldn't be assembled; the
    /// caller checks `d.has_errors()` to gate on any parse-time
    /// failure. Non-fatal (info/warning) diagnostics accompany a
    /// successful `Some(program)` return.
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

        // Multi-error: emit every ERROR/MISSING region as its own
        // diagnostic. Only fall through to CST-to-AST conversion if
        // the tree is syntactically clean — a partial CST would
        // otherwise produce spurious downstream errors.
        if root.has_error() {
            self.walk_syntax_errors(root, None, None, d);
            return None;
        }

        let program = self.map_program(root, d);
        if d.has_errors() {
            None
        } else {
            Some(program)
        }
    }

    fn get_text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    /// Build a `Diagnostic` at `node`'s start position.
    fn diag(&self, node: Node, code: ParserCode, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(code, SourceInfo::written(span_of(node)), message)
    }

    /// Emit `ReservedIdent` if `name` is the reserved word `Self` and
    /// return whether it was rejected. `context` fills the diagnostic
    /// message ("a type-parameter name", "a struct name", etc.).
    fn reject_self_ident(
        &self,
        name: &str,
        node: Node,
        context: &str,
        d: &mut Diagnostics,
    ) -> bool {
        if name == "Self" {
            d.push_error(self.diag(
                node,
                ParserCode::ReservedIdent,
                format!("'Self' is reserved and cannot be used as {context}"),
            ));
            true
        } else {
            false
        }
    }

    /// Wrap a `Result<T, String>` produced by a literal decoder into a
    /// `Diagnostic` with `InvalidLiteral` code and the source span of
    /// the literal token, pushing the diagnostic into `d` and returning
    /// `None` on error.
    fn lit_diag<T>(&self, res: Result<T, String>, node: Node, d: &mut Diagnostics) -> Option<T> {
        match res {
            Ok(v) => Some(v),
            Err(s) => {
                d.push_error(self.diag(node, ParserCode::InvalidLiteral, s));
                None
            }
        }
    }

    /// Walk the CST emitting one diagnostic per tree-sitter ERROR or
    /// MISSING node. Tracks function/block context so errors report
    /// which function/block they're in when the surrounding structure
    /// is intact enough for the walker to identify.
    fn walk_syntax_errors<'a>(
        &'a self,
        node: Node<'a>,
        ctx_fn: Option<&'a str>,
        ctx_block: Option<&'a str>,
        diags: &mut Diagnostics,
    ) {
        // Refine context on entry: descending into a function_decl or
        // basic_block pins the appropriate label. Uses field-name
        // lookup so a partially-parsed decl (missing name/label) just
        // leaves the context unset.
        let (ctx_fn, ctx_block) = match node.kind() {
            "function_decl" => (
                node.child_by_field_name("name").map(|n| self.get_text(n)),
                None,
            ),
            "basic_block" => (
                ctx_fn,
                node.child_by_field_name("label").map(|n| self.get_text(n)),
            ),
            _ => (ctx_fn, ctx_block),
        };

        if node.is_missing() {
            let mut d = Diagnostic::new(
                ParserCode::MissingToken,
                SourceInfo::written(span_of(node)),
                format!("missing '{}'", node.kind()),
            );
            if let Some(f) = ctx_fn {
                d = d.in_function(f);
            }
            if let Some(b) = ctx_block {
                d = d.in_block(b);
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
            if let Some(f) = ctx_fn {
                d = d.in_function(f);
            }
            if let Some(b) = ctx_block {
                d = d.in_block(b);
            }
            diags.push_error(d);
        }

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            self.walk_syntax_errors(child, ctx_fn, ctx_block, diags);
        }
    }

    fn map_program(&self, node: Node, d: &mut Diagnostics) -> Program {
        let mut declarations = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() != "declaration" {
                continue;
            }
            if let Some(decl) = self.map_declaration(child, d) {
                declarations.push(decl);
            }
        }
        Program {
            declarations,
            source: self.source.clone(),
        }
    }

    fn map_declaration(&self, node: Node, d: &mut Diagnostics) -> Option<Declaration> {
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "empty declaration"));
            return None;
        };
        match child.kind() {
            "struct_decl" => Some(Declaration::Struct(self.map_struct_decl(child, d)?)),
            "enum_decl" => Some(Declaration::Enum(self.map_enum_decl(child, d)?)),
            "function_decl" => Some(Declaration::Fn(self.map_function_decl(child, d)?)),
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

    fn map_type(&self, node: Node, d: &mut Diagnostics) -> Option<Type> {
        let span = span_of(node);
        Some(self.map_type_inner(node, d)?.with_written_span(span))
    }

    /// Same as `map_type` but leaves the outermost type marked as synthesized;
    /// the caller (`map_type`) stamps the node's written span. Inner types built
    /// recursively via `map_type` already carry their own child-node spans.
    fn map_type_inner(&self, node: Node, d: &mut Diagnostics) -> Option<Type> {
        if let Some(ty) = scalar_kind_to_type(node.kind()) {
            return Some(ty);
        }
        match node.kind() {
            "bool" => Some(bool_ty()),
            "unit" => Some(unit_ty()),
            "never" => Some(never_ty()),
            "identifier" => {
                let text = self.get_text(node);
                if text == "bool" {
                    Some(bool_ty())
                } else if self.type_scope.borrow().contains(text) {
                    Some(param_ty(text))
                } else if text == "Self" {
                    d.push_error(self.diag(
                        node,
                        ParserCode::ReservedIdent,
                        "'Self' may only appear as a type reference inside a trait or impl body",
                    ));
                    None
                } else {
                    Some(custom_ty(text))
                }
            }
            "type" => {
                let Some(first_child) = node.child(0) else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "type node has no children",
                    ));
                    return None;
                };
                if let Some(ty) = scalar_kind_to_type(first_child.kind()) {
                    return Some(ty);
                }
                let kind = first_child.kind();
                if kind == "bool" || kind == "unit" || kind == "never" {
                    return self.map_type_inner(first_child, d);
                }
                if kind == "identifier" {
                    let text = self.get_text(first_child);
                    let (lifetimes, args) = if let Some(ta) = node.child(1) {
                        if ta.kind() == "type_args" {
                            self.map_type_args(ta, d)?
                        } else {
                            (Vec::new(), Vec::new())
                        }
                    } else {
                        (Vec::new(), Vec::new())
                    };
                    if text == "Self" {
                        if !lifetimes.is_empty() || !args.is_empty() {
                            d.push_error(self.diag(
                                first_child,
                                ParserCode::ReservedIdent,
                                "'Self' does not take type or lifetime arguments",
                            ));
                            return None;
                        }
                        if !self.type_scope.borrow().contains(text) {
                            d.push_error(self.diag(
                                first_child,
                                ParserCode::ReservedIdent,
                                "'Self' may only appear as a type reference inside a trait or impl body",
                            ));
                            return None;
                        }
                        return Some(param_ty(text));
                    }
                    if !lifetimes.is_empty() || !args.is_empty() {
                        return Some(custom_ty_generic(text, lifetimes, args));
                    }
                    if text == "bool" {
                        return Some(bool_ty());
                    }
                    if self.type_scope.borrow().contains(text) {
                        return Some(param_ty(text));
                    }
                    return Some(custom_ty(text));
                }

                let text = self.get_text(first_child);
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
                    let Some(inner) = node.child(inner_idx) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            format!("missing inner type for {}", text),
                        ));
                        return None;
                    };
                    let inner = self.map_type(inner, d)?;
                    return Some(match lt {
                        Some(lt) => named_ref_ty(kind, lt, inner),
                        None => ref_ty(kind, inner),
                    });
                }

                if text == "*" {
                    // Raw pointer type `*T`. Distinct from the deref
                    // place operator `*p` — types occupy a different
                    // grammar position.
                    let Some(inner) = node.child(1) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "missing inner type for raw pointer",
                        ));
                        return None;
                    };
                    return Some(raw_ptr_ty(self.map_type(inner, d)?));
                }

                if text == "[" {
                    // Fixed-size array `[T; N]`.
                    let Some(elem_node) = node.child_by_field_name("element") else {
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
                    let elem = self.map_type(elem_node, d)?;
                    let ConstVal::Int { bits, .. } =
                        self.lit_diag(parse_int_literal(self.get_text(len_node)), len_node, d)?
                    else {
                        d.push_error(self.diag(
                            len_node,
                            ParserCode::InvalidLiteral,
                            format!(
                                "array length must be an integer literal, got {}",
                                self.get_text(len_node)
                            ),
                        ));
                        return None;
                    };
                    return Some(array_ty(elem, bits));
                }

                match text {
                    "fn" => {
                        let mut params = Vec::new();
                        let mut cursor = node.walk();
                        for child in node.children(&mut cursor) {
                            if child.kind() == "type" {
                                params.push(self.map_type(child, d)?);
                            }
                        }
                        Some(fn_ty(params))
                    }
                    _ => {
                        d.push_error(self.diag(
                            first_child,
                            ParserCode::MalformedCst,
                            format!("unexpected token in type: {}", text),
                        ));
                        None
                    }
                }
            }
            _ => {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("unexpected node kind in type: {}", node.kind()),
                ));
                None
            }
        }
    }

    fn map_place(&self, node: Node, d: &mut Diagnostics) -> Option<Place> {
        match node.kind() {
            "identifier" => Some(Place::Var(self.get_text(node).to_string())),
            "place" => {
                let Some(first_child) = node.child(0) else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "place node has no children",
                    ));
                    return None;
                };
                if first_child.kind() == "identifier" && node.child_count() == 1 {
                    return Some(Place::Var(self.get_text(first_child).to_string()));
                }

                let n = node.child_count();
                if n >= 3 {
                    let last_child = node.child((n - 1) as u32).unwrap();
                    let second_to_last = node.child((n - 2) as u32).unwrap();
                    if self.get_text(last_child) == "*" && self.get_text(second_to_last) == "." {
                        let Some(inner) = node.child(0) else {
                            d.push_error(self.diag(
                                node,
                                ParserCode::MalformedCst,
                                "deref missing inner place",
                            ));
                            return None;
                        };
                        return Some(deref_place(self.map_place(inner, d)?));
                    }
                }

                let inner_place = self.map_place(first_child, d)?;
                if let Some(variant_node) = node.child_by_field_name("variant") {
                    let variant = self.get_text(variant_node).to_string();
                    Some(downcast_place(inner_place, variant))
                } else if let Some(field_node) = node.child_by_field_name("field") {
                    let field_name = self.get_text(field_node).to_string();
                    Some(field_place(inner_place, field_name))
                } else if let Some(index_node) = node.child_by_field_name("index") {
                    let index = self.map_operand(index_node, d)?;
                    Some(index_place(inner_place, index))
                } else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        format!("unrecognized place suffix: {}", self.get_text(node)),
                    ));
                    None
                }
            }
            _ => {
                d.push_error(self.diag(
                    node,
                    ParserCode::MalformedCst,
                    format!("unexpected node kind in place: {}", node.kind()),
                ));
                None
            }
        }
    }

    fn map_operand(&self, node: Node, d: &mut Diagnostics) -> Option<Operand> {
        if node.kind() == "operand" {
            let Some(first_child) = node.child(0) else {
                d.push_error(self.diag(node, ParserCode::MalformedCst, "operand missing children"));
                return None;
            };
            let text = self.get_text(first_child);
            match text {
                "copy" => {
                    let Some(place_node) = node.child(1) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "copy missing place",
                        ));
                        return None;
                    };
                    Some(copy_op(self.map_place(place_node, d)?))
                }
                "move" => {
                    let Some(place_node) = node.child(1) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "move missing place",
                        ));
                        return None;
                    };
                    Some(move_op(self.map_place(place_node, d)?))
                }
                "take" => {
                    let Some(place_node) = node.child(1) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "take missing place",
                        ));
                        return None;
                    };
                    Some(Operand::Take(self.map_place(place_node, d)?))
                }
                _ => Some(Operand::Const(self.map_const(first_child, d)?)),
            }
        } else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                format!("expected operand, found: {}", node.kind()),
            ));
            None
        }
    }

    fn map_const(&self, node: Node, d: &mut Diagnostics) -> Option<ConstVal> {
        match node.kind() {
            "int_lit" => self.lit_diag(parse_int_literal(self.get_text(node)), node, d),
            "float_lit" => self.lit_diag(parse_float_literal(self.get_text(node)), node, d),
            "byte_str_lit" => self.lit_diag(parse_byte_str_literal(self.get_text(node)), node, d),
            "byte_char_lit" => self.lit_diag(parse_byte_char_literal(self.get_text(node)), node, d),
            "const" => {
                let Some(child) = node.child(0) else {
                    d.push_error(self.diag(node, ParserCode::MalformedCst, "const node is empty"));
                    return None;
                };
                self.map_const(child, d)
            }
            // `fn_name`: two shapes — free-fn `foo<T>` or UFCS-style
            // trait-method callee `<SelfTy as Trait<Args>>::method<A>`.
            // The UFCS form carries a `self_ty` field; the free form
            // starts with the identifier at child(0).
            "fn_name" => {
                if let Some(self_ty_node) = node.child_by_field_name("self_ty") {
                    let self_ty = self.map_type(self_ty_node, d)?;
                    let Some(trait_name_node) = node.child_by_field_name("trait_name") else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "trait-method callee missing trait name",
                        ));
                        return None;
                    };
                    let trait_name = self.get_text(trait_name_node).to_string();
                    let (trait_lt_args, trait_type_args) =
                        if let Some(ta) = node.child_by_field_name("trait_args") {
                            self.map_type_args(ta, d)?
                        } else {
                            (Vec::new(), Vec::new())
                        };
                    let Some(method_name_node) = node.child_by_field_name("method_name") else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "trait-method callee missing method name",
                        ));
                        return None;
                    };
                    let method_name = self.get_text(method_name_node).to_string();
                    let (method_lt_args, method_type_args) =
                        if let Some(ma) = node.child_by_field_name("method_args") {
                            self.map_type_args(ma, d)?
                        } else {
                            (Vec::new(), Vec::new())
                        };
                    return Some(ConstVal::TraitFn {
                        trait_path: Instance::new(trait_name, trait_lt_args, trait_type_args),
                        self_ty,
                        method: Instance::new(method_name, method_lt_args, method_type_args),
                    });
                }
                let Some(ident_node) = node.child(0) else {
                    d.push_error(self.diag(
                        node,
                        ParserCode::MalformedCst,
                        "fn_name missing identifier",
                    ));
                    return None;
                };
                let name = self.get_text(ident_node).to_string();
                let (_lifetime_args, type_args) = if let Some(ta) = node.child(1) {
                    if ta.kind() == "type_args" {
                        self.map_type_args(ta, d)?
                    } else {
                        (Vec::new(), Vec::new())
                    }
                } else {
                    (Vec::new(), Vec::new())
                };
                Some(fn_name_const_with_args(name, type_args))
            }
            _ => {
                let text = self.get_text(node);
                match text {
                    "true" => Some(ConstVal::Bool(true)),
                    "false" => Some(ConstVal::Bool(false)),
                    "unit" => Some(ConstVal::Unit),
                    _ => Some(ConstVal::FnName(text.to_string(), Vec::new())),
                }
            }
        }
    }

    fn map_rvalue(&self, node: Node, d: &mut Diagnostics) -> Option<RValue> {
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "rvalue node is empty"));
            return None;
        };
        match child.kind() {
            "operand" => Some(RValue::Use(self.map_operand(child, d)?)),
            "pointer_cast" => {
                let Some(val_node) = child.child_by_field_name("value") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "ptr_cast missing value",
                    ));
                    return None;
                };
                let Some(ty_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "ptr_cast missing type",
                    ));
                    return None;
                };
                let op = self.map_operand(val_node, d)?;
                let ty = self.map_type(ty_node, d)?;
                Some(RValue::PtrCast(op, ty))
            }
            _ => {
                let text = self.get_text(child);
                let ref_kind = match text {
                    "&" => Some(RefKind::Shared),
                    "&mut" => Some(RefKind::Mut),
                    "&out" => Some(RefKind::Out),
                    "&drop" => Some(RefKind::Drop),
                    "&uninit" => Some(RefKind::Uninit),
                    _ => None,
                };
                if let Some(kind) = ref_kind {
                    let Some(place_node) = node.child(1) else {
                        d.push_error(self.diag(
                            node,
                            ParserCode::MalformedCst,
                            "ref missing place",
                        ));
                        return None;
                    };
                    return Some(ref_rv(kind, self.map_place(place_node, d)?));
                }
                match text {
                    "&raw" => {
                        let Some(place_node) = node.child(1) else {
                            d.push_error(self.diag(
                                node,
                                ParserCode::MalformedCst,
                                "&raw missing place",
                            ));
                            return None;
                        };
                        Some(raw_ref_rv(self.map_place(place_node, d)?))
                    }
                    "[" => {
                        // Array literal: [op0, op1, ..., opN-1].
                        let mut cursor = node.walk();
                        let mut ops: Vec<Operand> = Vec::new();
                        for c in node.children(&mut cursor).filter(|c| c.kind() == "operand") {
                            ops.push(self.map_operand(c, d)?);
                        }
                        Some(array_lit_rv(ops))
                    }
                    _ => {
                        let Some(enum_name_node) = node.child_by_field_name("enum_name") else {
                            d.push_error(self.diag(
                                node,
                                ParserCode::MalformedCst,
                                "enum construction missing enum name",
                            ));
                            return None;
                        };
                        let enum_name = self.get_text(enum_name_node).to_string();
                        let Some(variant_name_node) = node.child_by_field_name("variant_name")
                        else {
                            d.push_error(self.diag(
                                node,
                                ParserCode::MalformedCst,
                                "enum construction missing variant name",
                            ));
                            return None;
                        };
                        let variant_name = self.get_text(variant_name_node).to_string();
                        let mut cursor = node.walk();
                        let (_lifetime_args, type_args) = if let Some(ta) =
                            node.children(&mut cursor).find(|c| c.kind() == "type_args")
                        {
                            self.map_type_args(ta, d)?
                        } else {
                            (Vec::new(), Vec::new())
                        };
                        let mut cursor = node.walk();
                        let Some(operand_node) =
                            node.children(&mut cursor).find(|c| c.kind() == "operand")
                        else {
                            d.push_error(self.diag(
                                node,
                                ParserCode::MalformedCst,
                                "enum construction missing operand",
                            ));
                            return None;
                        };
                        let operand = self.map_operand(operand_node, d)?;
                        Some(enum_constr_rv_with_args(
                            enum_name,
                            type_args,
                            variant_name,
                            operand,
                        ))
                    }
                }
            }
        }
    }

    fn map_statement(&self, node: Node, d: &mut Diagnostics) -> Option<Statement> {
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "statement empty"));
            return None;
        };
        let child_span = span_of(child);
        match child.kind() {
            "assignment" => {
                let Some(lhs_node) = child.child_by_field_name("lhs") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "assignment missing lhs",
                    ));
                    return None;
                };
                let lhs = self.map_place(lhs_node, d)?;
                let Some(rhs_node) = child.child_by_field_name("rhs") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "assignment missing rhs",
                    ));
                    return None;
                };
                let rhs = self.map_rvalue(rhs_node, d)?;
                Some(assign_stmt(lhs, rhs, child_span))
            }
            "call" => {
                let Some(func_node) = child.child_by_field_name("function") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "call missing function",
                    ));
                    return None;
                };
                let func = self.map_operand(func_node, d)?;

                let mut args = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "operand" && item != func_node {
                        args.push(self.map_operand(item, d)?);
                    }
                }
                Some(call_stmt(func, args, child_span))
            }
            "drop_stmt" => {
                let Some(place_node) = child.child_by_field_name("place") else {
                    d.push_error(self.diag(child, ParserCode::MalformedCst, "drop missing place"));
                    return None;
                };
                Some(drop_stmt(self.map_place(place_node, d)?, child_span))
            }
            "unborrow_stmt" => {
                let Some(place_node) = child.child_by_field_name("place") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "unborrow missing place",
                    ));
                    return None;
                };
                Some(unborrow_stmt(self.map_place(place_node, d)?, child_span))
            }
            "require_uninit_stmt" => {
                let Some(place_node) = child.child_by_field_name("place") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "require_uninit missing place",
                    ));
                    return None;
                };
                Some(require_uninit_stmt(
                    self.map_place(place_node, d)?,
                    child_span,
                ))
            }
            _ => {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("unknown statement kind: {}", child.kind()),
                ));
                None
            }
        }
    }

    fn map_terminator(&self, node: Node, d: &mut Diagnostics) -> Option<Terminator> {
        let Some(child) = node.child(0) else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "terminator empty"));
            return None;
        };
        let child_span = span_of(child);
        match child.kind() {
            "goto" => {
                let Some(label_node) = child.child_by_field_name("label") else {
                    d.push_error(self.diag(child, ParserCode::MalformedCst, "goto missing label"));
                    return None;
                };
                Some(goto_term(self.get_text(label_node), child_span))
            }
            "return" => Some(return_term(child_span)),
            "branch" => {
                let Some(cond_node) = child.child_by_field_name("condition") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "branch missing condition",
                    ));
                    return None;
                };
                let cond = self.map_operand(cond_node, d)?;
                let Some(true_node) = child.child_by_field_name("true_label") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "branch missing true_label",
                    ));
                    return None;
                };
                let true_label = self.get_text(true_node).to_string();
                let Some(false_node) = child.child_by_field_name("false_label") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "branch missing false_label",
                    ));
                    return None;
                };
                let false_label = self.get_text(false_node).to_string();
                Some(branch_term(cond, true_label, false_label, child_span))
            }
            "switchEnum" => {
                let Some(place_node) = child.child_by_field_name("place") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "switchEnum missing place",
                    ));
                    return None;
                };
                let place = self.map_place(place_node, d)?;

                let mut cases = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "switch_case" {
                        let Some(variant_node) = item.child_by_field_name("variant") else {
                            d.push_error(self.diag(
                                item,
                                ParserCode::MalformedCst,
                                "switch case missing variant",
                            ));
                            return None;
                        };
                        let variant = self.get_text(variant_node).to_string();
                        let Some(label_node) = item.child_by_field_name("label") else {
                            d.push_error(self.diag(
                                item,
                                ParserCode::MalformedCst,
                                "switch case missing label",
                            ));
                            return None;
                        };
                        let label = self.get_text(label_node).to_string();
                        cases.push((variant, label));
                    }
                }
                Some(switch_enum_term(place, cases, child_span))
            }
            "abort" => Some(abort_term(child_span)),
            "unreachable" => Some(unreachable_term(child_span)),
            _ => {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("unknown terminator kind: {}", child.kind()),
                ));
                None
            }
        }
    }

    fn map_basic_block(&self, node: Node, d: &mut Diagnostics) -> Option<BasicBlock> {
        let Some(label_node) = node.child_by_field_name("label") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "basic block missing label"));
            return None;
        };
        let label = self.get_text(label_node).to_string();
        let label_span = span_of(label_node);

        // Record the diagnostics length before descending so any errors
        // pushed by statement/terminator sub-parses can be tagged with
        // this block's label after the fact.
        let errors_before = d.error_count();
        let result = self.map_basic_block_body(node, &label, label_span, d);
        d.annotate_errors_in_block(errors_before, &label);
        result
    }

    fn map_basic_block_body(
        &self,
        node: Node,
        label: &str,
        label_span: Span,
        d: &mut Diagnostics,
    ) -> Option<BasicBlock> {
        let mut statements = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "statement" {
                statements.push(self.map_statement(child, d)?);
            }
        }

        let Some(term_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "terminator")
        else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                "basic block missing terminator",
            ));
            return None;
        };
        let terminator = self.map_terminator(term_node, d)?;

        Some(BasicBlock {
            label: label.to_string(),
            label_source: SourceInfo::written(label_span),
            statements,
            terminator,
        })
    }

    /// Parse a `type_args` node (`<'a, T, U>`) into (lifetime_args,
    /// type_args). Requires the type_scope already reflects the
    /// enclosing decl's params so nested `Param` refs resolve.
    fn map_type_args(&self, node: Node, d: &mut Diagnostics) -> Option<(Vec<Lifetime>, Vec<Type>)> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "lifetime" {
                let name = self.get_text(child).trim_start_matches('\'').to_string();
                lifetimes.push(Lifetime(name));
            } else if child.kind() == "type" || scalar_kind_to_type(child.kind()).is_some() {
                types.push(self.map_type(child, d)?);
            }
        }
        Some((lifetimes, types))
    }

    /// Parse a `type_params` node (`<'a, 'b: 'a, T, U: Copy + Drop>`)
    /// into (lifetime_params, type_params, outlives). Side-effects:
    /// pushes each type-param name into `type_scope` for subsequent
    /// map_type calls. Outlives pairs `(subject, must_outlive)` are
    /// collected from the `'a: 'b + 'c` inline bounds; the tuple
    /// convention matches `DeclMeta::outlives`.
    fn map_type_params(
        &self,
        node: Node,
        d: &mut Diagnostics,
    ) -> Option<(Vec<LifetimeParam>, Vec<TypeParam>, Vec<OutlivesBound>)> {
        let mut lifetimes = Vec::new();
        let mut types = Vec::new();
        let mut outlives = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "lifetime_param" => {
                    // `field('name', $.lifetime)` on the param; every
                    // `field('bound', $.lifetime)` after `:` is an
                    // outlives axiom `subject outlives bound`.
                    let Some(name_node) = child.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "lifetime param missing name",
                        ));
                        return None;
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
                        return None;
                    };
                    let pname = self.get_text(name_node).to_string();
                    if self.reject_self_ident(&pname, name_node, "a type-parameter name", d) {
                        continue;
                    }
                    if self.type_scope.borrow().contains(&pname) {
                        d.push_error(self.diag(
                            name_node,
                            ParserCode::MalformedCst,
                            format!("Duplicate type parameter '{}'", pname),
                        ));
                        continue;
                    }
                    let markers = if let Some(m) = child
                        .children(&mut child.walk())
                        .find(|c| c.kind() == "markers")
                    {
                        Markers::from_iter(self.map_marker_tokens(m, d)?)
                    } else {
                        Markers::empty()
                    };
                    self.type_scope.borrow_mut().insert(pname.clone());
                    types.push(TypeParam {
                        name: pname,
                        bounds: Bounds::from_markers(markers),
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

    /// Parse a `markers` node (one or more `Copy`/`Drop`/`Move` in any
    /// order) into the raw sequence the user wrote. Errors on duplicates.
    /// Returns the raw `Vec<Marker>` — callers that want the canonical
    /// value call `Markers::from_iter`; callers that want to lint on
    /// the pre-canonicalization shape (e.g. redundant Move) inspect the
    /// vec first.
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

    fn map_struct_decl(&self, node: Node, d: &mut Diagnostics) -> Option<StructDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "struct decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);
        if self.reject_self_ident(&name, name_node, "a struct name", d) {
            return None;
        }

        let mut cursor = node.walk();
        // Populate scope BEFORE walking fields so `t: T` resolves to
        // `Param`. Cleared on return so scopes don't leak across decls.
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, d)?
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
                    return None;
                };
                let f_name = self.get_text(f_name_node).to_string();
                let Some(f_type_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "struct field missing type",
                    ));
                    return None;
                };
                if self.reject_self_ident(&f_name, f_name_node, "a field name", d) {
                    continue;
                }
                let f_type = self.map_type(f_type_node, d)?;
                fields.push(StructField {
                    name: f_name,
                    ty: f_type,
                    source: SourceInfo::written(span_of(child)),
                });
            }
        }
        self.type_scope.borrow_mut().clear();

        Some(StructDecl {
            meta: DeclMeta {
                name,
                name_source: SourceInfo::written(name_span),
                params: GenericParams {
                    lifetime_params,
                    outlives,
                    type_params,
                    source: SourceInfo::written(span_of(node)),
                },
                markers,
            },
            fields,
        })
    }

    fn map_enum_decl(&self, node: Node, d: &mut Diagnostics) -> Option<EnumDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "enum decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);
        if self.reject_self_ident(&name, name_node, "an enum name", d) {
            return None;
        }

        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, d)?
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
                    return None;
                };
                let v_name = self.get_text(v_name_node).to_string();
                let Some(v_type_node) = child.child_by_field_name("type") else {
                    d.push_error(self.diag(
                        child,
                        ParserCode::MalformedCst,
                        "enum variant missing type",
                    ));
                    return None;
                };
                if self.reject_self_ident(&v_name, v_name_node, "a variant name", d) {
                    continue;
                }
                let v_type = self.map_type(v_type_node, d)?;
                variants.push(EnumVariant {
                    name: v_name,
                    ty: v_type,
                    source: SourceInfo::written(span_of(child)),
                });
            }
        }
        self.type_scope.borrow_mut().clear();

        Some(EnumDecl {
            meta: DeclMeta {
                name,
                name_source: SourceInfo::written(name_span),
                params: GenericParams {
                    lifetime_params,
                    outlives,
                    type_params,
                    source: SourceInfo::written(span_of(node)),
                },
                markers,
            },
            variants,
        })
    }

    fn map_trait_decl(&self, node: Node, d: &mut Diagnostics) -> Option<TraitDecl> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "trait decl missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);
        if self.reject_self_ident(&name, name_node, "a trait name", d) {
            return None;
        }

        let mut cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Bind the implicit `Self` type parameter into the trait's scope
        // so method signatures can reference it. Impls substitute
        // `Self` with the target type at check time.
        self.type_scope.borrow_mut().insert("Self".to_string());

        // `map_function_decl` clears the entire type_scope when it
        // exits — appropriate for top-level fns, but for trait
        // methods we need the trait's type_params + Self to persist
        // across method sigs. Snapshot here and restore before each.
        let trait_scope: std::collections::BTreeSet<String> = self.type_scope.borrow().clone();

        let mut methods: Vec<Function> = Vec::new();
        let mut seen_names: std::collections::HashSet<String> = Default::default();
        for child in node.children(&mut cursor) {
            if child.kind() != "function_decl" {
                continue;
            }
            *self.type_scope.borrow_mut() = trait_scope.clone();
            let f = self.map_function_decl(child, d)?;
            if f.is_extern {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("trait method '{}' cannot be extern", f.meta.name),
                ));
                continue;
            }
            if f.body.is_some() {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("trait method '{}' must not have a body", f.meta.name),
                ));
                continue;
            }
            if !seen_names.insert(f.meta.name.clone()) {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("duplicate trait method '{}'", f.meta.name),
                ));
                continue;
            }
            methods.push(f);
        }
        self.type_scope.borrow_mut().clear();

        Some(TraitDecl {
            meta: DeclMeta {
                name,
                name_source: SourceInfo::written(name_span),
                params: GenericParams {
                    lifetime_params,
                    outlives,
                    type_params,
                    source: SourceInfo::written(span_of(node)),
                },
                markers: Markers::empty(),
            },
            methods,
        })
    }

    fn map_impl_decl(&self, node: Node, d: &mut Diagnostics) -> Option<ImplBlock> {
        let Some(trait_name_node) = node.child_by_field_name("trait_name") else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                "impl decl missing trait name",
            ));
            return None;
        };
        let trait_name = self.get_text(trait_name_node).to_string();
        let trait_name_span = span_of(trait_name_node);
        if self.reject_self_ident(&trait_name, trait_name_node, "a trait reference", d) {
            return None;
        }

        let mut cursor = node.walk();

        // Impl-header generics come first (`impl<T> ...`). Populates
        // the type_scope so the trait_path type_args, target, and
        // method bodies can reference them.
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        // Optional trait type_args (`Iter<T>`). Absent = non-generic
        // trait (`Iter`).
        let (trait_lt_args, trait_type_args) =
            if let Some(args_node) = node.children(&mut cursor).find(|c| c.kind() == "type_args") {
                self.map_type_args(args_node, d)?
            } else {
                (Vec::new(), Vec::new())
            };
        let trait_path = Instance::new(&trait_name, trait_lt_args, trait_type_args);

        let Some(target_node) = node.child_by_field_name("target") else {
            d.push_error(self.diag(
                node,
                ParserCode::MalformedCst,
                "impl decl missing target type",
            ));
            return None;
        };
        let target = self.map_type(target_node, d)?;

        // Bind the implicit `Self` type parameter into the impl's method
        // scope so method sigs and bodies can reference `Self` instead of
        // repeating the target type. The `desugar::self_alias` pass
        // rewrites `Self := target` before type-check runs. Inserted
        // after `target` is parsed so `impl Trait for Self` is a
        // reference to an undeclared type, not a paradox.
        self.type_scope.borrow_mut().insert("Self".to_string());

        // Snapshot the impl-header scope so it persists across each
        // method's `map_function_decl` call (which clears the scope
        // on exit — see `map_trait_decl` for the same pattern).
        let impl_scope: std::collections::BTreeSet<String> = self.type_scope.borrow().clone();

        let mut methods: Vec<Function> = Vec::new();
        let mut seen_names: std::collections::HashSet<String> = Default::default();
        for child in node.children(&mut cursor) {
            if child.kind() != "function_decl" {
                continue;
            }
            *self.type_scope.borrow_mut() = impl_scope.clone();
            let f = self.map_function_decl(child, d)?;
            if f.is_extern {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("impl method '{}' cannot be extern", f.meta.name),
                ));
                continue;
            }
            if f.body.is_none() {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("impl method '{}' requires a body", f.meta.name),
                ));
                continue;
            }
            if !seen_names.insert(f.meta.name.clone()) {
                d.push_error(self.diag(
                    child,
                    ParserCode::MalformedCst,
                    format!("duplicate impl method '{}'", f.meta.name),
                ));
                continue;
            }
            methods.push(f);
        }
        self.type_scope.borrow_mut().clear();

        Some(ImplBlock {
            params: GenericParams {
                lifetime_params,
                outlives,
                type_params,
                source: SourceInfo::written(trait_name_span),
            },
            trait_path,
            target,
            methods,
        })
    }

    fn map_function_decl(&self, node: Node, d: &mut Diagnostics) -> Option<Function> {
        let Some(name_node) = node.child_by_field_name("name") else {
            d.push_error(self.diag(node, ParserCode::MalformedCst, "function missing name"));
            return None;
        };
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);
        if self.reject_self_ident(&name, name_node, "a function name", d) {
            return None;
        }
        let is_extern = self.get_text(node).starts_with("extern");
        let abi = if let Some(abi_node) = node.child_by_field_name("abi") {
            let raw = self.get_text(abi_node);
            Some(raw.trim_matches('"').to_string())
        } else {
            None
        };

        // Record diagnostics length so any errors pushed while parsing
        // this function's body can be tagged with `in_function(name)`
        // after the fact — mirrors the block-context annotation.
        let errors_before = d.error_count();
        let result = self.map_function_decl_body(node, name.clone(), name_span, is_extern, abi, d);
        d.annotate_errors_in_function(errors_before, &name);
        self.type_scope.borrow_mut().clear();
        result
    }

    fn map_function_decl_body(
        &self,
        node: Node,
        name: String,
        name_span: Span,
        is_extern: bool,
        abi: Option<String>,
        d: &mut Diagnostics,
    ) -> Option<Function> {
        // Populate the type-param scope before mapping any types in
        // params, locals, or body — same as struct/enum. Both extern and
        // defined functions can have type parameters.
        let mut tp_cursor = node.walk();
        let (lifetime_params, type_params, outlives) = if let Some(tp_node) = node
            .children(&mut tp_cursor)
            .find(|c| c.kind() == "type_params")
        {
            self.map_type_params(tp_node, d)?
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };

        let mut params = Vec::new();
        let mut locals = Vec::new();
        let mut blocks = Vec::new();
        let mut has_body = false;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "param_decl" => {
                    let Some(p_name_node) = child.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "param missing name",
                        ));
                        return None;
                    };
                    let p_name = self.get_text(p_name_node).to_string();
                    let Some(p_type_node) = child.child_by_field_name("type") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "param missing type",
                        ));
                        return None;
                    };
                    if self.reject_self_ident(&p_name, p_name_node, "a parameter name", d) {
                        continue;
                    }
                    let p_type = self.map_type(p_type_node, d)?;
                    params.push(Param {
                        name: p_name,
                        ty: p_type,
                        source: SourceInfo::written(span_of(child)),
                    });
                }
                "local_decl" => {
                    has_body = true;
                    let Some(l_name_node) = child.child_by_field_name("name") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "local missing name",
                        ));
                        return None;
                    };
                    let l_name = self.get_text(l_name_node).to_string();
                    let Some(l_type_node) = child.child_by_field_name("type") else {
                        d.push_error(self.diag(
                            child,
                            ParserCode::MalformedCst,
                            "local missing type",
                        ));
                        return None;
                    };
                    if self.reject_self_ident(&l_name, l_name_node, "a local name", d) {
                        continue;
                    }
                    let l_type = self.map_type(l_type_node, d)?;
                    locals.push(Local {
                        name: l_name,
                        ty: l_type,
                        source: SourceInfo::written(span_of(child)),
                    });
                }
                "basic_block" => {
                    has_body = true;
                    blocks.push(self.map_basic_block(child, d)?);
                }
                "{" | "}" => {
                    has_body = true;
                }
                _ => {}
            }
        }

        let body = if has_body {
            Some(FunctionBody { locals, blocks })
        } else {
            None
        };

        Some(Function {
            meta: DeclMeta {
                name,
                name_source: SourceInfo::written(name_span),
                params: GenericParams {
                    lifetime_params,
                    outlives,
                    type_params,
                    source: SourceInfo::written(span_of(node)),
                },
                markers: trivial_markers(),
            },
            is_extern,
            abi,
            params,
            body,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_struct_decl() {
        let source = "
            struct Point: Copy + Drop {
                x: i64
                y: i64
            }
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(s) = &program.declarations[0] {
            assert_eq!(s.meta.name, "Point");
            assert!(s.meta.markers.declared(Marker::Copy));
            assert!(s.meta.markers.declared(Marker::Drop));
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].name, "x");
            assert_eq!(s.fields[0].ty, i64_ty());
            assert_eq!(s.fields[1].name, "y");
            assert_eq!(s.fields[1].ty, i64_ty());
        } else {
            panic!("Expected struct declaration");
        }
    }

    #[test]
    fn test_parse_enum_decl() {
        let source = "
            enum Option {
                None: Option
                Some: i64
            }
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(e) = &program.declarations[0] {
            assert_eq!(e.meta.name, "Option");
            assert!(!e.meta.markers.declared(Marker::Copy));
            assert!(!e.meta.markers.declared(Marker::Drop));
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].name, "None");
            assert_eq!(e.variants[0].ty, custom_ty("Option"));
            assert_eq!(e.variants[1].name, "Some");
            assert_eq!(e.variants[1].ty, i64_ty());
        } else {
            panic!("Expected enum declaration");
        }
    }

    #[test]
    fn test_parse_function_decl() {
        let source = "
            fn add(a: i64, b: i64) {
                ret: &out i64;
                entry:
                    r1 = copy a;
                    r2 = copy b;
                    call add_impl(move r1, move r2);
                    return
            }
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.meta.name, "add");
            assert!(!f.is_extern);
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.params[0].name, "a");
            assert_eq!(f.params[0].ty, i64_ty());

            let body = f.body.as_ref().unwrap();
            assert_eq!(body.locals.len(), 1);
            assert_eq!(body.locals[0].name, "ret");
            assert_eq!(body.blocks.len(), 1);
            let block = &body.blocks[0];
            assert_eq!(block.label, "entry");
            assert_eq!(block.statements.len(), 3);
            assert_eq!(
                block.terminator,
                return_term(Span {
                    line: 8,
                    col: 21,
                    end_line: 8,
                    end_col: 27
                })
            );
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn test_parse_require_uninit_stmt() {
        let source = "
            fn f(x: i64) {
                entry:
                    require_uninit x;
                    return
            }
        ";
        let program = Parser::parse_or_panic(source);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected function declaration");
        };
        let body = f.body.as_ref().unwrap();
        assert!(matches!(
            body.blocks[0].statements.as_slice(),
            [Statement {
                kind: StatementKind::RequireUninit(Place::Var(name)),
                ..
            }] if name == "x"
        ));
    }

    #[test]
    fn test_parse_extern_fn() {
        let source = "
            extern fn add_impl(a: i64, b: i64);
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.meta.name, "add_impl");
            assert!(f.is_extern);
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.params[0].name, "a");
            assert_eq!(f.params[0].ty, i64_ty());
            assert!(f.body.is_none());
        } else {
            panic!("Expected extern function declaration");
        }
    }

    #[test]
    fn test_parse_generic_extern_fn() {
        let source = "
            extern fn<'a, T: Move> add_impl(a: &mut i64, b: T);
        ";
        let program = Parser::parse_or_panic(source);
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.meta.name, "add_impl");
            assert!(f.is_extern);
            assert_eq!(f.meta.params.lifetime_params.len(), 1);
            assert_eq!(f.meta.params.lifetime_params[0].0, "a");
            assert_eq!(f.meta.params.type_params.len(), 1);
            assert_eq!(f.meta.params.type_params[0].name, "T");
            assert_eq!(f.params.len(), 2);
            assert!(f.body.is_none());
        } else {
            panic!("Expected extern function declaration");
        }
    }

    // ---------- Scalar type parsing ----------

    fn ty_of_param(src: &str, idx: usize) -> Type {
        let program = Parser::parse_or_panic(src);
        match &program.declarations[0] {
            Declaration::Fn(f) => f.params[idx].ty.clone(),
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn parse_all_int_type_keywords() {
        let src = "extern fn f(a: i8, b: i16, c: i32, d: i64, e: u8, g: u16, h: u32, i: u64);";
        assert_eq!(ty_of_param(src, 0), i8_ty());
        assert_eq!(ty_of_param(src, 1), i16_ty());
        assert_eq!(ty_of_param(src, 2), i32_ty());
        assert_eq!(ty_of_param(src, 3), i64_ty());
        assert_eq!(ty_of_param(src, 4), u8_ty());
        assert_eq!(ty_of_param(src, 5), u16_ty());
        assert_eq!(ty_of_param(src, 6), u32_ty());
        assert_eq!(ty_of_param(src, 7), u64_ty());
    }

    #[test]
    fn parse_float_type_keywords() {
        let src = "extern fn f(a: f32, b: f64);";
        assert_eq!(ty_of_param(src, 0), f32_ty());
        assert_eq!(ty_of_param(src, 1), f64_ty());
    }

    // ---------- Integer literal parsing ----------

    /// Parse a fn body with `x = <literal>` and return the ConstVal.
    fn const_of_first_assign(src: &str) -> ConstVal {
        let program = Parser::parse_or_panic(src);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        let body = f.body.as_ref().unwrap();
        let stmt = &body.blocks[0].statements[0];
        let StatementKind::Assign(_, RValue::Use(Operand::Const(c))) = &stmt.kind else {
            panic!("expected assign of const, got {:?}", stmt);
        };
        c.clone()
    }

    #[test]
    fn parse_unsuffixed_int_defaults_to_i64() {
        let src = "fn f() { x: i64; entry: x = 42; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 42,
                ty: IntTy::I64
            }
        );
    }

    #[test]
    fn parse_suffixed_int_uses_suffix_type() {
        let src = "fn f() { x: i8; entry: x = 42i8; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 42,
                ty: IntTy::I8
            }
        );
    }

    #[test]
    fn parse_hex_int() {
        let src = "fn f() { x: u32; entry: x = 0xFFu32; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 255,
                ty: IntTy::U32
            }
        );
    }

    #[test]
    fn parse_binary_int() {
        let src = "fn f() { x: u8; entry: x = 0b1010u8; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 10,
                ty: IntTy::U8
            }
        );
    }

    #[test]
    fn parse_int_with_underscores() {
        let src = "fn f() { x: i64; entry: x = 1_000_000; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 1_000_000,
                ty: IntTy::I64
            }
        );
    }

    #[test]
    fn parse_hex_with_underscores() {
        let src = "fn f() { x: u32; entry: x = 0xDEAD_BEEFu32; return }";
        assert_eq!(
            const_of_first_assign(src),
            ConstVal::Int {
                bits: 0xDEAD_BEEF,
                ty: IntTy::U32
            }
        );
    }

    // ---------- Float literal parsing ----------

    #[test]
    fn parse_unsuffixed_float_defaults_to_f64() {
        let src = "fn f() { x: f64; entry: x = 3.14; return }";
        let c = const_of_first_assign(src);
        let ConstVal::Float { bits, ty } = c else {
            panic!("expected float, got {:?}", c);
        };
        assert_eq!(ty, FloatTy::F64);
        assert_eq!(f64::from_bits(bits), 3.14);
    }

    #[test]
    fn parse_suffixed_f32_float() {
        let src = "fn f() { x: f32; entry: x = 2.5f32; return }";
        let c = const_of_first_assign(src);
        let ConstVal::Float { bits, ty } = c else {
            panic!("expected float, got {:?}", c);
        };
        assert_eq!(ty, FloatTy::F32);
        assert_eq!(f32::from_bits(bits as u32), 2.5);
    }

    // ---------- Marker parsing ----------

    #[test]
    fn duplicate_marker_rejected() {
        // `map_markers` returns an error on duplicates.
        let src = "struct P: Copy + Copy { x: i64 }";
        let mut diags = Diagnostics::default();
        let prog = Parser::new(src.to_string()).parse(&mut diags);
        assert!(
            prog.is_none(),
            "expected parse failure for duplicate marker"
        );
        let errs = diags.errors_str();
        assert!(
            errs.iter().any(|e| e.contains("Duplicate marker")),
            "expected 'Duplicate marker' in errors, got: {:?}",
            errs
        );
    }

    #[test]
    fn marker_order_is_commutative() {
        // Any permutation of {Copy, Drop, Move} yields the same set
        // of flags — canonicalization is not by textual order.
        fn markers_of(src: &str) -> Markers {
            let program = Parser::parse_or_panic(src);
            let Declaration::Struct(s) = &program.declarations[0] else {
                panic!("expected struct");
            };
            s.meta.markers
        }
        let a = markers_of("struct P: Copy + Drop + Move { x: i64 }");
        let b = markers_of("struct P: Move + Drop + Copy { x: i64 }");
        let c = markers_of("struct P: Drop + Copy + Move { x: i64 }");
        assert_eq!(a, b);
        assert_eq!(b, c);
        // All three implied — Move canonicalizes to implied-only when
        // Copy and Drop are declared, so `declared(Move)` is false but
        // `implies(Move)` holds.
        assert!(a.implies(Marker::Copy) && a.implies(Marker::Drop) && a.implies(Marker::Move));
    }

    #[test]
    fn syntax_errors_emit_one_diagnostic_per_region() {
        // Two broken functions. Regression against the pre-hoist
        // "Syntax error in source code" fallback that collapsed every
        // parse failure into a single opaque string. The walker now
        // emits at least one Parser(UnexpectedToken|MissingToken)
        // diagnostic per broken region so users can locate each
        // independently.
        let src = "\
            fn a( { entry: return }\n\
            fn b( { entry: return }\n";
        let mut diags = Diagnostics::default();
        let _ = Parser::new(src.to_string()).parse(&mut diags);
        assert!(
            diags.error_count() >= 2,
            "expected multi-error output, got {} error(s): {:?}",
            diags.error_count(),
            diags.errors_str()
        );
        for e in diags.errors() {
            match e.code() {
                DiagCode::Parser(ParserCode::UnexpectedToken)
                | DiagCode::Parser(ParserCode::MissingToken) => {}
                other => panic!(
                    "walker should emit only UnexpectedToken/MissingToken; got {:?}",
                    other
                ),
            }
        }
    }

    #[test]
    fn syntax_error_carries_function_context() {
        // A syntax error inside a function body should be tagged with
        // the enclosing function's name so the diagnostic reads
        // "at L:C: In function 'f': ...". Uses `in_function` context
        // threading in the ERROR/MISSING walker.
        let src = "fn my_fn(x: i64) {\n  entry:\n    x = @@;\n    return\n}\n";
        let mut diags = Diagnostics::default();
        let _ = Parser::new(src.to_string()).parse(&mut diags);
        let rendered = diags.errors_str().join("\n");
        assert!(
            rendered.contains("In function 'my_fn'"),
            "expected function context in errors:\n{}",
            rendered
        );
    }

    #[test]
    fn syntax_error_carries_block_context() {
        // A syntax error inside a basic_block should be tagged with
        // both the enclosing function AND the enclosing block label.
        // Uses `in_block` context threading in the walker.
        let src = "fn f() {\n  my_block:\n    @@;\n    return\n}\n";
        let mut diags = Diagnostics::default();
        let _ = Parser::new(src.to_string()).parse(&mut diags);
        let rendered = diags.errors_str().join("\n");
        assert!(
            rendered.contains("block 'my_block'"),
            "expected block context in errors:\n{}",
            rendered
        );
    }

    #[test]
    fn mir_fn_type_rejects_return_arrow() {
        // MIR's `fn(T,...)` type has no return arrow — returns go
        // through `&out $return` params. If someone writes an HLL-style
        // `fn(i64) -> i64` in a .sim file, the arrow tokens shouldn't
        // parse (they belong to HLL's grammar variant, not MIR's).
        let src = "fn f(g: fn(i64) -> i64) { entry: return }";
        let mut diags = Diagnostics::default();
        let _ = Parser::new(src.to_string()).parse(&mut diags);
        assert!(
            diags.error_count() >= 1,
            "expected at least one syntax error, got {}",
            diags.error_count()
        );
    }

    #[test]
    fn struct_decl_accepts_whitespace_or_comma_separators() {
        // MIR struct/enum decls tolerate either whitespace-only or
        // comma-separated fields. Locked in so we don't accidentally
        // regress to whitespace-only.
        let ws = "struct P { x: i64 y: i64 }";
        let comma = "struct P { x: i64, y: i64 }";
        let mixed = "struct P { x: i64, y: i64 }";
        let trailing = "struct P { x: i64, y: i64, }";
        for src in [ws, comma, mixed, trailing] {
            let prog = Parser::parse_or_panic(src);
            let Declaration::Struct(s) = &prog.declarations[0] else {
                panic!()
            };
            assert_eq!(s.fields.len(), 2, "for source: {:?}", src);
        }
    }

    #[test]
    fn bool_type_keyword_parses_as_type_bool() {
        // Regression: the grammar previously spelled the boolean type
        // keyword as `boolean` while the rest of the codebase (Rust
        // sources, pretty printer, HLL) used `bool`. Source text `bool`
        // silently fell through to the `identifier` alternative and
        // produced `TypeKind::Custom("bool")`, which downstream typecheck
        // rejected as "undeclared type 'bool'". The pretty printer emits
        // `bool`, so round-tripping any bool-using program was broken.
        let src = "fn f(x: bool) { entry: return }";
        let program = Parser::parse_or_panic(src);
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        assert_eq!(f.params[0].ty, bool_ty());
    }

    #[test]
    fn basic_block_accepts_trailing_semicolon_after_terminator() {
        // MIR terminators can optionally be followed by a semicolon.
        // Tolerates both with and without semicolons.
        let with_semi = "fn f() { entry: return; }";
        let without_semi = "fn f() { entry: return }";
        let multiple_with_semi = "fn f() { entry: goto loop; loop: return; }";
        for src in [with_semi, without_semi, multiple_with_semi] {
            Parser::parse_or_panic(src);
        }
    }
}
