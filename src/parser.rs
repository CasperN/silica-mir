use crate::ast::*;
use tree_sitter::{Node, Parser as TSParser};

extern "C" {
    fn tree_sitter_silica_mir() -> *const std::ffi::c_void;
}

pub fn language() -> tree_sitter::Language {
    unsafe { tree_sitter::Language::from_raw(tree_sitter_silica_mir() as *const _) }
}

fn span_of(node: Node) -> Span {
    let p = node.start_position();
    Span {
        line: (p.row as u32).saturating_add(1),
        col: (p.column as u32).saturating_add(1),
    }
}

/// Map a scalar type keyword's tree-sitter node kind to `Type`.
/// Returns `None` if the kind isn't one of the ten scalar keywords.
fn scalar_kind_to_type(kind: &str) -> Option<Type> {
    Some(match kind {
        "i8" => Type::Int(IntTy::I8),
        "i16" => Type::Int(IntTy::I16),
        "i32" => Type::Int(IntTy::I32),
        "i64" => Type::Int(IntTy::I64),
        "u8" => Type::Int(IntTy::U8),
        "u16" => Type::Int(IntTy::U16),
        "u32" => Type::Int(IntTy::U32),
        "u64" => Type::Int(IntTy::U64),
        "f32" => Type::Float(FloatTy::F32),
        "f64" => Type::Float(FloatTy::F64),
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
    Ok(ConstVal::Int { bits, ty })
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
            Ok(ConstVal::Float {
                bits: v.to_bits() as u64,
                ty,
            })
        }
        FloatTy::F64 => {
            let v: f64 = cleaned
                .parse()
                .map_err(|e| format!("invalid f64 literal {:?}: {}", text, e))?;
            Ok(ConstVal::Float {
                bits: v.to_bits(),
                ty,
            })
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
    Ok(ConstVal::ByteStr(decode_byte_escapes(inner)?))
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
    Ok(ConstVal::Int {
        bits: bytes[0] as u64,
        ty: IntTy::U8,
    })
}

/// Decode the escape sequences in a `b"..."` / `b'...'` literal body
/// (quote delimiters already stripped). Shared by both parsers so the
/// escape set stays consistent.
fn decode_byte_escapes(inner: &str) -> Result<Vec<u8>, String> {
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
    source: String,
}

impl Parser {
    pub fn new(source: String) -> Self {
        Self { source }
    }

    pub fn parse(&self) -> Result<Program, String> {
        let mut parser = TSParser::new();
        parser
            .set_language(&language())
            .map_err(|e| e.to_string())?;

        let tree = parser
            .parse(&self.source, None)
            .ok_or("Failed to parse source code")?;
        let root = tree.root_node();

        if root.has_error() {
            return Err("Syntax error in source code".to_string());
        }

        self.map_program(root)
    }

    fn get_text(&self, node: Node) -> &str {
        &self.source[node.byte_range()]
    }

    fn map_program(&self, node: Node) -> Result<Program, String> {
        let mut declarations = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "declaration" {
                declarations.push(self.map_declaration(child)?);
            }
        }
        Ok(Program { declarations })
    }

    fn map_declaration(&self, node: Node) -> Result<Declaration, String> {
        let child = node.child(0).ok_or("Empty declaration")?;
        match child.kind() {
            "struct_decl" => Ok(Declaration::Struct(self.map_struct_decl(child)?)),
            "enum_decl" => Ok(Declaration::Enum(self.map_enum_decl(child)?)),
            "function_decl" => Ok(Declaration::Fn(self.map_function_decl(child)?)),
            _ => Err(format!("Unknown declaration kind: {}", child.kind())),
        }
    }

    fn map_type(&self, node: Node) -> Result<Type, String> {
        // Scalar type keywords are tokenized as anonymous tree-sitter
        // nodes whose `kind()` equals the keyword itself.
        if let Some(ty) = scalar_kind_to_type(node.kind()) {
            return Ok(ty);
        }
        match node.kind() {
            "boolean" => Ok(Type::Boolean),
            "unit" => Ok(Type::Unit),
            "never" => Ok(Type::Never),
            "identifier" => Ok(Type::Custom(self.get_text(node).to_string())),
            "type" => {
                let first_child = node.child(0).ok_or("Type node has no children")?;
                if let Some(ty) = scalar_kind_to_type(first_child.kind()) {
                    return Ok(ty);
                }
                let kind = first_child.kind();
                if kind == "boolean"
                    || kind == "unit"
                    || kind == "never"
                    || kind == "identifier"
                {
                    return self.map_type(first_child);
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
                    let inner = node
                        .child(1)
                        .ok_or_else(|| format!("Missing inner type for {}", text))?;
                    return Ok(Type::Ref(kind, Box::new(self.map_type(inner)?)));
                }

                if text == "*" {
                    // Raw pointer type `*T`. Distinct from the deref
                    // place operator `*p` — types occupy a different
                    // grammar position.
                    let inner = node
                        .child(1)
                        .ok_or("Missing inner type for raw pointer")?;
                    return Ok(Type::RawPtr(Box::new(self.map_type(inner)?)));
                }

                if text == "[" {
                    // Fixed-size array `[T; N]`.
                    let elem_node = node
                        .child_by_field_name("element")
                        .ok_or("Array type missing element")?;
                    let len_node = node
                        .child_by_field_name("length")
                        .ok_or("Array type missing length")?;
                    let elem = self.map_type(elem_node)?;
                    let ConstVal::Int { bits, .. } =
                        parse_int_literal(self.get_text(len_node))?
                    else {
                        return Err(format!(
                            "Array length must be an integer literal, got {}",
                            self.get_text(len_node)
                        ));
                    };
                    return Ok(Type::Array(Box::new(elem), bits));
                }

                match text {
                    "fn" => {
                        let mut params = Vec::new();
                        let mut cursor = node.walk();
                        for child in node.children(&mut cursor) {
                            if child.kind() == "type" {
                                params.push(self.map_type(child)?);
                            }
                        }
                        Ok(Type::Fn(params))
                    }
                    _ => Err(format!("Unexpected token in type: {}", text)),
                }
            }
            _ => Err(format!("Unexpected node kind in type: {}", node.kind())),
        }
    }

    fn map_place(&self, node: Node) -> Result<Place, String> {
        match node.kind() {
            "identifier" => Ok(Place::Var(self.get_text(node).to_string())),
            "place" => {
                let first_child = node.child(0).ok_or("Place node has no children")?;
                if first_child.kind() == "identifier" && node.child_count() == 1 {
                    return Ok(Place::Var(self.get_text(first_child).to_string()));
                }

                if self.get_text(first_child) == "*" {
                    let inner = node.child(1).ok_or("Deref missing inner place")?;
                    return Ok(Place::Deref(Box::new(self.map_place(inner)?)));
                }

                // Parenthesized place: `(<place>)` — transparently unwraps.
                if self.get_text(first_child) == "(" {
                    let inner = node.child(1).ok_or("Paren-place missing inner")?;
                    return self.map_place(inner);
                }

                let inner_place = self.map_place(first_child)?;
                if let Some(variant_node) = node.child_by_field_name("variant") {
                    let variant = self.get_text(variant_node).to_string();
                    Ok(Place::Downcast(Box::new(inner_place), variant))
                } else if let Some(field_node) = node.child_by_field_name("field") {
                    let field_name = self.get_text(field_node).to_string();
                    Ok(Place::Field(Box::new(inner_place), field_name))
                } else if let Some(index_node) = node.child_by_field_name("index") {
                    let index = self.map_operand(index_node)?;
                    Ok(Place::Index(Box::new(inner_place), Box::new(index)))
                } else {
                    Err(format!(
                        "Unrecognized place suffix: {}",
                        self.get_text(node)
                    ))
                }
            }
            _ => Err(format!("Unexpected node kind in place: {}", node.kind())),
        }
    }

    fn map_operand(&self, node: Node) -> Result<Operand, String> {
        if node.kind() == "operand" {
            let first_child = node.child(0).ok_or("Operand missing children")?;
            let text = self.get_text(first_child);
            match text {
                "copy" => {
                    let place_node = node.child(1).ok_or("Copy missing place")?;
                    Ok(Operand::Copy(self.map_place(place_node)?))
                }
                "move" => {
                    let place_node = node.child(1).ok_or("Move missing place")?;
                    Ok(Operand::Move(self.map_place(place_node)?))
                }
                _ => Ok(Operand::Const(self.map_const(first_child)?)),
            }
        } else {
            Err(format!("Expected operand, found: {}", node.kind()))
        }
    }

    fn map_const(&self, node: Node) -> Result<ConstVal, String> {
        match node.kind() {
            "int_lit" => parse_int_literal(self.get_text(node)),
            "float_lit" => parse_float_literal(self.get_text(node)),
            "byte_str_lit" => parse_byte_str_literal(self.get_text(node)),
            "byte_char_lit" => parse_byte_char_literal(self.get_text(node)),
            "const" => {
                let child = node.child(0).ok_or("Const node is empty")?;
                self.map_const(child)
            }
            _ => {
                let text = self.get_text(node);
                match text {
                    "true" => Ok(ConstVal::Boolean(true)),
                    "false" => Ok(ConstVal::Boolean(false)),
                    "unit" => Ok(ConstVal::Unit),
                    _ => Ok(ConstVal::FnName(text.to_string())),
                }
            }
        }
    }

    fn map_rvalue(&self, node: Node) -> Result<RValue, String> {
        let child = node.child(0).ok_or("RValue node is empty")?;
        match child.kind() {
            "operand" => Ok(RValue::Use(self.map_operand(child)?)),
            _ => {
                let text = self.get_text(child);
                match text {
                    "&" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Shared, self.map_place(place_node)?))
                    }
                    "&mut" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Mut, self.map_place(place_node)?))
                    }
                    "&out" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Out, self.map_place(place_node)?))
                    }
                    "&drop" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Drop, self.map_place(place_node)?))
                    }
                    "&uninit" => {
                        let place_node = node.child(1).ok_or("Ref missing place")?;
                        Ok(RValue::Ref(RefKind::Uninit, self.map_place(place_node)?))
                    }
                    "&raw" => {
                        let place_node = node.child(1).ok_or("&raw missing place")?;
                        Ok(RValue::RawRef(self.map_place(place_node)?))
                    }
                    "[" => {
                        // Array literal: [op0, op1, ..., opN-1].
                        let mut cursor = node.walk();
                        let ops: Result<Vec<Operand>, String> = node
                            .children(&mut cursor)
                            .filter(|c| c.kind() == "operand")
                            .map(|c| self.map_operand(c))
                            .collect();
                        Ok(RValue::ArrayLit(ops?))
                    }
                    _ => {
                        let enum_name_node = node
                            .child_by_field_name("enum_name")
                            .ok_or("Enum construction missing enum name")?;
                        let enum_name = self.get_text(enum_name_node).to_string();
                        let variant_name_node = node
                            .child_by_field_name("variant_name")
                            .ok_or("Enum construction missing variant name")?;
                        let variant_name = self.get_text(variant_name_node).to_string();
                        let mut cursor = node.walk();
                        let operand_node = node
                            .children(&mut cursor)
                            .find(|c| c.kind() == "operand")
                            .ok_or("Enum construction missing operand")?;
                        let operand = self.map_operand(operand_node)?;
                        Ok(RValue::EnumConstr(enum_name, variant_name, operand))
                    }
                }
            }
        }
    }

    fn map_statement(&self, node: Node) -> Result<Statement, String> {
        let child = node.child(0).ok_or("Statement empty")?;
        match child.kind() {
            "assignment" => {
                let lhs_node = child
                    .child_by_field_name("lhs")
                    .ok_or("Assignment missing LHS")?;
                let lhs = self.map_place(lhs_node)?;
                let rhs_node = child
                    .child_by_field_name("rhs")
                    .ok_or("Assignment missing RHS")?;
                let rhs = self.map_rvalue(rhs_node)?;
                Ok(Statement::Assign(lhs, rhs))
            }
            "call" => {
                let func_node = child
                    .child_by_field_name("function")
                    .ok_or("Call missing function")?;
                let func = self.map_operand(func_node)?;

                let mut args = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "operand" && item != func_node {
                        args.push(self.map_operand(item)?);
                    }
                }
                Ok(Statement::Call(func, args))
            }
            "drop_stmt" => {
                let place_node = child
                    .child_by_field_name("place")
                    .ok_or("Drop missing place")?;
                Ok(Statement::Drop(self.map_place(place_node)?))
            }
            "unborrow_stmt" => {
                let place_node = child
                    .child_by_field_name("place")
                    .ok_or("Unborrow missing place")?;
                Ok(Statement::Unborrow(self.map_place(place_node)?))
            }
            _ => Err(format!("Unknown statement kind: {}", child.kind())),
        }
    }

    fn map_terminator(&self, node: Node) -> Result<Terminator, String> {
        let child = node.child(0).ok_or("Terminator empty")?;
        match child.kind() {
            "goto" => {
                let label_node = child
                    .child_by_field_name("label")
                    .ok_or("Goto missing label")?;
                Ok(Terminator::Goto(self.get_text(label_node).to_string()))
            }
            "return" => Ok(Terminator::Return),
            "branch" => {
                let cond_node = child
                    .child_by_field_name("condition")
                    .ok_or("Branch missing condition")?;
                let cond = self.map_operand(cond_node)?;
                let true_node = child
                    .child_by_field_name("true_label")
                    .ok_or("Branch missing true_label")?;
                let true_label = self.get_text(true_node).to_string();
                let false_node = child
                    .child_by_field_name("false_label")
                    .ok_or("Branch missing false_label")?;
                let false_label = self.get_text(false_node).to_string();
                Ok(Terminator::Branch {
                    cond,
                    true_label,
                    false_label,
                })
            }
            "switchEnum" => {
                let place_node = child
                    .child_by_field_name("place")
                    .ok_or("SwitchEnum missing place")?;
                let place = self.map_place(place_node)?;

                let mut cases = Vec::new();
                let mut cursor = child.walk();
                for item in child.children(&mut cursor) {
                    if item.kind() == "switch_case" {
                        let variant_node = item
                            .child_by_field_name("variant")
                            .ok_or("Switch case missing variant")?;
                        let variant = self.get_text(variant_node).to_string();
                        let label_node = item
                            .child_by_field_name("label")
                            .ok_or("Switch case missing label")?;
                        let label = self.get_text(label_node).to_string();
                        cases.push((variant, label));
                    }
                }
                Ok(Terminator::SwitchEnum { place, cases })
            }
            "abort" => Ok(Terminator::Abort),
            "unreachable" => Ok(Terminator::Unreachable),
            _ => Err(format!("Unknown terminator kind: {}", child.kind())),
        }
    }

    fn map_basic_block(&self, node: Node) -> Result<BasicBlock, String> {
        let label_node = node
            .child_by_field_name("label")
            .ok_or("Basic block missing label")?;
        let label = self.get_text(label_node).to_string();
        let label_span = span_of(label_node);

        let mut statements = Vec::new();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() == "statement" {
                let span = span_of(child);
                statements.push((self.map_statement(child)?, span));
            }
        }

        let term_node = node
            .children(&mut cursor)
            .find(|c| c.kind() == "terminator")
            .ok_or("Basic block missing terminator")?;
        let terminator_span = span_of(term_node);
        let terminator = self.map_terminator(term_node)?;

        Ok(BasicBlock {
            label,
            label_span,
            statements,
            terminator,
            terminator_span,
        })
    }

    /// Parse a `markers` node (one or more `Copy`/`Drop`/`Move` in any
    /// order). Errors on duplicates.
    fn map_markers(&self, node: Node) -> Result<Markers, String> {
        let mut copy = false;
        let mut drop = false;
        let mut mov = false;
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.kind() != "marker" {
                continue;
            }
            let text = self.get_text(child);
            let flag = match text {
                "Copy" => &mut copy,
                "Drop" => &mut drop,
                "Move" => &mut mov,
                other => return Err(format!("Unknown marker: {}", other)),
            };
            if *flag {
                return Err(format!(
                    "Duplicate marker '{}' at {}",
                    text,
                    span_of(child)
                ));
            }
            *flag = true;
        }
        Ok(Markers { copy, drop, mov })
    }

    fn map_struct_decl(&self, node: Node) -> Result<StructDecl, String> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or("Struct decl missing name")?;
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);

        let mut cursor = node.walk();
        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            self.map_markers(markers_node)?
        } else {
            Markers { copy: false, drop: false, mov: false }
        };

        let mut fields = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "struct_field" {
                let f_name_node = child
                    .child_by_field_name("name")
                    .ok_or("Struct field missing name")?;
                let f_name = self.get_text(f_name_node).to_string();
                let f_type_node = child
                    .child_by_field_name("type")
                    .ok_or("Struct field missing type")?;
                let f_type = self.map_type(f_type_node)?;
                fields.push(StructField {
                    name: f_name,
                    ty: f_type,
                    span: span_of(child),
                });
            }
        }

        Ok(StructDecl {
            name,
            name_span,
            markers,
            fields,
        })
    }

    fn map_enum_decl(&self, node: Node) -> Result<EnumDecl, String> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or("Enum decl missing name")?;
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);

        let mut cursor = node.walk();
        let markers = if let Some(markers_node) =
            node.children(&mut cursor).find(|c| c.kind() == "markers")
        {
            self.map_markers(markers_node)?
        } else {
            Markers { copy: false, drop: false, mov: false }
        };

        let mut variants = Vec::new();
        for child in node.children(&mut cursor) {
            if child.kind() == "enum_variant" {
                let v_name_node = child
                    .child_by_field_name("name")
                    .ok_or("Enum variant missing name")?;
                let v_name = self.get_text(v_name_node).to_string();
                let v_type_node = child
                    .child_by_field_name("type")
                    .ok_or("Enum variant missing type")?;
                let v_type = self.map_type(v_type_node)?;
                variants.push(EnumVariant {
                    name: v_name,
                    ty: v_type,
                    span: span_of(child),
                });
            }
        }

        Ok(EnumDecl {
            name,
            name_span,
            markers,
            variants,
        })
    }

    fn map_function_decl(&self, node: Node) -> Result<Function, String> {
        let name_node = node
            .child_by_field_name("name")
            .ok_or("Function missing name")?;
        let name = self.get_text(name_node).to_string();
        let name_span = span_of(name_node);
        let is_extern = self.get_text(node).starts_with("extern");

        let mut params = Vec::new();
        let mut locals = Vec::new();
        let mut blocks = Vec::new();
        let mut has_body = false;

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            match child.kind() {
                "param_decl" => {
                    let p_name_node = child
                        .child_by_field_name("name")
                        .ok_or("Param missing name")?;
                    let p_name = self.get_text(p_name_node).to_string();
                    let p_type_node = child
                        .child_by_field_name("type")
                        .ok_or("Param missing type")?;
                    let p_type = self.map_type(p_type_node)?;
                    params.push(Param {
                        name: p_name,
                        ty: p_type,
                        span: span_of(child),
                    });
                }
                "local_decl" => {
                    has_body = true;
                    let l_name_node = child
                        .child_by_field_name("name")
                        .ok_or("Local missing name")?;
                    let l_name = self.get_text(l_name_node).to_string();
                    let l_type_node = child
                        .child_by_field_name("type")
                        .ok_or("Local missing type")?;
                    let l_type = self.map_type(l_type_node)?;
                    locals.push(Local {
                        name: l_name,
                        ty: l_type,
                        span: span_of(child),
                    });
                }
                "basic_block" => {
                    has_body = true;
                    blocks.push(self.map_basic_block(child)?);
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

        Ok(Function {
            name,
            name_span,
            is_extern,
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
            struct Copy Drop Point {
                x: i64
                y: i64
            }
        ";
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(s) = &program.declarations[0] {
            assert_eq!(s.name, "Point");
            assert!(s.markers.copy);
            assert!(s.markers.drop);
            assert_eq!(s.fields.len(), 2);
            assert_eq!(s.fields[0].name, "x");
            assert_eq!(s.fields[0].ty, Type::Int(IntTy::I64));
            assert_eq!(s.fields[1].name, "y");
            assert_eq!(s.fields[1].ty, Type::Int(IntTy::I64));
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
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(e) = &program.declarations[0] {
            assert_eq!(e.name, "Option");
            assert!(!e.markers.copy);
            assert!(!e.markers.drop);
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].name, "None");
            assert_eq!(e.variants[0].ty, Type::Custom("Option".to_string()));
            assert_eq!(e.variants[1].name, "Some");
            assert_eq!(e.variants[1].ty, Type::Int(IntTy::I64));
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
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.name, "add");
            assert!(!f.is_extern);
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.params[0].name, "a");
            assert_eq!(f.params[0].ty, Type::Int(IntTy::I64));

            let body = f.body.as_ref().unwrap();
            assert_eq!(body.locals.len(), 1);
            assert_eq!(body.locals[0].name, "ret");
            assert_eq!(body.blocks.len(), 1);
            let block = &body.blocks[0];
            assert_eq!(block.label, "entry");
            assert_eq!(block.statements.len(), 3);
            assert_eq!(block.terminator, Terminator::Return);
        } else {
            panic!("Expected function declaration");
        }
    }

    #[test]
    fn test_parse_extern_fn() {
        let source = "
            extern fn add_impl(a: i64, b: i64);
        ";
        let parser = Parser::new(source.to_string());
        let program = parser.parse().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(f) = &program.declarations[0] {
            assert_eq!(f.name, "add_impl");
            assert!(f.is_extern);
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.params[0].name, "a");
            assert_eq!(f.params[0].ty, Type::Int(IntTy::I64));
            assert!(f.body.is_none());
        } else {
            panic!("Expected extern function declaration");
        }
    }

    // ---------- Scalar type parsing ----------

    fn ty_of_param(src: &str, idx: usize) -> Type {
        let program = Parser::new(src.to_string()).parse().unwrap();
        match &program.declarations[0] {
            Declaration::Fn(f) => f.params[idx].ty.clone(),
            _ => panic!("expected fn decl"),
        }
    }

    #[test]
    fn parse_all_int_type_keywords() {
        let src = "extern fn f(a: i8, b: i16, c: i32, d: i64, e: u8, g: u16, h: u32, i: u64);";
        assert_eq!(ty_of_param(src, 0), Type::Int(IntTy::I8));
        assert_eq!(ty_of_param(src, 1), Type::Int(IntTy::I16));
        assert_eq!(ty_of_param(src, 2), Type::Int(IntTy::I32));
        assert_eq!(ty_of_param(src, 3), Type::Int(IntTy::I64));
        assert_eq!(ty_of_param(src, 4), Type::Int(IntTy::U8));
        assert_eq!(ty_of_param(src, 5), Type::Int(IntTy::U16));
        assert_eq!(ty_of_param(src, 6), Type::Int(IntTy::U32));
        assert_eq!(ty_of_param(src, 7), Type::Int(IntTy::U64));
    }

    #[test]
    fn parse_float_type_keywords() {
        let src = "extern fn f(a: f32, b: f64);";
        assert_eq!(ty_of_param(src, 0), Type::Float(FloatTy::F32));
        assert_eq!(ty_of_param(src, 1), Type::Float(FloatTy::F64));
    }

    // ---------- Integer literal parsing ----------

    /// Parse a fn body with `x = <literal>` and return the ConstVal.
    fn const_of_first_assign(src: &str) -> ConstVal {
        let program = Parser::new(src.to_string()).parse().unwrap();
        let Declaration::Fn(f) = &program.declarations[0] else {
            panic!("expected fn");
        };
        let body = f.body.as_ref().unwrap();
        let (stmt, _) = &body.blocks[0].statements[0];
        let Statement::Assign(_, RValue::Use(Operand::Const(c))) = stmt else {
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
        let src = "struct Copy Copy P { x: i64 }";
        let err = Parser::new(src.to_string())
            .parse()
            .expect_err("expected duplicate-marker error");
        assert!(
            err.contains("Duplicate marker"),
            "expected 'Duplicate marker' in error, got: {}",
            err
        );
    }

    #[test]
    fn marker_order_is_commutative() {
        // Any permutation of {Copy, Drop, Move} yields the same set
        // of flags — canonicalization is not by textual order.
        fn markers_of(src: &str) -> Markers {
            let program = Parser::new(src.to_string()).parse().unwrap();
            let Declaration::Struct(s) = &program.declarations[0] else {
                panic!("expected struct");
            };
            s.markers
        }
        let a = markers_of("struct Copy Drop Move P { x: i64 }");
        let b = markers_of("struct Move Drop Copy P { x: i64 }");
        let c = markers_of("struct Drop Copy Move P { x: i64 }");
        assert_eq!(a, b);
        assert_eq!(b, c);
        assert!(a.copy && a.drop && a.mov);
    }
}
