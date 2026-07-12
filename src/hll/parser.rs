use crate::mir::ast::{IntTy, FloatTy, RefKind, Span};
use crate::hll::ast::*;

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Ident(String),
    IntLit(i64, Option<IntTy>),
    FloatLit(f64, Option<FloatTy>),
    // Keywords
    Struct,
    Enum,
    Fn,
    Let,
    Mut,
    If,
    Else,
    Loop,
    Break,
    Continue,
    Return,
    As,
    Match,
    // Types
    Bool,
    Unit,
    Never,
    FatArrow, // =>
    // Operators
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Semicolon,
    Dot,
    Arrow,
    Eq,
    Star,
    Amp,
    AmpRaw,
    PathSep, // ::
    LBracket,
    RBracket,
    // Special
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    line: u32,
    col: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn step(&mut self) {
        if let Some(c) = self.current_char() {
            self.pos += c.len_utf8();
            if c == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
    }

    fn span(&self) -> Span {
        Span {
            line: self.line,
            col: self.col,
        }
    }

    pub fn next_token(&mut self) -> Result<Token, String> {
        while let Some(c) = self.current_char() {
            if c.is_whitespace() {
                self.step();
                continue;
            }
            if c == '/' {
                // Line comment
                if self.input[self.pos + 1..].starts_with('/') {
                    while let Some(curr) = self.current_char() {
                        self.step();
                        if curr == '\n' {
                            break;
                        }
                    }
                    continue;
                }
            }
            break;
        }

        let span = self.span();
        let Some(c) = self.current_char() else {
            return Ok(Token {
                kind: TokenKind::Eof,
                span,
            });
        };

        // Identifiers or Keywords
        if c.is_ascii_alphabetic() || c == '_' || c == '$' {
            let start = self.pos;
            while let Some(curr) = self.current_char() {
                if curr.is_ascii_alphanumeric() || curr == '_' || curr == '$' {
                    self.step();
                } else {
                    break;
                }
            }
            let text = &self.input[start..self.pos];
            let kind = match text {
                "struct" => TokenKind::Struct,
                "enum" => TokenKind::Enum,
                "fn" => TokenKind::Fn,
                "let" => TokenKind::Let,
                "mut" => TokenKind::Mut,
                "if" => TokenKind::If,
                "else" => TokenKind::Else,
                "loop" => TokenKind::Loop,
                "break" => TokenKind::Break,
                "continue" => TokenKind::Continue,
                "return" => TokenKind::Return,
                "as" => TokenKind::As,
                "match" => TokenKind::Match,
                "bool" => TokenKind::Bool,
                "unit" => TokenKind::Unit,
                "never" => TokenKind::Never,
                _ => TokenKind::Ident(text.to_string()),
            };
            return Ok(Token { kind, span });
        }

        // Numeric Literals
        if c.is_ascii_digit() {
            let start = self.pos;
            let mut is_float = false;
            while let Some(curr) = self.current_char() {
                if curr.is_ascii_digit() || curr == '_' {
                    self.step();
                } else if curr == '.' {
                    // Check if next char is digit (to avoid field access matching)
                    let next = self.input[self.pos + 1..].chars().next();
                    if next.map(|ch| ch.is_ascii_digit()).unwrap_or(false) {
                        is_float = true;
                        self.step();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            let num_str = &self.input[start..self.pos];
            let num_clean = num_str.replace('_', "");

            // Look for optional suffix
            let suffix_start = self.pos;
            while let Some(curr) = self.current_char() {
                if curr.is_ascii_alphanumeric() || curr == '_' {
                    self.step();
                } else {
                    break;
                }
            }
            let suffix_str = &self.input[suffix_start..self.pos];

            if is_float {
                let val: f64 = num_clean.parse().map_err(|e| format!("invalid float literal: {}", e))?;
                let suffix = match suffix_str {
                    "" => None,
                    "f32" => Some(FloatTy::F32),
                    "f64" => Some(FloatTy::F64),
                    other => return Err(format!("invalid float suffix: {}", other)),
                };
                return Ok(Token {
                    kind: TokenKind::FloatLit(val, suffix),
                    span,
                });
            } else {
                let val: i64 = num_clean.parse().map_err(|e| format!("invalid integer literal: {}", e))?;
                let suffix = match suffix_str {
                    "" => None,
                    "i8" => Some(IntTy::I8),
                    "i16" => Some(IntTy::I16),
                    "i32" => Some(IntTy::I32),
                    "i64" => Some(IntTy::I64),
                    "u8" => Some(IntTy::U8),
                    "u16" => Some(IntTy::U16),
                    "u32" => Some(IntTy::U32),
                    "u64" => Some(IntTy::U64),
                    other => return Err(format!("invalid integer suffix: {}", other)),
                };
                return Ok(Token {
                    kind: TokenKind::IntLit(val, suffix),
                    span,
                });
            }
        }

        // Parentheses / Braces / Punctuation
        let kind = match c {
            '(' => {
                self.step();
                TokenKind::LParen
            }
            ')' => {
                self.step();
                TokenKind::RParen
            }
            '{' => {
                self.step();
                TokenKind::LBrace
            }
            '}' => {
                self.step();
                TokenKind::RBrace
            }
            '[' => {
                self.step();
                TokenKind::LBracket
            }
            ']' => {
                self.step();
                TokenKind::RBracket
            }
            ',' => {
                self.step();
                TokenKind::Comma
            }
            ':' => {
                self.step();
                if self.current_char() == Some(':') {
                    self.step();
                    TokenKind::PathSep
                } else {
                    TokenKind::Colon
                }
            }
            ';' => {
                self.step();
                TokenKind::Semicolon
            }
            '.' => {
                self.step();
                TokenKind::Dot
            }
            '*' => {
                self.step();
                TokenKind::Star
            }
            '=' => {
                self.step();
                if self.current_char() == Some('>') {
                    self.step();
                    TokenKind::FatArrow
                } else {
                    TokenKind::Eq
                }
            }
            '-' => {
                self.step();
                if self.current_char() == Some('>') {
                    self.step();
                    TokenKind::Arrow
                } else {
                    return Err(format!("unexpected character: {}", c));
                }
            }
            '&' => {
                self.step();
                if self.input[self.pos..].starts_with("raw") {
                    let next = self.input[self.pos + 3..].chars().next();
                    if next.is_none() || !next.unwrap().is_ascii_alphanumeric() {
                        for _ in 0..3 {
                            self.step();
                        }
                        TokenKind::AmpRaw
                    } else {
                        TokenKind::Amp
                    }
                } else {
                    TokenKind::Amp
                }
            }
            _ => return Err(format!("unexpected character: {}", c)),
        };

        Ok(Token { kind, span })
    }
}

pub struct Parser<'a> {
    tokens: Vec<Token>,
    index: usize,
    _source: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Result<Self, String> {
        let mut lexer = Lexer::new(source);
        let mut tokens = Vec::new();
        loop {
            let t = lexer.next_token()?;
            let is_eof = t.kind == TokenKind::Eof;
            tokens.push(t);
            if is_eof {
                break;
            }
        }
        Ok(Self {
            tokens,
            index: 0,
            _source: source,
        })
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.index]
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.index].clone();
        if tok.kind != TokenKind::Eof {
            self.index += 1;
        }
        tok
    }

    fn expect(&mut self, kind: TokenKind) -> Result<Token, String> {
        let tok = self.peek().clone();
        if tok.kind == kind {
            Ok(self.advance())
        } else {
            Err(format!(
                "at {}: expected {:?}, found {:?}",
                tok.span, kind, tok.kind
            ))
        }
    }

    fn parse_identifier(&mut self) -> Result<(String, Span), String> {
        let tok = self.peek();
        if let TokenKind::Ident(ref name) = tok.kind {
            let name_str = name.clone();
            let span = tok.span;
            self.advance();
            Ok((name_str, span))
        } else {
            Err(format!("at {}: expected identifier, found {:?}", tok.span, tok.kind))
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, String> {
        let mut declarations = Vec::new();
        while self.peek().kind != TokenKind::Eof {
            declarations.push(self.parse_declaration()?);
        }
        Ok(Program { declarations })
    }

    fn parse_declaration(&mut self) -> Result<Declaration, String> {
        let tok = self.peek();
        match tok.kind {
            TokenKind::Struct => Ok(Declaration::Struct(self.parse_struct_decl()?)),
            TokenKind::Enum => Ok(Declaration::Enum(self.parse_enum_decl()?)),
            TokenKind::Fn => Ok(Declaration::Fn(self.parse_fn_decl()?)),
            _ => Err(format!(
                "at {}: expected 'struct', 'enum', or 'fn', found {:?}",
                tok.span, tok.kind
            )),
        }
    }

    fn parse_struct_decl(&mut self) -> Result<StructDecl, String> {
        let start = self.expect(TokenKind::Struct)?.span;
        let (name, _) = self.parse_identifier()?;
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while self.peek().kind != TokenKind::RBrace && self.peek().kind != TokenKind::Eof {
            let (f_name, f_span) = self.parse_identifier()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type()?;
            fields.push(StructField {
                name: f_name,
                ty,
                span: f_span,
            });
            if self.peek().kind == TokenKind::Comma {
                self.advance();
            } else if self.peek().kind != TokenKind::RBrace {
                return Err(format!("at {}: expected ',' or '}}'", self.peek().span));
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(StructDecl {
            name,
            fields,
            span: start,
        })
    }

    fn parse_enum_decl(&mut self) -> Result<EnumDecl, String> {
        let start = self.expect(TokenKind::Enum)?.span;
        let (name, _) = self.parse_identifier()?;
        self.expect(TokenKind::LBrace)?;
        let mut variants = Vec::new();
        while self.peek().kind != TokenKind::RBrace && self.peek().kind != TokenKind::Eof {
            let (v_name, v_span) = self.parse_identifier()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type()?;
            variants.push(EnumVariant {
                name: v_name,
                ty,
                span: v_span,
            });
            if self.peek().kind == TokenKind::Comma {
                self.advance();
            } else if self.peek().kind != TokenKind::RBrace {
                return Err(format!("at {}: expected ',' or '}}'", self.peek().span));
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(EnumDecl {
            name,
            variants,
            span: start,
        })
    }

    fn parse_fn_decl(&mut self) -> Result<FnDecl, String> {
        let start = self.expect(TokenKind::Fn)?.span;
        let (name, _) = self.parse_identifier()?;
        self.expect(TokenKind::LParen)?;
        let mut params = Vec::new();
        while self.peek().kind != TokenKind::RParen && self.peek().kind != TokenKind::Eof {
            let (p_name, p_span) = self.parse_identifier()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type()?;
            params.push(Param {
                name: p_name,
                ty,
                span: p_span,
            });
            if self.peek().kind == TokenKind::Comma {
                self.advance();
            } else if self.peek().kind != TokenKind::RParen {
                return Err(format!("at {}: expected ',' or ')'", self.peek().span));
            }
        }
        self.expect(TokenKind::RParen)?;
        let ret_ty = if self.peek().kind == TokenKind::Arrow {
            self.advance();
            self.parse_type()?
        } else {
            Type::Unit
        };
        let body = self.parse_expr()?;
        Ok(FnDecl {
            name,
            params,
            ret_ty,
            body,
            span: start,
        })
    }

    fn parse_type(&mut self) -> Result<Type, String> {
        let tok = self.peek();
        match tok.kind {
            TokenKind::Bool => {
                self.advance();
                Ok(Type::Bool)
            }
            TokenKind::Unit => {
                self.advance();
                Ok(Type::Unit)
            }
            TokenKind::Never => {
                self.advance();
                Ok(Type::Never)
            }
            TokenKind::Ident(ref name) => {
                // Scalar shorthand types
                let ty = match name.as_str() {
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
                    other => Type::Custom(other.to_string()),
                };
                self.advance();
                Ok(ty)
            }
            TokenKind::Star => {
                self.advance();
                let inner = self.parse_type()?;
                Ok(Type::RawPtr(Box::new(inner)))
            }
            TokenKind::Amp => {
                self.advance();
                let kind = if self.peek().kind == TokenKind::Mut {
                    self.advance();
                    RefKind::Mut
                } else if self.peek().kind == TokenKind::Ident("out".to_string()) {
                    self.advance();
                    RefKind::Out
                } else if self.peek().kind == TokenKind::Ident("deinit".to_string()) {
                    self.advance();
                    RefKind::Drop
                } else if self.peek().kind == TokenKind::Ident("uninit".to_string()) {
                    self.advance();
                    RefKind::Uninit
                } else {
                    RefKind::Shared
                };
                let inner = self.parse_type()?;
                Ok(Type::Ref(kind, Box::new(inner)))
            }
            TokenKind::LBracket => {
                self.advance();
                let inner = self.parse_type()?;
                self.expect(TokenKind::Semicolon)?;
                let tok_size = self.advance();
                let size = if let TokenKind::IntLit(val, _) = tok_size.kind {
                    val as usize
                } else {
                    return Err(format!("at {}: expected integer literal for array size", tok_size.span));
                };
                self.expect(TokenKind::RBracket)?;
                Ok(Type::Array(Box::new(inner), size))
            }
            _ => Err(format!("at {}: expected type, found {:?}", tok.span, tok.kind)),
        }
    }

    fn parse_stmt(&mut self) -> Result<Stmt, String> {
        let tok = self.peek();
        if tok.kind == TokenKind::Let {
            let start = self.advance().span;
            let is_mut = if self.peek().kind == TokenKind::Mut {
                self.advance();
                true
            } else {
                false
            };
            let (name, _) = self.parse_identifier()?;
            let ty = if self.peek().kind == TokenKind::Colon {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };
            self.expect(TokenKind::Eq)?;
            let init = self.parse_expr()?;
            self.expect(TokenKind::Semicolon)?;
            Ok(Stmt::Let {
                is_mut,
                name,
                ty,
                init,
                span: start,
            })
        } else {
            let expr = self.parse_expr()?;
            // If the next token is a semicolon, we consume it and return Stmt::Expr.
            // Wait, does block parsing rely on this?
            // In a block `{ stmt1; stmt2; expr }`, stmt1 and stmt2 are statements (terminated by `;`).
            // So we parse them as Stmt, expecting a semicolon.
            self.expect(TokenKind::Semicolon)?;
            Ok(Stmt::Expr(expr))
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_expr_assignment()
    }

    fn parse_expr_assignment(&mut self) -> Result<Expr, String> {
        let mut lhs = self.parse_expr_lowest()?;
        if self.peek().kind == TokenKind::Eq {
            self.advance();
            let rhs = self.parse_expr_assignment()?;
            let span = lhs.span;
            lhs = Expr {
                kind: ExprKind::Assign(Box::new(lhs), Box::new(rhs)),
                span,
            };
        }
        Ok(lhs)
    }

    fn parse_expr_lowest(&mut self) -> Result<Expr, String> {
        // Break/Continue/Return / Loop / If / Block / Let are parsed as expressions or statements.
        // Wait, loop/if/block can be primary.
        // Precedence: prefix operators (deref, borrow, raw borrow) -> postfix (call, field access, downcast).
        self.parse_expr_prefix()
    }

    fn parse_expr_prefix(&mut self) -> Result<Expr, String> {
        let tok = self.peek();
        match tok.kind {
            TokenKind::Star => {
                let start = self.advance().span;
                let inner = self.parse_expr_prefix()?;
                Ok(Expr {
                    kind: ExprKind::Deref(Box::new(inner)),
                    span: start,
                })
            }
            TokenKind::Amp => {
                let start = self.advance().span;
                let kind = if self.peek().kind == TokenKind::Mut {
                    self.advance();
                    RefKind::Mut
                } else if self.peek().kind == TokenKind::Ident("out".to_string()) {
                    self.advance();
                    RefKind::Out
                } else if self.peek().kind == TokenKind::Ident("deinit".to_string()) {
                    self.advance();
                    RefKind::Drop
                } else if self.peek().kind == TokenKind::Ident("uninit".to_string()) {
                    self.advance();
                    RefKind::Uninit
                } else {
                    RefKind::Shared
                };
                let inner = self.parse_expr_prefix()?;
                Ok(Expr {
                    kind: ExprKind::Borrow(kind, Box::new(inner)),
                    span: start,
                })
            }
            TokenKind::AmpRaw => {
                let start = self.advance().span;
                let inner = self.parse_expr_prefix()?;
                Ok(Expr {
                    kind: ExprKind::RawBorrow(Box::new(inner)),
                    span: start,
                })
            }
            _ => self.parse_expr_postfix(),
        }
    }

    fn parse_expr_postfix(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_expr_primary()?;
        loop {
            let tok = self.peek();
            match tok.kind {
                TokenKind::Dot => {
                    self.advance();
                    let (field, _) = self.parse_identifier()?;
                    let span = expr.span;
                    expr = Expr {
                        kind: ExprKind::FieldAccess(Box::new(expr), field),
                        span,
                    };
                }
                TokenKind::As => {
                    self.advance();
                    let (variant, _) = self.parse_identifier()?;
                    let span = expr.span;
                    expr = Expr {
                        kind: ExprKind::Downcast(Box::new(expr), variant),
                        span,
                    };
                }
                TokenKind::LParen => {
                    self.advance();
                    let mut args = Vec::new();
                    while self.peek().kind != TokenKind::RParen && self.peek().kind != TokenKind::Eof {
                        args.push(self.parse_expr()?);
                        if self.peek().kind == TokenKind::Comma {
                            self.advance();
                        } else if self.peek().kind != TokenKind::RParen {
                            return Err(format!("at {}: expected ',' or ')'", self.peek().span));
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = expr.span;
                    expr = Expr {
                        kind: ExprKind::Call(Box::new(expr), args),
                        span,
                    };
                }
                TokenKind::Match => {
                    self.advance();
                    self.expect(TokenKind::LBrace)?;
                    let mut arms = Vec::new();
                    while self.peek().kind != TokenKind::RBrace && self.peek().kind != TokenKind::Eof {
                        let (variant, _) = self.parse_identifier()?;
                        let bound_var = if self.peek().kind == TokenKind::LParen {
                            self.advance();
                            let (bound, _) = self.parse_identifier()?;
                            self.expect(TokenKind::RParen)?;
                            Some(bound)
                        } else {
                            None
                        };
                        let pattern = Pattern::Variant(variant, bound_var);
                        self.expect(TokenKind::FatArrow)?;
                        let body = self.parse_expr()?;
                        arms.push((pattern, body));
                        if self.peek().kind == TokenKind::Comma {
                            self.advance();
                        } else if self.peek().kind != TokenKind::RBrace {
                            return Err(format!("at {}: expected ',' or '}}'", self.peek().span));
                        }
                    }
                    self.expect(TokenKind::RBrace)?;
                    let span = expr.span;
                    expr = Expr {
                        kind: ExprKind::Match(Box::new(expr), arms),
                        span,
                    };
                }
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr()?;
                    self.expect(TokenKind::RBracket)?;
                    let span = expr.span;
                    expr = Expr {
                        kind: ExprKind::ArrayIndex(Box::new(expr), Box::new(index)),
                        span,
                    };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_expr_primary(&mut self) -> Result<Expr, String> {
        let tok = self.peek();
        match tok.kind {
            TokenKind::IntLit(val, suffix) => {
                let start = self.advance().span;
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Int(val, suffix)),
                    span: start,
                })
            }
            TokenKind::FloatLit(val, suffix) => {
                let start = self.advance().span;
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Float(val, suffix)),
                    span: start,
                })
            }
            TokenKind::Ident(ref name) => {
                let name_str = name.clone();
                let start = self.advance().span;
                if name_str == "true" {
                    Ok(Expr {
                        kind: ExprKind::Literal(Literal::Bool(true)),
                        span: start,
                    })
                } else if name_str == "false" {
                    Ok(Expr {
                        kind: ExprKind::Literal(Literal::Bool(false)),
                        span: start,
                    })
                } else if self.peek().kind == TokenKind::LBrace
                    && (self.tokens[self.index + 1].kind == TokenKind::RBrace
                        || (matches!(self.tokens[self.index + 1].kind, TokenKind::Ident(_))
                            && self.tokens[self.index + 2].kind == TokenKind::Colon))
                {
                    self.advance();
                    let mut fields = Vec::new();
                    while self.peek().kind != TokenKind::RBrace && self.peek().kind != TokenKind::Eof {
                        let (field_name, _) = self.parse_identifier()?;
                        self.expect(TokenKind::Colon)?;
                        let value = self.parse_expr()?;
                        fields.push((field_name, value));
                        if self.peek().kind == TokenKind::Comma {
                            self.advance();
                        } else if self.peek().kind != TokenKind::RBrace {
                            return Err(format!("at {}: expected ',' or '}}'", self.peek().span));
                        }
                    }
                    self.expect(TokenKind::RBrace)?;
                    Ok(Expr {
                        kind: ExprKind::StructConstr(name_str, fields),
                        span: start,
                    })
                } else if self.peek().kind == TokenKind::PathSep {
                    self.advance();
                    let (variant_name, _) = self.parse_identifier()?;
                    self.expect(TokenKind::LParen)?;
                    let payload = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    Ok(Expr {
                        kind: ExprKind::EnumConstr(name_str, variant_name, Box::new(payload)),
                        span: start,
                    })
                } else {
                    Ok(Expr {
                        kind: ExprKind::Variable(name_str),
                        span: start,
                    })
                }
            }
            TokenKind::LBracket => {
                let start = self.advance().span;
                let mut elements = Vec::new();
                while self.peek().kind != TokenKind::RBracket && self.peek().kind != TokenKind::Eof {
                    let expr = self.parse_expr()?;
                    elements.push(expr);
                    if self.peek().kind == TokenKind::Comma {
                        self.advance();
                    } else if self.peek().kind != TokenKind::RBracket {
                        return Err(format!("at {}: expected ',' or ']'", self.peek().span));
                    }
                }
                self.expect(TokenKind::RBracket)?;
                Ok(Expr {
                    kind: ExprKind::Array(elements),
                    span: start,
                })
            }
            TokenKind::Unit => {
                let start = self.advance().span;
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Unit),
                    span: start,
                })
            }
            TokenKind::LParen => {
                let start = self.advance().span;
                if self.peek().kind == TokenKind::RParen {
                    self.advance();
                    Ok(Expr {
                        kind: ExprKind::Literal(Literal::Unit),
                        span: start,
                    })
                } else {
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::RParen)?;
                    Ok(expr)
                }
            }
            TokenKind::LBrace => {
                let start = self.advance().span;
                let mut stmts = Vec::new();
                let mut last_expr = None;
                while self.peek().kind != TokenKind::RBrace && self.peek().kind != TokenKind::Eof {
                    // Check if this looks like a statement or trailing expression.
                    // If it's a statement, we parse it as Stmt.
                    // Let binding is always a statement.
                    // Expressions followed by `;` are Stmt::Expr.
                    // The last expression might not be followed by `;`.
                    if self.peek().kind == TokenKind::Let {
                        stmts.push(self.parse_stmt()?);
                    } else {
                        // Parse expression.
                        let expr = self.parse_expr()?;
                        if self.peek().kind == TokenKind::Semicolon {
                            self.advance();
                            stmts.push(Stmt::Expr(expr));
                        } else {
                            // This is the trailing expression!
                            last_expr = Some(Box::new(expr));
                            break;
                        }
                    }
                }
                self.expect(TokenKind::RBrace)?;
                Ok(Expr {
                    kind: ExprKind::Block(stmts, last_expr),
                    span: start,
                })
            }
            TokenKind::If => {
                let start = self.advance().span;
                let cond = self.parse_expr()?;
                let true_block = self.parse_block_as_expr()?;
                let false_block = if self.peek().kind == TokenKind::Else {
                    self.advance();
                    self.parse_block_as_expr()?
                } else {
                    Expr {
                        kind: ExprKind::Block(Vec::new(), None),
                        span: start,
                    }
                };
                Ok(Expr {
                    kind: ExprKind::If(Box::new(cond), Box::new(true_block), Box::new(false_block)),
                    span: start,
                })
            }
            TokenKind::Loop => {
                let start = self.advance().span;
                let body = self.parse_block_as_expr()?;
                Ok(Expr {
                    kind: ExprKind::Loop(Box::new(body)),
                    span: start,
                })
            }
            TokenKind::Break => {
                let start = self.advance().span;
                let expr = if self.peek().kind != TokenKind::Semicolon
                    && self.peek().kind != TokenKind::RBrace
                    && self.peek().kind != TokenKind::RParen
                    && self.peek().kind != TokenKind::Comma
                {
                    Some(Box::new(self.parse_expr()?))
                } else {
                    None
                };
                Ok(Expr {
                    kind: ExprKind::Break(expr),
                    span: start,
                })
            }
            TokenKind::Continue => {
                let start = self.advance().span;
                Ok(Expr {
                    kind: ExprKind::Continue,
                    span: start,
                })
            }
            TokenKind::Return => {
                let start = self.advance().span;
                let expr = if self.peek().kind != TokenKind::Semicolon
                    && self.peek().kind != TokenKind::RBrace
                    && self.peek().kind != TokenKind::RParen
                    && self.peek().kind != TokenKind::Comma
                {
                    Some(Box::new(self.parse_expr()?))
                } else {
                    None
                };
                Ok(Expr {
                    kind: ExprKind::Return(expr),
                    span: start,
                })
            }

            _ => Err(format!(
                "at {}: expected expression primary, found {:?}",
                tok.span, tok.kind
            )),
        }
    }

    fn parse_block_as_expr(&mut self) -> Result<Expr, String> {
        let tok = self.peek();
        if tok.kind == TokenKind::LBrace {
            self.parse_expr_primary()
        } else {
            Err(format!("at {}: expected block starting with '{{'", tok.span))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_struct_decl_test() {
        let source = "struct Point { x: i64, y: i64 }";
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Struct(ref s) = program.declarations[0] {
            assert_eq!(s.name, "Point");
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
    fn parse_enum_decl_test() {
        let source = "enum Option { None: unit, Some: i64 }";
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Enum(ref e) = program.declarations[0] {
            assert_eq!(e.name, "Option");
            assert_eq!(e.variants.len(), 2);
            assert_eq!(e.variants[0].name, "None");
            assert_eq!(e.variants[0].ty, Type::Unit);
            assert_eq!(e.variants[1].name, "Some");
            assert_eq!(e.variants[1].ty, Type::Int(IntTy::I64));
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
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(ref f) = program.declarations[0] {
            assert_eq!(f.name, "add");
            assert_eq!(f.params.len(), 2);
            assert_eq!(f.ret_ty, Type::Int(IntTy::I64));
            if let ExprKind::Block(ref stmts, ref last) = f.body.kind {
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
                let a = *ptr;
                let b = &raw a;
                let c = &out a;
                let d = &deinit a;
                let e = &uninit a;
            }
        ";
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
        if let Declaration::Fn(ref f) = program.declarations[0] {
            assert_eq!(f.params[0].ty, Type::RawPtr(Box::new(Type::Int(IntTy::I64))));
            assert_eq!(f.params[1].ty, Type::Ref(RefKind::Mut, Box::new(Type::Int(IntTy::I64))));
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
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
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
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
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
        let mut p = Parser::new(source).unwrap();
        let program = p.parse_program().unwrap();
        assert_eq!(program.declarations.len(), 1);
    }
}
