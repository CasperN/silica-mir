//! Pretty-printer for MIR programs.
//!
//! The output is exact-parse: `Parser::new(pretty_print(program)).parse()`
//! yields a program equivalent to `program` modulo spans. This gives us a
//! textual golden-file style for tests (see `drop_elaboration` tests) and
//! makes elaborated output human-readable.
//!
//! Style choices:
//! - Two-space indent inside function bodies.
//! - One statement per line, terminator on its own line.
//! - Struct/enum bodies are one field/variant per line.
//! - Markers are emitted as `Copy`, `Drop`, or `Copy Drop`.
//! - Types render with the same tokens the parser accepts.

use crate::ast::*;
use std::fmt::Write;

pub fn pretty_print(program: &Program) -> String {
    let mut out = String::new();
    let mut first = true;
    for decl in &program.declarations {
        if !first {
            out.push('\n');
        }
        first = false;
        write_declaration(&mut out, decl);
    }
    out
}

fn write_declaration(out: &mut String, decl: &Declaration) {
    match decl {
        Declaration::Struct(s) => write_struct(out, s),
        Declaration::Enum(e) => write_enum(out, e),
        Declaration::Fn(f) => write_function(out, f),
    }
}

fn write_markers(out: &mut String, m: &Markers) {
    // Canonical order: Copy, Drop, Move.
    if m.copy {
        out.push_str("Copy ");
    }
    if m.drop {
        out.push_str("Drop ");
    }
    if m.mov {
        out.push_str("Move ");
    }
}

fn write_struct(out: &mut String, s: &StructDecl) {
    out.push_str("struct ");
    write_markers(out, &s.markers);
    out.push_str(&s.name);
    out.push_str(" {\n");
    for f in &s.fields {
        write!(out, "  {}: ", f.name).unwrap();
        write_type(out, &f.ty);
        out.push('\n');
    }
    out.push_str("}\n");
}

fn write_enum(out: &mut String, e: &EnumDecl) {
    out.push_str("enum ");
    write_markers(out, &e.markers);
    out.push_str(&e.name);
    out.push_str(" {\n");
    for v in &e.variants {
        write!(out, "  {}: ", v.name).unwrap();
        write_type(out, &v.ty);
        out.push('\n');
    }
    out.push_str("}\n");
}

fn write_function(out: &mut String, f: &Function) {
    if f.is_extern {
        out.push_str("extern fn ");
    } else {
        out.push_str("fn ");
    }
    out.push_str(&f.name);
    out.push('(');
    for (i, p) in f.params.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        write!(out, "{}: ", p.name).unwrap();
        write_type(out, &p.ty);
    }
    out.push(')');

    let Some(body) = &f.body else {
        out.push_str(";\n");
        return;
    };
    out.push_str(" {\n");
    for l in &body.locals {
        write!(out, "  {}: ", l.name).unwrap();
        write_type(out, &l.ty);
        out.push_str(";\n");
    }
    for block in &body.blocks {
        write!(out, "  {}:\n", block.label).unwrap();
        for (stmt, _) in &block.statements {
            out.push_str("    ");
            write_statement(out, stmt);
            out.push_str(";\n");
        }
        out.push_str("    ");
        write_terminator(out, &block.terminator);
        out.push('\n');
    }
    out.push_str("}\n");
}

fn write_type(out: &mut String, ty: &Type) {
    match ty {
        Type::Int(i) => out.push_str(i.name()),
        Type::Float(f) => out.push_str(f.name()),
        Type::Bool => out.push_str("bool"),
        Type::Unit => out.push_str("unit"),
        Type::Never => out.push_str("never"),
        Type::Custom(name) => out.push_str(name),
        Type::Fn(params) => {
            out.push_str("fn(");
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_type(out, p);
            }
            out.push(')');
        }
        Type::Ref(kind, inner) => {
            out.push_str(match kind {
                RefKind::Shared => "&",
                RefKind::Mut => "&mut ",
                RefKind::Out => "&out ",
                RefKind::Drop => "&drop ",
                RefKind::Uninit => "&uninit ",
            });
            if matches!(kind, RefKind::Shared) {
                out.push(' ');
            }
            write_type(out, inner);
        }
        Type::RawPtr(inner) => {
            out.push('*');
            write_type(out, inner);
        }
        Type::Array(elem, n) => {
            out.push('[');
            write_type(out, elem);
            write!(out, "; {}", n).unwrap();
            out.push(']');
        }
    }
}

fn write_place(out: &mut String, place: &Place) {
    match place {
        Place::Var(name) => out.push_str(name),
        Place::Field(inner, field) => {
            write_place_projection_base(out, inner);
            out.push('.');
            out.push_str(field);
        }
        Place::Downcast(inner, variant) => {
            write_place_projection_base(out, inner);
            out.push_str(" as ");
            out.push_str(variant);
        }
        Place::Deref(inner) => {
            write_place(out, inner);
            out.push_str(".*");
        }
        Place::Index(inner, op) => {
            write_place_projection_base(out, inner);
            out.push('[');
            write_operand(out, op);
            out.push(']');
        }
    }
}

/// Write a place that appears to the left of `.field`, `as V`, or `[i]`.
/// With postfix `.*`, all projections are left-associative at the same
/// precedence, so no parenthesization is ever needed.
fn write_place_projection_base(out: &mut String, place: &Place) {
    write_place(out, place);
}

fn write_operand(out: &mut String, op: &Operand) {
    match op {
        Operand::Copy(p) => {
            out.push_str("copy ");
            write_place(out, p);
        }
        Operand::Move(p) => {
            out.push_str("move ");
            write_place(out, p);
        }
        Operand::Const(c) => write_const(out, c),
    }
}

fn write_const(out: &mut String, c: &ConstVal) {
    match c {
        // Integer literals emit the decimal value; the type suffix is
        // omitted for the parser's default (`i64`) so unsuffixed source
        // round-trips as unsuffixed.
        ConstVal::Int { bits, ty } => {
            let mask: u64 = if ty.bits() == 64 {
                u64::MAX
            } else {
                (1u64 << ty.bits()) - 1
            };
            let value = bits & mask;
            if *ty == IntTy::I64 {
                write!(out, "{}", value).unwrap();
            } else {
                write!(out, "{}{}", value, ty.name()).unwrap();
            }
        }
        // Float literals emit `<decimal>.<decimal>` and add the type
        // suffix only when the type isn't the parser default (`f64`).
        ConstVal::Float { bits, ty } => match ty {
            FloatTy::F32 => {
                let v = f32::from_bits(*bits as u32);
                write!(out, "{:?}f32", v).unwrap();
            }
            FloatTy::F64 => {
                let v = f64::from_bits(*bits);
                write!(out, "{:?}", v).unwrap();
            }
        },
        ConstVal::ByteStr(bytes) => {
            // Emit `b"..."` with the same escape set the parser
            // accepts. Round-trippable: `Parser::parse` of the
            // output decodes to the same byte sequence.
            out.push_str("b\"");
            for &b in bytes {
                match b {
                    b'\n' => out.push_str("\\n"),
                    b'\t' => out.push_str("\\t"),
                    b'\r' => out.push_str("\\r"),
                    b'\0' => out.push_str("\\0"),
                    b'\\' => out.push_str("\\\\"),
                    b'"' => out.push_str("\\\""),
                    0x20..=0x7E => out.push(b as char),
                    _ => write!(out, "\\x{:02X}", b).unwrap(),
                }
            }
            out.push('"');
        }
        ConstVal::Bool(true) => out.push_str("true"),
        ConstVal::Bool(false) => out.push_str("false"),
        ConstVal::Unit => out.push_str("unit"),
        ConstVal::FnName(name) => out.push_str(name),
    }
}

fn write_rvalue(out: &mut String, rv: &RValue) {
    match rv {
        RValue::Use(op) => write_operand(out, op),
        RValue::Ref(kind, place) => {
            out.push_str(match kind {
                RefKind::Shared => "&",
                RefKind::Mut => "&mut ",
                RefKind::Out => "&out ",
                RefKind::Drop => "&drop ",
                RefKind::Uninit => "&uninit ",
            });
            if matches!(kind, RefKind::Shared) {
                out.push(' ');
            }
            write_place(out, place);
        }
        RValue::RawRef(place) => {
            out.push_str("&raw ");
            write_place(out, place);
        }
        RValue::EnumConstr(enum_name, variant, op) => {
            write!(out, "{}::{}(", enum_name, variant).unwrap();
            write_operand(out, op);
            out.push(')');
        }
        RValue::ArrayLit(ops) => {
            out.push('[');
            for (i, op) in ops.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_operand(out, op);
            }
            out.push(']');
        }
    }
}

fn write_statement(out: &mut String, stmt: &Statement) {
    match stmt {
        Statement::Assign(place, rvalue) => {
            write_place(out, place);
            out.push_str(" = ");
            write_rvalue(out, rvalue);
        }
        Statement::Call(target, args) => {
            out.push_str("call ");
            write_operand(out, target);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write_operand(out, a);
            }
            out.push(')');
        }
        Statement::Drop(place) => {
            out.push_str("drop ");
            write_place(out, place);
        }
        Statement::Unborrow(place) => {
            out.push_str("unborrow ");
            write_place(out, place);
        }
    }
}

fn write_terminator(out: &mut String, term: &Terminator) {
    match term {
        Terminator::Goto(label) => write!(out, "goto {}", label).unwrap(),
        Terminator::Return => out.push_str("return"),
        Terminator::Branch {
            cond,
            true_label,
            false_label,
        } => {
            out.push_str("branch(");
            write_operand(out, cond);
            write!(out, ") [true: {}, false: {}]", true_label, false_label).unwrap();
        }
        Terminator::SwitchEnum { place, cases } => {
            out.push_str("switchEnum(");
            write_place(out, place);
            out.push_str(") [");
            for (i, (variant, label)) in cases.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                write!(out, "{}: {}", variant, label).unwrap();
            }
            out.push(']');
        }
        Terminator::Abort => out.push_str("abort"),
        Terminator::Unreachable => out.push_str("unreachable"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Parser;

    /// Parse `src`, pretty-print, and verify the output re-parses to a
    /// program equivalent to the first (spans intentionally ignored — we
    /// strip them before compare).
    #[track_caller]
    fn assert_roundtrip(src: &str) {
        let original = Parser::new(src.to_string())
            .parse()
            .unwrap_or_else(|e| panic!("parse error on original: {}\n--- source ---\n{}", e, src));
        let printed = pretty_print(&original);
        let reparsed = Parser::new(printed.clone()).parse().unwrap_or_else(|e| {
            panic!(
                "parse error on pretty-printed output: {}\n--- pretty ---\n{}",
                e, printed
            )
        });
        assert_eq!(
            strip_spans(original.clone()),
            strip_spans(reparsed),
            "round-trip differed\n--- source ---\n{}\n--- pretty ---\n{}",
            src,
            printed
        );
    }

    /// Replace every span with a zero span so equality ignores positions.
    fn strip_spans(mut p: Program) -> Program {
        let zero = Span { line: 0, col: 0 };
        for decl in &mut p.declarations {
            match decl {
                Declaration::Struct(s) => {
                    s.name_span = zero;
                    for f in &mut s.fields {
                        f.span = zero;
                    }
                }
                Declaration::Enum(e) => {
                    e.name_span = zero;
                    for v in &mut e.variants {
                        v.span = zero;
                    }
                }
                Declaration::Fn(f) => {
                    f.name_span = zero;
                    for p in &mut f.params {
                        p.span = zero;
                    }
                    if let Some(body) = &mut f.body {
                        for l in &mut body.locals {
                            l.span = zero;
                        }
                        for b in &mut body.blocks {
                            b.label_span = zero;
                            b.terminator_span = zero;
                            for (_, s) in &mut b.statements {
                                *s = zero;
                            }
                        }
                    }
                }
            }
        }
        p
    }

    #[test]
    fn roundtrip_scalar_fn() {
        assert_roundtrip(
            "
            fn f(x: i64) {
              y: i64;
              entry:
                y = copy x;
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_struct_and_enum() {
        assert_roundtrip(
            "
            struct Copy Drop P { x: i64 y: i64 }
            enum Copy Drop Option { None: unit Some: i64 }
            fn f(p: P, o: Option) {
              n: i64;
              entry:
                switchEnum(o) [None: n_arm, Some: s_arm]
              s_arm:
                n = copy o as Some;
                return
              n_arm:
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_extern_fn() {
        assert_roundtrip("extern fn take(x: i64, y: &mut i64);");
    }

    #[test]
    fn roundtrip_all_ref_kinds() {
        assert_roundtrip(
            "
            fn f(a: &i64, b: &mut i64, c: &out i64, d: &drop i64, e: &uninit i64) {
              entry:
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_fn_type_and_call() {
        assert_roundtrip(
            "
            extern fn callee(a: i64);
            fn f() {
              g: fn(i64);
              entry:
                g = callee;
                call copy g(1);
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_branch_and_drop_and_abort() {
        assert_roundtrip(
            "
            fn f(b: bool, x: i64) {
              entry:
                drop x;
                branch(copy b) [true: t, false: fbr]
              t:
                return
              fbr:
                abort
            }
            ",
        );
    }

    #[test]
    fn roundtrip_nested_places() {
        assert_roundtrip(
            "
            struct Copy Drop Inner { a: i64 b: i64 }
            struct Copy Drop Outer { i: Inner c: i64 }
            fn f(o: Outer) {
              n: i64;
              entry:
                n = copy o.i.a;
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_field_of_downcast() {
        // `place as Variant` binds tighter than `.field` in the grammar,
        // so `e as A.x` parses as `Field(Downcast(e, A), x)`.
        assert_roundtrip(
            "
            struct Copy Drop Pair { x: i64 y: i64 }
            enum Copy Drop E { A: Pair B: i64 }
            fn f(e: E) {
              n: i64;
              entry:
                switchEnum(e) [A: a_arm, B: b_arm]
              a_arm:
                n = copy e as A.x;
                return
              b_arm:
                return
            }
            ",
        );
    }

    #[test]
    fn roundtrip_deref() {
        assert_roundtrip(
            "
            fn f(r: &mut i64) {
              n: i64;
              entry:
                n = copy r.*;
                r.* = 42;
                return
            }
            ",
        );
    }
}
