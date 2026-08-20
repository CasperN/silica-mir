//! Pretty-printer for MIR programs.
//!
//! The output is exact-parse: parsing `pretty_print(program)` yields a program
//! equivalent to the indexed declarations modulo spans. This gives us a
//! textual golden-file style for tests (see `drop_elaboration` tests) and
//! makes elaborated output human-readable.
//!
//! Style choices:
//! - Two-space indent inside function bodies.
//! - One statement per line, terminator on its own line.
//! - Struct/enum bodies are one field/variant per line.
//! - Markers appear after the name as `: Copy + Drop`. Absent when
//!   the type has none.
//! - Types render with the same tokens the parser accepts.

use crate::mir::ast::*;
use crate::mir::env::{DeclarationRef, IndexedProgram};
use std::fmt::Write;

pub fn pretty_print(program: &IndexedProgram) -> String {
    let mut out = String::new();
    let mut first = true;
    for decl in program.declarations() {
        if is_prelude_decl(decl) {
            continue;
        }
        if !first {
            out.push('\n');
        }
        first = false;
        write_declaration(&mut out, decl);
    }
    out
}

/// Compiler-injected prelude declarations are not user-authored and should
/// not appear in fixture-pinned pretty-printed output.
fn is_prelude_decl(decl: DeclarationRef<'_>) -> bool {
    let source = match decl {
        DeclarationRef::Impl(i) => i.methods.first().map(|m| m.meta.name_source),
        _ => decl.meta().map(|m| m.name_source),
    };
    matches!(
        source,
        Some(SourceInfo::Generated {
            kind: GeneratedKind::Prelude,
            ..
        }),
    )
}

fn write_declaration(out: &mut String, decl: DeclarationRef<'_>) {
    match decl {
        DeclarationRef::Struct(s) => write_struct(out, s),
        DeclarationRef::Enum(e) => write_enum(out, e),
        DeclarationRef::Function(f) => write_function(out, f),
        DeclarationRef::Trait(t) => write_trait(out, t),
        DeclarationRef::Impl(i) => write_impl(out, i),
    }
}

fn write_markers(out: &mut String, m: &Markers) {
    // Iterator yields declared markers in canonical order. Nothing
    // at all when the type has no markers.
    let names: Vec<&str> = m.iter_declared().map(|m| m.name()).collect();
    if names.is_empty() {
        return;
    }
    out.push_str(": ");
    out.push_str(&names.join(" + "));
}

fn write_bounds(out: &mut String, bounds: &Bounds) {
    let bounds = bounds
        .markers
        .iter_declared()
        .map(|marker| marker.name().to_string())
        .chain(
            bounds
                .traits
                .iter()
                .map(|bound| bound.trait_path.to_string()),
        )
        .collect::<Vec<_>>();
    if !bounds.is_empty() {
        out.push_str(": ");
        out.push_str(&bounds.join(" + "));
    }
}

fn write_type_params(out: &mut String, params: &GenericParams) {
    if params.lifetime_params.is_empty() && params.type_params.is_empty() {
        return;
    }
    out.push('<');
    let mut first = true;
    for lt in &params.lifetime_params {
        if !first {
            out.push_str(", ");
        }
        first = false;
        write!(out, "{}", lt).unwrap();
        // Emit any outlives bounds inline after each subject lifetime,
        // matching the source shape `'a: 'b + 'c`. Bounds keyed to
        // other subjects fall through this iteration and land next to
        // their subject.
        let mut bounds = params
            .outlives
            .iter()
            .filter(|bound| bound.longer == lt.lifetime)
            .peekable();
        if bounds.peek().is_some() {
            let mut first_bound = true;
            for bound in bounds {
                if first_bound {
                    out.push_str(": ");
                    first_bound = false;
                } else {
                    out.push_str(" + ");
                }
                write!(out, "{}", bound.shorter).unwrap();
            }
        }
    }
    for p in &params.type_params {
        if !first {
            out.push_str(", ");
        }
        first = false;
        out.push_str(&p.name);
        write_bounds(out, &p.bounds);
    }
    out.push('>');
}

fn write_struct(out: &mut String, s: &StructDecl) {
    out.push_str("struct ");
    out.push_str(&s.meta.name);
    write_type_params(out, &s.meta.params);
    write_markers(out, &s.meta.markers);
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
    out.push_str(&e.meta.name);
    write_type_params(out, &e.meta.params);
    write_markers(out, &e.meta.markers);
    out.push_str(" {\n");
    for v in &e.variants {
        write!(out, "  {}: ", v.name).unwrap();
        write_type(out, &v.ty);
        out.push('\n');
    }
    out.push_str("}\n");
}

fn write_trait(out: &mut String, t: &TraitDecl) {
    out.push_str("trait ");
    out.push_str(&t.meta.name);
    write_type_params(out, &t.meta.params);
    write_bounds(out, &t.self_bounds);
    out.push_str(" {\n");
    for m in &t.methods {
        out.push_str("  ");
        let abi = m.abi.as_str();
        if !abi.is_empty() {
            write!(out, "{} ", abi).unwrap();
        }
        out.push_str("fn ");
        out.push_str(&m.meta.name);
        write_type_params(out, &m.meta.params);
        out.push('(');
        for (i, p) in m.params.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            write!(out, "{}: ", p.name).unwrap();
            write_type(out, &p.ty);
        }
        out.push_str(");\n");
    }
    out.push_str("}\n");
}

fn write_impl(out: &mut String, i: &ImplBlock) {
    out.push_str("impl");
    write_type_params(out, &i.params);
    out.push(' ');
    if let Some(trait_path) = &i.trait_path {
        write!(out, "{} for ", trait_path).unwrap();
    }
    write_type(out, &i.target);
    out.push_str(" {\n");
    for m in &i.methods {
        // Reuse write_function; indent each line so nested methods
        // read like body members of the impl block.
        let mut body = String::new();
        write_function(&mut body, m);
        for line in body.lines() {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    }
    out.push_str("}\n");
}

fn write_function(out: &mut String, f: &Function) {
    if f.linkage == Linkage::Foreign {
        out.push_str("extern ");
    }
    let abi = f.abi.as_str();
    if !abi.is_empty() {
        write!(out, "{} ", abi).unwrap();
    }
    out.push_str("fn ");
    out.push_str(&f.meta.name);
    write_type_params(out, &f.meta.params);
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
        for stmt in block.statements.iter() {
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
    use std::fmt::Write;
    write!(out, "{}", ty).unwrap();
}

fn write_instance_head(out: &mut String, instance: &Instance) {
    out.push_str(&instance.name);
    if !instance.lifetime_args.is_empty() || !instance.type_args.is_empty() {
        out.push('<');
        let mut first = true;
        for lifetime in &instance.lifetime_args {
            if !first {
                out.push_str(", ");
            }
            first = false;
            use std::fmt::Write;
            write!(out, "{}", lifetime).unwrap();
        }
        for a in &instance.type_args {
            if !first {
                out.push_str(", ");
            }
            first = false;
            write_type(out, a);
        }
        out.push('>');
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
        Operand::Take(p) => {
            out.push_str("take ");
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
        ConstVal::EmptyStruct(instance) => {
            write_instance_head(out, instance);
            out.push_str(" {}");
        }
        ConstVal::FnName(instance) => {
            write_instance_head(out, instance);
        }
        ConstVal::InherentFn { self_ty, method } => {
            out.push('<');
            write_type(out, self_ty);
            out.push_str(">::");
            write!(out, "{}", method).unwrap();
        }
        // `<SelfTy as Trait<TraitArgs>>::method<MethodArgs>` — matches
        // the grammar's UFCS-style fn_name shape.
        ConstVal::TraitFn {
            trait_path,
            self_ty,
            method,
        } => {
            out.push('<');
            write_type(out, self_ty);
            out.push_str(" as ");
            write!(out, "{}", trait_path).unwrap();
            out.push_str(">::");
            write!(out, "{}", method).unwrap();
        }
    }
}

fn write_rvalue(out: &mut String, rv: &RValue) {
    match rv {
        RValue::Use(op) => write_operand(out, op),
        RValue::Ref(kind, place) => {
            write!(out, "{}", kind).unwrap();
            if *kind != RefKind::Shared {
                out.push(' ');
            }
            write_place(out, place);
        }
        RValue::RawRef(place) => {
            out.push_str("&raw ");
            write_place(out, place);
        }
        RValue::EnumConstr(enum_name, type_args, variant, op) => {
            write!(out, "{}", enum_name).unwrap();
            if !type_args.is_empty() {
                out.push('<');
                for (i, a) in type_args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    write!(out, "{}", a).unwrap();
                }
                out.push('>');
            }
            write!(out, "::{}(", variant).unwrap();
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
        RValue::PtrCast(op, ty) => {
            out.push_str("ptr_cast(");
            write_operand(out, op);
            out.push_str(", ");
            write!(out, "{}", ty).unwrap();
            out.push(')');
        }
    }
}

fn write_statement(out: &mut String, stmt: &Statement) {
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            write_place(out, place);
            out.push_str(" = ");
            write_rvalue(out, rvalue);
        }
        StatementKind::Call(target, args) => {
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
        StatementKind::Drop(place) => {
            out.push_str("drop ");
            write_place(out, place);
        }
        StatementKind::Unborrow(place) => {
            out.push_str("unborrow ");
            write_place(out, place);
        }
        StatementKind::RequireUninit(place) => {
            out.push_str("require_uninit ");
            write_place(out, place);
        }
    }
}

fn write_terminator(out: &mut String, term: &Terminator) {
    match &term.kind {
        TerminatorKind::Goto(label) => write!(out, "goto {}", label).unwrap(),
        TerminatorKind::Return => out.push_str("return"),
        TerminatorKind::Branch {
            cond,
            true_label,
            false_label,
        } => {
            out.push_str("branch(");
            write_operand(out, cond);
            write!(out, ") [true: {}, false: {}]", true_label, false_label).unwrap();
        }
        TerminatorKind::SwitchEnum { place, cases } => {
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
        TerminatorKind::Abort => out.push_str("abort"),
        TerminatorKind::Unreachable => out.push_str("unreachable"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::env::IndexedProgram;
    use crate::mir::parser::Parser;

    /// Parse `src`, pretty-print, and verify the output re-parses to a
    /// program equivalent to the first (spans intentionally ignored — we
    /// strip them before compare).
    #[track_caller]
    fn assert_roundtrip(src: &str) {
        let original = Parser::parse_or_panic(src);
        let indexed = IndexedProgram::build(&original).0;
        let printed = pretty_print(&indexed);
        let reparsed = Parser::parse_or_panic(printed.clone());
        assert_eq!(
            strip_spans(original.clone()),
            strip_spans(reparsed),
            "round-trip differed\n--- source ---\n{}\n--- pretty ---\n{}",
            src,
            printed
        );
    }

    fn strip_params(params: &mut GenericParams, zero: Span) {
        params.source = SourceInfo::written(zero);
        for lifetime in &mut params.lifetime_params {
            lifetime.source = SourceInfo::written(zero);
        }
        for bound in &mut params.outlives {
            bound.source = SourceInfo::written(zero);
        }
        for tp in &mut params.type_params {
            tp.source = SourceInfo::written(zero);
        }
    }

    /// Replace every span with a zero span AND clear the source arc so
    /// equality ignores positions and formatting of the original text
    /// (a re-parsed pretty-print is not byte-identical to the input).
    fn strip_spans(mut p: Program) -> Program {
        p.source = std::sync::Arc::new(String::new());
        let zero = Span::default();
        for decl in &mut p.declarations {
            let params = match decl {
                Declaration::Struct(s) => {
                    s.meta.name_source = SourceInfo::written(zero);
                    for f in &mut s.fields {
                        f.source = SourceInfo::written(zero);
                    }
                    &mut s.meta.params
                }
                Declaration::Enum(e) => {
                    e.meta.name_source = SourceInfo::written(zero);
                    for v in &mut e.variants {
                        v.source = SourceInfo::written(zero);
                    }
                    &mut e.meta.params
                }
                Declaration::Fn(f) => {
                    f.meta.name_source = SourceInfo::written(zero);
                    for p in &mut f.params {
                        p.source = SourceInfo::written(zero);
                    }
                    if let Some(body) = &mut f.body {
                        for l in &mut body.locals {
                            l.source = SourceInfo::written(zero);
                        }
                        for b in &mut body.blocks {
                            b.label_source = SourceInfo::written(zero);
                            b.terminator.source = SourceInfo::written(zero);
                            for statement in b.statements.iter_mut() {
                                statement.source = SourceInfo::written(zero);
                            }
                        }
                    }
                    &mut f.meta.params
                }
                Declaration::Trait(t) => {
                    t.meta.name_source = SourceInfo::written(zero);
                    for m in &mut t.methods {
                        m.meta.name_source = SourceInfo::written(zero);
                        strip_params(&mut m.meta.params, zero);
                        for p in &mut m.params {
                            p.source = SourceInfo::written(zero);
                        }
                    }
                    &mut t.meta.params
                }
                Declaration::Impl(i) => {
                    for m in &mut i.methods {
                        m.meta.name_source = SourceInfo::written(zero);
                        strip_params(&mut m.meta.params, zero);
                        for p in &mut m.params {
                            p.source = SourceInfo::written(zero);
                        }
                        if let Some(body) = &mut m.body {
                            for l in &mut body.locals {
                                l.source = SourceInfo::written(zero);
                            }
                            for b in &mut body.blocks {
                                b.label_source = SourceInfo::written(zero);
                                b.terminator.source = SourceInfo::written(zero);
                                for statement in b.statements.iter_mut() {
                                    statement.source = SourceInfo::written(zero);
                                }
                            }
                        }
                    }
                    &mut i.params
                }
            };
            strip_params(params, zero);
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
            struct P: Copy + Drop { x: i64 y: i64 }
            enum Option: Copy + Drop { None: $Tuple0 Some: i64 }
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
        assert_roundtrip("extern fn consume(x: i64, y: &mut i64);");
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
    fn roundtrip_named_lifetimes_on_decls_and_refs() {
        assert_roundtrip(
            "
            struct Pair<'a> { x: &'a i64 y: &'a i64 }
            enum Either<'a> { L: &'a i64 R: i64 }
            fn id<'a, T>(x: &'a T) {
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
    fn roundtrip_require_uninit() {
        assert_roundtrip(
            r#"
                fn f(x: i64) {
                    entry:
                        require_uninit x;
                        return
                }
            "#,
        );
    }

    #[test]
    fn roundtrip_nested_places() {
        assert_roundtrip(
            "
            struct Inner: Copy + Drop { a: i64 b: i64 }
            struct Outer: Copy + Drop { i: Inner c: i64 }
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
            struct Pair: Copy + Drop { x: i64 y: i64 }
            enum E: Copy + Drop { A: Pair B: i64 }
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

    #[test]
    fn roundtrip_trait_decl() {
        assert_roundtrip(
            "
            trait Simple {
              fn ping(recv: &Self);
            }
            trait Iter<T: Copy + Drop> {
              fn next(recv: &mut Self, out: &out T);
              fn map<U>(recv: &Self, other: &U, out: &out T);
            }
            ",
        );
    }

    #[test]
    fn roundtrip_impl_block() {
        assert_roundtrip(
            "
            trait Iter<T: Copy + Drop> {
              fn next(recv: &mut Self, out: &out T);
            }
            struct Foo: Copy + Drop { x: i64 }
            impl Iter<i64> for Foo {
              fn next(recv: &mut Foo, out: &out i64) {
                entry:
                  return
              }
            }
            ",
        );
    }

    #[test]
    fn roundtrip_method_abi() {
        assert_roundtrip(
            "
            struct Bar: Copy + Drop { x: i64 }
            trait Called { \"C\" fn call(recv: &Self, out: &out i64); }
            impl Called for Bar {
              \"C\" fn call(recv: &Bar, out: &out i64) { entry: return }
            }
            impl Bar {
              \"C\" fn inherent(recv: &Bar, out: &out i64) { entry: return }
            }
            ",
        );
    }

    #[test]
    fn roundtrip_trait_fn_callee() {
        assert_roundtrip(
            "
            trait Sink { fn accept(recv: &mut Self, v: i64); }
            struct Foo: Copy + Drop { x: i64 }
            impl Sink for Foo {
              fn accept(recv: &mut Foo, v: i64) {
                entry:
                  return
              }
            }
            fn drive(f: &mut Foo) {
              entry:
                call <Foo as Sink>::accept(move f, 7);
                return
            }
            ",
        );
    }
}
