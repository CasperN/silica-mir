//! Type layout: size / alignment computation, plus a check pass that
//! rejects direct recursion in struct and enum types.
//!
//! Silica types have known layouts (like Rust's default representation,
//! though not ABI-stable). Direct recursion — a struct containing itself
//! by value, or an enum whose variant carries the enum by value — would
//! require infinite size, so it's rejected here. Recursion through a
//! reference is fine: the referent is behind a pointer of bounded size.
//!
//! ## Layout rules
//! - `number`                 → 8 bytes, align 8 (i64)
//! - `boolean`                → 1 byte,  align 1
//! - `unit`, `never`          → 0 bytes, align 1 (never is uninhabited)
//! - `fn(...)`, `&T` (any kind) → 8 bytes, align 8 (pointer on 64-bit target)
//! - **struct**: fields laid out in declaration order, each padded to its
//!   own alignment; total size rounded up to the struct's alignment (=
//!   max field alignment).
//! - **enum**: `{i16 discriminant, [max_payload_size x i8] payload}`.
//!   Enum alignment = `max(2, max_variant_payload_align)`; total size
//!   rounded up to enum alignment.
//!
//! **Assumes 64-bit pointers.** When we start caring about 32-bit targets
//! this table gets parameterized by a `Target` struct.
//!
//! `size_of` / `align_of` panic on unknown type names; callers must run
//! `type_check` first. `check_program` runs before that becomes a
//! problem — it only walks the declared-type graph.

use crate::ast::*;
use crate::diagnostics::Diagnostics;
use crate::type_check::{Env, TypeDecl};
use indexmap::IndexMap;
use std::collections::BTreeSet;

// ---------- Size / alignment ----------
//
// `size_of` / `align_of` (and their helpers) are exercised by tests but
// not yet consumed by any non-test caller. Enum codegen (slice 2) will
// wire them into `codegen::generate_llvm`. `dead_code` is silenced on
// each until then.

#[allow(dead_code)]
/// Size of `ty` in bytes on a 64-bit target.
pub fn size_of(ty: &Type, env: &Env) -> u64 {
    match ty {
        Type::Number => 8,
        Type::Boolean => 1,
        Type::Unit | Type::Never => 0,
        Type::Fn(_) | Type::Ref(_, _) => 8,
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => struct_size(s, env),
            Some(TypeDecl::Enum(e)) => enum_size(e, env),
            None => panic!("layout::size_of: unknown type '{}'", name),
        },
    }
}

#[allow(dead_code)]
/// Alignment of `ty` in bytes on a 64-bit target. Always a power of two.
pub fn align_of(ty: &Type, env: &Env) -> u64 {
    match ty {
        Type::Number => 8,
        Type::Boolean => 1,
        Type::Unit | Type::Never => 1,
        Type::Fn(_) | Type::Ref(_, _) => 8,
        Type::Custom(name) => match env.types.get(name) {
            Some(TypeDecl::Struct(s)) => struct_align(s, env),
            Some(TypeDecl::Enum(e)) => enum_align(e, env),
            None => panic!("layout::align_of: unknown type '{}'", name),
        },
    }
}

#[allow(dead_code)]
fn struct_size(s: &StructDecl, env: &Env) -> u64 {
    let mut offset = 0u64;
    let mut align = 1u64;
    for f in &s.fields {
        let fa = align_of(&f.ty, env);
        offset = align_up(offset, fa);
        offset += size_of(&f.ty, env);
        align = align.max(fa);
    }
    align_up(offset, align)
}

#[allow(dead_code)]
fn struct_align(s: &StructDecl, env: &Env) -> u64 {
    let mut align = 1u64;
    for f in &s.fields {
        align = align.max(align_of(&f.ty, env));
    }
    align
}

#[allow(dead_code)]
fn enum_size(e: &EnumDecl, env: &Env) -> u64 {
    // {i16 discriminant, [N x i8] payload} with the whole thing aligned
    // to the enum's overall alignment. Discriminant lives at offset 0;
    // payload starts at max(2, max_payload_align).
    let disc_size = 2u64;
    let disc_align = 2u64;
    let mut max_payload_size = 0u64;
    let mut max_payload_align = 1u64;
    for v in &e.variants {
        max_payload_size = max_payload_size.max(size_of(&v.ty, env));
        max_payload_align = max_payload_align.max(align_of(&v.ty, env));
    }
    let overall_align = disc_align.max(max_payload_align);
    let payload_offset = align_up(disc_size, overall_align);
    align_up(payload_offset + max_payload_size, overall_align)
}

#[allow(dead_code)]
fn enum_align(e: &EnumDecl, env: &Env) -> u64 {
    let mut a = 2u64; // discriminant alignment
    for v in &e.variants {
        a = a.max(align_of(&v.ty, env));
    }
    a
}

#[allow(dead_code)]
/// Round `x` up to the next multiple of `a`. `a` must be a power of two.
fn align_up(x: u64, a: u64) -> u64 {
    debug_assert!(a.is_power_of_two(), "align must be a power of two");
    (x + a - 1) & !(a - 1)
}

// ---------- Recursion check ----------

/// Report each maximal group of struct/enum types that participates in a
/// by-value cycle. Recursion through references or function pointers is
/// allowed (the referent is behind a pointer of bounded size).
pub fn check_sizes_finite(env: &Env, d: &mut Diagnostics) {
    let strongly_connected_components = tarjan_sccs(env);
    for scc in strongly_connected_components {
        if scc.len() > 1 || (scc.len() == 1 && has_self_loop(&scc[0], env)) {
            report_cycle(&scc, env, d);
        }
    }
}

fn report_cycle(scc: &[String], env: &Env, d: &mut Diagnostics) {
    let head = &scc[0];
    let span = decl_span(head, env);
    let members = scc.join(", ");
    d.errors.push(format!(
        "at {}: type '{}' is recursive by value (cycle: {}). Break the cycle by wrapping a field/variant payload in a reference.",
        span, head, members
    ));
}

fn decl_span(name: &str, env: &Env) -> Span {
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => s.name_span,
        Some(TypeDecl::Enum(e)) => e.name_span,
        None => Span { line: 0, col: 0 },
    }
}

/// Names of nominal types that appear by value in the declaration of
/// `name`. References and function types don't contribute — the pointer
/// is bounded regardless of the pointee.
fn by_value_edges(name: &str, env: &Env) -> Vec<String> {
    let mut out = Vec::new();
    match env.types.get(name) {
        Some(TypeDecl::Struct(s)) => {
            for f in &s.fields {
                if let Type::Custom(sub) = &f.ty {
                    out.push(sub.clone());
                }
            }
        }
        Some(TypeDecl::Enum(e)) => {
            for v in &e.variants {
                if let Type::Custom(sub) = &v.ty {
                    out.push(sub.clone());
                }
            }
        }
        None => {}
    }
    out
}

fn has_self_loop(name: &str, env: &Env) -> bool {
    by_value_edges(name, env).iter().any(|n| n == name)
}

/// Tarjan's strongly-connected components on the by-value edge graph.
/// Nodes are struct/enum names in declaration order. Result: one Vec
/// per SCC; single-node SCCs without a self-loop are trivial (not
/// cycles) but included — the caller filters them.
fn tarjan_sccs(env: &Env) -> Vec<Vec<String>> {
    let mut state = Tarjan {
        env,
        index: IndexMap::new(),
        lowlink: IndexMap::new(),
        on_stack: BTreeSet::new(),
        stack: Vec::new(),
        counter: 0,
        sccs: Vec::new(),
    };
    let names: Vec<String> = env.types.keys().cloned().collect();
    for n in &names {
        if !state.index.contains_key(n) {
            state.strongconnect(n);
        }
    }
    state.sccs
}

struct Tarjan<'a> {
    env: &'a Env,
    index: IndexMap<String, u32>,
    lowlink: IndexMap<String, u32>,
    on_stack: BTreeSet<String>,
    stack: Vec<String>,
    counter: u32,
    sccs: Vec<Vec<String>>,
}

impl<'a> Tarjan<'a> {
    fn strongconnect(&mut self, v: &str) {
        let v_owned = v.to_string();
        self.index.insert(v_owned.clone(), self.counter);
        self.lowlink.insert(v_owned.clone(), self.counter);
        self.counter += 1;
        self.stack.push(v_owned.clone());
        self.on_stack.insert(v_owned.clone());

        for w in by_value_edges(v, self.env) {
            // Successor referring to a non-declared type: type_check will
            // have reported "undeclared type" elsewhere. Skip here to
            // avoid touching a non-existent node.
            if !self.env.types.contains_key(&w) {
                continue;
            }
            if !self.index.contains_key(&w) {
                self.strongconnect(&w);
                let w_low = self.lowlink[&w];
                let v_low = self.lowlink.get_mut(&v_owned).unwrap();
                *v_low = (*v_low).min(w_low);
            } else if self.on_stack.contains(&w) {
                let w_idx = self.index[&w];
                let v_low = self.lowlink.get_mut(&v_owned).unwrap();
                *v_low = (*v_low).min(w_idx);
            }
        }

        if self.lowlink[&v_owned] == self.index[&v_owned] {
            let mut scc = Vec::new();
            loop {
                let w = self.stack.pop().expect("Tarjan: stack underflow");
                self.on_stack.remove(&w);
                scc.push(w.clone());
                if w == v_owned {
                    break;
                }
            }
            self.sccs.push(scc);
        }
    }
}

#[cfg(test)]
mod size_align_tests;
#[cfg(test)]
mod recursion_tests;
