//! Source-facing formatting for MIR values embedded in diagnostics.
//!
//! Canonical MIR formatting deliberately preserves compiler-assigned lifetime
//! names. Diagnostics need a different projection: user-written lifetimes keep
//! their spelling, while elided lifetimes receive names that are local to one
//! diagnostic (`'1`, `'2`, ...). This formatter owns that per-diagnostic state
//! and formats structured MIR values directly; it never rewrites completed
//! prose.

use crate::common::{GeneratedKind, Lifetime, SourceInfo};
use crate::diagnostics::Diagnostic;
use crate::mir::ast::{DeclMeta, GenericParams, Instance, Type, TypeKind};
use crate::mir::lifetime::Region;
use std::collections::HashMap;
use std::fmt::Write;

/// An enclosing declaration's lifetime namespace within one diagnostic.
///
/// Scope identity is allocated by [`DiagnosticFormat`], so two declarations
/// that both happen to contain a generated `'s0` still receive distinct
/// diagnostic names.
#[derive(Debug, Clone)]
pub struct DiagnosticScope {
    id: usize,
    generated: HashMap<Lifetime, SourceInfo>,
}

#[derive(Debug)]
pub struct DiagnosticFormat {
    next_scope: usize,
    next_lifetime: usize,
    aliases: HashMap<(usize, Lifetime), usize>,
    introductions: Vec<(SourceInfo, usize)>,
}

impl Default for DiagnosticFormat {
    fn default() -> Self {
        Self {
            next_scope: 0,
            next_lifetime: 1,
            aliases: HashMap::new(),
            introductions: Vec::new(),
        }
    }
}

impl DiagnosticFormat {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register one declaration namespace. Call this once per declaration
    /// mentioned by the diagnostic and reuse the returned scope for every
    /// fragment from that declaration.
    pub fn scope(&mut self, meta: &DeclMeta) -> DiagnosticScope {
        self.scope_params(&meta.params)
    }

    pub fn scope_params(&mut self, params: &GenericParams) -> DiagnosticScope {
        let id = self.next_scope;
        self.next_scope += 1;
        let generated = params
            .lifetime_params
            .iter()
            .filter(|param| param.source.generated_kind() == Some(GeneratedKind::LifetimeElision))
            .map(|param| (param.lifetime.clone(), param.source))
            .collect();
        DiagnosticScope { id, generated }
    }

    pub fn lifetime(&mut self, scope: &DiagnosticScope, lifetime: &Lifetime) -> String {
        let Some(source) = scope.generated.get(lifetime).copied() else {
            return lifetime.to_string();
        };
        let key = (scope.id, lifetime.clone());
        let alias = if let Some(alias) = self.aliases.get(&key) {
            *alias
        } else {
            let alias = self.next_lifetime;
            self.next_lifetime += 1;
            self.aliases.insert(key, alias);
            self.introductions.push((source, alias));
            alias
        };
        format!("'{}", alias)
    }

    pub fn region(&mut self, scope: &DiagnosticScope, region: &Region) -> String {
        match region {
            Region::Named(lifetime) => self.lifetime(scope, lifetime),
            Region::Free(index) => format!("'?{}", index),
            Region::Inference(index) => format!("'?call{}", index),
            Region::Static => "'static".to_string(),
        }
    }

    pub fn ty(&mut self, scope: &DiagnosticScope, ty: &Type) -> String {
        let mut out = String::new();
        self.write_type(scope, ty, &mut out)
            .expect("writing a diagnostic type to String cannot fail");
        out
    }

    /// Attach source labels introducing every generated lifetime alias used by
    /// this diagnostic. Aliases are reported in allocation order so the labels
    /// remain stable and correspond to the order in the primary message.
    pub fn finish(self, mut diagnostic: Diagnostic) -> Diagnostic {
        for (source, alias) in self.introductions {
            diagnostic = diagnostic.with_secondary(
                source,
                format!(
                    "the lifetime of this reference is called '{} in this diagnostic",
                    alias,
                ),
            );
        }
        diagnostic
    }

    fn write_type(
        &mut self,
        scope: &DiagnosticScope,
        ty: &Type,
        out: &mut String,
    ) -> std::fmt::Result {
        match &ty.kind {
            TypeKind::Int(int) => out.write_str(int.name()),
            TypeKind::Float(float) => out.write_str(float.name()),
            TypeKind::Bool => out.write_str("bool"),
            TypeKind::Unit => out.write_str("unit"),
            TypeKind::Never => out.write_str("never"),
            TypeKind::Custom(Instance {
                name,
                lifetime_args: lifetimes,
                type_args: args,
            }) => {
                out.write_str(name)?;
                if lifetimes.is_empty() && args.is_empty() {
                    return Ok(());
                }
                out.push('<');
                let mut first = true;
                for lifetime in lifetimes {
                    if !first {
                        out.write_str(", ")?;
                    }
                    first = false;
                    out.write_str(&self.lifetime(scope, lifetime))?;
                }
                for arg in args {
                    if !first {
                        out.write_str(", ")?;
                    }
                    first = false;
                    self.write_type(scope, arg, out)?;
                }
                out.push('>');
                Ok(())
            }
            TypeKind::Param(name) => out.write_str(name),
            TypeKind::Fn(params) => {
                out.write_str("fn(")?;
                for (index, param) in params.iter().enumerate() {
                    if index > 0 {
                        out.write_str(", ")?;
                    }
                    self.write_type(scope, param, out)?;
                }
                out.push(')');
                Ok(())
            }
            TypeKind::Ref(kind, lifetime, inner) => {
                let lifetime = lifetime
                    .as_ref()
                    .map(|lifetime| self.lifetime(scope, lifetime));
                kind.write_type_prefix(out, lifetime.as_ref())?;
                self.write_type(scope, inner, out)
            }
            TypeKind::RawPtr(inner) => {
                out.push('*');
                self.write_type(scope, inner, out)
            }
            TypeKind::Array(element, size) => {
                out.push('[');
                self.write_type(scope, element, out)?;
                write!(out, "; {}]", size)
            }
        }
    }
}

/// Build a diagnostic containing one type from one declaration scope. The
/// callback receives the source-facing type text, and the returned diagnostic
/// is completed with any generated-lifetime introductions that text requires.
pub fn format_type_diagnostic(
    meta: &DeclMeta,
    ty: &Type,
    build: impl FnOnce(String) -> Diagnostic,
) -> Diagnostic {
    format_type_diagnostic_params(&meta.params, ty, build)
}

pub fn format_type_diagnostic_params(
    params: &GenericParams,
    ty: &Type,
    build: impl FnOnce(String) -> Diagnostic,
) -> Diagnostic {
    let mut format = DiagnosticFormat::new();
    let scope = format.scope_params(params);
    let ty = format.ty(&scope, ty);
    format.finish(build(ty))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{LifetimeParam, Markers, SourceInfo, Span};
    use crate::mir::ast::{DeclMeta, RefKind};

    fn meta(name: &str, params: Vec<LifetimeParam>) -> DeclMeta {
        let source = SourceInfo::generated(GeneratedKind::TestHelper, Span::default());
        DeclMeta {
            name: name.into(),
            name_source: source,
            params: GenericParams {
                lifetime_params: params,
                outlives: Vec::new(),
                type_params: Vec::new(),
                source,
            },
            markers: Markers::empty(),
        }
    }

    #[test]
    fn generated_lifetimes_are_distinct_and_stable_within_a_scope() {
        let meta = meta(
            "f",
            vec![
                LifetimeParam::generated(
                    Lifetime("s0".into()),
                    GeneratedKind::LifetimeElision,
                    Span::default(),
                ),
                LifetimeParam::generated(
                    Lifetime("s1".into()),
                    GeneratedKind::LifetimeElision,
                    Span::default(),
                ),
            ],
        );
        let mut format = DiagnosticFormat::default();
        let scope = format.scope(&meta);

        assert_eq!(format.lifetime(&scope, &Lifetime("s0".into())), "'1");
        assert_eq!(format.lifetime(&scope, &Lifetime("s1".into())), "'2");
        assert_eq!(format.lifetime(&scope, &Lifetime("s0".into())), "'1");
    }

    #[test]
    fn scopes_do_not_alias_same_internal_name() {
        let generated = || {
            vec![LifetimeParam::generated(
                Lifetime("s0".into()),
                GeneratedKind::LifetimeElision,
                Span::default(),
            )]
        };
        let caller = meta("caller", generated());
        let callee = meta("callee", generated());
        let mut format = DiagnosticFormat::new();
        let caller_scope = format.scope(&caller);
        let callee_scope = format.scope(&callee);

        assert_eq!(format.lifetime(&caller_scope, &Lifetime("s0".into())), "'1");
        assert_eq!(format.lifetime(&callee_scope, &Lifetime("s0".into())), "'2");
    }

    #[test]
    fn explicit_names_are_preserved_even_when_they_resemble_internal_names() {
        let meta = meta(
            "f",
            vec![LifetimeParam::written(
                Lifetime("s0".into()),
                Span {
                    line: 1,
                    col: 1,
                    end_line: 1,
                    end_col: 4,
                },
            )],
        );
        let ty = Type::new(
            TypeKind::Ref(
                RefKind::Mut,
                Some(Lifetime("s0".into())),
                Box::new(Type::synthesized(TypeKind::Int(crate::common::IntTy::I64))),
            ),
            SourceInfo::generated(GeneratedKind::TestHelper, Span::default()),
        );
        let mut format = DiagnosticFormat::new();
        let scope = format.scope(&meta);

        assert_eq!(format.ty(&scope, &ty), "&mut 's0 i64");
    }
}
