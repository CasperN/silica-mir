//! Structured diagnostic type shared by all analysis passes.
//!
//! A `Diagnostic` carries the source position, function/block context,
//! and message for a single error or warning. `Diagnostics` collects
//! them into two lists (errors and warnings).
//!
//! **Construction**: `Diagnostic::new(code, span, message)` for the
//! required fields, then chain `.in_function(...)` and/or
//! `.in_block(...)` for optional context. Adding a new optional
//! field is a non-breaking change — add a setter, existing sites
//! keep working.
//!
//! **Extending `DiagCode`**: dedicated codes live in per-pass
//! sub-enums (see `type_check::TypeCheckCode`, `init_state::
//! InitStateCode`, etc.) and are dispatched by one variant here per
//! pass. Adding a new code within a pass is a one-line change in
//! that pass; `diagnostics.rs` only changes when a new pass is added.
//!
//! **String view**: `Diagnostic` implements `Display` in the format
//! `at L:C: In function 'f', block 'b': msg`. `Diagnostics::
//! errors_str()` produces `Vec<String>` for tests that still assert
//! on substring content.

use crate::mir::ast::Span;

/// Machine-readable error kind. One variant per analysis pass; the
/// pass owns its own sub-enum of specific codes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagCode {
    /// Errors from the type checker (see `type_check::TypeCheckCode`).
    TypeCheck(crate::mir::type_check::TypeCheckCode),
    /// Errors from initialization-state dataflow
    /// (see `init_state::InitStateCode`).
    InitState(crate::mir::init_state::InitStateCode),
    /// Diagnostics from the variant-flow / `switchEnum` analysis
    /// (see `variant_flow::VariantFlowCode`).
    VariantFlow(crate::mir::variant_flow::VariantFlowCode),
    /// Errors from the substructural per-statement checker
    /// (see `substructural::check::SubstructuralCheckCode`).
    SubstructuralCheck(crate::mir::substructural::check::SubstructuralCheckCode),
    /// Errors from the substructural class-composition validator
    /// (see `substructural::composition::SubstructuralCompositionCode`).
    SubstructuralComposition(crate::mir::substructural::composition::SubstructuralCompositionCode),
    /// Errors from the layout / recursion-cycle check
    /// (see `layout::LayoutCode`).
    Layout(crate::mir::layout::LayoutCode),
    /// Errors from the lifetime / loan-conflict check
    /// (see `lifetime::LifetimeCode`).
    Lifetime(crate::mir::lifetime::LifetimeCode),
    /// Warnings from the block-reachability pass
    /// (see `block_reachability::BlockReachabilityCode`).
    BlockReachability(crate::mir::block_reachability::BlockReachabilityCode),
    /// Errors from the MIR parser — surface syntax errors from the
    /// tree-sitter ERROR/MISSING walker, plus CST-to-AST invariant
    /// failures and literal decode errors (see `parser::ParserCode`).
    Parser(crate::mir::parser::ParserCode),
    /// Errors from HLL type-checking (`hll::type_check::HllTypeCheckCode`).
    HllTypeCheck(crate::hll::type_check::HllTypeCheckCode),
    /// Errors from HLL mutability checking (`hll::mut_check::HllMutCheckCode`).
    HllMutCheck(crate::hll::mut_check::HllMutCheckCode),
    /// Errors from HLL → MIR lowering (`hll::lowering::HllLoweringCode`).
    HllLowering(crate::hll::lowering::HllLoweringCode),
}

impl DiagCode {
    pub fn tag(&self) -> String {
        match self {
            DiagCode::TypeCheck(c) => format!("TC-{:?}", c),
            DiagCode::InitState(c) => format!("INIT-{:?}", c),
            DiagCode::VariantFlow(c) => format!("VF-{:?}", c),
            DiagCode::SubstructuralCheck(c) => format!("SUB-{:?}", c),
            DiagCode::SubstructuralComposition(c) => format!("COMP-{:?}", c),
            DiagCode::Layout(c) => format!("LAY-{:?}", c),
            DiagCode::Lifetime(c) => format!("LT-{:?}", c),
            DiagCode::BlockReachability(c) => format!("REACH-{:?}", c),
            DiagCode::Parser(c) => format!("PARSE-{:?}", c),
            DiagCode::HllTypeCheck(c) => format!("HTC-{:?}", c),
            DiagCode::HllMutCheck(c) => format!("HMC-{:?}", c),
            DiagCode::HllLowering(c) => format!("HLO-{:?}", c),
        }
    }
}

/// A single compiler diagnostic (error or warning). The container in
/// [`Diagnostics`] determines severity; this struct is the shared shape.
///
/// **Construct with [`Diagnostic::new`]** and chain optional setters:
///
/// ```ignore
/// Diagnostic::new(TypeCheckCode::NoEntryBlock, span, "no entry block")
///     .in_function(&func.name)
///     .in_block(&block.label)
/// ```
///
/// Fields are private. Read via the accessor methods; write only via
/// construction / builder chain. Keeps the struct extension-safe:
/// new optional fields need only a setter, no existing site changes.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    code: DiagCode,
    span: Span,
    function: String,
    block: String,
    message: String,
    hint: String,
    /// Related spans with human labels. Each entry becomes a snippet
    /// block after the primary snippet in [`Diagnostics::render_diagnostic`],
    /// prefixed by the label (rustc-style "borrow of x occurs here" et al).
    /// Empty for existing emission sites — infra is opt-in per site.
    secondary: Vec<(Span, String)>,
}

impl Diagnostic {
    /// Build a diagnostic with the three required fields: code, span,
    /// and message. Add optional context via [`in_function`] and
    /// [`in_block`]. `code` accepts anything that converts into a
    /// `DiagCode`, so per-pass code enums can be passed directly
    /// (e.g., `Diagnostic::new(TypeCheckCode::NoEntryBlock, span, msg)`).
    ///
    /// A span is required because every diagnostic needs a source
    /// location — that's what makes it addressable in editors, LSP,
    /// and error output. Callers that don't have a span at
    /// construction time should build closer to the error site.
    pub fn new(code: impl Into<DiagCode>, span: Span, message: impl Into<String>) -> Self {
        Diagnostic {
            code: code.into(),
            span,
            function: String::new(),
            block: String::new(),
            message: message.into(),
            hint: String::new(),
            secondary: Vec::new(),
        }
    }

    /// Attach an enclosing function name.
    pub fn in_function(mut self, name: impl Into<String>) -> Self {
        self.function = name.into();
        self
    }

    /// Attach an enclosing basic-block label.
    pub fn in_block(mut self, label: impl Into<String>) -> Self {
        self.block = label.into();
        self
    }

    /// Attach a hint to suggest how to fix the diagnostic.
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hint = hint.into();
        self
    }

    /// Attach a related labeled span (e.g., "borrow occurs here",
    /// "expected because of this signature"). Rendered after the
    /// primary snippet in emission order.
    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondary.push((span, label.into()));
        self
    }

    // Read-only accessors. Kept minimal until a specific pass needs
    // more (e.g., LSP mapping will want `span()` and `code()`).

    pub fn code(&self) -> DiagCode {
        self.code
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn hint(&self) -> &str {
        &self.hint
    }
}


/// Which surface language the diagnostics apply to. Controls
/// user-facing rendering choices — HLL users don't know about MIR
/// concepts like basic blocks, so those get suppressed for `Hll`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SourceKind {
    /// MIR source (`.sim`). Show all context including block labels.
    #[default]
    Mir,
    /// HLL source (`.si`). Suppress MIR-only context (block labels).
    Hll,
}

/// Collected errors and warnings for a single compilation.
///
/// Fields are private. All access goes through methods so we can
/// change the internal representation (add source-file tracking,
/// deduplicate, batch by pass, etc.) without a whole-tree edit.
#[derive(Debug, Default)]
pub struct Diagnostics {
    errors: Vec<Diagnostic>,
    warnings: Vec<Diagnostic>,
    /// Internal compiler errors — invariant violations, "should've been
    /// caught by an earlier pass," unreachable branches. Distinct from
    /// user-facing errors so we can render them with a bug-report
    /// preamble and route them differently in the CLI.
    internal_errors: Vec<Diagnostic>,
    source: Option<std::sync::Arc<String>>,
    source_kind: SourceKind,
}

impl Diagnostics {
    /// Build diagnostics container associated with a source code.
    pub fn with_source(mut self, source: std::sync::Arc<String>) -> Self {
        self.source = Some(source);
        self
    }

    /// Set the surface language. Defaults to `Mir`; HLL compilations
    /// should set `Hll` so MIR-only context (block labels) is hidden.
    pub fn with_source_kind(mut self, kind: SourceKind) -> Self {
        self.source_kind = kind;
        self
    }

    /// Append an error.
    pub fn push_error(&mut self, diagnostic: Diagnostic) {
        self.errors.push(diagnostic);
    }

    /// Append a warning.
    pub fn push_warning(&mut self, diagnostic: Diagnostic) {
        self.warnings.push(diagnostic);
    }

    /// Append an internal compiler error. Use for invariant violations
    /// and cases that should have been rejected by an earlier pass —
    /// user code cannot trigger these; if one fires, it's a compiler
    /// bug.
    pub fn push_internal_error(&mut self, diagnostic: Diagnostic) {
        self.internal_errors.push(diagnostic);
    }

    /// Append every diagnostic from `other` as errors. Used by
    /// `run_all_passes` to fold in `Env::build`'s pre-typecheck
    /// errors.
    pub fn extend_errors(&mut self, other: impl IntoIterator<Item = Diagnostic>) {
        self.errors.extend(other);
    }

    /// Keep only errors matching `f`; drop the rest. Emission sites
    /// use this to dedupe when a later, more accurate diagnostic
    /// supersedes an earlier one (e.g., a Write conflict replacing a
    /// drop-elab-inserted Move conflict at the same span).
    pub fn retain_errors(&mut self, f: impl FnMut(&Diagnostic) -> bool) {
        self.errors.retain(f);
    }

    /// True if no errors OR internal errors have been recorded.
    /// Warnings are ignored.
    pub fn is_clean(&self) -> bool {
        self.errors.is_empty() && self.internal_errors.is_empty()
    }

    /// True if any error (user or internal) has been recorded.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty() || !self.internal_errors.is_empty()
    }

    /// Number of recorded user errors.
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Number of recorded warnings.
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Number of recorded internal errors.
    pub fn internal_error_count(&self) -> usize {
        self.internal_errors.len()
    }

    /// Iterate structured user errors.
    pub fn errors(&self) -> impl Iterator<Item = &Diagnostic> {
        self.errors.iter()
    }

    /// Iterate structured warnings.
    pub fn warnings(&self) -> impl Iterator<Item = &Diagnostic> {
        self.warnings.iter()
    }

    /// Iterate structured internal errors.
    pub fn internal_errors(&self) -> impl Iterator<Item = &Diagnostic> {
        self.internal_errors.iter()
    }

    /// String view of `errors`, one preformatted line per diagnostic
    /// in the same format the old `Vec<String>` container produced.
    /// Used by the test harness so existing `assert_errors_contain`
    /// assertions keep matching.
    pub fn errors_str(&self) -> Vec<String> {
        self.errors.iter().map(|d| self.render_diagnostic(d)).collect()
    }

    /// String view of `warnings`. Mirrors [`errors_str`].
    pub fn warnings_str(&self) -> Vec<String> {
        self.warnings.iter().map(|d| self.render_diagnostic(d)).collect()
    }

    /// String view of `internal_errors`. Mirrors [`errors_str`].
    pub fn internal_errors_str(&self) -> Vec<String> {
        self.internal_errors.iter().map(|d| self.render_diagnostic(d)).collect()
    }

    fn render_diagnostic(&self, d: &Diagnostic) -> String {
        let mut out = String::new();
        let has_pos = d.span.line != 0 || d.span.col != 0;
        if has_pos {
            out.push_str(&format!("at {}: ", d.span));
        }
        out.push_str(&format!("[{}] ", d.code.tag()));
        let show_block = self.source_kind == SourceKind::Mir;
        if !d.function.is_empty() {
            if !d.block.is_empty() && show_block {
                out.push_str(&format!("In function '{}', block '{}': ", d.function, d.block));
            } else {
                out.push_str(&format!("In function '{}': ", d.function));
            }
        }
        out.push_str(&d.message);

        // Gutter width = digits in the largest line number across
        // primary + secondaries, so every snippet in this diagnostic
        // aligns to the same column. Line numbers make each snippet
        // navigable to a specific location; a shared width keeps the
        // stack readable when notes reference lines far from primary.
        let max_line = std::iter::once(d.span.line)
            .chain(d.secondary.iter().map(|(s, _)| s.line))
            .max()
            .unwrap_or(0);
        let gutter_width = max_line.to_string().len();

        if has_pos {
            if let Some(snippet) = self.render_snippet(d.span, gutter_width) {
                out.push_str(&snippet);
            }
        }

        for (span, label) in &d.secondary {
            out.push_str(&format!("\n  = note: {}", label));
            if let Some(snippet) = self.render_snippet(*span, gutter_width) {
                out.push_str(&snippet);
            }
        }

        if !d.hint.is_empty() {
            out.push_str(&format!("\n  hint: {}", d.hint));
        }

        out
    }

    /// Format one source-snippet block with a numbered gutter:
    ///
    /// ```text
    ///    |
    ///  4 | source line
    ///    | ^^^
    /// ```
    ///
    /// `gutter_width` is the number of digits reserved for the line
    /// number; caller should pass the max width across all spans in
    /// the diagnostic so blocks align. Returns `None` when there's no
    /// source arc or the span lies outside it.
    fn render_snippet(&self, span: Span, gutter_width: usize) -> Option<String> {
        let source = self.source.as_ref()?;
        let lines: Vec<&str> = source.lines().collect();
        let line_idx = (span.line as usize).saturating_sub(1);
        if line_idx >= lines.len() {
            return None;
        }
        let line_str = lines[line_idx];
        let start_col = span.col as usize;
        let end_col = if span.end_line == span.line && span.end_col > span.col {
            span.end_col as usize
        } else {
            start_col + 1
        };
        let mut caret_line = String::new();
        for c in line_str.chars().take(start_col.saturating_sub(1)) {
            caret_line.push(if c == '\t' { '\t' } else { ' ' });
        }
        let count = end_col.saturating_sub(start_col).max(1);
        for _ in 0..count {
            caret_line.push('^');
        }
        let blank = format!(" {:>w$} |", "", w = gutter_width);
        let numbered = format!(" {:>w$} | {}", span.line, line_str, w = gutter_width);
        let caret = format!(" {:>w$} | {}", "", caret_line, w = gutter_width);
        Some(format!("\n{}\n{}\n{}", blank, numbered, caret))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::type_check::TypeCheckCode;

    fn span(line: u32, col: u32, end_col: u32) -> Span {
        Span { line, col, end_line: line, end_col }
    }

    #[test]
    fn secondary_spans_render_as_notes_with_snippets() {
        let source = std::sync::Arc::new(
            "line one\nsecond line here\nthird line goes here\n".to_string(),
        );
        let d = Diagnostic::new(
            TypeCheckCode::AssignmentTypeMismatch,
            span(2, 8, 12),
            "primary problem",
        )
        .with_secondary(span(1, 6, 9), "related thing over here")
        .with_secondary(span(3, 7, 11), "another related thing");
        let mut ds = Diagnostics::default().with_source(source);
        ds.push_error(d);

        let expected = "\
at 2:8: [TC-AssignmentTypeMismatch] primary problem
   |
 2 | second line here
   |        ^^^^
  = note: related thing over here
   |
 1 | line one
   |      ^^^
  = note: another related thing
   |
 3 | third line goes here
   |       ^^^^";
        assert_eq!(ds.errors_str()[0], expected);
    }

    #[test]
    fn internal_errors_are_separate_from_user_errors() {
        let mut ds = Diagnostics::default();
        ds.push_error(Diagnostic::new(
            TypeCheckCode::AssignmentTypeMismatch,
            Span::default(),
            "user error",
        ));
        ds.push_internal_error(Diagnostic::new(
            crate::hll::lowering::HllLoweringCode::MissingType,
            Span::default(),
            "internal boom",
        ));

        // Distinct buckets, distinct counters.
        assert_eq!(ds.error_count(), 1);
        assert_eq!(ds.internal_error_count(), 1);

        // Neither is-clean nor has-errors ignores internal errors.
        assert!(!ds.is_clean());
        assert!(ds.has_errors());

        // Each bucket renders through its own accessor.
        let errs = ds.errors_str();
        let internals = ds.internal_errors_str();
        assert_eq!(errs.len(), 1);
        assert_eq!(internals.len(), 1);
        assert!(errs[0].contains("user error"));
        assert!(internals[0].contains("[HLO-MissingType]"));
        assert!(internals[0].contains("internal boom"));
    }

    #[test]
    fn hll_source_kind_suppresses_block_context() {
        let d = Diagnostic::new(
            TypeCheckCode::AssignmentTypeMismatch,
            Span::default(),
            "msg",
        )
        .in_function("f")
        .in_block("entry");
        let mut ds = Diagnostics::default().with_source_kind(SourceKind::Hll);
        ds.push_error(d);
        let rendered = &ds.errors_str()[0];
        assert!(
            rendered.contains("In function 'f':"),
            "expected block suppressed for HLL, got: {}",
            rendered
        );
        assert!(
            !rendered.contains("block"),
            "block context should not appear for HLL, got: {}",
            rendered
        );
    }
}
