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
    /// `elaborate_and_check_mir` to fold in `Env::build`'s pre-typecheck
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

    /// Annotate all errors added at or after index `from` with the given
    /// function name. Used by callers that push errors into a shared
    /// `Diagnostics` container and then want to label the batch with the
    /// enclosing function context.
    pub fn annotate_errors_in_function(&mut self, from: usize, name: &str) {
        for d in &mut self.errors[from..] {
            if d.function.is_empty() {
                d.function = name.to_owned();
            }
        }
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

        // Gather all valid spans.
        struct GroupedSpan {
            span: Span,
            label: Option<String>,
            is_primary: bool,
        }

        let mut grouped_spans = Vec::new();
        if has_pos {
            grouped_spans.push(GroupedSpan {
                span: d.span,
                label: None,
                is_primary: true,
            });
        }
        for (span, label) in &d.secondary {
            if span.line != 0 || span.col != 0 {
                grouped_spans.push(GroupedSpan {
                    span: *span,
                    label: Some(label.clone()),
                    is_primary: false,
                });
            }
        }

        if !grouped_spans.is_empty() && self.source.is_some() {
            let source = self.source.as_ref().unwrap();
            let lines: Vec<&str> = source.lines().collect();

            // Sort spans by line and column.
            grouped_spans.sort_by(|a, b| {
                match a.span.line.cmp(&b.span.line) {
                    std::cmp::Ordering::Equal => a.span.col.cmp(&b.span.col),
                    ord => ord,
                }
            });

            // Group spans into contiguous blocks (gap <= 2 lines).
            let mut blocks: Vec<Vec<GroupedSpan>> = Vec::new();
            for gs in grouped_spans {
                if let Some(last_block) = blocks.last_mut() {
                    let last_span = last_block.last().unwrap().span;
                    if gs.span.line.saturating_sub(last_span.line) <= 3 {
                        last_block.push(gs);
                        continue;
                    }
                }
                blocks.push(vec![gs]);
            }

            // Gutter width = digits in the largest line number across
            // primary + secondaries.
            let max_line = std::iter::once(d.span.line)
                .chain(d.secondary.iter().map(|(s, _)| s.line))
                .max()
                .unwrap_or(0);
            let gutter_width = max_line.to_string().len();

            // Render each block.
            for (block_idx, block) in blocks.iter().enumerate() {
                if block_idx > 0 {
                    // Print a separator between blocks.
                    out.push_str(&format!("\n {:>w$} | ...", "", w = gutter_width));
                }

                // Block range with 1 line of context before and after.
                let min_line = block.iter().map(|gs| gs.span.line).min().unwrap();
                let max_line = block.iter().map(|gs| gs.span.line).max().unwrap();
                let start_line = min_line.saturating_sub(1).max(1);
                let end_line = (max_line + 1).min(lines.len() as u32);

                // Print block start padding.
                out.push_str(&format!("\n {:>w$} |", "", w = gutter_width));

                for line_num in start_line..=end_line {
                    let line_idx = (line_num - 1) as usize;
                    if line_idx >= lines.len() {
                        continue;
                    }
                    let line_str = lines[line_idx];
                    out.push_str(&format!("\n {:>w$} | {}", line_num, line_str, w = gutter_width));

                    // Check if this line contains any spans.
                    let spans_on_line: Vec<&GroupedSpan> = block.iter().filter(|gs| gs.span.line == line_num).collect();
                    if !spans_on_line.is_empty() {
                        // Find the max end column to size the caret buffer.
                        let mut max_end_col = 0;
                        for gs in &spans_on_line {
                            let start_col = gs.span.col as usize;
                            let end_col = if gs.span.end_line == gs.span.line && gs.span.end_col > gs.span.col {
                                gs.span.end_col as usize
                            } else {
                                start_col + 1
                            };
                            max_end_col = max_end_col.max(end_col);
                        }

                        // Build the caret characters buffer, mapping tabs properly.
                        let mut caret_chars: Vec<char> = Vec::new();
                        for (idx, c) in line_str.chars().enumerate() {
                            if idx >= max_end_col {
                                break;
                            }
                            if c == '\t' {
                                caret_chars.push('\t');
                            } else {
                                caret_chars.push(' ');
                            }
                        }
                        while caret_chars.len() < max_end_col {
                            caret_chars.push(' ');
                        }

                        // Underline the spans.
                        for gs in &spans_on_line {
                            let start_col = gs.span.col.saturating_sub(1) as usize;
                            let end_col = if gs.span.end_line == gs.span.line && gs.span.end_col > gs.span.col {
                                gs.span.end_col.saturating_sub(1) as usize
                            } else {
                                start_col + 1
                            };
                            let caret_char = if gs.is_primary { '^' } else { '-' };
                            for idx in start_col..end_col {
                                if idx < caret_chars.len() {
                                    if caret_chars[idx] == ' ' || caret_chars[idx] == '\t' || caret_char == '^' {
                                        caret_chars[idx] = caret_char;
                                    }
                                }
                            }
                        }

                        let caret_str: String = caret_chars.into_iter().collect();
                        let caret_str = caret_str.trim_end();
                        out.push_str(&format!("\n {:>w$} | {}", "", caret_str, w = gutter_width));

                        // Interleave/stack labels.
                        let labeled_spans: Vec<&GroupedSpan> = spans_on_line.iter().filter(|gs| gs.label.is_some()).cloned().collect();
                        if labeled_spans.len() == 1 {
                            // Single label: print next to the caret line.
                            let label = labeled_spans[0].label.as_ref().unwrap();
                            out.push_str(&format!(" {}", label));
                        } else if labeled_spans.len() > 1 {
                            // Multiple labels: print them stacked (right-to-left).
                            let mut labeled = labeled_spans.clone();
                            labeled.sort_by_key(|gs| gs.span.col);

                            for i in (0..labeled.len()).rev() {
                                let mut pointer_chars: Vec<char> = Vec::new();
                                let max_active_col = labeled[i].span.col.saturating_sub(1) as usize;
                                for (idx, c) in line_str.chars().enumerate() {
                                    if idx >= max_active_col {
                                        break;
                                    }
                                    if c == '\t' {
                                        pointer_chars.push('\t');
                                    } else {
                                        pointer_chars.push(' ');
                                    }
                                }
                                while pointer_chars.len() < max_active_col {
                                    pointer_chars.push(' ');
                                }

                                for j in 0..i {
                                    let col = labeled[j].span.col.saturating_sub(1) as usize;
                                    if col < pointer_chars.len() {
                                        pointer_chars[col] = '|';
                                    }
                                }

                                let pointer_prefix: String = pointer_chars.into_iter().collect();
                                let label = labeled[i].label.as_ref().unwrap();
                                out.push_str(&format!("\n {:>w$} | {}|-- {}", "", pointer_prefix, label, w = gutter_width));
                            }
                        }
                    }
                }

                // Block end padding.
                out.push_str(&format!("\n {:>w$} |", "", w = gutter_width));
            }
        }

        if !d.hint.is_empty() {
            out.push_str(&format!("\n  hint: {}", d.hint));
        }

        out
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
 1 | line one
   |      --- related thing over here
 2 | second line here
   |        ^^^^
 3 | third line goes here
   |       ---- another related thing
   |";
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
