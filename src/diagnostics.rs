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
//! sub-enums (see `type_check::TypeCheckCode`) and are dispatched by
//! one variant here per pass. `DiagCode::Unspecified` is a migration
//! placeholder for call sites that haven't been assigned a specific
//! code yet.
//!
//! **String view**: `Diagnostic` implements `Display` in the format
//! `at L:C: In function 'f', block 'b': msg`. `Diagnostics::
//! errors_str()` produces `Vec<String>` for tests that still assert
//! on substring content.

use crate::ast::Span;

/// Machine-readable error kind. New variants added over time as
/// `push_error!` sites are migrated from ad-hoc strings to specific
/// codes. The default `Unspecified` covers all unmigrated call sites.
///
/// Per-pass sub-enums live in each pass's own file (e.g.
/// `type_check::TypeCheckCode`) and are dispatched by one variant
/// here per pass. Adding a new code within a pass is a one-line
/// change in that pass; `diagnostics.rs` only changes when a new
/// pass is added.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum DiagCode {
    /// Sentinel for call sites that haven't been assigned a specific
    /// code yet. Replace with a dedicated variant during migration.
    #[default]
    Unspecified,
    /// Errors from the type checker (see `type_check::TypeCheckCode`).
    TypeCheck(crate::type_check::TypeCheckCode),
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
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Omit `at L:C:` when the span is `(0, 0)` — the default —
        // since that means "no source location". Real diagnostics
        // always pass a real span through `Diagnostic::new`.
        let has_pos = self.span.line != 0 || self.span.col != 0;
        if has_pos {
            write!(f, "at {}: ", self.span)?;
        }
        if !self.function.is_empty() {
            if !self.block.is_empty() {
                write!(f, "In function '{}', block '{}': ", self.function, self.block)?;
            } else {
                write!(f, "In function '{}': ", self.function)?;
            }
        }
        // Block-only (function empty) is treated as no context —
        // block labels are only meaningful relative to a function.
        write!(f, "{}", self.message)
    }
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
}

impl Diagnostics {
    /// Append an error. Used by [`push_error!`] and by any pass that
    /// has already constructed a `Diagnostic`.
    pub fn push_error(&mut self, diagnostic: Diagnostic) {
        self.errors.push(diagnostic);
    }

    /// Append a warning. Used by [`push_warning!`] and by callers
    /// with a prebuilt `Diagnostic`.
    pub fn push_warning(&mut self, diagnostic: Diagnostic) {
        self.warnings.push(diagnostic);
    }

    /// Append every diagnostic from `other` as errors. Used by
    /// `run_all_passes` to fold in `Env::build`'s pre-typecheck
    /// errors.
    pub fn extend_errors(&mut self, other: impl IntoIterator<Item = Diagnostic>) {
        self.errors.extend(other);
    }

    /// True if no errors have been recorded. Warnings are ignored.
    pub fn is_clean(&self) -> bool {
        self.errors.is_empty()
    }

    /// True if any error has been recorded.
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Number of recorded errors.
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Number of recorded warnings.
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Iterate structured errors.
    pub fn errors(&self) -> impl Iterator<Item = &Diagnostic> {
        self.errors.iter()
    }

    /// Iterate structured warnings.
    pub fn warnings(&self) -> impl Iterator<Item = &Diagnostic> {
        self.warnings.iter()
    }

    /// String view of `errors`, one preformatted line per diagnostic
    /// in the same format the old `Vec<String>` container produced.
    /// Used by the test harness so existing `assert_errors_contain`
    /// assertions keep matching.
    pub fn errors_str(&self) -> Vec<String> {
        self.errors.iter().map(|d| d.to_string()).collect()
    }

    /// String view of `warnings`. Mirrors [`errors_str`].
    pub fn warnings_str(&self) -> Vec<String> {
        self.warnings.iter().map(|d| d.to_string()).collect()
    }
}

/// Build a `Diagnostic` with the standard `at L:C: In function 'f',
/// block 'b': ...` shape. Used inside `push_error!` and `push_warning!`
/// and also by any pass that needs to construct a diagnostic for a
/// `Result<_, Diagnostic>` return.
///
/// The code defaults to `DiagCode::Unspecified` — replace via a
/// dedicated variant when migrating a specific call site.
#[macro_export]
macro_rules! fmt_error {
    ($span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {
        $crate::diagnostics::Diagnostic::new(
            $crate::diagnostics::DiagCode::Unspecified,
            $span,
            format!($($fmt)*),
        )
        .in_function(&$func.name)
        .in_block(&$block.label)
    };
}


/// Push an error with the standard `at L:C: In function 'f', block 'b':`
/// prefix into `d`.
#[macro_export]
macro_rules! push_error {
    ($d:expr, $span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {{
        $d.push_error($crate::fmt_error!($span, $func, $block, $($fmt)*));
    }};
}


/// Push an error with just a span (no function/block context) into
/// `d`. Used at declaration scope — before we have a Function or
/// BasicBlock to attribute the error to (duplicate types, malformed
/// struct fields, function-signature checks, etc.).
#[macro_export]
macro_rules! push_error_at {
    ($d:expr, $span:expr, $($fmt:tt)*) => {{
        $d.push_error(
            $crate::diagnostics::Diagnostic::new(
                $crate::diagnostics::DiagCode::Unspecified,
                $span,
                format!($($fmt)*),
            )
        );
    }};
}


/// Push a warning with the same prefix as `push_error!` into `d`.
#[macro_export]
macro_rules! push_warning {
    ($d:expr, $span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {{
        $d.push_warning($crate::fmt_error!($span, $func, $block, $($fmt)*));
    }};
}
