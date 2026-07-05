//! Shared diagnostic container for analysis passes. Every pass takes a
//! `&mut Diagnostics` and pushes into `errors` / `warnings` directly.
//!
//! `push_error!` / `push_warning!` macros abstract the ubiquitous
//! `at L:C: In function 'f', block 'b': <msg>` prefix.

#[derive(Debug, Default)]
pub struct Diagnostics {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

/// Format a diagnostic string with `at <span>: In function '<f>', block '<b>':`
/// prefix — for use where the caller already has an owned `String` sink
/// (e.g. inside a `.map_err(|e| ...)` closure).
#[macro_export]
macro_rules! fmt_error {
    ($span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {
        format!(
            "at {}: In function '{}', block '{}': {}",
            $span,
            $func.name,
            $block.label,
            format_args!($($fmt)*)
        )
    };
}

/// Push an error formatted with `at <span>: In function '<f>', block '<b>':`
/// prefix into `d.errors`.
#[macro_export]
macro_rules! push_error {
    ($d:expr, $span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {{
        $d.errors.push($crate::fmt_error!($span, $func, $block, $($fmt)*));
    }};
}

/// Push a warning with the same prefix as `push_error!` into `d.warnings`.
#[macro_export]
macro_rules! push_warning {
    ($d:expr, $span:expr, $func:expr, $block:expr, $($fmt:tt)*) => {{
        $d.warnings.push($crate::fmt_error!($span, $func, $block, $($fmt)*));
    }};
}
