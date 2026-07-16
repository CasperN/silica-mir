use silica_mir::{
    diagnostics::{self, Diagnostics},
    elaborate_and_check_mir, lower_hll_to_mir, mir,
};

const USAGE: &str = "Usage: silica-mir [--llvm] <file.si | file.sim>";

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut emit_llvm = false;
    let mut path: Option<&str> = None;
    for a in &args[1..] {
        if a == "--llvm" {
            emit_llvm = true;
        } else if path.is_none() {
            path = Some(a.as_str());
        } else {
            eprintln!("Unexpected extra argument: {}", a);
            std::process::exit(1);
        }
    }
    let Some(path) = path else {
        eprintln!("{}", USAGE);
        std::process::exit(1);
    };

    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read file '{}': {}", path, e);
            std::process::exit(1);
        }
    };

    // Route by file extension. `.si` (HLL) also runs the HLL frontend
    // before the MIR pipeline; `.sim` (MIR) skips straight to it.
    let source_kind = match std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
    {
        Some("sim") => diagnostics::SourceKind::Mir,
        Some("si") => diagnostics::SourceKind::Hll,
        other => {
            eprintln!(
                "Unknown file extension: {:?}. Expected `.si` (HLL) or `.sim` (MIR).",
                other
            );
            std::process::exit(1);
        }
    };

    // Pre-populate the source arc on `d` so error rendering can
    // produce snippets even if parsing itself fails (the parser
    // returns a Diagnostics without our source arc otherwise).
    let source_arc = std::sync::Arc::new(source);
    let mut d = Diagnostics::default()
        .with_source(source_arc.clone())
        .with_source_kind(source_kind);

    let program = match source_kind {
        diagnostics::SourceKind::Hll => lower_hll_to_mir(&source_arc, &mut d),
        diagnostics::SourceKind::Mir => match mir::parser::Parser::new(&**source_arc).parse() {
            Ok(p) => Some(p),
            Err(diags) => {
                d.extend_errors(diags.errors().cloned());
                None
            }
        },
    };
    let Some(program) = program else {
        report_and_exit(&d);
    };

    let (elaborated, env) = elaborate_and_check_mir(&program, &mut d);

    if d.has_errors() {
        report_and_exit(&d);
    }
    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }

    if d.warning_count() > 0 {
        eprintln!("({} warning(s))", d.warning_count());
    }

    if emit_llvm {
        print!("{}", mir::codegen::lower_mir_to_llvm(&elaborated, &env));
    } else {
        print!("{}", mir::pretty_print::pretty_print(&elaborated));
    }
}

fn report_and_exit(d: &Diagnostics) -> ! {
    for e in d.errors_str() {
        eprintln!("Error: {}", e);
    }
    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }
    if d.internal_error_count() > 0 {
        eprintln!();
        eprintln!("!!! Internal compiler error(s) — please file a bug !!!");
        for e in d.internal_errors_str() {
            eprintln!("Internal: {}", e);
        }
    }
    eprintln!(
        "{} error(s), {} warning(s), {} internal error(s)",
        d.error_count(),
        d.warning_count(),
        d.internal_error_count(),
    );
    std::process::exit(1);
}

// End-to-end diagnostic-rendering tests live in the library
// (src/lib.rs) so they can call the pipeline entry points directly.
