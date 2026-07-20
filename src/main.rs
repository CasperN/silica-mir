use silica_mir::{
    diagnostics::{self, Diagnostics},
    elaborate_and_check_mir, lower_hll_to_mir, mir,
};

const USAGE: &str = "Usage: silica-mir [--emit=<mir|pre-elab-mir|llvm>] <file.si | file.sim>";

#[derive(Clone, Copy)]
enum EmitKind {
    /// Post-elaboration MIR (default). Runs the full checker pipeline.
    Mir,
    /// Pre-elaboration MIR. Skips the checker pipeline — useful for
    /// isolating HLL-lowering output from downstream pass errors.
    PreElabMir,
    /// Textual LLVM IR. Runs the full pipeline and codegen.
    Llvm,
}

fn parse_emit(s: &str) -> Option<EmitKind> {
    match s {
        "mir" => Some(EmitKind::Mir),
        "pre-elab-mir" => Some(EmitKind::PreElabMir),
        "llvm" => Some(EmitKind::Llvm),
        _ => None,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut emit = EmitKind::Mir;
    let mut path: Option<&str> = None;
    for a in &args[1..] {
        if let Some(rest) = a.strip_prefix("--emit=") {
            match parse_emit(rest) {
                Some(k) => emit = k,
                None => {
                    eprintln!(
                        "Unknown --emit value '{}'. Expected one of: mir, pre-elab-mir, llvm.",
                        rest,
                    );
                    std::process::exit(1);
                }
            }
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

    if matches!(emit, EmitKind::PreElabMir) {
        print!("{}", mir::pretty_print::pretty_print(&program));
        return;
    }

    let (elaborated, _env) = elaborate_and_check_mir(program, &mut d);

    if d.has_errors() {
        report_and_exit(&d);
    }
    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }
    for i in d.infos_str() {
        eprintln!("Note: {}", i);
    }

    if d.warning_count() > 0 || d.info_count() > 0 {
        eprintln!("({} warning(s), {} note(s))", d.warning_count(), d.info_count());
    }
    match emit {
        EmitKind::Llvm => {
            print!("{}", mir::codegen::lower_mir_to_llvm(elaborated));
        }
        EmitKind::Mir => print!("{}", mir::pretty_print::pretty_print(&elaborated)),
        EmitKind::PreElabMir => unreachable!("handled above"),
    }
}

fn report_and_exit(d: &Diagnostics) -> ! {
    for e in d.errors_str() {
        eprintln!("Error: {}", e);
    }
    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }
    for i in d.infos_str() {
        eprintln!("Note: {}", i);
    }
    if d.internal_error_count() > 0 {
        eprintln!();
        eprintln!("!!! Internal compiler error(s) — please file a bug !!!");
        for e in d.internal_errors_str() {
            eprintln!("Internal: {}", e);
        }
    }
    eprintln!(
        "{} error(s), {} warning(s), {} note(s), {} internal error(s)",
        d.error_count(),
        d.warning_count(),
        d.info_count(),
        d.internal_error_count(),
    );
    std::process::exit(1);
}

// End-to-end diagnostic-rendering tests live in the library
// (src/lib.rs) so they can call the pipeline entry points directly.
