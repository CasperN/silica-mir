pub mod mir;
pub mod hll;
mod diagnostics;

use mir::ast::Program;
use diagnostics::Diagnostics;

/// Run the HLL frontend (parse → typecheck → mutability check → lower)
/// and return the resulting MIR program. Errors are pushed into `d` and
/// `None` is returned; the caller decides whether to continue.
///
/// HLL passes currently return `Result<_, String>`; those strings are
/// wrapped in a `Diagnostic` with a placeholder code and a zero span.
/// Replacing this adapter with real HLL diagnostic codes is a follow-up
/// (see punchlist).
pub fn lower_hll_to_mir(source: &str, d: &mut Diagnostics) -> Option<Program> {
    let hll_prog = match hll::parser::Parser::new(source).parse() {
        Ok(prog) => prog,
        Err(diags) => {
            d.extend_errors(diags.errors().cloned());
            return None;
        }
    };
    let types = hll::type_check::typecheck_program_collect(&hll_prog)
        .map_err(|e| push_placeholder(d, e))
        .ok()?;
    hll::mut_check::check_mutability(&hll_prog)
        .map_err(|e| push_placeholder(d, e))
        .ok()?;
    hll::lowering::lower_program(&hll_prog, &types)
        .map_err(|e| push_placeholder(d, e))
        .ok()
}

/// Wrap a `String` HLL-pass error as a `Diagnostic`. Placeholder code
/// until HLL passes produce real diagnostics.
fn push_placeholder(d: &mut Diagnostics, msg: String) {
    d.push_error(diagnostics::Diagnostic::new(
        mir::type_check::TypeCheckCode::AssignmentTypeMismatch,
        mir::ast::Span::default(),
        msg,
    ));
}

/// Run every post-parse pass against `program`, pushing errors and
/// warnings into `d`. Returns the elaborated MIR and its type env.
/// Callers own the `Diagnostics` so they can pre-populate source /
/// source-kind context and merge parse-time diagnostics in the same
/// container.
pub fn run_all_passes(program: &Program, d: &mut Diagnostics) -> (Program, mir::type_check::Env) {
    let (mut env, env_errs) = mir::type_check::Env::build(program);
    d.extend_errors(env_errs);
    env.typecheck(d);
    mir::substructural::composition::check_program(&env, d);
    mir::layout::check_sizes_finite(&env, d);
    mir::substructural::check::check_statements(&env, d);
    mir::variant_flow::check_program(&env, d);
    mir::block_reachability::check_program(&env, d);
    mir::init_state::check_program(&env, d);

    if d.has_errors() {
        return (program.clone(), env);
    }

    let mut elaborated = program.clone();

    // Elaboration passes mutate function bodies only; `types` never
    // changes. After each mutation, resync env's cached function bodies
    // so downstream passes see the up-to-date form.
    mir::lifetime::nll::elaborate(&mut elaborated, &env);
    env.sync_functions(&elaborated);

    mir::substructural::drop_elaboration::elaborate(&mut elaborated, &env);
    env.sync_functions(&elaborated);

    // Post-elab checks. init_state re-runs so NLL-inserted `unborrow r`
    // on an unfulfilled `&out`/`&drop` obligation surfaces its error at
    // the insertion site (via close_ref_if_present), not silently.
    mir::init_state::check_program(&env, d);
    mir::substructural::check::check_return_leaks(&env, d);
    mir::lifetime::check_program(&env, d);

    (elaborated, env)
}

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
    eprintln!("AST parsed successfully.");

    let (elaborated, env) = run_all_passes(&program, &mut d);

    if d.has_errors() {
        report_and_exit(&d);
    }
    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }
    eprintln!("Type checking successful!");
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
    eprintln!(
        "{} error(s), {} warning(s)",
        d.error_count(),
        d.warning_count()
    );
    std::process::exit(1);
}

#[cfg(test)]
mod error_display_tests;
