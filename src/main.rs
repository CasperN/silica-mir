pub mod mir;
pub use mir::ast;
pub use mir::type_check;
pub use mir::init_state;
pub use mir::lifetime;
pub use mir::substructural;
pub use mir::codegen;
pub use mir::pretty_print;
pub use mir::parser;
pub use mir::intrinsics;
pub use mir::layout;
pub use mir::variant_flow;
pub use mir::block_reachability;
pub use mir::dataflow;
pub use mir::cfg_edit;

#[cfg(test)]
pub use mir::test_util;

pub mod hll;
mod diagnostics;

use mir::ast::Program;
use diagnostics::Diagnostics;

// TODO: Hoist the HLL passes and MIR passes into their own functions, possibly living in their
// respective modules.

/// Run every post-parse pass against `program` and return both the
/// elaborated MIR and the collected diagnostics.
///
/// Pipeline:
///   1. Pre-elab: `type_check`, `substructural::composition`, `layout`,
///      `substructural::check::check_statements`, `variant_flow`,
///      `block_reachability`, `init_state`.
///   2. If step 1 found errors, bail before elaboration (a broken program's
///      init state is unreliable, so elaboration would be unsound).
///   3. Elaboration, in order:
///      - `lifetime::nll::elaborate` inserts `unborrow` at NLL
///        last-use points.
///      - `substructural::drop_elaboration::elaborate` inserts drops
///        for values still alive at return.
///      Env is resynced between the two so drop-elab sees the post-NLL
///      init state (borrowers now consumed at their last-use points).
///   4. Post-elab: `substructural::check::check_return_leaks` and
///      `lifetime::check_program` validate the elaborated MIR. Lifetime
///      is position-dependent, so it belongs on the elaborated form
///      where every loan-closing point is explicit.
///
/// Used by `main` and by test helpers.
pub fn run_hll_pipeline(source: &str) -> (Option<Program>, Option<mir::type_check::Env>, Diagnostics) {
    let source_arc = std::sync::Arc::new(source.to_string());
    let mut d = Diagnostics::default()
        .with_source(source_arc.clone())
        .with_source_kind(diagnostics::SourceKind::Hll);
    
    // 1. Parse HLL
    let hll_prog = match hll::parser::Parser::new(source.to_string()).parse() {
        Ok(prog) => prog,
        Err(diags) => {
            d.extend_errors(diags.errors().cloned());
            return (None, None, d);
        }
    };
    
    // 2. Type-check HLL
    let types = match hll::type_check::typecheck_program_collect(&hll_prog) {
        Ok(t) => t,
        Err(e) => {
            d.push_error(diagnostics::Diagnostic::new(mir::type_check::TypeCheckCode::AssignmentTypeMismatch, mir::ast::Span::default(), e));
            return (None, None, d);
        }
    };
    
    // 3. Mutability-check HLL
    if let Err(e) = hll::mut_check::check_mutability(&hll_prog) {
        d.push_error(diagnostics::Diagnostic::new(mir::type_check::TypeCheckCode::AssignmentTypeMismatch, mir::ast::Span::default(), e));
        return (None, None, d);
    }
    
    // 4. Lower to MIR
    let mir_program = match hll::lowering::lower_program(&hll_prog, &types) {
        Ok(p) => p,
        Err(e) => {
            d.push_error(diagnostics::Diagnostic::new(mir::type_check::TypeCheckCode::AssignmentTypeMismatch, mir::ast::Span::default(), e));
            return (None, None, d);
        }
    };
    
    // 5. Run all MIR passes
    let (elaborated, env, mir_diags) = run_all_passes(&mir_program);
    d.extend_errors(mir_diags.errors().cloned());
    (Some(elaborated), Some(env), d)
}

/// Run every post-parse pass against `program` and return both the
/// elaborated MIR and the collected diagnostics.
pub fn run_all_passes(program: &Program) -> (Program, mir::type_check::Env, Diagnostics) {
    let mut d = Diagnostics::default().with_source(program.source.clone());
    let (mut env, env_errs) = mir::type_check::Env::build(program);
    d.extend_errors(env_errs);
    env.typecheck(&mut d);
    mir::substructural::composition::check_program(&env, &mut d);
    mir::layout::check_sizes_finite(&env, &mut d);
    mir::substructural::check::check_statements(&env, &mut d);
    mir::variant_flow::check_program(&env, &mut d);
    mir::block_reachability::check_program(&env, &mut d);
    mir::init_state::check_program(&env, &mut d);

    if d.has_errors() {
        return (program.clone(), env, d);
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
    mir::init_state::check_program(&env, &mut d);
    mir::substructural::check::check_return_leaks(&env, &mut d);
    mir::lifetime::check_program(&env, &mut d);

    (elaborated, env, d)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} [--llvm] <file.silica>", args[0]);
        std::process::exit(1);
    }

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
        eprintln!("Usage: {} [--llvm] <file.silica>", args[0]);
        std::process::exit(1);
    };

    let source = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Failed to read file '{}': {}", path, e);
            std::process::exit(1);
        }
    };

    // Route by file extension:
    //   `.sim` → MIR directly.
    //   `.si`  → HLL, parse then lower to MIR.
    // Anything else is rejected; ambiguity here would hide user
    // errors under the wrong pipeline.
    let (elaborated, env, d) = match std::path::Path::new(path)
        .extension()
        .and_then(|e| e.to_str())
    {
        Some("sim") => {
            let p = mir::parser::Parser::new(source);
            let program = match p.parse() {
                Ok(program) => program,
                Err(diags) => {
                    for e in diags.errors_str() {
                        eprintln!("Error: {}", e);
                    }
                    eprintln!("{} error(s)", diags.error_count());
                    std::process::exit(1);
                }
            };
            eprintln!("AST parsed successfully.");
            run_all_passes(&program)
        }
        Some("si") => {
            let (elaborated_opt, env_opt, d) = run_hll_pipeline(&source);
            let (Some(elaborated), Some(env)) = (elaborated_opt, env_opt) else {
                for e in d.errors_str() {
                    eprintln!("Error: {}", e);
                }
                eprintln!("{} error(s)", d.error_count());
                std::process::exit(1);
            };
            eprintln!("AST parsed successfully.");
            (elaborated, env, d)
        }
        other => {
            eprintln!(
                "Unknown file extension: {:?}. Expected `.si` (HLL) or `.sim` (MIR).",
                other
            );
            std::process::exit(1);
        }
    };

    for w in d.warnings_str() {
        eprintln!("Warning: {}", w);
    }

    if d.has_errors() {
        for e in d.errors_str() {
            eprintln!("Error: {}", e);
        }
        eprintln!(
            "{} error(s), {} warning(s)",
            d.error_count(),
            d.warning_count()
        );
        std::process::exit(1);
    }

    eprintln!("Type checking successful!");
    if d.warning_count() > 0 {
        eprintln!("({} warning(s))", d.warning_count());
    }

    if emit_llvm {
        print!("{}", mir::codegen::generate_llvm(&elaborated, &env));
    } else {
        print!("{}", mir::pretty_print::pretty_print(&elaborated));
    }
}

#[cfg(test)]
mod error_display_tests;
