mod ast;
mod block_reachability;
mod cfg_edit;
mod codegen;
mod dataflow;
mod diagnostics;
mod init_state;
mod intrinsics;
mod layout;
mod lifetime;
mod parser;
mod pretty_print;
mod substructural;
mod type_check;
mod variant_flow;

#[cfg(test)]
mod raw_ptr_tests;
#[cfg(test)]
mod test_util;

use ast::Program;
use diagnostics::Diagnostics;

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
pub fn run_all_passes(program: &Program) -> (Program, type_check::Env, Diagnostics) {
    let mut d = Diagnostics::default();
    let (mut env, env_errs) = type_check::Env::build(program);
    d.errors.extend(env_errs);
    env.typecheck(&mut d);
    substructural::composition::check_program(&env, &mut d);
    layout::check_sizes_finite(&env, &mut d);
    substructural::check::check_statements(&env, &mut d);
    variant_flow::check_program(&env, &mut d);
    block_reachability::check_program(&env, &mut d);
    init_state::check_program(&env, &mut d);

    if !d.errors.is_empty() {
        return (program.clone(), env, d);
    }

    let mut elaborated = program.clone();

    // Elaboration passes mutate function bodies only; `types` never
    // changes. After each mutation, resync env's cached function bodies
    // so downstream passes see the up-to-date form.
    lifetime::nll::elaborate(&mut elaborated, &env);
    env.sync_functions(&elaborated);

    substructural::drop_elaboration::elaborate(&mut elaborated, &env);
    env.sync_functions(&elaborated);

    // Post-elab checks. init_state re-runs so NLL-inserted `unborrow r`
    // on an unfulfilled `&out`/`&drop` obligation surfaces its error at
    // the insertion site (via close_ref_if_present), not silently.
    init_state::check_program(&env, &mut d);
    substructural::check::check_return_leaks(&env, &mut d);
    lifetime::check_program(&env, &mut d);

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

    let p = parser::Parser::new(source);
    let program = match p.parse() {
        Ok(program) => program,
        Err(err) => {
            eprintln!("Parse error: {}", err);
            std::process::exit(1);
        }
    };

    eprintln!("AST parsed successfully.");

    let (elaborated, env, d) = run_all_passes(&program);

    for w in &d.warnings {
        eprintln!("Warning: {}", w);
    }

    if !d.errors.is_empty() {
        for e in &d.errors {
            eprintln!("Error: {}", e);
        }
        eprintln!(
            "{} error(s), {} warning(s)",
            d.errors.len(),
            d.warnings.len()
        );
        std::process::exit(1);
    }

    eprintln!("Type checking successful!");
    if !d.warnings.is_empty() {
        eprintln!("({} warning(s))", d.warnings.len());
    }

    if emit_llvm {
        print!("{}", codegen::generate_llvm(&elaborated, &env));
    } else {
        print!("{}", pretty_print::pretty_print(&elaborated));
    }
}
