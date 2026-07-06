mod ast;
mod block_reachability;
mod dataflow;
mod diagnostics;
mod init_state;
mod parser;
mod pretty_print;
mod substructural;
mod type_check;
mod variant_flow;

#[cfg(test)]
mod test_util;

use ast::Program;
use diagnostics::Diagnostics;

/// Run every post-parse pass against `program` and return both the
/// elaborated MIR and the collected diagnostics.
///
/// Pipeline:
///   1. `type_check`, `marker_composition`, per-statement `substructural_check`
///      class checks, `variant_flow`, `block_reachability`, `init_state`.
///   2. If step 1 found errors, bail before elaboration (a broken program's
///      init state is unreliable, so elaboration would be unsound).
///   3. `drop_elaboration::elaborate` inserts drops on the returned
///      program.
///   4. `substructural_check::check_return_leaks` validates the elaborated
///      MIR — surviving leaks indicate elaboration was insufficient (e.g.
///      Partial or Diverged states the current elaborator doesn't touch).
///
/// Used by `main` and by test helpers.
pub fn run_all_passes(program: &Program) -> (Program, Diagnostics) {
    let mut d = Diagnostics::default();
    let env = type_check::Env::build(program, &mut d);
    env.typecheck(&mut d);
    substructural::composition::check_program(&env, &mut d);
    substructural::check::check_program(&env, &mut d);
    variant_flow::check_program(&env, &mut d);
    block_reachability::check_program(&env, &mut d);
    init_state::check_program(&env, &mut d);

    if !d.errors.is_empty() {
        return (program.clone(), d);
    }

    let mut elaborated = program.clone();
    substructural::elaboration::elaborate(&mut elaborated, &env);

    // Re-build env from elaborated program (inserted drops introduce new
    // statements that init_state / leak check need to see accurately).
    let env2 = type_check::Env::build(&elaborated, &mut d);
    substructural::check::check_return_leaks(&env2, &mut d);

    (elaborated, d)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file.silica>", args[0]);
        std::process::exit(1);
    }

    let path = &args[1];
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

    println!("AST parsed successfully.");

    let (elaborated, d) = run_all_passes(&program);

    for w in &d.warnings {
        eprintln!("Warning: {}", w);
    }

    if !d.errors.is_empty() {
        for e in &d.errors {
            eprintln!("Error: {}", e);
        }
        eprintln!("{} error(s), {} warning(s)", d.errors.len(), d.warnings.len());
        std::process::exit(1);
    }

    println!("Type checking successful!");
    if !d.warnings.is_empty() {
        println!("({} warning(s))", d.warnings.len());
    }

    println!("\n=== Elaborated MIR ===");
    print!("{}", pretty_print::pretty_print(&elaborated));
}
