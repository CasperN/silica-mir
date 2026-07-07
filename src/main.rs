mod ast;
mod block_reachability;
mod cfg_edit;
mod dataflow;
mod diagnostics;
mod init_state;
mod lifetime;
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
///   1. Pre-elab: `type_check`, `marker_composition`, per-statement
///      `substructural::check` class checks, `variant_flow`,
///      `block_reachability`, `init_state`.
///   2. If step 1 found errors, bail before elaboration (a broken program's
///      init state is unreliable, so elaboration would be unsound).
///   3. Elaboration, in order:
///      - `lifetime::elaboration::elaborate` inserts `unborrow` at NLL
///        last-use points.
///      - `substructural::elaboration::elaborate` inserts drops for
///        values still alive at return.
///      Env is rebuilt between the two so drop-elab sees the post-NLL
///      init state (borrowers now consumed at their last-use points).
///   4. Post-elab: `substructural::check::check_return_leaks` and
///      `lifetime::check_program` validate the elaborated MIR. Lifetime
///      is position-dependent, so it belongs on the elaborated form
///      where every loan-closing point is explicit.
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
    lifetime::elaboration::elaborate(&mut elaborated, &env);

    // Env rebuild #1: NLL added `unborrow` statements and possibly
    // split edges. Drop-elab reads init-state through env; it needs to
    // see the elaborated bodies.
    let env2 = type_check::Env::build(&elaborated, &mut d);
    substructural::elaboration::elaborate(&mut elaborated, &env2);

    // Env rebuild #2: drop-elab appended `drop` statements. Post-elab
    // checks read init state and loans from the final form.
    let env3 = type_check::Env::build(&elaborated, &mut d);
    // init_state re-run: NLL may have inserted `unborrow r` where the
    // pointee obligation isn't fulfilled (e.g. an `&out` never written
    // to). That triggers `close_ref_if_present`'s obligation error
    // at the insertion site — which we'd otherwise swallow silently
    // because check_return_leaks only sees state *after* unborrow ran.
    init_state::check_program(&env3, &mut d);
    substructural::check::check_return_leaks(&env3, &mut d);
    lifetime::check_program(&env3, &mut d);

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
        eprintln!(
            "{} error(s), {} warning(s)",
            d.errors.len(),
            d.warnings.len()
        );
        std::process::exit(1);
    }

    println!("Type checking successful!");
    if !d.warnings.is_empty() {
        println!("({} warning(s))", d.warnings.len());
    }

    println!("\n=== Elaborated MIR ===");
    print!("{}", pretty_print::pretty_print(&elaborated));
}
