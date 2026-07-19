pub mod common;
pub mod diagnostics;
pub mod hll;
pub mod mir;

use diagnostics::Diagnostics;
use mir::ast::Program;

/// Run the HLL frontend (parse → typecheck → mutability check → lower)
/// and return the resulting MIR program. Errors are pushed into `d` and
/// `None` is returned; the caller decides whether to continue.
pub fn lower_hll_to_mir(source: &str, d: &mut Diagnostics) -> Option<Program> {
    let hll_prog = match hll::parser::Parser::new(source).parse() {
        Ok(prog) => prog,
        Err(diags) => {
            d.extend_errors(diags.errors().cloned());
            return None;
        }
    };
    let types = hll::type_check::run_type_check(&hll_prog, d)?;
    hll::mut_check::check_mutability(&hll_prog, d);
    if d.has_errors() {
        return None;
    }
    hll::lowering::run_lowering(&hll_prog, &types, d)
}

pub fn elaborate_and_check_mir(
    mut program: Program,
    d: &mut Diagnostics,
) -> (Program, mir::type_check::Env) {
    mir::elision::elide_program(&mut program);
    let (mut env, env_errs) = mir::type_check::Env::build(&program);
    d.extend_errors(env_errs);
    env.typecheck(d);
    mir::substructural::composition::check_program(&env, d);
    mir::layout::check_sizes_finite(&env, d);
    mir::substructural::check::check_statements(&env, d);
    mir::variant_flow::check_program(&env, d);
    mir::block_reachability::check_program(&env, d);
    mir::init_state::check_program(&env, d);

    if d.has_errors() {
        return (program, env);
    }

    let mut elaborated = program;

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

#[cfg(test)]
mod error_display_tests;
