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
    let hll_prog = hll::parser::Parser::new(source).parse(d)?;
    let types = hll::type_check::run_type_check(&hll_prog, d)?;
    hll::mut_check::check_mutability(&hll_prog, d);
    if d.has_errors() {
        return None;
    }
    hll::lowering::run_lowering(&hll_prog, &types, d)
}

fn run_mir_pipeline(
    mut raw_program: Program,
    diagnostics: &mut Diagnostics,
    elaborate: bool,
) -> mir::env::IndexedProgram {
    raw_program
        .declarations
        .extend(mir::intrinsics::prelude_body_decls());
    let (mut program, env_errs) = mir::type_check::IndexedProgram::build(&raw_program);

    diagnostics.extend_errors(env_errs);
    mir::desugar::self_alias::desugar_self_alias(&mut program);
    mir::desugar::lifetime::desugar_program(&mut program);
    program.typecheck(diagnostics);
    mir::substructural::composition::check_program(&program, diagnostics);
    mir::layout::check_sizes_finite(&program, diagnostics);
    mir::substructural::check::check_statements(&program, diagnostics);

    if elaborate {
        mir::place_state::copy_relaxation::elaborate(&mut program, diagnostics);
        // Downstream passes assume `take` is relaxed into `copy` or `move`.
        mir::place_state::copy_relaxation::verify_no_take(&program, diagnostics);
        if diagnostics.internal_error_count() > 0 {
            return program;
        }

        mir::lifetime::nll::elaborate(&mut program);
        mir::place_state::drop_elaboration::elaborate(&mut program);
    }
    mir::place_state::check::check_program(&program, diagnostics);
    mir::lifetime::check::check_program(&program, diagnostics);
    mir::reachability::check_program(&program, diagnostics);
    program
}

/// Type-check and validate MIR without running NLL or place-state
/// elaboration. This is for MIR that must exercise the checker without a
/// repair pass changing it first.
pub fn check_mir_without_elaboration(
    program: Program,
    d: &mut Diagnostics,
) -> mir::env::IndexedProgram {
    run_mir_pipeline(program, d, false)
}

/// Run the MIR pipeline: pre-elab sanity checks, elaboration
/// passes, post-elab checks. Returns the indexed, elaborated program.
pub fn elaborate_and_check_mir(program: Program, d: &mut Diagnostics) -> mir::env::IndexedProgram {
    run_mir_pipeline(program, d, true)
}
