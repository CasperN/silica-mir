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

/// Normalize and run the checks that precede MIR elaboration.
///
/// This preparation is deliberately shared by both pipelines below: the
/// check-only pipeline validates MIR exactly as written, while the full
/// pipeline elaborates it before the final dynamic checks.
fn prepare_mir_for_analysis(
    mut program: Program,
    d: &mut Diagnostics,
) -> (Program, mir::type_check::IndexedProgram) {
    // Inject compiler-provided prelude wrappers (non-`$` names like
    // `size_of<T>`, `ptr_offset<T>` that forward to the reserved
    // `$sizeof<T>` / `$ptr_offset<T>` intrinsics) before any pass
    // observes the program. Elision, type-check, mono, and codegen
    // then handle them as ordinary generic fns.
    program
        .declarations
        .extend(mir::intrinsics::prelude_body_decls());
    mir::desugar::self_alias::desugar_self_alias(&mut program);
    mir::desugar::lifetime::desugar_program(&mut program);
    let (env, env_errs) = mir::type_check::IndexedProgram::build(&program);
    d.extend_errors(env_errs);
    env.typecheck(&program, d);
    mir::substructural::composition::check_program(&env, d);
    mir::layout::check_sizes_finite(&env, d);
    mir::substructural::check::check_statements(&program, &env, d);
    (program, env)
}

/// Validate initialization state and lifetime loans.
fn check_place_and_loan_state(
    program: &mir::env::IndexedProgram,
    d: &mut Diagnostics,
) {
    mir::place_state::check::check_program(program, d);
    mir::lifetime::check::check_program(program, d);
    mir::reachability::check_program(program, d);
}

/// Type-check and validate MIR without running NLL or place-state
/// elaboration. This is for MIR that must exercise the checker without a
/// repair pass changing it first.
///
/// Lifetime elision still runs: it is signature normalization, not an
/// ownership/lifetime elaboration pass.
pub fn check_mir_without_elaboration(
    program: Program,
    d: &mut Diagnostics,
) -> (Program, mir::type_check::IndexedProgram) {
    let (program, env) = prepare_mir_for_analysis(program, d);
    check_place_and_loan_state(&env, d);
    (program, env)
}

/// Run the MIR pipeline: pre-elab sanity checks, elaboration
/// passes, post-elab checks. Returns the indexed, elaborated program.
///
/// # Pipeline contract
///
/// Preparation reports static errors but produces a normalized program and
/// [`mir::env::IndexedProgram`] for subsequent passes. Elaboration
/// is total on parsed MIR: it may recover conservatively from malformed input
/// so independent diagnostics can accumulate in one compiler run.
///
/// The passes then construct the canonical MIR in dependency order: copy
/// relaxation precedes NLL because a copy does not close a borrower loan; NLL
/// precedes place-state cleanup because its `unborrow`s affect initialization.
/// The dynamic init-state and loan checkers each run once, on that canonical
/// elaborated form. [`check_mir_without_elaboration`] is the explicit
/// check-only entry point for fixtures that need to observe raw MIR.
pub fn elaborate_and_check_mir(
    program: Program,
    d: &mut Diagnostics,
) -> mir::env::IndexedProgram {
    let (program, env) = prepare_mir_for_analysis(program, d);

    // No `d.has_errors()` gate here: pre-elab checks accumulate their
    // diagnostics and elaboration proceeds regardless. Elaborators are
    // total on parsed+typed MIR — they compute states via
    // `transfer_stmt_silent` (never emits) and degrade conservatively
    // on garbage input. Post-elab checks below then emit their own
    // diagnostics on the elaborated form. This way a program with
    // a `TC-*` violation in one fn and an `INIT-*` violation in
    // another surfaces both classes in a single run.

    let mut elaborated = program;

    // Elaboration still mutates the declaration tree while these passes are
    // being migrated. The final index is rebuilt from the canonical bodies
    // before returning.
    mir::place_state::copy_relaxation::elaborate(&mut elaborated, &env, d);

    // Downstream passes assume every operand is `move` or `copy`; a
    // surviving `take` means copy relaxation missed a case. Emit an
    // internal-error diagnostic (aggregated, not per-operand) and bail
    // before NLL and later passes, which would `unreachable!` on the
    // first `take` they saw.
    mir::place_state::copy_relaxation::verify_no_take(&elaborated, d);
    if d.internal_error_count() > 0 {
        return mir::env::IndexedProgram::build(&elaborated).0;
    }

    mir::lifetime::nll::elaborate(&mut elaborated, &env);
    let mut elaborated = mir::env::IndexedProgram::build(&elaborated).0;
    mir::place_state::drop_elaboration::elaborate(&mut elaborated);

    // Final dynamic validation runs once, over the canonical elaborated MIR.
    // This surfaces invalid source transitions that no elaborator repaired,
    // plus obligations exposed by NLL-inserted `unborrow` statements.
    check_place_and_loan_state(&elaborated, d);
    elaborated
}
