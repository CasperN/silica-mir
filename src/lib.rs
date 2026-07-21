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

/// Run the MIR pipeline: pre-elab sanity checks, elaboration
/// passes, post-elab checks. Returns the elaborated program and
/// its type environment.
///
/// # Architecture invariant (currently violated)
///
/// Each MIR subsystem (init-state, substructural, lifetime) owns
/// exactly two artifacts: one elaboration pass that produces the
/// canonical elaborated form assuming type-checked, structurally
/// valid input; and one checker pass that emits every diagnostic
/// the subsystem is responsible for, once, on the elaborated
/// form.
///
/// Elab may emit its own diagnostics for facts unique to
/// elaboration — a lifetime-constraint set with no solution, a
/// value with no valid destructor — but must not duplicate what
/// the checker will catch. The checker is authoritative and runs
/// exactly once; no downstream pass may depend on a re-run to
/// fire diagnostics.
///
/// The violation: `init_state::check_program` is called twice
/// below. The pre-elab call is a "user MIR sanity" gate; the
/// post-elab call catches issues NLL insertion creates. Both
/// calls emit the same diagnostic vocabulary, so what looks like
/// "check once" from each call site is really "check twice for
/// different reasons" hidden behind one name. The intent
/// difference is invisible to the callee.
///
/// The enabling smuggle vector at the function level is
/// `apply_deref_op(place, op, state, report: Option<...>)`: one
/// routine serves silent dataflow transfer (`report = None`) and
/// diagnostic-emitting check (`report = Some(...)`), so
/// loosening the check to accommodate elab is a one-line edit
/// inside a shared helper.
///
/// # Target shape
///
/// - Split `apply_deref_op` into `apply_deref_op_transfer`
///   (dataflow only, no `Option`) and `check_deref_op`
///   (validation, returns diagnostics). Do the same for other
///   `report: Option<_>` sites in init-state.
/// - One `pub fn check_program` per subsystem, run once. If a
///   phase genuinely needs its own recheck, name it
///   `recheck_after_<phase>` so the intent surfaces at the call
///   site.
/// - Pipeline: elaborate-then-check per subsystem, no double
///   calls.
///
/// # Prerequisite blocker
///
/// Removing the pre-elab `init_state::check_program` call
/// requires `state.refs` to track ref-typed fields of struct
/// params, not just ref-typed params themselves. Without this,
/// NLL's `unborrow y.r` on `y: Struct { r: &out i64 }` masks the
/// overwrite that pre-elab catches as
/// `INIT-OverwriteWithoutDrop` — see
/// `tests/init_state/overwrite/overwrite_init_linear_whole`.
/// Land the coverage extension first, verify no fixture
/// regresses, then delete the pre-elab call as its own commit.
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
