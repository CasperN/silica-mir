//! Fixture-based integration tests.
//!
//! Each `.sim` (MIR) or `.si` (HLL) file under `tests/` is a source
//! program; its sibling `.expected` file pins the output.
//!
//! Layout: pass-oriented top-level dirs at `tests/{init_state,lifetime,
//! substructural,type_check,layout,variant_flow,block_reachability}/`,
//! plus feature-oriented dirs (`array/`, `string/`, `raw_ptr/`,
//! `programs/`, `error_display/`), plus `smoke/` seed fixtures, plus
//! two codegen dirs (`codegen/` = full pipeline, `codegen-raw/` =
//! parse+codegen only).
//!
//! The pipeline stage and expected artifact are auto-detected from the
//! sibling `.expected` extension:
//!
//!   - `foo.expected.sim` → run parse+elaborate+check, compare
//!     pretty-printed MIR.
//!   - `foo.err.expected` → run parse+elaborate+check, compare
//!     rendered diagnostics.
//!   - `foo.preelaborated.sim` with `foo.preelaborated.expected.sim` or
//!     `foo.preelaborated.err.expected`
//!     → run parse+check without elaboration,
//!     compare pretty-printed MIR.
//!   - `foo.expected.ll` under `codegen/` → run full pipeline +
//!     codegen, compare LLVM IR.
//!   - `foo.expected.ll` under `codegen-raw/` → parse + codegen (no
//!     checks), compare LLVM IR.
//!
//! `UPDATE_EXPECT=1 cargo test --test fixtures` rewrites every
//! `.expected` file with the observed output. A fixture with no
//! sibling `.expected` fails with a pointer to UPDATE_EXPECT.

use silica_mir::{
    check_mir_without_elaboration,
    diagnostics::{Diagnostics, SourceKind},
    elaborate_and_check_mir, lower_hll_to_mir, mir,
};
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
enum Stage {
    /// Full check pipeline, including elaboration.
    Elab,
    /// Parse an already-elaborated `.preelaborated.sim` fixture and check it
    /// without running NLL/place-state elaboration again.
    Check,
    /// Full check pipeline + codegen → LLVM IR.
    Codegen,
    /// Parse + codegen (no checker pipeline) → LLVM IR. For hand-crafted
    /// codegen tests that exercise a specific lowering path with a
    /// minimal program that wouldn't pass the substructural or leak
    /// checks.
    CodegenRaw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Expectation {
    Mir,
    Diagnostics,
    Llvm,
}

#[derive(Clone, Copy, Debug)]
struct FixtureKind {
    stage: Stage,
    expectation: Expectation,
}

impl FixtureKind {
    fn expected_extension(self) -> &'static str {
        match (self.stage, self.expectation) {
            (Stage::Elab | Stage::Check, Expectation::Mir) => "expected.sim",
            (Stage::Elab | Stage::Check, Expectation::Diagnostics) => "err.expected",
            (Stage::Codegen | Stage::CodegenRaw, Expectation::Llvm) => "expected.ll",
            _ => panic!("invalid fixture stage and expectation"),
        }
    }
}

fn source_kind_for(path: &Path) -> SourceKind {
    match path.extension().and_then(|e| e.to_str()) {
        Some("si") => SourceKind::Hll,
        Some("sim") => SourceKind::Mir,
        other => panic!(
            "fixture {} has unexpected extension {:?}",
            path.display(),
            other
        ),
    }
}

fn expected_path(fixture: &Path, kind: FixtureKind) -> PathBuf {
    let stem = fixture
        .file_stem()
        .expect("fixture has no stem")
        .to_string_lossy();
    fixture.with_file_name(format!("{}.{}", stem, kind.expected_extension()))
}

fn stage_for_fixture(fixture: &Path) -> Stage {
    let is_elaborated_mir = fixture.extension().and_then(|ext| ext.to_str()) == Some("sim")
        && fixture
            .file_stem()
            .is_some_and(|stem| stem.to_string_lossy().ends_with(".preelaborated"));
    if is_elaborated_mir {
        Stage::Check
    } else {
        Stage::Elab
    }
}

/// Determine a fixture's pipeline stage and expected artifact. Codegen
/// fixtures are identified by their location under `tests/codegen{,-raw}/`;
/// a `.preelaborated.sim` input selects the no-elaboration pipeline; all other
/// fixtures select the full pipeline. The sibling `.expected` file chooses
/// the expected artifact.
///
/// Returns `None` if the fixture has no `.expected` sibling — the
/// caller reports it as an unpinned fixture.
fn detect_fixture_kind(fixture: &Path) -> Option<FixtureKind> {
    let root = fixtures_root();
    let rel = fixture.strip_prefix(&root).unwrap_or(fixture);
    let first = rel.components().next().and_then(|c| c.as_os_str().to_str());
    match first {
        Some("codegen") => Some(FixtureKind {
            stage: Stage::Codegen,
            expectation: Expectation::Llvm,
        }),
        Some("codegen-raw") => Some(FixtureKind {
            stage: Stage::CodegenRaw,
            expectation: Expectation::Llvm,
        }),
        _ => {
            let stage = stage_for_fixture(fixture);
            let candidates = [
                FixtureKind {
                    stage,
                    expectation: Expectation::Mir,
                },
                FixtureKind {
                    stage,
                    expectation: Expectation::Diagnostics,
                },
            ];
            let found: Vec<_> = candidates
                .into_iter()
                .filter(|kind| expected_path(fixture, *kind).exists())
                .collect();
            match found.as_slice() {
                [] => None,
                [kind] => Some(*kind),
                _ => panic!(
                    "fixture {} has multiple .expected siblings; keep exactly one",
                    fixture.display()
                ),
            }
        }
    }
}

struct FixtureRun {
    program: Option<mir::ast::Program>,
    diagnostics: Diagnostics,
}

/// Parse and run one pipeline stage for a fixture.
fn execute_fixture(path: &Path, stage: Stage) -> FixtureRun {
    let source =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let source_arc = Arc::new(source);
    let source_kind = source_kind_for(path);
    let mut d = Diagnostics::default()
        .with_source(source_arc.clone())
        .with_source_kind(source_kind);

    let program = match source_kind {
        SourceKind::Hll => lower_hll_to_mir(&source_arc, &mut d),
        SourceKind::Mir => match mir::parser::Parser::new(&**source_arc).parse() {
            Ok(p) => Some(p),
            Err(diags) => {
                d.extend_errors(diags.errors().cloned());
                None
            }
        },
    };

    let program = match stage {
        Stage::Elab | Stage::Codegen => program
            .as_ref()
            .map(|p| elaborate_and_check_mir(p.clone(), &mut d).0),
        Stage::Check => program
            .as_ref()
            .map(|p| check_mir_without_elaboration(p.clone(), &mut d).0),
        Stage::CodegenRaw => program,
    };

    FixtureRun {
        program,
        diagnostics: d,
    }
}

/// Render a completed fixture run according to its expected artifact.
fn render_fixture(path: &Path, run: &FixtureRun, expectation: Expectation) -> String {
    match expectation {
        Expectation::Mir => match &run.program {
            Some(program) if !run.diagnostics.has_errors() => {
                mir::pretty_print::pretty_print(program)
            }
            _ => panic!(
                "MIR fixture {} produced errors — use an .err.expected sibling or fix it:\n{}",
                path.display(),
                render_diagnostics(&run.diagnostics),
            ),
        },
        Expectation::Diagnostics => render_diagnostics(&run.diagnostics),
        Expectation::Llvm => match &run.program {
            Some(program) if !run.diagnostics.has_errors() => {
                mir::codegen::lower_mir_to_llvm(program.clone())
            }
            _ => panic!(
                "codegen fixture {} produced errors:\n{}",
                path.display(),
                render_diagnostics(&run.diagnostics),
            ),
        },
    }
}

/// Format all diagnostics in a stable, snapshot-friendly form.
fn render_diagnostics(d: &Diagnostics) -> String {
    let mut out = String::new();
    for e in d.errors_str() {
        out.push_str("error: ");
        out.push_str(&e);
        out.push('\n');
    }
    for e in d.internal_errors_str() {
        out.push_str("internal: ");
        out.push_str(&e);
        out.push('\n');
    }
    for w in d.warnings_str() {
        out.push_str("warning: ");
        out.push_str(&w);
        out.push('\n');
    }
    for i in d.infos_str() {
        out.push_str("note: ");
        out.push_str(&i);
        out.push('\n');
    }
    out
}

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn collect_fixtures(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in
        std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {}", dir.display(), e))
    {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_fixtures(&path, out);
        } else if !path
            .file_name()
            .is_some_and(|name| name.to_string_lossy().contains(".expected."))
            && matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("si") | Some("sim")
            )
        {
            out.push(path);
        }
    }
}

fn update_expect_enabled() -> bool {
    std::env::var("UPDATE_EXPECT").ok().as_deref() == Some("1")
}

/// Under UPDATE_EXPECT, we may need to remove a stale `.expected`
/// sibling with the wrong extension (e.g. a test that used to error
/// but now runs clean). Returns the path that WAS written.
fn write_expected(fixture: &Path, kind: FixtureKind, actual: &str) -> PathBuf {
    let path = expected_path(fixture, kind);

    // Remove the opposite expectation for this same pipeline stage if the
    // fixture flipped between clean MIR and diagnostics.
    let other_expectation = match kind.expectation {
        Expectation::Mir => Some(Expectation::Diagnostics),
        Expectation::Diagnostics => Some(Expectation::Mir),
        Expectation::Llvm => None,
    };
    if let Some(expectation) = other_expectation {
        let other = expected_path(
            fixture,
            FixtureKind {
                stage: kind.stage,
                expectation,
            },
        );
        if other.exists() {
            let _ = std::fs::remove_file(&other);
        }
    }

    std::fs::write(&path, actual).unwrap_or_else(|e| panic!("write {}: {}", path.display(), e));
    path
}

fn run_all_fixtures() {
    let root = fixtures_root();
    let mut fixtures = Vec::new();
    collect_fixtures(&root, &mut fixtures);
    fixtures.sort();

    let update = update_expect_enabled();
    let mut failures = Vec::new();

    for fixture in &fixtures {
        let rel = fixture.strip_prefix(&root).unwrap_or(fixture);

        if update {
            let stage = infer_stage_for_update(fixture);
            let run = execute_fixture(fixture, stage);
            let expectation = match stage {
                Stage::Codegen | Stage::CodegenRaw => Expectation::Llvm,
                _ if run.diagnostics.has_errors() => Expectation::Diagnostics,
                _ => Expectation::Mir,
            };
            let kind = FixtureKind { stage, expectation };
            let actual = render_fixture(fixture, &run, expectation);
            write_expected(fixture, kind, &actual);
            continue;
        }

        let kind = match detect_fixture_kind(fixture) {
            Some(kind) => kind,
            None => {
                failures.push(format!(
                    "  {}: no sibling .expected file — run `UPDATE_EXPECT=1 cargo test --test fixtures` to create",
                    rel.display(),
                ));
                continue;
            }
        };

        let run = execute_fixture(fixture, kind.stage);
        let actual = render_fixture(fixture, &run, kind.expectation);
        let expected_path = expected_path(fixture, kind);

        let expected = match std::fs::read_to_string(&expected_path) {
            Ok(s) => s,
            Err(_) => {
                failures.push(format!(
                    "  {}: missing {}",
                    rel.display(),
                    expected_path.file_name().unwrap().to_string_lossy(),
                ));
                continue;
            }
        };

        if actual != expected {
            failures.push(format!(
                "  {}: output differs from {}\n--- expected ---\n{}\n--- actual ---\n{}",
                rel.display(),
                expected_path.file_name().unwrap().to_string_lossy(),
                expected,
                actual,
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} fixture failure(s):\n{}\n\n(Run `UPDATE_EXPECT=1 cargo test --test fixtures` if the new output is intentional.)",
            failures.len(),
            failures.join("\n"),
        );
    }

    // Fixture count summary — helps confirm every intended fixture
    // was discovered when a whole dir gets skipped by mistake.
    // Visible with `cargo test -- --nocapture`.
    if update {
        println!("Regenerated {} fixture(s)", fixtures.len());
    } else {
        println!("Verified {} fixture(s)", fixtures.len());
    }
}

/// Under UPDATE_EXPECT, a `.preelaborated.sim` input preserves the check-only
/// pipeline; every other input uses the full elaboration pipeline. The
/// completed run selects whether the fixture expects MIR or diagnostics.
fn infer_stage_for_update(fixture: &Path) -> Stage {
    let root = fixtures_root();
    let rel = fixture.strip_prefix(&root).unwrap_or(fixture);
    match rel.components().next().and_then(|c| c.as_os_str().to_str()) {
        Some("codegen") => return Stage::Codegen,
        Some("codegen-raw") => return Stage::CodegenRaw,
        _ => {}
    }

    stage_for_fixture(fixture)
}

#[test]
fn all_fixtures() {
    run_all_fixtures();
}
