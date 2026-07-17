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
//! Stage is auto-detected from the sibling `.expected` extension:
//!
//!   - `foo.sim.expected` → run parse+elaborate+check, compare
//!     pretty-printed MIR.
//!   - `foo.err.expected` → run parse+elaborate+check, compare
//!     rendered diagnostics.
//!   - `foo.ll.expected` under `codegen/` → run full pipeline +
//!     codegen, compare LLVM IR.
//!   - `foo.ll.expected` under `codegen-raw/` → parse + codegen (no
//!     checks), compare LLVM IR.
//!
//! `UPDATE_EXPECT=1 cargo test --test fixtures` rewrites every
//! `.expected` file with the observed output. A fixture with no
//! sibling `.expected` fails with a pointer to UPDATE_EXPECT.

use silica_mir::{
    diagnostics::{Diagnostics, SourceKind},
    elaborate_and_check_mir, lower_hll_to_mir, mir,
};
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
enum Stage {
    /// Full check pipeline → clean run → pretty-printed elaborated MIR.
    Elab,
    /// Full check pipeline → diagnostics.
    Errors,
    /// Full check pipeline + codegen → LLVM IR.
    Codegen,
    /// Parse + codegen (no checker pipeline) → LLVM IR. For hand-crafted
    /// codegen tests that exercise a specific lowering path with a
    /// minimal program that wouldn't pass the substructural or leak
    /// checks.
    CodegenRaw,
}

impl Stage {
    fn expected_extension(self) -> &'static str {
        match self {
            Stage::Elab => "sim.expected",
            Stage::Errors => "err.expected",
            Stage::Codegen | Stage::CodegenRaw => "ll.expected",
        }
    }
}

fn source_kind_for(path: &Path) -> SourceKind {
    match path.extension().and_then(|e| e.to_str()) {
        Some("si") => SourceKind::Hll,
        Some("sim") => SourceKind::Mir,
        other => panic!("fixture {} has unexpected extension {:?}", path.display(), other),
    }
}

/// Determine which stage a fixture belongs to. Codegen fixtures are
/// identified by their location under `tests/codegen{,-raw}/`; other
/// fixtures pick between Elab and Errors based on which sibling
/// `.expected` file exists.
///
/// Returns `None` if the fixture has no `.expected` sibling — the
/// caller reports it as an unpinned fixture.
fn detect_stage(fixture: &Path) -> Option<Stage> {
    let root = fixtures_root();
    let rel = fixture.strip_prefix(&root).unwrap_or(fixture);
    let first = rel.components().next().and_then(|c| c.as_os_str().to_str());
    match first {
        Some("codegen") => Some(Stage::Codegen),
        Some("codegen-raw") => Some(Stage::CodegenRaw),
        _ => {
            // Check for sibling .sim.expected or .err.expected.
            let stem = fixture.file_stem()?.to_string_lossy();
            let sim_expected = fixture.with_file_name(format!("{}.sim.expected", stem));
            let err_expected = fixture.with_file_name(format!("{}.err.expected", stem));
            if sim_expected.exists() {
                Some(Stage::Elab)
            } else if err_expected.exists() {
                Some(Stage::Errors)
            } else {
                None
            }
        }
    }
}

/// Run the pipeline for a fixture and produce the actual output.
fn run_fixture(path: &Path, stage: Stage) -> String {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
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

    let elaborated_env = program.as_ref().map(|p| elaborate_and_check_mir(p, &mut d));

    match stage {
        Stage::Elab => match &elaborated_env {
            Some((elaborated, _)) if !d.has_errors() => {
                mir::pretty_print::pretty_print(elaborated)
            }
            _ => panic!(
                "elab fixture {} produced errors — rename to .err.expected or fix it:\n{}",
                path.display(),
                render_diagnostics(&d),
            ),
        },
        Stage::Errors => render_diagnostics(&d),
        Stage::Codegen => match &elaborated_env {
            Some((elaborated, env)) if !d.has_errors() => {
                mir::codegen::lower_mir_to_llvm(elaborated, env)
            }
            _ => panic!(
                "codegen fixture {} produced errors:\n{}",
                path.display(),
                render_diagnostics(&d),
            ),
        },
        Stage::CodegenRaw => {
            let program = program.unwrap_or_else(|| {
                panic!(
                    "codegen-raw fixture {} failed to parse:\n{}",
                    path.display(),
                    render_diagnostics(&d),
                )
            });
            let (env, _) = mir::type_check::Env::build(&program);
            mir::codegen::lower_mir_to_llvm(&program, &env)
        }
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
    out
}

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn collect_fixtures(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read_dir {}: {}", dir.display(), e)) {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_fixtures(&path, out);
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("si") | Some("sim")
        ) {
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
fn write_expected(fixture: &Path, stage: Stage, actual: &str) -> PathBuf {
    let stem = fixture.file_stem().expect("fixture has no stem").to_string_lossy();
    let expected_path = fixture.with_file_name(format!("{}.{}", stem, stage.expected_extension()));

    // Remove the *other* stage's .expected if it exists (stage flipped).
    let other_ext = match stage {
        Stage::Elab => Some("err.expected"),
        Stage::Errors => Some("sim.expected"),
        _ => None,
    };
    if let Some(ext) = other_ext {
        let other = fixture.with_file_name(format!("{}.{}", stem, ext));
        if other.exists() {
            let _ = std::fs::remove_file(&other);
        }
    }

    std::fs::write(&expected_path, actual)
        .unwrap_or_else(|e| panic!("write {}: {}", expected_path.display(), e));
    expected_path
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
            // In update mode we need to know the stage. For codegen paths
            // it's fixed; for others we run the pipeline and let
            // has_errors() decide (Errors if any errors else Elab).
            let stage = infer_stage_for_update(fixture);
            let actual = run_fixture(fixture, stage);
            write_expected(fixture, stage, &actual);
            continue;
        }

        let stage = match detect_stage(fixture) {
            Some(s) => s,
            None => {
                failures.push(format!(
                    "  {}: no sibling .expected file — run `UPDATE_EXPECT=1 cargo test --test fixtures` to create",
                    rel.display(),
                ));
                continue;
            }
        };

        let actual = run_fixture(fixture, stage);
        let stem = fixture.file_stem().unwrap().to_string_lossy();
        let expected_path = fixture.with_file_name(format!("{}.{}", stem, stage.expected_extension()));

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
}

/// Under UPDATE_EXPECT, decide which stage a fixture should be
/// pinned to. Codegen paths are fixed by directory; everything else
/// runs the pipeline dry and picks Errors if it produced errors,
/// else Elab. Called only in update mode; in verify mode we use
/// `detect_stage` based on the existing `.expected` sibling.
fn infer_stage_for_update(fixture: &Path) -> Stage {
    let root = fixtures_root();
    let rel = fixture.strip_prefix(&root).unwrap_or(fixture);
    match rel.components().next().and_then(|c| c.as_os_str().to_str()) {
        Some("codegen") => return Stage::Codegen,
        Some("codegen-raw") => return Stage::CodegenRaw,
        _ => {}
    }

    let source = std::fs::read_to_string(fixture).unwrap();
    let source_arc = Arc::new(source);
    let source_kind = source_kind_for(fixture);
    let mut d = Diagnostics::default()
        .with_source(source_arc.clone())
        .with_source_kind(source_kind);
    match source_kind {
        SourceKind::Hll => {
            if let Some(p) = lower_hll_to_mir(&source_arc, &mut d) {
                elaborate_and_check_mir(&p, &mut d);
            }
        }
        SourceKind::Mir => match mir::parser::Parser::new(&**source_arc).parse() {
            Ok(p) => {
                elaborate_and_check_mir(&p, &mut d);
            }
            Err(diags) => d.extend_errors(diags.errors().cloned()),
        },
    }
    if d.has_errors() {
        Stage::Errors
    } else {
        Stage::Elab
    }
}

#[test]
fn all_fixtures() {
    run_all_fixtures();
}
