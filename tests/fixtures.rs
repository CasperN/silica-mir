//! Fixture-based integration tests.
//!
//! Each file under `tests/{elab,errors,codegen}/` is a Silica source
//! program (`.si` = HLL, `.sim` = MIR). The directory name determines
//! what the runner asserts on:
//!
//!   - `elab/`     — parse+elaborate; compare pretty-printed MIR
//!                   against `<stem>.sim.expected`.
//!   - `errors/`   — run the pipeline; compare rendered diagnostics
//!                   (errors + internal errors) against
//!                   `<stem>.err.expected`.
//!   - `codegen/`  — run the pipeline + codegen; compare emitted
//!                   LLVM IR against `<stem>.ll.expected`.
//!
//! Expected-file extensions match the *output* language so editors
//! syntax-highlight the .expected file: `.sim.expected` for MIR,
//! `.ll.expected` for LLVM, `.err.expected` for diagnostics.
//!
//! `UPDATE_EXPECT=1 cargo test --test fixtures` rewrites every
//! `.expected` file with the observed output instead of failing. Use
//! after adding a new fixture or when a cosmetic change to
//! diagnostics/pretty_print/codegen ripples through many fixtures.
//!
//! A fixture with no `.expected` file fails with a message pointing
//! to `UPDATE_EXPECT=1` — new fixtures need explicit approval.

use silica_mir::{
    diagnostics::{Diagnostics, SourceKind},
    elaborate_and_check_mir, lower_hll_to_mir, mir,
};
use std::path::{Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Copy)]
enum Stage {
    Elab,
    Errors,
    Codegen,
    /// Codegen without the checker pipeline. Parses the fixture,
    /// builds the type env, and lowers directly. Matches what the
    /// old `codegen/test_util::ll_of` did — many hand-crafted
    /// codegen tests use minimal programs that would fail the leak
    /// check but exercise a specific codegen path.
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

    fn dir_name(self) -> &'static str {
        match self {
            Stage::Elab => "elab",
            Stage::Errors => "errors",
            Stage::Codegen => "codegen",
            Stage::CodegenRaw => "codegen-raw",
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

/// Run the pipeline for a fixture and produce the actual output string
/// the runner will compare against the `.expected` file.
fn run_fixture(path: &Path, stage: Stage) -> String {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {}", path.display(), e));
    let source_arc = Arc::new(source);
    let source_kind = source_kind_for(path);
    let mut d = Diagnostics::default()
        .with_source(source_arc.clone())
        .with_source_kind(source_kind);

    // Parse (route by extension). On parse failure we still fall
    // through to the stage-specific output — errors fixtures need
    // to see parse diagnostics; elab/codegen fixtures will report
    // "no program".
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
                "elab fixture {} produced errors — move it to tests/errors/ or fix it:\n{}",
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
                "codegen fixture {} produced errors — move it to tests/errors/ or fix it:\n{}",
                path.display(),
                render_diagnostics(&d),
            ),
        },
        Stage::CodegenRaw => {
            // Bypass the checker pipeline entirely: parse, build env,
            // codegen. Matches the semantics of the old
            // `codegen/test_util::ll_of` helper.
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
/// Errors first, then internal errors, then warnings — each prefixed
/// by category so a bucket-shift is visible in the diff.
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

fn expected_path_for(fixture: &Path, stage: Stage) -> PathBuf {
    // `foo.sim` → `foo.sim.expected`; drops the source extension and
    // appends the stage-specific expected extension.
    let stem = fixture.file_stem().expect("fixture has no stem");
    fixture.with_file_name(format!("{}.{}", stem.to_string_lossy(), stage.expected_extension()))
}

fn run_stage(stage: Stage) {
    let dir = fixtures_root().join(stage.dir_name());
    if !dir.exists() {
        return; // Empty stage dir is fine — no fixtures to run.
    }

    let mut fixtures = Vec::new();
    collect_fixtures(&dir, &mut fixtures);
    fixtures.sort();

    let update = update_expect_enabled();
    let mut failures = Vec::new();

    for fixture in &fixtures {
        let actual = run_fixture(fixture, stage);
        let expected_path = expected_path_for(fixture, stage);

        if update {
            std::fs::write(&expected_path, &actual)
                .unwrap_or_else(|e| panic!("write {}: {}", expected_path.display(), e));
            continue;
        }

        let expected = match std::fs::read_to_string(&expected_path) {
            Ok(s) => s,
            Err(_) => {
                failures.push(format!(
                    "  {}: missing {} — run `UPDATE_EXPECT=1 cargo test --test fixtures` to create",
                    fixture.strip_prefix(fixtures_root()).unwrap_or(fixture).display(),
                    expected_path.file_name().unwrap().to_string_lossy(),
                ));
                continue;
            }
        };

        if actual != expected {
            failures.push(format!(
                "  {}: output differs from {}\n--- expected ---\n{}\n--- actual ---\n{}",
                fixture.strip_prefix(fixtures_root()).unwrap_or(fixture).display(),
                expected_path.file_name().unwrap().to_string_lossy(),
                expected,
                actual,
            ));
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} fixture failure(s) in tests/{}/:\n{}\n\n(Run `UPDATE_EXPECT=1 cargo test --test fixtures` if the new output is intentional.)",
            failures.len(),
            stage.dir_name(),
            failures.join("\n"),
        );
    }
}

#[test]
fn elab_fixtures() {
    run_stage(Stage::Elab);
}

#[test]
fn errors_fixtures() {
    run_stage(Stage::Errors);
}

#[test]
fn codegen_fixtures() {
    run_stage(Stage::Codegen);
}

#[test]
fn codegen_raw_fixtures() {
    run_stage(Stage::CodegenRaw);
}
