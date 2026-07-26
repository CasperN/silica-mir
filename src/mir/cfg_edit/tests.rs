//! Tests for the edge splitter.
//!
//! Constructs minimal `FunctionBody` values directly rather than going
//! through the parser — the splitter's contract is purely structural
//! (labels, terminators, block order) and doesn't need real statements.

use super::*;

fn span() -> Span {
    Span::default()
}

fn source() -> SourceInfo {
    SourceInfo::generated(GeneratedKind::TestHelper, span())
}

fn block(label: &str, term: Terminator) -> BasicBlock {
    BasicBlock {
        label: label.to_string(),
        label_source: SourceInfo::generated(GeneratedKind::TestHelper, span()),
        statements: Vec::new(),
        terminator: term,
    }
}

fn control_flow_block(label: &str, term: Terminator) -> BasicBlock {
    BasicBlock {
        label: label.to_string(),
        label_source: SourceInfo::generated(GeneratedKind::ControlFlowElaboration, span()),
        statements: Vec::new(),
        terminator: term,
    }
}

fn goto(label: &str) -> Terminator {
    goto_term(label, source())
}

fn generated_goto(label: &str) -> Terminator {
    goto_term(
        label,
        SourceInfo::generated(GeneratedKind::ControlFlowElaboration, span()),
    )
}

fn branch(t: &str, f: &str) -> Terminator {
    branch_term(const_op(bool_const(true)), t, f, source())
}

fn return_() -> Terminator {
    return_term(source())
}

fn switch(cases: &[(&str, &str)]) -> Terminator {
    switch_enum_term(
        var_place("dummy"),
        cases
            .iter()
            .map(|(v, l)| (v.to_string(), l.to_string()))
            .collect(),
        source(),
    )
}

fn find<'a>(body: &'a FunctionBody, label: &str) -> &'a BasicBlock {
    body.blocks
        .iter()
        .find(|b| b.label == label)
        .expect("block not found")
}

// ---------- Basic splits ----------

#[test]
fn split_branch_true_arm() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", branch("t", "f")),
            block("t", goto("end")),
            block("f", goto("end")),
            block("end", return_()),
        ],
    };

    let split = split_edge(&mut body, "entry", "t");
    assert_eq!(split, "$edge0");

    // entry.true_label now points at the split.
    match &find(&body, "entry").terminator.kind {
        TerminatorKind::Branch {
            true_label,
            false_label,
            ..
        } => {
            assert_eq!(true_label, "$edge0");
            assert_eq!(false_label, "f");
        }
        _ => panic!("expected Branch"),
    }

    // Split block falls through to t.
    let sb = find(&body, "$edge0");
    assert!(sb.statements.is_empty());
    assert_eq!(sb.terminator, generated_goto("t"));
}

#[test]
fn split_branch_false_arm() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", branch("t", "f")),
            block("t", return_term(source())),
            block("f", return_term(source())),
        ],
    };

    let split = split_edge(&mut body, "entry", "f");
    match &find(&body, "entry").terminator.kind {
        TerminatorKind::Branch {
            true_label,
            false_label,
            ..
        } => {
            assert_eq!(true_label, "t");
            assert_eq!(false_label, &split);
        }
        _ => panic!("expected Branch"),
    }
}

#[test]
fn split_branch_both_arms_same_succ_rewrites_both() {
    // pathological but legal shape: both arms of Branch point to the
    // same block. Splitting funnels both flows through the split.
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![block("entry", branch("j", "j")), block("j", return_())],
    };

    let split = split_edge(&mut body, "entry", "j");
    match &find(&body, "entry").terminator.kind {
        TerminatorKind::Branch {
            true_label,
            false_label,
            ..
        } => {
            assert_eq!(true_label, &split);
            assert_eq!(false_label, &split);
        }
        _ => panic!("expected Branch"),
    }
    assert_eq!(find(&body, &split).terminator, generated_goto("j"));
}

#[test]
fn split_switchenum_arm() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", switch(&[("A", "a_lbl"), ("B", "b_lbl")])),
            block("a_lbl", return_()),
            block("b_lbl", return_()),
        ],
    };

    let split = split_edge(&mut body, "entry", "a_lbl");
    match &find(&body, "entry").terminator.kind {
        TerminatorKind::SwitchEnum { cases, .. } => {
            assert_eq!(cases[0].1, split);
            assert_eq!(cases[1].1, "b_lbl");
        }
        _ => panic!("expected SwitchEnum"),
    }
}

#[test]
fn split_switchenum_two_arms_same_succ_rewrites_both() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", switch(&[("A", "j"), ("B", "j")])),
            block("j", return_()),
        ],
    };

    let split = split_edge(&mut body, "entry", "j");
    match &find(&body, "entry").terminator.kind {
        TerminatorKind::SwitchEnum { cases, .. } => {
            assert_eq!(cases[0].1, split);
            assert_eq!(cases[1].1, split);
        }
        _ => panic!("expected SwitchEnum"),
    }
}

#[test]
fn split_goto_edge() {
    // Even non-critical edges get split — always-split contract.
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![block("entry", goto("next")), block("next", return_())],
    };

    let split = split_edge(&mut body, "entry", "next");
    assert_eq!(find(&body, "entry").terminator, goto(&split));
    assert_eq!(find(&body, &split).terminator, generated_goto("next"));
}

// ---------- Idempotence ----------

#[test]
fn split_edge_is_idempotent() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", branch("t", "f")),
            block("t", return_()),
            block("f", return_()),
        ],
    };

    let first = split_edge(&mut body, "entry", "t");
    let block_count = body.blocks.len();

    // Second call — same edge — no new block, same label returned.
    let second = split_edge(&mut body, "entry", "t");
    assert_eq!(first, second);
    assert_eq!(body.blocks.len(), block_count);
}

#[test]
fn split_edge_idempotent_on_switchenum() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", switch(&[("A", "a_lbl"), ("B", "b_lbl")])),
            block("a_lbl", return_()),
            block("b_lbl", return_()),
        ],
    };

    let first = split_edge(&mut body, "entry", "a_lbl");
    let n = body.blocks.len();
    let second = split_edge(&mut body, "entry", "a_lbl");
    assert_eq!(first, second);
    assert_eq!(body.blocks.len(), n);
}

#[test]
fn split_edge_recognizes_prior_split_from_provenance_and_shape() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", goto("$prior_split")),
            control_flow_block("$prior_split", generated_goto("target")),
            block("target", return_()),
        ],
    };

    let block_count = body.blocks.len();
    let split = split_edge(&mut body, "entry", "target");

    assert_eq!(split, "$prior_split");
    assert_eq!(body.blocks.len(), block_count);
}

#[test]
fn split_edge_skips_existing_generated_label_candidate() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", goto("target")),
            block("$edge0", return_()),
            block("target", return_()),
        ],
    };

    let split = split_edge(&mut body, "entry", "target");

    assert_eq!(split, "$edge1");
    assert_eq!(find(&body, "$edge0").terminator, return_());
    assert_eq!(find(&body, "$edge1").terminator, generated_goto("target"));
}

// ---------- Block ordering ----------

#[test]
fn split_block_inserted_after_pred() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", branch("t", "f")),
            block("t", return_()),
            block("f", return_()),
        ],
    };

    split_edge(&mut body, "entry", "t");
    let labels: Vec<&str> = body.blocks.iter().map(|b| b.label.as_str()).collect();
    // "entry" at 0, split at 1, then the rest.
    assert_eq!(labels[0], "entry");
    assert_eq!(labels[1], "$edge0");
}

// ---------- Panic paths ----------

#[test]
#[should_panic(expected = "does not target succ")]
fn split_edge_panics_when_edge_missing() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", goto("next")),
            block("next", return_()),
            block("orphan", return_()),
        ],
    };
    // entry doesn't target orphan.
    split_edge(&mut body, "entry", "orphan");
}

#[test]
#[should_panic(expected = "pred 'ghost' not found")]
fn split_edge_panics_when_pred_missing() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![block("entry", return_())],
    };
    split_edge(&mut body, "ghost", "entry");
}

#[test]
#[should_panic(expected = "does not target succ")]
fn split_edge_does_not_claim_user_authored_lookalike() {
    let mut body = FunctionBody {
        locals: Vec::new(),
        blocks: vec![
            block("entry", goto("$edge0")),
            block("$edge0", goto("target")),
            block("target", return_()),
        ],
    };

    split_edge(&mut body, "entry", "target");
}

#[test]
fn generated_split_label_round_trips_through_mir_syntax() {
    use crate::mir::ast::Declaration;
    use crate::mir::parser::Parser;
    use crate::mir::pretty_print::pretty_print;

    let src = "
        fn f() {
          entry:
            goto target
          target:
            return
        }
        ";
    let mut program = Parser::new(src.to_string()).parse().unwrap();

    let function = program
        .declarations
        .iter_mut()
        .find_map(|decl| match decl {
            Declaration::Fn(function) => Some(function),
            _ => None,
        })
        .expect("fixture contains a function");
    split_edge(
        function.body.as_mut().expect("function has a body"),
        "entry",
        "target",
    );

    let printed = pretty_print(&program);
    assert!(printed.contains("$edge0:"));
    Parser::new(printed)
        .parse()
        .expect("pretty-printed generated label must be valid MIR syntax");
}

// ---------- End-to-end: elaborated program still passes ----------

#[test]
fn split_then_full_pipeline_still_clean() {
    // Parse a simple program, split a critical edge in the AST, then
    // run the full pipeline — semantics are preserved so the check
    // should still be clean.
    use crate::elaborate_and_check_mir;
    use crate::mir::ast::Declaration;
    use crate::mir::parser::Parser;

    let src = "
        fn f(b: bool, x: i64) {
          y: i64;
          entry:
            branch(copy b) [true: t, false: fbr]
          t:
            y = 1;
            goto end
          fbr:
            y = 2;
            goto end
          end:
            return
        }
        ";
    let mut program = Parser::new(src.to_string()).parse().unwrap();

    // Split the entry→t edge. `t` doesn't have multiple preds here, so
    // the edge isn't strictly critical, but the always-split contract
    // still applies and semantics must be preserved.
    for decl in &mut program.declarations {
        if let Declaration::Fn(func) = decl {
            if let Some(body) = &mut func.body {
                split_edge(body, "entry", "t");
            }
        }
    }

    let mut d = crate::diagnostics::Diagnostics::default().with_source(program.source.clone());
    elaborate_and_check_mir(program, &mut d);
    assert!(
        d.is_clean(),
        "expected clean, got errors: {:?}",
        d.errors_str()
    );
}
