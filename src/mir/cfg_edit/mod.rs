//! CFG mutation utilities shared across elaboration passes.
//!
//! Right now: critical-edge splitting. Both
//! `substructural::drop_elaboration` (for `Diverged` join resolution)
//! and `lifetime::nll` (for ASAP `unborrow` insertion on per-arm
//! last-use points) need a place to attach per-edge statements. This
//! module provides the primitive so neither pass invents its own.

use crate::mir::ast::*;
use crate::mir::helpers::*;

/// Ensure a dedicated block exists on the edge from `pred_label` to
/// `succ_label`, and return its label. The returned block has an empty
/// `statements` list and `Goto(succ_label)` terminator — callers append
/// per-edge statements to it.
///
/// Splits unconditionally (no critical-edge check). Rewriting `pred`'s
/// terminator so every occurrence of `succ_label` targets the new block
/// preserves semantics: the new block just falls through to `succ_label`.
/// A non-critical edge gets a trivial extra block — negligible cost and a
/// simpler contract for callers than "if critical do X else Y".
///
/// Idempotent: repeated calls with the same `(pred, succ)` recognize an
/// existing compiler-generated target block that falls through to `succ`, so
/// multiple elaboration passes can independently split the same edge and share
/// the slot. Generated labels are allocated fresh against the whole function;
/// their spelling is never used as proof that an edge was already split.
///
/// Panics if `pred_label` isn't in `body`, or if `pred`'s terminator
/// doesn't currently target `succ_label` (nor a prior split for it).
pub fn split_edge(body: &mut FunctionBody, pred_label: &str, succ_label: &str) -> String {
    let pred_idx = body
        .blocks
        .iter()
        .position(|b| b.label == pred_label)
        .unwrap_or_else(|| panic!("split_edge: pred '{}' not found", pred_label));

    let targets: Vec<String> = terminator_successors(&body.blocks[pred_idx].terminator)
        .iter()
        .map(|s| s.to_string())
        .collect();

    if let Some(split_label) = existing_split_label(body, &targets, succ_label) {
        return split_label;
    }

    if !targets.iter().any(|s| s == succ_label) {
        panic!(
            "split_edge: pred '{}' does not target succ '{}' (targets: {:?})",
            pred_label, succ_label, targets
        );
    }

    let split_label = fresh_split_label(body);

    let pred_span = body.blocks[pred_idx].terminator.span();
    replace_target_label(
        &mut body.blocks[pred_idx].terminator,
        succ_label,
        &split_label,
    );

    let split_block = BasicBlock {
        label: split_label.clone(),
        label_source: SourceInfo::generated(GeneratedKind::ControlFlowElaboration, pred_span),
        statements: Vec::new(),
        terminator: goto_term(
            succ_label,
            SourceInfo::generated(GeneratedKind::ControlFlowElaboration, pred_span),
        ),
    };
    // Insert right after pred so the block ordering stays roughly
    // control-flow adjacent. Not load-bearing for correctness.
    body.blocks.insert(pred_idx + 1, split_block);

    split_label
}

/// Find a prior split of this edge from structure and provenance, not from a
/// guessed label. Statements may already have been appended by an elaboration
/// pass; only the generated block identity and fallthrough target are
/// invariant.
fn existing_split_label(
    body: &FunctionBody,
    pred_targets: &[String],
    succ_label: &str,
) -> Option<String> {
    pred_targets.iter().find_map(|target| {
        let block = body.blocks.iter().find(|block| block.label == *target)?;
        if block.label_source.generated_kind() != Some(GeneratedKind::ControlFlowElaboration) {
            return None;
        }
        match &block.terminator.kind {
            TerminatorKind::Goto(next) if next == succ_label => Some(block.label.clone()),
            _ => None,
        }
    })
}

/// Allocate a valid MIR identifier that cannot collide with any existing block
/// in this function. Among `block_count + 1` candidates, at least one must be
/// absent, so this search is bounded without a global counter or overflow path.
fn fresh_split_label(body: &FunctionBody) -> String {
    for index in 0..=body.blocks.len() {
        let candidate = format!("$edge{}", index);
        if body.blocks.iter().all(|block| block.label != candidate) {
            return candidate;
        }
    }
    unreachable!("block_count + 1 generated label candidates cannot all be occupied")
}

fn replace_target_label(term: &mut Terminator, old: &str, new: &str) {
    match &mut term.kind {
        TerminatorKind::Goto(lbl) => {
            if lbl == old {
                *lbl = new.to_string();
            }
        }
        TerminatorKind::Branch {
            true_label,
            false_label,
            ..
        } => {
            if true_label == old {
                *true_label = new.to_string();
            }
            if false_label == old {
                *false_label = new.to_string();
            }
        }
        TerminatorKind::SwitchEnum { cases, .. } => {
            for (_, lbl) in cases.iter_mut() {
                if lbl == old {
                    *lbl = new.to_string();
                }
            }
        }
        TerminatorKind::Return | TerminatorKind::Abort | TerminatorKind::Unreachable => {}
    }
}

#[cfg(test)]
mod tests;
