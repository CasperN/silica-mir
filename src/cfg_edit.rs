//! CFG mutation utilities shared across elaboration passes.
//!
//! Right now: critical-edge splitting. Both `substructural::elaboration`
//! (for `Diverged` join resolution) and `lifetime::elaboration` (for
//! ASAP `unborrow` insertion on per-arm last-use points) need a place to
//! attach per-edge statements. This module provides the primitive so
//! neither pass invents its own.

use crate::ast::*;

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
/// Idempotent: repeated calls with the same `(pred, succ)` return the
/// same split block without further mutation, so multiple elaboration
/// passes can independently split the same edge and share the slot.
///
/// Panics if `pred_label` isn't in `body`, or if `pred`'s terminator
/// doesn't currently target `succ_label` (nor a prior split for it).
pub fn split_edge(body: &mut FunctionBody, pred_label: &str, succ_label: &str) -> String {
    let split_label = format!("{}__to__{}", pred_label, succ_label);

    let pred_idx = body
        .blocks
        .iter()
        .position(|b| b.label == pred_label)
        .unwrap_or_else(|| panic!("split_edge: pred '{}' not found", pred_label));

    let targets: Vec<String> = terminator_successors(&body.blocks[pred_idx].terminator)
        .iter()
        .map(|s| s.to_string())
        .collect();

    // Idempotence: if pred already targets the split block, we've split
    // this edge before — reuse it.
    if targets.iter().any(|s| s == &split_label) {
        return split_label;
    }

    if !targets.iter().any(|s| s == succ_label) {
        panic!(
            "split_edge: pred '{}' does not target succ '{}' (targets: {:?})",
            pred_label, succ_label, targets
        );
    }

    let pred_span = body.blocks[pred_idx].terminator_span;
    replace_target_label(&mut body.blocks[pred_idx].terminator, succ_label, &split_label);

    let split_block = BasicBlock {
        label: split_label.clone(),
        label_span: pred_span,
        statements: Vec::new(),
        terminator: Terminator::Goto(succ_label.to_string()),
        terminator_span: pred_span,
    };
    // Insert right after pred so the block ordering stays roughly
    // control-flow adjacent. Not load-bearing for correctness.
    body.blocks.insert(pred_idx + 1, split_block);

    split_label
}

fn replace_target_label(term: &mut Terminator, old: &str, new: &str) {
    match term {
        Terminator::Goto(lbl) => {
            if lbl == old {
                *lbl = new.to_string();
            }
        }
        Terminator::Branch {
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
        Terminator::SwitchEnum { cases, .. } => {
            for (_, lbl) in cases.iter_mut() {
                if lbl == old {
                    *lbl = new.to_string();
                }
            }
        }
        Terminator::Return | Terminator::Abort | Terminator::Unreachable => {}
    }
}

#[cfg(test)]
mod tests;
