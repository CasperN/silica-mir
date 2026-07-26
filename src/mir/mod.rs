pub mod ast;
pub mod block_reachability;
pub mod cfg_edit;
pub mod codegen;
pub mod dataflow;
pub(crate) mod diagnostic_format;
pub mod helpers;
pub mod intrinsics;
pub mod layout;
pub mod lifetime;
pub mod mono;
pub mod parser;
pub mod place_state;
pub mod pretty_print;
pub mod substructural;
pub mod type_check;
pub mod type_util;
pub mod variant_flow;

#[cfg(test)]
pub mod test_util;
