pub mod ast;
pub mod block_reachability;
pub mod cfg_edit;
pub mod codegen;
pub mod dataflow;
pub mod init_state;
pub mod intrinsics;
pub mod layout;
pub mod lifetime;
pub mod parser;
pub mod pretty_print;
pub mod substructural;
pub mod type_check;
pub mod variant_flow;

#[cfg(test)]
pub mod array_tests;
#[cfg(test)]
pub mod programs;
#[cfg(test)]
pub mod raw_ptr_tests;
#[cfg(test)]
pub mod test_util;
#[cfg(test)]
pub mod string_tests;
#[cfg(test)]
pub mod error_display_tests;
