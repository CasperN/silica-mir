// Compile the tree-sitter parsers for each Silica language.
//
// Layout: `tree-sitter-silica/{hll,mir}/src/parser.c` is the generated
// C parser for each language. Common grammar rules live in
// `tree-sitter-silica/common/grammar.js` and are `require`d by both
// `hll/grammar.js` and `mir/grammar.js` at grammar-authoring time —
// there is no separate common parser.c to compile.
//
// Each parser.c defines a distinct extern (`tree_sitter_silica_mir`,
// `tree_sitter_silica`) that the Rust frontends declare via FFI.
fn main() {
    let base = std::path::PathBuf::from("tree-sitter-silica");
    for lang in ["mir", "hll"] {
        let src_dir = base.join(lang).join("src");
        let parser_c = src_dir.join("parser.c");
        if !parser_c.exists() {
            // The HLL parser.c isn't generated yet during the initial
            // migration commits. Skip silently rather than failing the
            // build — Rust code only links what's needed via cfg.
            continue;
        }
        let mut c_config = cc::Build::new();
        c_config.include(&src_dir);
        c_config.file(&parser_c);

        let scanner = src_dir.join("scanner.c");
        if scanner.exists() {
            c_config.file(&scanner);
        }

        c_config.compile(&format!("tree-sitter-silica-{}", lang));

        println!("cargo:rerun-if-changed={}", parser_c.to_str().unwrap());
        if scanner.exists() {
            println!("cargo:rerun-if-changed={}", scanner.to_str().unwrap());
        }
    }
}
