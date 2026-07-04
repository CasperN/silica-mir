fn main() {
    let dir = std::path::PathBuf::from("tree-sitter-silica-mir");
    let src_dir = dir.join("src");

    if src_dir.exists() {
        let mut c_config = cc::Build::new();
        c_config.include(&src_dir);
        c_config.file(src_dir.join("parser.c"));

        let scanner = src_dir.join("scanner.c");
        if scanner.exists() {
            c_config.file(&scanner);
        }

        c_config.compile("tree-sitter-silica-mir");

        println!("cargo:rerun-if-changed={}", src_dir.join("parser.c").to_str().unwrap());
        if scanner.exists() {
            println!("cargo:rerun-if-changed={}", scanner.to_str().unwrap());
        }
    }
}
