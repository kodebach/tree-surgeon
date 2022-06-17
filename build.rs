use std::path::PathBuf;

fn main() {
    let dir: PathBuf = ["tree-sitter-c", "src"].iter().collect();

    cc::Build::new()
        .include(&dir)
        .file(dir.join("parser.c"))
        .flag("-Wno-unused-but-set-variable")
        .compile("tree-sitter-c");
}
