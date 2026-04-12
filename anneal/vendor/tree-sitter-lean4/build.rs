#![deny(clippy::pedantic)]
use std::{
    fs, io,
    path::{Path, PathBuf},
    process::Command,
};

fn copy_dir(src: &Path, dst: &Path) -> io::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        if entry.path().is_file() {
            // Use read/write instead of copy (nix store compatibility)
            let content = fs::read(entry.path())?;
            fs::write(dst.join(entry.file_name()), content)?;
        }
    }
    Ok(())
}

fn generate_parser(out_dir: &Path) -> PathBuf {
    fs::create_dir_all(out_dir).expect("create OUT_DIR");

    // Copy files using read+write (nix store has special permissions that break fs::copy)
    let grammar = fs::read("grammar.js").expect("read grammar.js");
    fs::write(out_dir.join("grammar.js"), grammar).expect("write grammar.js");
    let tree_sitter_json = fs::read("tree-sitter.json").expect("read tree-sitter.json");
    fs::write(out_dir.join("tree-sitter.json"), tree_sitter_json).expect("write tree-sitter.json");
    copy_dir(Path::new("grammar"), &out_dir.join("grammar"))
        .unwrap_or_else(|e| panic!("copy grammar/: {e}"));
    copy_dir(Path::new("src"), &out_dir.join("src")).ok();

    println!(
        "cargo:warning=Generating parser.c in {}...",
        out_dir.display()
    );
    let status = Command::new("tree-sitter")
        .arg("generate")
        .current_dir(out_dir)
        .status()
        .expect("tree-sitter CLI not found");
    assert!(status.success(), "tree-sitter generate failed");

    out_dir.join("src")
}

fn main() {
    println!("cargo:rerun-if-changed=grammar.js");
    println!("cargo:rerun-if-changed=tree-sitter.json");
    println!("cargo:rerun-if-changed=src/parser.c");
    println!("cargo:rerun-if-changed=src/scanner.c");

    let src_dir = if Path::new("src/parser.c").exists() {
        PathBuf::from("src")
    } else {
        let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
        generate_parser(&out_dir)
    };

    let mut build = cc::Build::new();
    build
        .include(&src_dir)
        .flag_if_supported("-Wno-unused-parameter")
        .flag_if_supported("-Wno-unused-but-set-variable")
        .flag_if_supported("-Wno-trigraphs")
        .opt_level(2)
        .file(src_dir.join("parser.c"));

    let scanner = src_dir.join("scanner.c");
    if scanner.exists() {
        build.file(scanner);
    }

    build.compile("parser");
}
