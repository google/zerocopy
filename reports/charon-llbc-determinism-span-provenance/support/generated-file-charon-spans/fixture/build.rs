use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let template = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("generated_template.rs");
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"))
        .join("generated.rs");
    fs::copy(&template, &output).expect("copy generated source template");
    println!("cargo:rerun-if-changed=generated_template.rs");
}
