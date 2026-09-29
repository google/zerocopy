use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-env-changed=BUILD_VALUE");
    let value: u32 = env::var("BUILD_VALUE").unwrap_or_else(|_| "7".to_owned()).parse().unwrap();
    let path_len = env::var("CARGO_MANIFEST_DIR").unwrap().len() as u32;
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    fs::write(out.join("generated.rs"), format!("pub const BUILD_SUBJECT: u32 = {value} + {path_len};\n")).unwrap();
}
