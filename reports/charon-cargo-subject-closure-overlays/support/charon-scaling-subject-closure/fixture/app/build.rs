use std::{env, fs, path::PathBuf};
fn main() {
  println!("cargo:rerun-if-env-changed=BUILD_VALUE");
  let value = env::var("BUILD_VALUE").unwrap_or_else(|_| "7".to_owned());
  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
  fs::write(out.join("generated.rs"), format!("pub const BUILD_VALUE: u32 = {value};\n")).unwrap();
}
