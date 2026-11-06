use std::{env, fs, path::PathBuf};
fn main() {
  println!("cargo:rerun-if-env-changed=BUILD_VALUE");
  let explicit: u32 = env::var("BUILD_VALUE").unwrap_or_else(|_| "7".into()).parse().unwrap();
  let location = env::var("CARGO_MANIFEST_DIR").unwrap();
  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
  fs::write(out.join("generated.rs"), format!("pub const SNAPSHOT_VALUE: u32 = {};\n", explicit + location.len() as u32)).unwrap();
}
