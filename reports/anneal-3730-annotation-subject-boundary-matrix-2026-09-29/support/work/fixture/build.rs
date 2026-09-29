use std::{env,fs,path::Path};
fn main() {
  let p = Path::new("src/lib.rs");
  println!("cargo:rerun-if-changed={}", p.display());
  let s = fs::read_to_string(p).unwrap();
  let sum: u64 = s.lines().filter(|l| l.trim_start().starts_with("//% "))
    .flat_map(|l| l.bytes()).map(u64::from).sum();
  println!("cargo:rustc-env=PROOF_STAMP={sum}");
  println!("cargo:warning=proof-stamp:{sum}");
  let _ = env::var("OUT_DIR").unwrap();
}
