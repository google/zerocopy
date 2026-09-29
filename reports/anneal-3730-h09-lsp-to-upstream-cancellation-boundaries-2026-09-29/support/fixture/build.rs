use std::{env, fs, process::{self, Command}};
fn main() {
    let root = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut child = Command::new("/bin/sleep").arg("5").spawn().unwrap();
    fs::write(format!("{root}/entered"), format!("{} {}\n", process::id(), child.id())).unwrap();
    assert!(child.wait().unwrap().success());
    println!("cargo:rerun-if-changed=build.rs");
}
