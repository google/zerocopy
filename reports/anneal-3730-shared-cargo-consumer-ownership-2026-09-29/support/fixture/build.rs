use std::{env, fs, process::{self, Command}};
fn main() {
    let root = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut child = Command::new("/bin/sleep").arg("2").spawn().unwrap();
    fs::write(format!("{root}/entered"), format!("{} {}\n", process::id(), child.id())).unwrap();
    assert!(child.wait().unwrap().success());
    if env::var("FAIL_BUILD").ok().as_deref() == Some("1") { panic!("injected build-script failure"); }
    println!("cargo:rerun-if-env-changed=FAIL_BUILD");
}
