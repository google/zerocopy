use std::{path::PathBuf, process::Command};

use ui_test::*;

#[test]
fn ui() {
    std::env::set_var("HERMES_UI_TEST_MODE", "true");

    let mut config = Config::rustc(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/ui"));

    let args = Args::test().unwrap();
    config.with_args(&args);

    let binary_path = compile_and_find_binary("hermes");
    config.program.program = binary_path;

    run_tests(config).unwrap();
}

fn compile_and_find_binary(name: &str) -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let status = Command::new("cargo")
        .arg("build")
        .arg("--bin")
        .arg(name)
        .current_dir(manifest_dir)
        .status()
        .expect("Failed to execute cargo build");

    assert!(status.success(), "Failed to build binary '{}'", name);

    let mut path = PathBuf::from(manifest_dir);
    path.push("..");
    path.push("target");
    path.push("debug");
    path.push(name);

    assert!(path.exists(), "Binary not found at {:?}", path);
    path
}
