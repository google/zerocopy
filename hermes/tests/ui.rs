use std::{path::PathBuf, process::Command};

use ui_test::*;

#[test]
fn ui() {
    unsafe { std::env::set_var("HERMES_UI_TEST_MODE", "true") };

    let mut config = Config::rustc(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/ui"));

    let args = Args::test().unwrap();
    config.with_args(&args);

    let binary_path = compile_and_find_binary("cargo-hermes");
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

    let target_dir = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(manifest_dir).join("target"));

    let target_dir = if target_dir.is_absolute() {
        target_dir
    } else {
        PathBuf::from(manifest_dir).join(target_dir)
    };

    let mut path = target_dir;
    path.push("debug");
    path.push(name);

    assert!(path.exists(), "Binary not found at {:?}", path);
    path
}
