// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[cfg(feature = "exocrate_tests")]
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::OnceLock,
};

#[cfg(feature = "exocrate_tests")]
fn cargo_anneal_bin_path() -> PathBuf {
    std::env::var("CARGO_BIN_EXE_cargo-anneal")
        .or_else(|_| std::env::var("CARGO_BIN_EXE_cargo_anneal"))
        .expect("CARGO_BIN_EXE_* not set")
        .into()
}

#[cfg(feature = "exocrate_tests")]
fn ensure_test_toolchain(bin_path: &Path) {
    static SETUP_RESULT: OnceLock<Result<(), String>> = OnceLock::new();

    let result = SETUP_RESULT.get_or_init(|| {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let output = Command::new(bin_path)
            .arg("setup")
            .arg("--local-archive")
            .arg(manifest_dir.join("target/anneal-exocrate.tar.zst"))
            .env("__ANNEAL_LOCAL_DEV", "1")
            .env("CARGO_MANIFEST_DIR", manifest_dir)
            .output()
            .map_err(|err| format!("failed to execute cargo-anneal setup: {err}"))?;

        if output.status.success() {
            return Ok(());
        }

        Err(format!(
            "cargo-anneal setup failed\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    });

    if let Err(err) = result {
        panic!("{err}");
    }
}

#[cfg(feature = "exocrate_tests")]
#[test]
fn test_expand_subcommand_simple() {
    let temp_dir = tempfile::tempdir().unwrap();
    let project_dir = temp_dir.path().join("project");
    let output_dir = temp_dir.path().join("llbc_out");
    fs::create_dir_all(project_dir.join("examples")).unwrap();
    fs::write(
        project_dir.join("Cargo.toml"),
        r#"
            [package]
            name = "test_proj"
            version = "0.1.0"
            edition = "2021"

            [[example]]
            name = "simple"
            path = "examples/simple.rs"
        "#,
    )
    .unwrap();
    fs::write(
        project_dir.join("examples").join("simple.rs"),
        r#"
            pub fn add(left: usize, right: usize) -> usize {
                left + right
            }

            fn main() {
                println!("Hello, world! {}", add(1, 2));
            }
        "#,
    )
    .unwrap();

    let bin_path = cargo_anneal_bin_path();
    ensure_test_toolchain(&bin_path);

    let mut cmd = Command::new(bin_path);
    cmd.arg("expand")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .arg("--example")
        .arg("simple")
        .arg("--output-dir")
        .arg(&output_dir);
    cmd.arg("--no-progress");

    cmd.env("__ANNEAL_LOCAL_DEV", "1");
    cmd.env("CARGO_MANIFEST_DIR", env!("CARGO_MANIFEST_DIR"));

    let output = cmd.output().expect("failed to execute cargo-anneal");

    println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
    println!("stderr: {}", String::from_utf8_lossy(&output.stderr));

    assert!(output.status.success(), "cargo-anneal failed");

    let mut found_llbc = false;
    if output_dir.exists() {
        for entry in fs::read_dir(&output_dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "llbc") {
                found_llbc = true;
                break;
            }
        }
    }

    assert!(found_llbc, "No .llbc file found in output directory {:?}", output_dir);
}
