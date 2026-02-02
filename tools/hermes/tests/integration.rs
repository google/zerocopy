// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    env, fs,
    io::Write as _,
    path::{Path, PathBuf},
};

use cargo_hermes::pipeline::run_pipeline;

struct TestTempDir {
    path: PathBuf,
}

impl TestTempDir {
    fn new() -> Self {
        // Use a persistent directory in target/ to allow caching across runs
        let target_dir = env::var("CARGO_TARGET_DIR").map(PathBuf::from).unwrap_or_else(|_| {
            let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
            manifest_dir.join("../../target")
        });
        let cache_dir = target_dir.join("hermes_integration_cache");
        fs::create_dir_all(&cache_dir).expect("Failed to create cache dir");

        Self { path: cache_dir }
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TestTempDir {
    fn drop(&mut self) {
        // Do NOT delete the directory to preserve cache (Mathlib takes forever to download/build)
        // clean up specific files if needed, but not the whole thing.
    }
}

fn setup_env() -> (PathBuf, PathBuf) {
    println!("DEBUG: Starting setup_env");
    std::io::stdout().flush().unwrap();
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cases_dir = manifest_dir.join("tests/cases");

    let aeneas_path =
        PathBuf::from("/usr/local/google/home/joshlf/workspace/zerocopy/hermes2/aeneas");
    let aeneas_lean_path = aeneas_path.join("backends/lean");

    let charon_bin = aeneas_path.join("charon/bin");
    let aeneas_bin = aeneas_path.join("bin");
    if charon_bin.exists() {
        println!("DEBUG: Found charon bin at {:?}", charon_bin);
        std::io::stdout().flush().unwrap();
        let home_dir = env::var("HOME").map(PathBuf::from).unwrap_or_else(|_| PathBuf::from("."));
        let elan_bin = home_dir.join(".elan/bin");
        let current_path = env::var("PATH").unwrap_or_default();
        let new_path = format!(
            "{}:{}:{}:{}",
            charon_bin.display(),
            aeneas_bin.display(),
            elan_bin.display(),
            current_path
        );
        unsafe {
            env::set_var("PATH", new_path);
        }
    }
    println!("DEBUG: setup_env complete");
    std::io::stdout().flush().unwrap();
    (cases_dir, aeneas_lean_path)
}

fn run_suite(suite_name: &str, expect_success: bool) {
    println!("DEBUG: Starting run_{}_cases", suite_name);
    std::io::stdout().flush().unwrap();
    let (cases_dir, aeneas_lean_path) = setup_env();
    let suite_dir = cases_dir.join(suite_name);
    if suite_dir.exists() {
        for entry in fs::read_dir(suite_dir)
            .unwrap_or_else(|_| panic!("Failed to read {} cases dir", suite_name))
        {
            let entry = entry.expect("Failed to read entry");
            let path = entry.path();
            if path.extension().map_or(false, |e| e == "rs") {
                let file_name = path.file_stem().unwrap().to_string_lossy().to_string();
                println!("Running {} test case: {:?}", suite_name, path.file_name().unwrap());
                run_case(&path, &aeneas_lean_path, Some(file_name), expect_success);
            }
        }
    }
}

#[test]
fn test_integration_suite() {
    run_suite("success", true);
    run_suite("failure", false);
}

fn run_case(
    source_path: &Path,
    aeneas_path: &Path,
    crate_name: Option<String>,
    expect_success: bool,
) {
    let temp_dir = TestTempDir::new();
    let crate_root = temp_dir.path();

    // Run pipeline directly on the script source path
    let dest = crate_root.join("verification");
    let result = run_pipeline(
        crate_name.clone(),
        crate_root,
        &dest,
        Some(aeneas_path.to_path_buf()),
        Some(source_path.to_path_buf()),
    );

    if expect_success {
        result.expect("Pipeline failed for success case");
        // Assert Output
        assert!(dest.join("UserProofs.lean").exists(), "UserProofs.lean not generated");
        assert!(dest.join("lakefile.lean").exists(), "lakefile.lean not generated");
    } else {
        assert!(
            result.is_err(),
            "Pipeline succeeded for failure case {:?}, expected error",
            source_path.file_name()
        );
    }
}
