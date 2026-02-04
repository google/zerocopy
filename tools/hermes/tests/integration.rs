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

use cargo_hermes::pipeline::{Sorry, run_pipeline};

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
                if let Ok(filter) = env::var("HERMES_FILTER") {
                    if !file_name.contains(&filter) {
                        continue;
                    }
                }
                println!("Running {} test case: {:?}", suite_name, path.file_name().unwrap());
                run_case(
                    &path,
                    &aeneas_lean_path,
                    Some(file_name),
                    expect_success,
                    Sorry::RejectSorry,
                );
            }
        }
    }
}

#[test]
fn test_integration_suite() {
    run_suite("success", true);
    run_suite("failure", false);

    // Should succeed with allow_sorry=true
    let (cases_dir, aeneas_lean_path) = setup_env();
    let path = cases_dir.join("failure/missing_proof.rs");
    println!("Running allow_sorry test case: {:?}", path.file_name().unwrap());
    run_case(&path, &aeneas_lean_path, Some("missing_proof".to_string()), true, Sorry::AllowSorry);
}

fn run_case(
    source_path: &Path,
    aeneas_path: &Path,
    crate_name: Option<String>,
    expect_success: bool,
    sorry_mode: Sorry,
) {
    let temp_dir = TestTempDir::new();
    let crate_root = temp_dir.path();

    let shared_packages = crate_root.join("shared_lake_packages");
    fs::create_dir_all(&shared_packages).expect("Failed to create shared packages dir");
    let shared_build = crate_root.join("shared_lake_build");
    fs::create_dir_all(&shared_build).expect("Failed to create shared build dir");

    // Run pipeline directly on the script source path
    let dest = crate_root
        .join("verification")
        .join(crate_name.clone().unwrap_or_else(|| "unknown".to_string()));

    // Pre-create .lake structure
    let dest_lake = dest.join(".lake");
    fs::create_dir_all(&dest_lake).expect("Failed to create .lake dir");

    let dest_packages = dest_lake.join("packages");
    // Force symlink packages
    if dest_packages.exists() {
        if !dest_packages.is_symlink() {
            fs::remove_dir_all(&dest_packages).expect("Failed to remove existing packages dir");
        }
    }
    if !dest_packages.exists() {
        std::os::unix::fs::symlink(&shared_packages, &dest_packages)
            .expect("Failed to symlink packages");
    }

    let dest_build = dest_lake.join("build");
    // Force symlink build
    if dest_build.exists() {
        if !dest_build.is_symlink() {
            if dest_build.is_dir() {
                fs::remove_dir_all(&dest_build).expect("Failed to remove existing build dir");
            } else {
                fs::remove_file(&dest_build).expect("Failed to remove existing build file");
            }
        }
    }
    if !dest_build.exists() {
        std::os::unix::fs::symlink(&shared_build, &dest_build).expect("Failed to symlink build");
    }

    let result = run_pipeline(
        crate_name.clone(),
        crate_root,
        &dest,
        Some(aeneas_path.to_path_buf()),
        Some(source_path.to_path_buf()),
        sorry_mode,
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
