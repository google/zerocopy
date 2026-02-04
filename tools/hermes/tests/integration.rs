// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    env, fs,
    path::{Path, PathBuf},
    sync::Once,
};

use anyhow::{Context, Result};
use cargo_hermes::pipeline::{Sorry, run_pipeline};
use walkdir::WalkDir;

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

static INIT: Once = Once::new();

fn setup_env() -> (PathBuf, PathBuf) {
    INIT.call_once(|| {
        env_logger::builder().is_test(true).try_init().ok();
    });
    log::debug!("Starting setup_env");
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let cases_dir = manifest_dir.join("tests/cases");

    let aeneas_path = env::var("AENEAS_PATH").map(PathBuf::from).unwrap_or_else(|_| {
        PathBuf::from("/usr/local/google/home/joshlf/workspace/zerocopy/hermes2/aeneas")
    });
    let aeneas_lean_path = aeneas_path.join("backends/lean");

    let charon_bin = aeneas_path.join("charon/bin");
    let aeneas_bin = aeneas_path.join("bin");
    if charon_bin.exists() {
        log::debug!("Found charon bin at {:?}", charon_bin);
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
    log::debug!("setup_env complete");
    (cases_dir, aeneas_lean_path)
}

/// Runs the full integration test suite.
///
/// This test harness:
/// 1.  Locates test cases in `tests/cases/`.
/// 2.  Sets up a cache directory for Lean builds (`target/hermes_integration_cache`) to speed up tests.
/// 3.  Iterates over each test case, running the Hermes pipeline.
/// 4.  Validates that successful tests pass verification and failing tests fail as expected.
#[test]
fn integration_tests() -> Result<()> {
    // Enable logging for diagnostics during test failure
    let _ = env_logger::builder().is_test(true).try_init();

    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    // Note: setup_env actually returns cases_dir as constructed inside,
    // but we can also just reuse the one we might have constructed.
    // The setup_env construction is authoritative for valid paths.
    let (cases_dir, aeneas_lean_path) = setup_env();

    // Collect tests
    for entry in WalkDir::new(&cases_dir) {
        let entry = entry?;
        let path = entry.path();
        if path.extension().is_some_and(|e| e == "rs") {
            let file_name = path.file_stem().unwrap().to_string_lossy().to_string();

            // HERMES_FILTER support
            // Can be "pattern" or "!pattern"
            if let Ok(filter) = env::var("HERMES_FILTER") {
                if let Some(negated) = filter.strip_prefix('!') {
                    if file_name.contains(negated) {
                        continue;
                    }
                } else if !file_name.contains(&filter) {
                    continue;
                }
            }

            let expect_fail = file_name.starts_with("fail_") || file_name.starts_with("repro_");

            log::info!("Running test case: {:?}", file_name);
            run_case(path, &aeneas_lean_path, Some(file_name), !expect_fail, Sorry::RejectSorry);
        }
    }

    // Explicit manual test for allow_sorry
    let path = cases_dir.join("failure/missing_proof.rs");
    if path.exists() {
        log::info!("Running allow_sorry test case: {:?}", path.file_name().unwrap());
        run_case(
            &path,
            &aeneas_lean_path,
            Some("missing_proof".to_string()),
            true,
            Sorry::AllowSorry,
        );
    }

    Ok(())
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
    if dest_packages.exists() && !dest_packages.is_symlink() {
        fs::remove_dir_all(&dest_packages).expect("Failed to remove existing packages dir");
    }
    if !dest_packages.exists() {
        std::os::unix::fs::symlink(&shared_packages, &dest_packages)
            .expect("Failed to symlink packages");
    }

    let dest_build = dest_lake.join("build");
    // Force symlink build
    if dest_build.exists() && !dest_build.is_symlink() {
        if dest_build.is_dir() {
            fs::remove_dir_all(&dest_build).expect("Failed to remove existing build dir");
        } else {
            fs::remove_file(&dest_build).expect("Failed to remove existing build file");
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
        result.expect(&format!(
            "Pipeline failed for success case {:?}",
            source_path.file_name().unwrap()
        ));
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
