// Copyright 2019 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(clippy::uninlined_format_args)]

use std::env;

fn main() {
    let version = testutil::ToolchainVersion::extract_from_pwd().unwrap();
    let source_files_dirname = version.get_ui_source_files_dirname_and_maybe_print_warning();
    let tests_dir = env::current_dir().unwrap().join("tests").join(source_files_dirname);

    // Run the main UI tests, excluding the special cfg tests
    testutil::run_ui_tests(version, &tests_dir, &["!union_into_bytes_cfg"]);

    // This tests the behavior when `--cfg zerocopy_derive_union_into_bytes` is
    // not present, so remove it. If this logic is wrong, that's fine - it will
    // exhibit as a test failure that we can debug at that point.
    let rustflags = env::var("RUSTFLAGS").unwrap_or_default();
    // Handle potential quoting or spacing differences
    let new_rustflags = rustflags.replace("--cfg zerocopy_derive_union_into_bytes", "")
                                 .replace("--cfg=zerocopy_derive_union_into_bytes", "");

    // Safety: set_var is safe in a single-threaded test binary.
    // #[warn(unused_unsafe)] is on by default, so we can drop the unsafe block if we want,
    // but the user's code had it.
    env::set_var("RUSTFLAGS", new_rustflags);
    // Filter out the cfg that we want to test missing
    let rustflags = env::var("RUSTFLAGS").unwrap_or_default();
    let filtered_rustflags = rustflags.replace("--cfg zerocopy_derive_union_into_bytes", "");
    
    // We might also need to handle the case where it's part of a larger string without leading space,
    // or passed differently?
    // Given the debug output: ` --cfg zerocopy_derive_union_into_bytes ...` (with leading space).
    // Simple replace should catch the common case injected by cargo-zerocopy.
    
    // We may trigger unexpected cfgs warning if we remove it but check-cfg expects it?
    // Actually we WANT it removed so check-cfg logic sees it missing?
    // Wait, if check-cfg is enabled, and we remove the cfg, it's fine.
    
    // Also re-add check-cfg suppression if needed, though we want the error.
    
    env::set_var("RUSTFLAGS", filtered_rustflags);

    let mut cmd = std::process::Command::new("cargo");
    cmd.arg("build")
        .arg("-p").arg("zerocopy-derive")
        .arg("--target-dir").arg("target/ui-test-derive-build");
    
    // Clear RUSTFLAGS to ensure we don't accidentally inherit the config
    cmd.env_remove("RUSTFLAGS");
    cmd.env_remove("CARGO_ENCODED_RUSTFLAGS");

    let status = cmd.status().expect("failed to build zerocopy-derive for test");
    assert!(status.success(), "failed to build zerocopy-derive for test");

    // Find the artifact
    let mut derive_lib_path = std::path::PathBuf::from("target/ui-test-derive-build/debug/deps");
    // We need to find the .so/.dylib/.dll
    let entry = std::fs::read_dir(&derive_lib_path).unwrap()
        .filter_map(|e| e.ok())
        .find(|e| {
            let name = e.file_name().to_string_lossy().to_string();
            name.starts_with("libzerocopy_derive") && (name.ends_with(".so") || name.ends_with(".dylib") || name.ends_with(".dll"))
        })
        .expect("could not find built zerocopy-derive artifact");
    
    derive_lib_path.push(entry.file_name());

    // Run the test with the override
    env::set_var("ZEROCOPY_DERIVE_LIB_PATH", derive_lib_path);

    // Run only the special cfg tests
    // Note: We point to the same root dir but filter to include likely only the relevant file(s).
    // Or we can point explicitly to the subdirectory if `ui-runner` supports it?
    // `ui-runner` expects `tests_dir` to be the root.
    // If we pass a filter "union_into_bytes_cfg", `ui_test` will run files containing that path string.
    testutil::run_ui_tests(version, &tests_dir, &["union_into_bytes_cfg"]);
}
