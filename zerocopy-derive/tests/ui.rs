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

    // Run the main UI tests.
    //
    // We exclude `union_into_bytes_cfg` because it requires a special build configuration
    // (disabled `zerocopy_derive_union_into_bytes` cfg) that differs from the default.
    testutil::run_ui_tests(version, &tests_dir, &["!union_into_bytes_cfg"]);

    // Test the behavior when `--cfg zerocopy_derive_union_into_bytes` is NOT present.
    //
    // To do this, we manually rebuild `zerocopy-derive` with the cfg stripped from RUSTFLAGS.
    // We then point the test runner to this custom artifact using `ZEROCOPY_DERIVE_LIB_PATH`.

    let mut cmd = std::process::Command::new("cargo");
    cmd.arg("build")
        .arg("-p")
        .arg("zerocopy-derive")
        .arg("--target-dir")
        .arg("target/ui-test-derive-build");

    // Clear RUSTFLAGS for the child process to ensure we don't accidentally inherit
    // the config from the environment. We specifically want to run *without* the
    // `zerocopy_derive_union_into_bytes` cfg, which is normally injected via RUSTFLAGS
    // by `cargo-zerocopy`. Running with empty RUSTFLAGS achieves this.
    cmd.env_remove("RUSTFLAGS");
    cmd.env_remove("CARGO_ENCODED_RUSTFLAGS");

    let status = cmd.status().expect("failed to build zerocopy-derive for test");
    assert!(status.success(), "failed to build zerocopy-derive for test");

    // Find the built artifact (dylib/so/dll).
    let derive_lib_path = std::path::PathBuf::from("target/ui-test-derive-build/debug/deps");
    let entry = std::fs::read_dir(&derive_lib_path)
        .unwrap()
        .filter_map(|e| e.ok())
        .find(|e| {
            let name = e.file_name().to_string_lossy().to_string();
            name.starts_with("libzerocopy_derive")
                && (name.ends_with(".so") || name.ends_with(".dylib") || name.ends_with(".dll"))
        })
        .expect("could not find built zerocopy-derive artifact");

    // Tell ui-runner to use our custom artifact.
    env::set_var("ZEROCOPY_DERIVE_LIB_PATH", derive_lib_path.join(entry.file_name()));

    // Run only the special cfg test.
    testutil::run_ui_tests(version, &tests_dir, &["union_into_bytes_cfg"]);
}
