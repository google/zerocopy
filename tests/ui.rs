use std::env;

use testutil::ToolchainVersion;

/// Entry point for the `zerocopy` crate's UI tests.
///
/// This binary is invoked by `cargo test --test ui` (defined in `Cargo.toml`).
/// It delegates to `testutil::run_ui_tests`, which in turn invokes the `ui-runner`
/// trampoline to execute `ui_test` in a controlled environment.
fn main() {
    // Detect toolchain
    let version = ToolchainVersion::extract_from_pwd().unwrap();
    let tests_dir = env::current_dir().unwrap().join("tests/ui");
    testutil::run_ui_tests(version, &tests_dir, &[]);
}
