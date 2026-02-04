use std::env;

use testutil::ToolchainVersion;

fn main() {
    // Detect toolchain
    let version = ToolchainVersion::extract_from_pwd().unwrap();
    let tests_dir = env::current_dir().unwrap().join("tests/ui");
    testutil::run_ui_tests(version, &tests_dir, &[]);
}
