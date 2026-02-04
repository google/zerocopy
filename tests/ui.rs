use std::env;
use std::process::Command;
use testutil::ToolchainVersion;

fn main() {
    // Detect toolchain
    let version = ToolchainVersion::extract_from_pwd().unwrap();
    let toolchain_arg = match version {
        ToolchainVersion::PinnedMsrv => "msrv",
        ToolchainVersion::PinnedStable => "stable",
        ToolchainVersion::PinnedNightly => "nightly",
        ToolchainVersion::OtherStable => "stable",
        ToolchainVersion::OtherNightly => "nightly",
    };
    
    // Find dependencies.
    // We are running in `target/debug/deps` (or similar).
    // The executables and rlibs are in `target/debug/deps`.
    let current_exe = env::current_exe().unwrap();
    let deps_dir = current_exe.parent().unwrap();

    let cargo_bin = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let mut cmd = Command::new(cargo_bin);
    
    if matches!(version, ToolchainVersion::PinnedMsrv) {
        cmd.arg("+stable");
    }

    // Invoke ui-runner
    // cargo +stable run -p ui-runner -- --target-toolchain <T> --deps-dir <D>
    
    // We use `cargo +stable` because `ui-runner` itself tracks latest deps and might need stable to build?
    // Actually, `ui-runner` depends on `ui_test` which might require decent Rust.
    // zerocopy MSRV is 1.56.0, which is too old for recent `ui_test`.
    // So we MUST run `ui-runner` with stable.
    
    let tests_dir = env::current_dir().unwrap().join("tests/ui");

    let mut cmd = Command::new("cargo");
    cmd.current_dir("tools/ui-runner"); // Run from ui-runner dir to pick up its .cargo/config.toml
    cmd.arg("+stable");
    cmd.arg("run");
    // Use manifest-path relative to CWD
    cmd.arg("--manifest-path").arg("Cargo.toml")
       .arg("--quiet") // Reduce noise
       .arg("--")
       .arg("--target-toolchain")
       .arg(toolchain_arg)
       .arg("--deps-dir")
       .arg(deps_dir)
       .arg("--tests-dir")
       .arg(tests_dir);

    // Forward RUSTFLAGS if present, but clear them for the runner process itself
    // to avoid polluting the runner's build with nightly flags when running on stable.
    if let Ok(rustflags) = env::var("RUSTFLAGS") {
        cmd.env_remove("RUSTFLAGS");
        cmd.arg(format!("--rustflags={}", rustflags));
    }

    // Forward arguments
    if let Some(arg_idx) = env::args().position(|a| a == "--") {
        let args: Vec<_> = env::args().skip(arg_idx + 1).collect();
        cmd.args(args);
    } else {
         // cargo test --test ui -- foo
         // The args passed to main() include the binary name.
         // If generic `harness=false`, we get all args?
         // We might get flags meant for libtest if we are not careful?
         // But `harness=false` means we handle it.
         // If user runs `cargo test --test ui -- foo`, we get `.../ui foo`?
         // Let's assume valid filters are passed.
         // We skip the first arg (binary path).
         cmd.args(env::args().skip(1));
    }

    eprintln!("Running ui-runner with toolchain: {}", toolchain_arg);
    let status = cmd.status().expect("failed to spawn ui-runner");
    
    if !status.success() {
        panic!("ui-runner failed");
    }
}
