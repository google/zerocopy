use assert_cli::Assert;

#[test]
fn entrypoint_resolution_main() {
    let args = [
        "readme",
        "--project-root",
        "tests/entrypoint-resolution/main",
        "--no-title",
        "--no-license",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is("main")
        .unwrap();
}

#[test]
fn entrypoint_resolution_lib() {
    let args = [
        "readme",
        "--project-root",
        "tests/entrypoint-resolution/lib",
        "--no-title",
        "--no-license",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is("lib")
        .unwrap();
}

#[test]
fn entrypoint_resolution_cargo_lib() {
    let args = [
        "readme",
        "--project-root",
        "tests/entrypoint-resolution/cargo-lib",
        "--no-title",
        "--no-license",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is("cargo lib")
        .unwrap();
}

#[test]
fn entrypoint_resolution_cargo_bin() {
    let args = [
        "readme",
        "--project-root",
        "tests/entrypoint-resolution/cargo-bin",
        "--no-title",
        "--no-license",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is("cargo bin")
        .unwrap();
}
