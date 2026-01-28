use assert_cli::Assert;

const EXPECTED: &str = "# project-with-version

Current version: 0.1.0

A test project with a version provided.";

#[test]
fn template_with_version() {
    let args = [
        "readme",
        "--project-root",
        "tests/project-with-version",
        "--template",
        "README.tpl",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(EXPECTED)
        .unwrap();
}
