use assert_cli::Assert;

const EXPECTED: &str = "Error: No entrypoint found";

#[test]
fn no_entrypoint_fail() {
    let args = ["readme", "--project-root", "tests/no-entrypoint-fail"];

    Assert::main_binary()
        .with_args(&args)
        .fails()
        .and()
        .stderr()
        .is(EXPECTED)
        .unwrap();
}
