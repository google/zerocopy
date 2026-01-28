use assert_cli::Assert;

#[test]
fn alternate_input_empty_docs() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
        "--input",
        "src/no_docs.rs",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is("# readme-test\n\nLicense: MIT")
        .unwrap();
}

#[test]
fn alternate_input_single_line() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
        "--input",
        "src/single_line.rs",
    ];

    let expected = r#"
# readme-test

Test crate for cargo-readme

License: MIT
"#;

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(expected)
        .unwrap();
}

#[test]
fn alternate_input_a_little_bit_longer() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
        "--input",
        "src/other.rs",
    ];

    let expected = r#"
# readme-test

Test crate for cargo-readme

## Level 1 heading should become level 2

License: MIT
"#;

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(expected)
        .unwrap();
}
