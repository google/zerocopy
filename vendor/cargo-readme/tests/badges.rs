use assert_cli::Assert;

const EXPECTED: &str = r#"
[![Build Status](https://ci.appveyor.com/api/projects/status/github/cargo-readme/test?branch=master&svg=true)](https://ci.appveyor.com/project/cargo-readme/test/branch/master)
[![Build Status](https://circleci.com/gh/cargo-readme/test/tree/master.svg?style=shield)](https://circleci.com/gh/cargo-readme/test/tree/master)
[![Build Status](https://gitlab.com/cargo-readme/test/badges/master/pipeline.svg)](https://gitlab.com/cargo-readme/test/commits/master)
[![Build Status](https://travis-ci.org/cargo-readme/test.svg?branch=master)](https://travis-ci.org/cargo-readme/test)
[![Coverage Status](https://codecov.io/gh/cargo-readme/test/branch/master/graph/badge.svg)](https://codecov.io/gh/cargo-readme/test)
[![Coverage Status](https://coveralls.io/repos/github/cargo-readme/test/badge.svg?branch=branch)](https://coveralls.io/github/cargo-readme/test?branch=master)
[![Average time to resolve an issue](https://isitmaintained.com/badge/resolution/cargo-readme/test.svg)](https://isitmaintained.com/project/cargo-readme/test "Average time to resolve an issue")
[![Percentage of issues still open](https://isitmaintained.com/badge/open/cargo-readme/test.svg)](https://isitmaintained.com/project/cargo-readme/test "Percentage of issues still open")

# readme-test

Test crate for cargo-readme

License: MIT
"#;

#[test]
fn badges() {
    let args = ["readme", "--project-root", "tests/badges"];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(EXPECTED)
        .unwrap();
}
