use assert_cli::Assert;

const EXPECTED: &str = r#"
# readme-test

Test crate for cargo-readme

## Level 1 heading should become level 2

```rust
// This is standard doc test and should be output as ```rust
let condition = true;
if condition {
    // Some conditional code here
    if condition {
        // Some nested conditional code here
    }
}
```

### Level 2 heading should become level 3

```rust
// This also should output as ```rust
```
#### Level 3 heading should become level 4

```rust
// This also should output as ```rust
```

```rust
// This should output as ```rust too
```

```rust
// And also this should output as ```rust
```

```python
# This should be on the output
```
"#;

#[test]
fn append_license() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
    ];

    let expected = format!("{}\n\n{}", EXPECTED.trim(), "License: MIT");

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(&*expected)
        .unwrap();
}

#[test]
fn no_append_license() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
        "--no-license",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(EXPECTED)
        .unwrap();
}
