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

License: MIT
"#;

#[test]
fn no_template() {
    let args = [
        "readme",
        "--project-root",
        "tests/test-project",
        "--no-template",
        "--no-badges",
    ];

    Assert::main_binary()
        .with_args(&args)
        .succeeds()
        .and()
        .stdout()
        .is(EXPECTED)
        .unwrap();
}
