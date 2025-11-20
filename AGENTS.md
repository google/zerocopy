# Development Instructions

This repository uses a wrapper script around Cargo to ensure consistent toolchain usage and configuration.

## Build and Test

**IMPORTANT:** You must **NEVER** run `cargo` directly. Instead, you must **ALWAYS** use the `./cargo.sh` wrapper script for all `cargo` sub-commands (e.g., `check`, `test`, `build`).

### Syntax
`./cargo.sh +<toolchain> <command> [args]`

### Toolchains
The `<toolchain>` argument is mandatory and can be one of the following:

- `msrv`: Runs with the Minimum Supported Rust Version.
- `stable`: Runs with the stable toolchain.
- `nightly`: Runs with the nightly toolchain.
- `all`: Runs the command on `msrv`, `stable`, and `nightly` sequentially.
- Version-gated toolchains: You can also pass specific version-gated toolchains defined in `Cargo.toml`, such as `zerocopy-core-error-1-81-0`.

### Linting

Clippy should **always** be run on the `nightly` toolchain.

```bash
./cargo.sh +nightly clippy
./cargo.sh +nightly clippy --tests
```

### Examples

```bash
# Check the code using the nightly toolchain
# DO NOT RUN: cargo check
./cargo.sh +nightly check

# Run tests on all supported toolchains
# DO NOT RUN: cargo test
./cargo.sh +all test

# Run a specific test on stable
./cargo.sh +stable test -- test_name
```
