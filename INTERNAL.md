# Internal details

This file documents various internal details of zerocopy and its infrastructure
that consumers don't need to be concerned about. It focuses on details that
affect multiple files, and allows each affected code location to reference this
document rather than requiring us to repeat the same explanation in multiple
locations.

## CI and toolchain versions

In CI (`.github/workflows/ci.yml`), we pin to specific versions or dates of the
stable and nightly toolchains. The reason is twofold: First, our UI tests (see
`tests/trybuild.rs` and `zerocopy-derive/tests/trybuild.rs`) depend on the
format of rustc's error messages, and that format can change between toolchain
versions (we also maintain multiple copies of our UI tests - one for each
toolchain version pinned in CI - for this reason). Second, not all nightlies
have a working Miri, so we need to pin to one that does (see
https://rust-lang.github.io/rustup-components-history/).

Updating the versions pinned in CI may cause the UI tests to break. In order to
fix UI tests after a version update, set the environment variable
`TRYBUILD=overwrite` while running `cargo test`.
