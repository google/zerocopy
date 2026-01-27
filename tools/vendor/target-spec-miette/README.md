# target-spec-miette

[![target-spec-miette on crates.io](https://img.shields.io/crates/v/target-spec-miette)](https://crates.io/crates/target-spec-miette)
[![Documentation (latest release)](https://img.shields.io/badge/docs-latest-brightgreen.svg)](https://docs.rs/target-spec-miette/)
[![Documentation (main)](https://img.shields.io/badge/docs-main-purple)](https://guppy-rs.github.io/guppy/rustdoc/target_spec_miette/)
[![Changelog](https://img.shields.io/badge/changelog-latest-blue)](CHANGELOG.md)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

Integrate [target-spec](https://crates.io/crates/target-spec) errors with [miette](https://docs.rs/miette).

This crate has implementations of `Diagnostic` for the various kinds of errors that target-spec
produces. This can be used to pretty-print errors returned by target-spec.

### Features

- `fixtures`: Include [a set of fixtures](crate::fixtures) for testing
  downstream users against. This feature is disabled by default.

### Minimum supported Rust version

The minimum supported Rust version (MSRV) is **Rust 1.86**.

While this crate is in pre-release status (0.x), the MSRV may be bumped in
patch releases.

## Contributing

See the [CONTRIBUTING](../CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](../LICENSE-APACHE) or the [MIT
license](../LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
./scripts/regenerate-readmes.sh
-->
