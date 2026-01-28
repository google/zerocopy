# target-spec

[![target-spec on crates.io](https://img.shields.io/crates/v/target-spec)](https://crates.io/crates/target-spec)
[![Documentation (latest release)](https://img.shields.io/badge/docs-latest-brightgreen.svg)](https://docs.rs/target-spec/)
[![Documentation (main)](https://img.shields.io/badge/docs-main-purple)](https://guppy-rs.github.io/guppy/rustdoc/target_spec/)
[![Changelog](https://img.shields.io/badge/changelog-latest-blue)](CHANGELOG.md)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](../LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](../LICENSE-MIT)

Evaluate `Cargo.toml` target specifications against platform triples.

Cargo supports [platform-specific
dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies).
These dependencies can be specified in one of two ways:

```toml
# 1. As Rust-like `#[cfg]` syntax.
[target.'cfg(all(unix, target_arch = "x86_64"))'.dependencies]
native = { path = "native/x86_64" }

# 2. Listing out the full target triple.
[target.x86_64-pc-windows-gnu.dependencies]
winhttp = "0.4.0"
```

`target-spec` provides the `eval` API which can be used to figure out whether such a dependency
will be included on a particular platform.

```rust
use target_spec::eval;

// Evaluate Rust-like `#[cfg]` syntax.
let cfg_target = "cfg(all(unix, target_arch = \"x86_64\"))";
assert_eq!(eval(cfg_target, "x86_64-unknown-linux-gnu").unwrap(), Some(true));
assert_eq!(eval(cfg_target, "i686-unknown-linux-gnu").unwrap(), Some(false));
assert_eq!(eval(cfg_target, "x86_64-pc-windows-msvc").unwrap(), Some(false));

// Evaluate a full target-triple.
assert_eq!(eval("x86_64-unknown-linux-gnu", "x86_64-unknown-linux-gnu").unwrap(), Some(true));
assert_eq!(eval("x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc").unwrap(), Some(false));
```

For more advanced usage, see `Platform` and `TargetSpec`.

### Optional features

* **`custom`**: Adds support for [custom
  targets](https://docs.rust-embedded.org/embedonomicon/custom-target.html) via
  `Platform::new_custom`.
* **`summaries`**: Adds the `summaries` module to enable serialization of `Platform` and
  `TargetFeatures`.
* **`proptest1`**: Enables support for property-based testing of `Platform` and
  `TargetFeatures` using `proptest`.

### Minimum supported Rust version

The minimum supported Rust version (MSRV) is **Rust 1.82**. The MSRV history is:

* For target-spec 3.0.x: **Rust 1.66**.
* For target-spec 3.1.x: **Rust 1.73**.
* For target-spec 3.2.x: **Rust 1.75**.
* For target-spec 3.3.x and 3.4.x: **Rust 1.82**.
* For target-spec 3.5.x: **Rust 1.86**.

Within the 3.x series, MSRV bumps will be accompanied by a minor version
update. The last 6 months of stable Rust releases will be supported.

### Related crates

To pretty-print target-spec errors, consider using the [miette](https://docs.rs/miette)
diagnostic library with [target-spec-miette](https://crates.io/crates/target-spec-miette).

## Contributing

See the [CONTRIBUTING](../CONTRIBUTING.md) file for how to help out.

## License

This project is available under the terms of either the [Apache 2.0 license](../LICENSE-APACHE) or the [MIT
license](../LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
cargo readme > README.md
-->
