# cargo-config2

[![crates.io](https://img.shields.io/crates/v/cargo-config2?style=flat-square&logo=rust)](https://crates.io/crates/cargo-config2)
[![docs.rs](https://img.shields.io/badge/docs.rs-cargo--config2-blue?style=flat-square&logo=docs.rs)](https://docs.rs/cargo-config2)
[![license](https://img.shields.io/badge/license-Apache--2.0_OR_MIT-blue?style=flat-square)](#license)
[![msrv](https://img.shields.io/badge/msrv-1.76-blue?style=flat-square&logo=rust)](https://www.rust-lang.org)
[![github actions](https://img.shields.io/github/actions/workflow/status/taiki-e/cargo-config2/ci.yml?branch=main&style=flat-square&logo=github)](https://github.com/taiki-e/cargo-config2/actions)

<!-- tidy:sync-markdown-to-rustdoc:start:src/lib.rs -->

Load and resolve [Cargo configuration](https://doc.rust-lang.org/nightly/cargo/reference/config.html).

This library is intended to accurately emulate the actual behavior of Cargo configuration, for example, this supports the following behaviors:

- [Hierarchical structure and merge](https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure)
- [Environment variables](https://doc.rust-lang.org/nightly/cargo/reference/config.html#environment-variables) and [relative paths](https://doc.rust-lang.org/nightly/cargo/reference/config.html#config-relative-paths) resolution.
- `target.<triple>` and `target.<cfg>` resolution.

Supported tables and fields are mainly based on [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov)'s use cases, but feel free to submit an issue if you see something missing in your use case.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
cargo-config2 = "0.1"
```

`cargo-config2` is usually runnable with Cargo versions older than the Rust version required for build. (e.g., a cargo subcommand using `cargo-config2` could work with older versions such as `cargo +1.59 <subcommand>`.)

## Examples

```rust
// Read config files hierarchically from the current directory, merge them,
// apply environment variables, and resolve relative paths.
let config = cargo_config2::Config::load().unwrap();
let target = "x86_64-unknown-linux-gnu";
// Resolve target-specific configuration (`target.<triple>` and `target.<cfg>`),
// and returns the resolved rustflags for `target`.
let rustflags = config.rustflags(target).unwrap();
println!("{rustflags:?}");
```

See also the [`get` example](https://github.com/taiki-e/cargo-config2/blob/HEAD/examples/get.rs) that partial re-implementation of `cargo config get` using cargo-config2.

<!-- tidy:sync-markdown-to-rustdoc:end -->

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.

### Third party software

This product includes copies and modifications of software developed by third parties:

- [`src/cfg_expr`](https://github.com/taiki-e/cargo-config2/tree/HEAD/src/cfg_expr) includes copies and modifications of [`cfg-expr` crate](https://github.com/EmbarkStudios/cfg-expr) by Embark Studios, licensed under "Apache-2.0 OR MIT".

See the license files included in these directories for more details.
