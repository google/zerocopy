# Changelog

All notable changes to this project will be documented in this file.

This project adheres to [Semantic Versioning](https://semver.org).

Releases may yanked if there is a security bug, a soundness bug, or a regression.

<!--
Note: In this file, do not use the hard wrap in the middle of a sentence for compatibility with GitHub comment style markdown rendering.
-->

## [Unreleased]

## [0.1.39] - 2025-10-10

- Fix ["invalid type: ../, expected struct TargetConfig" error when a custom field used in `target.<triple>` config](https://github.com/taiki-e/cargo-llvm-cov/issues/454).

## [0.1.38] - 2025-10-04

- Improve support for target names that contain ".". ([#38](https://github.com/taiki-e/cargo-config2/pull/38))

## [0.1.37] - 2025-10-03

- Support `build.build-dir` [that stabilized in Cargo 1.91](https://github.com/rust-lang/cargo/pull/15833). ([#29](https://github.com/taiki-e/cargo-config2/pull/29), thanks @ranger-ross)

## [0.1.36] - 2025-09-05

- Update `windows-sys` to 0.61.

  This increases the minimum supported Rust version (MSRV) from Rust 1.70 to Rust 1.71.

## [0.1.35] - 2025-07-11

- Use `toml` instead of `toml_edit`.

## [0.1.34] - 2025-06-22

- Support the `[sources]` table. ([#31](https://github.com/taiki-e/cargo-config2/pull/31), thanks @Altair-Bueno)

- Update `windows-sys` to 0.60.

## [0.1.33] - 2025-06-07

- Add structs and fields for credential providers. ([#25](https://github.com/taiki-e/cargo-config2/pull/25), [#27](https://github.com/taiki-e/cargo-config2/pull/27), thanks @nox)

- Change merge behavior of `PathAndArgs` to align Cargo 1.86's behavior change. ([#26](https://github.com/taiki-e/cargo-config2/issues/26))

## [0.1.32] - 2025-01-06

- Expose `CargoNewConfig` and `HttpConfig`. ([69ecb94](https://github.com/taiki-e/cargo-config2/commit/69ecb94d6eb30702d0150043533146df489723cd))

## [0.1.31] - 2024-12-21

- Remove dependency on `home` to restore the MSRV on Windows.

- Add `home_dir`, `cargo_home_with_cwd`, and `rustup_home_with_cwd` functions.

## [0.1.30] - 2024-12-21

- Respect [`RUSTC_BOOTSTRAP=-1` recently added in nightly](https://github.com/rust-lang/rust/pull/132993) in rustc version detection.

## [0.1.29] - 2024-09-01

- Support `target.<triple>.rustdocflags` [that added in Cargo 1.78](https://github.com/rust-lang/cargo/pull/13197).
  `Config::rustdocflags` is a new recommended interface to get rustdocflags.

## [0.1.28] - 2024-09-01

- Support the `[cargo-new]` table. ([#21](https://github.com/taiki-e/cargo-config2/pull/21), thanks @ranger-ross)

## [0.1.27] - 2024-08-19

- Support the `[http]` table. ([#20](https://github.com/taiki-e/cargo-config2/pull/20), thanks @ranger-ross)

## [0.1.26] - 2024-04-20

- Fix regression [when buggy rustc_workspace_wrapper is set](https://github.com/cuviper/autocfg/issues/58#issuecomment-2067625980), introduced in 0.1.25.

## [0.1.25] - 2024-04-17

- Respect rustc_wrapper and rustc_workspace_wrapper in `Config::{rustc_version, host_triple}` to match the [Cargo's new behavior](https://github.com/rust-lang/cargo/pull/13659). (Other APIs such as `Config::rustc` are already respecting wrappers.)

## [0.1.24] - 2024-04-09

- Fix bug when merging array fields in config.

## [0.1.23] - 2024-03-29

- Fix `Config::rustc` when both rustc_wrapper and rustc_workspace_wrapper are set.

## [0.1.22] - 2024-03-20

- Implement `From<&PathAndArgs>` for `std::process::Command`.

## [0.1.21] - 2024-03-20

- Add `{RustcVersion,CargoVersion}::major_minor`.

## [0.1.20] - 2024-03-20

- Add `Config::{rustc_version, cargo_version}`.

## [0.1.19] - 2024-02-10

- Update `toml_edit` to 0.22.

## [0.1.18] - 2024-01-25

- Make `home` dependency Windows-only dependency.

## [0.1.17] - 2023-12-16

- Remove dependency on `once_cell`.

## [0.1.16] - 2023-11-17

- Support `target.'cfg(..)'.linker` [that added in Cargo 1.74](https://github.com/rust-lang/cargo/pull/12535).

- Update `toml_edit` to 0.21.

## [0.1.15] - 2023-10-24

- Improve compile time.

## [0.1.14] - 2023-10-18

- Improve compile time.

## [0.1.13] - 2023-10-17

- Improve compatibility with old Cargo.

## [0.1.12] - 2023-09-14

- Improve robustness when new cfgs are added in the future.

- Update `toml` to 0.8.

## [0.1.11] - 2023-09-11

- Remove dependency on `shell-escape`.

## [0.1.10] - 2023-09-08

- Remove dependency on `cfg-expr`.

## [0.1.9] - 2023-08-22

- Recognize unstable `target.cfg(relocation_model = "...")` on nightly.

## [0.1.8] - 2023-07-03

- Fix build error from dependency when built with `-Z minimal-versions`.

## [0.1.7] - 2023-04-05

- Update `cfg-expr` to 0.15.

## [0.1.6] - 2023-03-07

- Support the `[registries]` and `[registry]` tables. ([#8](https://github.com/taiki-e/cargo-config2/pull/8), thanks @yottalogical)

## [0.1.5] - 2023-02-23

- Fix handling of empty string rustc wrapper envs. ([#7](https://github.com/taiki-e/cargo-config2/pull/7), thanks @tofay)

## [0.1.4] - 2023-01-28

- Update `cfg-expr` to 0.14.

- Update `toml` to 0.7.

## [0.1.3] - 2023-01-24

- Migrate to `toml` 0.6. ([#6](https://github.com/taiki-e/cargo-config2/pull/6))

## [0.1.2] - 2023-01-10

- Improve error messages.

- Add `Config::cargo` method.

- Documentation improvements.

## [0.1.1] - 2023-01-09

- Fix `serde::Serialize` impl of `Config` after target resolved.

## [0.1.0] - 2023-01-09

Initial release

[Unreleased]: https://github.com/taiki-e/cargo-config2/compare/v0.1.39...HEAD
[0.1.39]: https://github.com/taiki-e/cargo-config2/compare/v0.1.38...v0.1.39
[0.1.38]: https://github.com/taiki-e/cargo-config2/compare/v0.1.37...v0.1.38
[0.1.37]: https://github.com/taiki-e/cargo-config2/compare/v0.1.36...v0.1.37
[0.1.36]: https://github.com/taiki-e/cargo-config2/compare/v0.1.35...v0.1.36
[0.1.35]: https://github.com/taiki-e/cargo-config2/compare/v0.1.34...v0.1.35
[0.1.34]: https://github.com/taiki-e/cargo-config2/compare/v0.1.33...v0.1.34
[0.1.33]: https://github.com/taiki-e/cargo-config2/compare/v0.1.32...v0.1.33
[0.1.32]: https://github.com/taiki-e/cargo-config2/compare/v0.1.31...v0.1.32
[0.1.31]: https://github.com/taiki-e/cargo-config2/compare/v0.1.30...v0.1.31
[0.1.30]: https://github.com/taiki-e/cargo-config2/compare/v0.1.29...v0.1.30
[0.1.29]: https://github.com/taiki-e/cargo-config2/compare/v0.1.28...v0.1.29
[0.1.28]: https://github.com/taiki-e/cargo-config2/compare/v0.1.27...v0.1.28
[0.1.27]: https://github.com/taiki-e/cargo-config2/compare/v0.1.26...v0.1.27
[0.1.26]: https://github.com/taiki-e/cargo-config2/compare/v0.1.25...v0.1.26
[0.1.25]: https://github.com/taiki-e/cargo-config2/compare/v0.1.24...v0.1.25
[0.1.24]: https://github.com/taiki-e/cargo-config2/compare/v0.1.23...v0.1.24
[0.1.23]: https://github.com/taiki-e/cargo-config2/compare/v0.1.22...v0.1.23
[0.1.22]: https://github.com/taiki-e/cargo-config2/compare/v0.1.21...v0.1.22
[0.1.21]: https://github.com/taiki-e/cargo-config2/compare/v0.1.20...v0.1.21
[0.1.20]: https://github.com/taiki-e/cargo-config2/compare/v0.1.19...v0.1.20
[0.1.19]: https://github.com/taiki-e/cargo-config2/compare/v0.1.18...v0.1.19
[0.1.18]: https://github.com/taiki-e/cargo-config2/compare/v0.1.17...v0.1.18
[0.1.17]: https://github.com/taiki-e/cargo-config2/compare/v0.1.16...v0.1.17
[0.1.16]: https://github.com/taiki-e/cargo-config2/compare/v0.1.15...v0.1.16
[0.1.15]: https://github.com/taiki-e/cargo-config2/compare/v0.1.14...v0.1.15
[0.1.14]: https://github.com/taiki-e/cargo-config2/compare/v0.1.13...v0.1.14
[0.1.13]: https://github.com/taiki-e/cargo-config2/compare/v0.1.12...v0.1.13
[0.1.12]: https://github.com/taiki-e/cargo-config2/compare/v0.1.11...v0.1.12
[0.1.11]: https://github.com/taiki-e/cargo-config2/compare/v0.1.10...v0.1.11
[0.1.10]: https://github.com/taiki-e/cargo-config2/compare/v0.1.9...v0.1.10
[0.1.9]: https://github.com/taiki-e/cargo-config2/compare/v0.1.8...v0.1.9
[0.1.8]: https://github.com/taiki-e/cargo-config2/compare/v0.1.7...v0.1.8
[0.1.7]: https://github.com/taiki-e/cargo-config2/compare/v0.1.6...v0.1.7
[0.1.6]: https://github.com/taiki-e/cargo-config2/compare/v0.1.5...v0.1.6
[0.1.5]: https://github.com/taiki-e/cargo-config2/compare/v0.1.4...v0.1.5
[0.1.4]: https://github.com/taiki-e/cargo-config2/compare/v0.1.3...v0.1.4
[0.1.3]: https://github.com/taiki-e/cargo-config2/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/taiki-e/cargo-config2/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/taiki-e/cargo-config2/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/taiki-e/cargo-config2/releases/tag/v0.1.0
