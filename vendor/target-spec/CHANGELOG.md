# Changelog

## [3.5.6] - 2025-01-12

### Fixed

- In custom targets, support arbitrary strings such as `"immediate-abort"` for `panic-strategy`.

## [3.5.5] - 2025-12-26

### Changed

- Updated `cfg-expr` to version 0.20.5, updating builtin targets to Rust 1.92.

## [3.5.4] - 2025-10-13

### Fixed

- For custom targets, updated the deserializer to handle [`target-pointer-width` becoming an integer](https://github.com/rust-lang/rust/pull/144443) in the newest Rust nightlies.

## [3.5.3] - 2025-10-12

### Changed

- Updated `cfg-expr` to version 0.20.3, updating builtin targets to Rust 1.90.

## [3.5.2] - 2025-09-29

### Fixed

Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

## [3.5.1] - 2025-09-14

### Changed

- Updated `cfg-expr` to version 0.20.2, updating builtin targets to Rust 1.89.

## [3.5.0] - 2025-07-11

### Changed

- Internal dependency `cfg-expr` updated to 0.20.2, updating builtin targets to Rust 1.88.
- MSRV updated to Rust 1.86, as required by dependencies. (Apologies for not fulfilling the 6 month support promise for this version series.)

## [3.4.2] - 2025-02-20

### Changed

Internal dependency `cfg-expr` updated to 0.18.0, updating builtin targets to Rust 1.85.

## [3.4.1] - 2025-02-15

### Fixed

- Removed unused direct dependency on unicode-ident. Thanks [hanna-kruppe](https://github.com/hanna-kruppe) for your contribution!

## [3.4.0] - 2025-02-08

### Added

- Added `Triple::from_rustc_version_verbose` and `Platform::from_rustc_version_verbose` to parse `rustc -vV` output and obtain a triple.

### Changed

- Renamed `Platform::current` to `Platform::build_target` to indicate that it is determined at build time, not at runtime. The old method is still available but has been marked deprecated.

## [3.3.1] - 2024-12-23

### Changed

- Improved error message for `CustomTripleCreateError::Unavailable`.

## [3.3.0] - 2024-12-22

### Added

- `CustomTripleCreateError` now has `input`, `input_string`, `line_and_column`,
  and `label` methods. These methods aid in implementing
  [`target-spec-miette`](https://docs.rs/target-spec-miette), and also allow
  dependencies to be oblivious to whether the `custom` feature is enabled.

### Fixed

- Custom platforms now deserialize the `target-family` and `target-endian`
  fields correctly. Previously, these fields were ignored and always treated
  as empty.

### Deprecated

- `Error::CustomTripleCreate` is now deprecated. This error was never actually
  created, and will be removed in the future.
- `CustomTripleCreateError::Deserialize` is now deprecated. target-spec now creates
  a different `DeserializeJson` variant when deserialization fails. This variant
  also contains the original input being deserialized.

### Changed

- MSRV updated to Rust 1.82.
- Internal dependency `cfg-expr` updated to 0.17.2, updating builtin targets to Rust 1.83.

## [3.2.2] - 2024-09-11

### Changed

- Internal dependency `cfg-expr` updated to 0.17.0, updating builtin targets to Rust 1.81.

## [3.2.1] - 2024-07-31

### Fixed

- Update minimum version of `target-lexicon` dependency to 0.12.16, to ensure that minimal-version builds work.

## [3.2.0] - 2024-07-29

### Changed

- MSRV updated to Rust 1.75.
- Internal dependency `cfg-expr` updated to 0.16.0, updating builtin targets to Rust 1.80.

## [3.1.0] - 2024-02-03

### Changed

- MSRV updated to Rust 1.73.
- Internal dependency `cfg-expr` updated to 0.15.6, updating builtin targets to Rust 1.75.

## [3.0.1] - 2023-07-29

### Changed

- Internal dependency `cfg-expr` updated to 0.15.4, updating builtin targets to Rust 1.71.

## [3.0.0] - 2023-06-25

### Changed

- `TargetSpec` now stores plain strings rather than parsed triples. This matches what Cargo does.
- `TargetExpression` has been renamed renamed to `TargetSpecExpression`.
- `Error::UnknownTargetTriple` has been renamed to `Error::InvalidTargetSpecString`, and returns a new `PlainStringParseError` type.

### Added

- `TargetSpec`, `TargetSpecExpression` and `TargetSpecPlainString` now implement `std::fmt::Display`.

## [2.0.1] - 2023-06-19

### Fixed

- `Triple`'s `Eq`, `PartialEq`, `Ord`, `PartialOrd` and `Hash` now take into account custom platforms.

## [2.0.0] - 2023-06-19

### Added

#### Custom platforms

Added support for custom triples and platforms via [JSON specifications](https://docs.rust-embedded.org/embedonomicon/custom-target.html):

- Added support for custom triples and platforms, under the optional `custom` feature.
- New methods on `Platform` and `Triple`:
  - `is_standard`: returns true if this is a standard platform (builtin or heuristic).
  - `is_custom`: returns true if this is a custom platform.
  - `is_builtin`: returns true if this is a builtin platform.
  - `is_heuristic`: returns true if this platform was determined heuristically.

#### Other additions

- Added `new_strict` methods to `Platform` and `Triple`, to disable heuristic target parsing.

### Fixed

- `target_os = "none"` is now correctly handled.

### Changed

- Internal dependency `cfg-expr` updated to 0.15.3, updating builtin targets to Rust 1.70.
- `PlatformSummary` is now non-exhaustive.
- `PlatformSummary::new` now creates a new `PlatformSummary` from a triple string. (The old `PlatformSummary::new` has been renamed to `PlatformSummary::from_platform`).

### Removed

- Removed deprecated `Error::UnknownPredicate` variant.
- `Error` no longer implements `Eq` or `PartialEq` due to one of its variants now containing `serde_json::Error`.

## [1.4.0] - 2023-04-15

### Changed

- Internal dependency `cfg-expr` updated to 0.15.0, updating builtin targets to Rust 1.68.
- MSRV updated to Rust 1.66.

## [1.3.1] - 2023-01-08

### Added

Added note to readme about MSRV for target-spec 1.3.x.

## [1.3.0] - 2023-01-08

### Changed

- Internal dependency `cfg-expr` updated to 0.13.0, updating builtin targets to Rust 1.66.
- MSRV updated to Rust 1.62.

## [1.2.2] - 2022-11-07

### Updated

Internal dependency `cfg-expr` updated to 0.12.0, enabling parsing of `target_abi`.

## [1.2.1] - 2022-10-25

### Added

- `ExpressionParseError` now carries information about the reason a target expression couldn't be
  parsed. This has been done to support pretty-printing via the new
  [target-spec-miette](https://crates.io/crates/target-spec-miette) crate.

## [1.2.0] - 2022-09-30

### Changed

- Repository location update.
- Internal dependency updates.
- MSRV updated to Rust 1.58.

Thanks to [Carol Nichols](https://github.com/carols10cents) for her contributions to this release!

## [1.1.0] - 2022-08-30

### Fixed

- Unknown predicates now evaluate to false, matching Cargo's behavior.
  - As a result, `Error::UnknownPredicate` is no longer in use and has been deprecated.

## [1.0.2] - 2022-05-29

### Changed

- Internal dependency updates.
- MSRV updated to Rust 1.56.

## [1.0.1] - 2022-02-07

### Added

- Update badges in README.
- Add `doc_cfg` to [the docs.rs build](https://docs.rs/target-spec).

## [1.0.0] - 2022-02-06

No breaking changes in this release compared to version 0.9.

### Changed

- Internal dependency version bump: `cfg-expr` updated to 0.10.0.

### [0.9.0] - 2021-10-01

## Added

- Target triples can now be parsed directly into a `PlatformSummary`.

### Changed

- `PlatformSummary::new` is now infallible.
- MSRV updated to Rust 1.53.

### Fixed

- `target-spec` now uses `cfg-expr`'s builtins by default, falling back to `target-lexicon` if `cfg-expr` isn't
  available.
  - This is because `target-lexicon` [may not always produce results](https://github.com/bytecodealliance/target-lexicon/issues/78)
    that match `rustc`'s target JSONs.

## [0.8.0] - 2021-09-13

### Added

- `Triple` represents a target triple, uniquely identified by a triple string.
- `TargetExpression` represents a target expression beginning with `cfg(`.

### Changed

- `target-spec` now uses [`target-lexicon`](https://github.com/bytecodealliance/target-lexicon) to parse triples,
  while continuing to use `cfg-expr` for expressions and evaluation.
  - Updated supported builtin targets to Rust 1.55.
  - `target-spec` is now more forward compatible, since new targets in future versions of Rust
    can be supported with non-breaking updates to `target-lexicon`.
- `TargetSpec` is now an enum with `Triple` and `TargetExpression` variants.
- `Platform` no longer has a lifetime parameter.
- Updated supported builtin targets to Rust 1.55.
- `cfg-expr` is now a private dependency again (`target-lexicon` is also a private dependency).
- MSRV updated to Rust 1.51.

## [0.7.0] - 2021-02-23

### Changed

- Public dependency version bumps:
  - `cfg-expr` updated to 0.7.1.
  - `proptest` updated to version 1 and the corresponding feature renamed to `proptest1`.

## [0.6.1] - 2021-02-14

### Changed

- `cfg-expr` version requirement relaxed: 0.6 through 0.7 are now supported. There are no API changes between
  the two versions.

## [0.6.0] - 2021-02-03

### Added

- `Platform` now implements `Hash + Eq + Ord`.

### Changed

- `TargetFeatures` and `Platform::add_flags` now accept `Cow<'static, str>`, simplifying lifetime management in many
  cases.
- `cfg-expr` updated to 0.6.0.

## [0.5.0] - 2020-12-02

### Changed

- Updated `cfg-expr` dependency to 0.5.0.

## [0.4.1] - 2020-08-28

### Fixed

- Fixed compilation on platforms without target features ([#175](https://github.com/guppy-rs/guppy/issues/175)).

## [0.4.0] - 2020-06-20

### Added

- New, optional feature `summaries` to provide serialization and deserialization
  for `Platform` and `TargetFeatures`.
- `Platform::is_custom` returns true if the platform was created with the `custom`
  constructor.

### Changed

- The error types have been unified into a single `Error` type.
- `Platform::new` and `Platform::current` now return errors instead of `None`.

## [0.3.0] - 2020-06-12

### Added

- `Platform::custom` creates platforms that are unknown to rustc.
  - This is supported through `cfg-expr`, which is now a public dependency.
  - Custom platforms are often found in embedded Rust.

### Changed

- In order to support custom platforms, `Platform::triple` now returns a `&'a str`
  instead of a `&'static str`.

## [0.2.4] - 2020-05-06

### Added

- New feature `proptest010` to generate random platforms for property testing.

## [0.2.3] - 2020-04-15

### Fixed

- Better handling of unknown flags.
  - Unknown flags now evaluate to false instead of erroring out.
  - Added `Platform::add_flags` to allow setting flags that evaluate to true.

These changes were prompted by how [`cargo-web`](https://github.com/koute/cargo-web) sets the `cargo_web` flag to
true for `cargo web build`.

## 0.2.2

This was mistakenly published and was yanked.

## [0.2.1] - 2020-04-07

### Changed

- Updated repository links.

## [0.2.0] - 2020-04-05

### Added

- Added support for parsing specs and platforms separately from evaluating them, making error-less evaluation possible.
- Added support for target features, including situations when target features are unknown.

### Changed

- Switched to [`cfg-expr`](https://github.com/EmbarkStudios/cfg-expr) as the backend for `cfg()` expressions.

## [0.1.0] - 2020-03-20

- Initial release.

[3.5.6]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.6
[3.5.5]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.5
[3.5.4]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.4
[3.5.3]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.3
[3.5.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.2
[3.5.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.1
[3.5.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.5.0
[3.4.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.4.2
[3.4.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.4.1
[3.4.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.4.0
[3.3.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.3.1
[3.3.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.3.0
[3.2.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.2.2
[3.2.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.2.1
[3.2.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.2.0
[3.1.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.1.0
[3.0.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.0.1
[3.0.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-3.0.0
[2.0.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-2.0.1
[2.0.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-2.0.0
[1.4.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.4.0
[1.3.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.3.1
[1.3.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.3.0
[1.2.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.2.2
[1.2.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.2.1
[1.2.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.2.0
[1.1.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.1.0
[1.0.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.0.2
[1.0.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.0.1
[1.0.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-1.0.0
[0.9.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.9.0
[0.8.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.8.0
[0.7.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.7.0
[0.6.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.6.1
[0.6.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.6.0
[0.5.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.5.0
[0.4.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.4.1
[0.4.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.4.0
[0.3.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.3.0
[0.2.4]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.2.4
[0.2.3]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.2.3
[0.2.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.2.1
[0.2.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.2.0
[0.1.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-0.1.0
