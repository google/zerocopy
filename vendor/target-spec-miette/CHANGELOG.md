# Changelog

## [0.4.5] - 2025-09-29

### Fixed

Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

### Changed

- MSRV updated to Rust 1.86.

## [0.4.4] - 2024-12-25

Fixed path to fixtures.

## [0.4.3] - 2024-12-25

### Added

A new optional `fixtures` feature includes a set of test fixture files, which
can be useful to test graceful error handling for downstream users.

The exact set of fixtures included and their contents are not part of the semver
guarantees. If you use the fixtures as inputs to snapshot tests, you may need to
update the snapshots as part of updating target-spec-miette. (So you'll likely
want to check in `Cargo.lock`.)

## [0.4.2] - 2024-12-23

### Changed

- Minor tweaks to `Diagnostic` error messages.

## [0.4.1] - 2024-12-22

### Added

- Added implementation for target-spec's `CustomTripleCreateError`.

### Changed

- MSRV updated to Rust 1.82.

## [0.4.0] - 2024-02-05

### Changed

- Updated to miette 7.
- MSRV updated to Rust 1.73.

## [0.3.0] - 2023-06-25

### Changed

- Updated to target-spec 3.

## [0.2.0] - 2023-06-19

### Changed

- Updated to target-spec 2.
- MSRV updated to Rust 1.66.

## [0.1.0] - 2022-10-25

Initial release with support for miette 5.

[0.4.5]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.5
[0.4.4]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.4
[0.4.3]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.3
[0.4.2]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.2
[0.4.1]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.1
[0.4.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.4.0
[0.3.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.3.0
[0.2.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.2.0
[0.1.0]: https://github.com/guppy-rs/guppy/releases/tag/target-spec-miette-0.1.0
