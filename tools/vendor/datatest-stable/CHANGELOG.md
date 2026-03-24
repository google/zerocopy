# Changelog

## [0.3.3] - 2025-09-29

### Fixed

Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

## [0.3.2] - 2024-12-28

### Added

- `pattern` is now optional in the `harness!` macro. If not specified, the default pattern is
  `r".*"` (match all files).

### Fixed

- Restored the ability to use absolute paths as the `root` argument.

## [0.3.1] - 2024-12-25

### Fixed

Fixed documentation for `include_dir` invocations. They must typically be called
via `include_dir!("$CARGO_MANIFEST_DIR/path/to/data")`.

## [0.3.0] - 2024-12-24

### Added

- Support for embedding data into the test binary via an optional `include-dir`
  feature. For more information and recommendations for when to use this, see [the
  readme](https://crates.io/crates/datatest-stable).

### Changed

- The macro call format has changed to:

  ```rust
  datatest_stable::harness! {
      { test = fn_name, path = &include_dir!("path/to/data"), pattern = r"^.*$" },
      // ...
  }
  ```

  This is both a nicer format for expressing multiple tests, and a signal to
  indicate the other breaking changes in this release.

- Regex patterns now match against the path relative to the *include directory*, rather
  than paths with respect to the crate root. This change was made for uniformity with the
  `include_dir` implementation.

- On Windows, paths are now universally normalized to use forward slashes. This change
  was made to ensure that test names and paths are consistent across platforms.

## [0.2.10] - 2024-12-08

- Internal dependency updates: update `libtest-mimic` to 0.8.1, and `fancy-regex` to 0.14.0.
- Update MSRV to Rust 1.72.

## [0.2.9] - 2024-04-25

### Added

Previously, the test functions supported were `fn(&Path) -> Result<()>` and `fn(&Utf8Path) -> Result<()>`. This release adds additional supported functions:

- `fn(&P, String) -> datatest_stable::Result<()>` where `P` is `Path` or `Utf8Path`. If the
  extra `String` parameter is specified, the contents of the file will be loaded and passed in
  as a string (erroring out if that failed).
- `fn(&P, Vec<u8>) -> datatest_stable::Result<()>` where `P` is `Path` or `Utf8Path`. If the
  extra `Vec<u8>` parameter is specified, the contents of the file will be
  loaded and passed in as a `Vec<u8>` (erroring out if that failed).

## [0.2.8] - 2024-04-24

### Fixed

- Fixed quadratic performance issue with nextest, where datatest-stable would iterate over the
  entire list of files for each test. Thanks [@zaneduffield](https://github.com/zaneduffield) for
  your first contribution!

## [0.2.7] - 2024-04-21

### Changed

- Switched to the `fancy-regex` crate, which allows for matching against regexes with
  lookahead/behind and backreferences. Thanks [@webbdays](https://github.com/webbdays) for your
  first contribution!

- MSRV updated to Rust 1.66.

## [0.2.6] - 2024-04-09

- Update to `libtest-mimic 0.7.2`, and use the upstream implementation of `ExitCode`.

## [0.2.5] - 2024-04-08

- Exit main via `ExitCode` rather than `std::process::exit()`. This appears to fix coverage on
  Windows.

## [0.2.4] - 2024-04-08

This is a periodic maintenance release.

- Update internal dependency versions, including libtest-mimic to 0.7.0.
- Update "docs (main)" link to the new location at [https://datatest-stable.nexte.st](https://datatest-stable.nexte.st).
- Update MSRV to Rust 1.65.

## [0.2.3] - 2023-08-29

Updated README.

## [0.2.2] - 2023-08-29

### Added

- Restored compatibility with `fn(&Path) -> Result<()>`. The harness now can take either `fn(&Path) -> Result<()>` or `fn(&Utf8Path) -> Result<()>`.

## [0.2.1] - 2023-08-29

### Changed

- The test signature is now `fn(&`[`Utf8Path`]`)` rather than `fn(&Path)`. If necessary, a `Utf8Path` can be converted to a `&Path` with [`.as_ref()`] or [`.as_std_path()`].
- Non-Unicode paths now consistently produce errors. Previously, the treatment of such paths was inconsistent -- they would either be skipped or produce errors.
- Internal dependency update: libtest-mimic updated to version 0.6.1.
- MSRV updated to Rust 1.60.

[`Utf8Path`]: https://docs.rs/camino/latest/camino/struct.Utf8Path.html
[`.as_ref()`]: https://docs.rs/camino/latest/camino/struct.Utf8Path.html#impl-AsRef%3COsStr%3E-for-Utf8Path
[`.as_std_path()`]: https://docs.rs/camino/latest/camino/struct.Utf8Path.html#method.as_std_path

## [0.2.0] - 2023-08-29

This version had a publishing issue.

## [0.1.3] - 2022-08-15

### Changed

- Errors are now displayed with the `Debug` implementation, which prints out the full error chain
  with libraries like `anyhow` or `eyre`, rather than the `Display` implementation. Thanks
  [Alex Badics] for your first contribution!
- MSRV updated to Rust 1.58.

### Internal improvements

- datatest-stable now uses libtest-mimic 0.5.2. Thanks [Lukas Kalbertodt] (maintainer of
  libtest-mimic) for your first contribution!

[Alex Badics]: https://github.com/badicsalex
[Lukas]: https://github.com/LukasKalbertodt

## [0.1.2] - 2022-05-22

### Changed

- New internal implementation, based on top of [libtest-mimic](https://github.com/LukasKalbertodt/libtest-mimic).
- Repository updated to [nextest-rs/datatest-stable](https://github.com/nextest-rs/datatest-stable).
- MSRV updated to Rust 1.56.

There are no functional changes in this release.

## [0.1.1] - 2021-04-16

### Added

- Initial release with basic support for data-driven tests.

(Version 0.1.0 was yanked because of a metadata issue.)

[0.3.3]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.3.3
[0.3.2]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.3.2
[0.3.1]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.3.1
[0.3.0]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.3.0
[0.2.10]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.10
[0.2.9]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.9
[0.2.8]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.8
[0.2.7]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.7
[0.2.6]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.6
[0.2.5]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.5
[0.2.4]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.4
[0.2.3]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.3
[0.2.2]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.2
[0.2.1]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.2.1
[0.1.3]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.1.3
[0.1.2]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.1.2
[0.1.1]: https://github.com/nextest-rs/datatest-stable/releases/tag/datatest-stable-0.1.1
