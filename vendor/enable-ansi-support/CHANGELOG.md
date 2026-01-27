# Changelog

All notable changes to this project will be documented in this file.

This project adheres to [Semantic Versioning](https://semver.org).

## [0.3.1] - 2025-10-02

- Bump Rust edition to 2021.

## [0.3.0] - 2025-10-02

- `windows-sys` dependency updated to version `0.61.0`.
- MSRV updated to Rust 1.71.

## [0.2.1] - 2022-12-10

### Changed

- `enable_ansi_support` now returns `std::io::Error` rather than the raw Win32 error code.
- Internal implementation now uses the windows-sys crate.
- MSRV updated to Rust 1.49, and new MSRV policy defined: updates will be considered a breaking
  change.

## [0.2.0] - 2022-12-10

This release encountered a publishing issue.

## [0.1.2] - 2022-01-19

- Update links to new repository location.

## [0.1.1] - 2021-12-06

- Add example to readme -- thanks [@jam1garner](https://github.com/jam1garner)!

## [0.1.0] - 2021-12-03

- Initial release.

[0.3.1]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.3.1
[0.3.0]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.3.0
[0.2.1]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.2.1
[0.2.0]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.2.0
[0.1.2]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.1.2
[0.1.1]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.1.1
[0.1.0]: https://github.com/sunshowers-code/enable-ansi-support/releases/tag/0.1.0
