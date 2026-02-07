# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.8.1] - 2024-10-05
- Fix bug when executing trial on fewer threads than trials (thanks @hanna-kruppe for catching this)

## [0.8.0] - 2024-10-05
- **Breaking**: bump MSRV to 1.65
- Remove `threadpool` dependency, getting rid of memory leaks observed when running under valgrind (thanks @Felix-El) in [#46](https://github.com/LukasKalbertodt/libtest-mimic/pull/46)
- Switch from `termcolor` to `anstream` to get rid of duplicate dependencies (thanks @hanna-kruppe) in [#44](https://github.com/LukasKalbertodt/libtest-mimic/pull/44)
- Bump dev-dependency `fastrand` to `2` (thanks @alexanderkjall) in [#47](https://github.com/LukasKalbertodt/libtest-mimic/pull/47)
- Fix outdated docs


## [0.7.3] - 2024-05-10
- Default to single-threaded tests for WebAssembly (thanks @alexcrichton) in [#41](https://github.com/LukasKalbertodt/libtest-mimic/pull/41)

## [0.7.2] - 2024-04-09
- Fix `Conclusion::exit_code` (logic was inverted in 0.7.1)

## [0.7.1] - 2024-04-09
- Add `Conclusion::exit_code` and note about destructors/cleanup to docs of `exit` and `exit_if_failed` [`e938e537e`](https://github.com/LukasKalbertodt/libtest-mimic/commit/e938e537e02d8cb9c9791fa63bcb8f4746dc3511)


## [0.7.0] - 2024-01-14
- Also check `kind` when filtering tests (thanks @sunshowers) in [#30](https://github.com/LukasKalbertodt/libtest-mimic/pull/30)
  - This is potentially breaking as additional or fewer tests might be executed in some situations.
- Add JSON format output (thanks @PaulWagener and @t-moe) in [#35](https://github.com/LukasKalbertodt/libtest-mimic/pull/35)
- Add no-op flags to add CLI compatibility for IntellJ Rust (thanks @Dinnerbone and @t-moe) [#28](https://github.com/LukasKalbertodt/libtest-mimic/pull/28) / [`70cdc55`](https://github.com/LukasKalbertodt/libtest-mimic/commit/70cdc55ee50df8325d11f5e2cbe53c6bf74d375d)

## [0.6.1] - 2022-11-05
### Fixed
- Actually spawn as many threads as specified by `--test-threads` (thanks @hgzimmerman) in [#32](https://github.com/LukasKalbertodt/libtest-mimic/pull/32).
- Fix & improve docs
- Fix badge in README

### Changed
- Deemphasize MSRV by removing check and note from README in [#24](https://github.com/LukasKalbertodt/libtest-mimic/pull/24).


## [0.6.0] - 2022-11-05
### Changed
- **Breaking**: Updated `clap` to version 4 (thanks @msrd0)
- **Breaking**: Bump MSRV to 1.60 (due to the clap update)

### Removed
- **Breaking**: Remove `FromStr` impls for `args::{ColorSetting, FormatSetting}` (use `clap::ValueEnum` instead).

## [0.5.2] - 2022-08-14
### Added
- Re-add `--nocapture` as a noop argument [#18](https://github.com/LukasKalbertodt/libtest-mimic/pull/18) (thanks @sunshowers)

### Fixed
- Link in documentation

## [0.5.1] - 2022-08-13
### Added
- `Trial::{name, kind, has_ignored_flag, is_test, is_bench}` getters

## [0.5.0] - 2022-08-13

Most parts of this library have been rewritten and the API has changed a lot.
You might be better of just reading the new docs instead of this change log.
I do think the new API is better in many regards.
Apart from an improved API, changes that motivated the rewrite are marked with ⭐.

### Changed
- **Breaking**: bump MSRV to 1.58
- **Breaking**: Rename `Test` to `Trial`
- **Breaking**: Rename `run_tests` to `run`
- ⭐ **Breaking**: Make every `Trial` have a runner function instead of `data` + a
  global runner function. Thus, the third parameter of `run` is no more. I think
  this model is more intuitive.
- **Breaking**: Add `Trial::{test, bench}` constructor functions, use builder
  pattern, and make fields private.
- **Breaking**: rename `Args::num_threads` to `test_threads`
- **Breaking**: make fields of `Conclusion` public and remove getter methods
- **Breaking**: remove `RunnerEvent`. This should not have been public.
- ⭐ Tests are now run in main thread when `--test-threads=1` is specified
- ⭐ Reduce number of indirect dependencies considerably
- Fix `rust-version` field in `Cargo.toml` (thanks @hellow554)
- Fix `--ignored` behavior
- Fix some CLI error messages

### Added
- ⭐Panics in test runners are caught and treated as failure
- ⭐ Lots of integration tests (should make any future development of this library way easier)
- Add `must_use` message for `Conclusion`
- Print total execution time at the end of the run
- Allow benchmarks to run in test mode
- `--include-ignored`

### Removed
- **Breaking**: remove unsupported CLI options. They were ignored anyway, but
  the CLI would accept them.


## [0.4.1] - 2022-06-07

- Add `rust = "1.56"` to `Cargo.toml`, stating the existing MSRV.
- Update `crossbeam-channel` to deduplicate some indirect dependencies.

## [0.4.0] - 2022-05-13
- **Breaking**: Update to Rust 2021, bumping MSRV to 1.56
- Fix `--list --ignored` behavior


## [0.3.0] - 2020-06-28
### Added
- Add support for running tests in parallel #4
- Add `Arguments::from_iter` #5

## [0.2.0] - 2019-10-02
### Changed
- Upgrade dependencies #3
- Flush stdout after printing test name 4a36b3318b69df233b0db7d1af3caf276e6bb070

### Fixed
- Fix overflow bug when calculating number of passed tests 264fe6f8a986ab0c02f4a85e64e42ee17596923c

## 0.1.0 - 2018-07-23
### Added
- Everything.


[Unreleased]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.8.1...HEAD
[0.8.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.8.0...v0.8.1
[0.8.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.7.3...v0.8.0
[0.7.3]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.7.2...v0.7.3
[0.7.2]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.7.1...v0.7.2
[0.7.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.7.0...v0.7.1
[0.7.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.6.1...v0.7.0
[0.6.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.6.0...v0.6.1
[0.6.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.5.2...v0.6.0
[0.5.2]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.4.1...v0.5.0
[0.4.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.1.0...v0.2.0
[0.1.1]: https://github.com/LukasKalbertodt/libtest-mimic/compare/v0.1.0...v0.1.1
