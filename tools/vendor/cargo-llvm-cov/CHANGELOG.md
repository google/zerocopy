# Changelog

All notable changes to this project will be documented in this file.

This project adheres to [Semantic Versioning](https://semver.org).

Releases may yanked if there is a security bug, a soundness bug, or a regression.

<!--
Note: In this file, do not use the hard wrap in the middle of a sentence for compatibility with GitHub comment style markdown rendering.
-->

## [Unreleased]

## [0.6.24] - 2026-01-22

- Support `*-windows-gnullvm` targets. ([#470](https://github.com/taiki-e/cargo-llvm-cov/pull/470), thanks @mati865)

- Fix a bug causing `--profraw-only` to remove too many files. ([#469](https://github.com/taiki-e/cargo-llvm-cov/pull/469), thanks @smoelius)

- Distribute prebuilt binary for AArch64 Windows.
  `-C instrument-coverage` doesn't support `aarch64-pc-windows-msvc` yet ([rust-lang/rust#150123](https://github.com/rust-lang/rust/issues/150123)), but cross-compile to `aarch64-pc-windows-gnullvm` works.

## [0.6.23] - 2026-01-06

- Enable [release immutability](https://docs.github.com/en/code-security/supply-chain-security/understanding-your-software-supply-chain/immutable-releases).

## [0.6.22] - 2025-12-30

- Update documentation to mention the way to get coverage for `wasm32-unknown-unknown` target.

- Exclude files named `tests.rs`/`*_tests.rs`/`*-tests.rs` from the report by default.

## [0.6.21] - 2025-10-10

- Update minimal version of `cargo-config2` to 0.1.39 to fix regression causing "invalid type: .., expected struct TargetConfig" error when a custom field used in `target.<triple>` config. ([#454](https://github.com/taiki-e/cargo-llvm-cov/issues/454))

## [0.6.20] - 2025-10-04

- Support Cargo `build-dir` that added in Cargo 1.91. ([#452](https://github.com/taiki-e/cargo-llvm-cov/pull/452))

- Update minimal version of `cargo-config2` to 0.1.38 to improve support for target names that contain ".". ([#446](https://github.com/taiki-e/cargo-llvm-cov/issues/446))

## [0.6.19] - 2025-09-07

- Distribute prebuilt binaries for powerpc64le/riscv64gc/s390x Linux.

## [0.6.18] - 2025-07-19

- Fix bug in exclude of local vendored sources on Windows. ([#442](https://github.com/taiki-e/cargo-llvm-cov/pull/442), thanks @LittleBoxOfSunshine)

## [0.6.17] - 2025-07-06

- Exclude local vendored sources by default. ([#438](https://github.com/taiki-e/cargo-llvm-cov/pull/438), thanks @Altair-Bueno)

- Remove dependency on `is_executable`. ([#422](https://github.com/taiki-e/cargo-llvm-cov/pull/422))

- Update `opener` to 0.8.

- Update `duct` to 1.

- Documentation improvements.

## [0.6.16] - 2025-01-16

- Add `--with-pwsh-env-prefix` to `cargo llvm-cov show-env` subcommand. ([#411](https://github.com/taiki-e/cargo-llvm-cov/pull/411), thanks @LittleBoxOfSunshine)

- Document usage with GitLab CI. ([#405](https://github.com/taiki-e/cargo-llvm-cov/pull/405), thanks @jaskij)

- Document usage with afl.rs. ([#369](https://github.com/taiki-e/cargo-llvm-cov/pull/369), thanks @njelich)

- Update `ruzstd` to 0.8.

  This increases the rustc version required to build cargo-llvm-cov. (rustc 1.73+ -> 1.81+)
  The cargo/rustc version required to run cargo-llvm-cov remains unchanged.

## [0.6.15] - 2024-12-21

- Remove dependency on `home` to relax the MSRV on Windows.

- Weaken errors related to rustc version to warnings. ([#407](https://github.com/taiki-e/cargo-llvm-cov/pull/407))

## [0.6.14] - 2024-10-12

- Add unstable `--mcdc` flag to enable mcdc coverage. ([#383](https://github.com/taiki-e/cargo-llvm-cov/pull/383), thanks @Swatinem)

## [0.6.13] - 2024-09-14

- Distribute prebuilt binary for x86_64 FreeBSD.

## [0.6.12] - 2024-09-03

- Add `--profraw-only` option to `cargo llvm-cov clean` subcommand. ([#385](https://github.com/taiki-e/cargo-llvm-cov/pull/385), thanks @smoelius)

- Respect `target.<triple>.rustdocflags` [that added in Cargo 1.78](https://github.com/rust-lang/cargo/pull/13197).

- Disable quick-install fallback of cargo-binstall.

## [0.6.11] - 2024-07-18

- Add support for MC/DC coverage. ([#363](https://github.com/taiki-e/cargo-llvm-cov/pull/363), thanks @aytey)

- Documentation improvements.

## [0.6.10] - 2024-06-01

- Update `ruzstd` to 0.7.

  This increases the rustc version required to build cargo-llvm-cov. (rustc 1.70+ -> 1.73+)
  The cargo/rustc version required to run cargo-llvm-cov remains unchanged.

## [0.6.9] - 2024-04-05

- Skip merging profraw data if profraw files don't exist and a profdata file already exists. ([#360](https://github.com/taiki-e/cargo-llvm-cov/pull/360), thanks @weiznich)

- Update `opener` to 0.7.

## [0.6.8] - 2024-03-16

- Add unstable `--branch` flag to enable branch coverage. ([#356](https://github.com/taiki-e/cargo-llvm-cov/pull/356))

## [0.6.7] - 2024-03-10

- Add `--nextest-archive-file` option to `cargo llvm-cov report` to support calling it for the result of `cargo llvm-cov nextest --archive-file`. ([#355](https://github.com/taiki-e/cargo-llvm-cov/pull/355))

- Add unstable `--dep-coverage` option to show coverage of th specified dependency instead of the crates in the current workspace. ([#353](https://github.com/taiki-e/cargo-llvm-cov/pull/353))

- Fix issues in report when merging coverage. ([#354](https://github.com/taiki-e/cargo-llvm-cov/pull/354))

## [0.6.6] - 2024-02-22

- It is no longer needed to pass `--target`/`--release`/`--cargo-profile` to `cargo llvm-cov nextest --archive-file` in most cases. Options passed to `cargo llvm-cov nextest-archive` are now respected. ([#349](https://github.com/taiki-e/cargo-llvm-cov/pull/349))

- Support `--release` and `--cargo-profile` options for `cargo llvm-cov nextest-archive`. ([#348](https://github.com/taiki-e/cargo-llvm-cov/pull/348))

## [0.6.5] - 2024-02-07

- Add `--skip-functions` flag to coverage generation. ([#346](https://github.com/taiki-e/cargo-llvm-cov/pull/346), thanks @mlveggo)

## [0.6.4] - 2024-01-25

- Make `home` dependency Windows-only dependency.

## [0.6.3] - 2024-01-24

- Fix "The file was not recognized as a valid object file" error with `--doc`/`--doctests` flag on WSL. ([#343](https://github.com/taiki-e/cargo-llvm-cov/pull/343))

## [0.6.2] - 2024-01-18

- Support setting file name of `LLVM_PROFILE_FILE`. ([#340](https://github.com/taiki-e/cargo-llvm-cov/pull/340))

## [0.6.1] - 2024-01-13

- Support `--target` option for `cargo llvm-cov nextest-archive`. ([#334](https://github.com/taiki-e/cargo-llvm-cov/pull/334))

- Support `--no-cfg-coverage` and `--no-cfg-coverage-nightly` flags in `cargo llvm-cov show-env`. ([#333](https://github.com/taiki-e/cargo-llvm-cov/pull/333))

## [0.6.0] - 2023-12-28

- Make `--hide-instantiations` flag default, and add `--show-instantiations` flag to allow opt-in of the previous behavior. ([#330](https://github.com/taiki-e/cargo-llvm-cov/pull/330))

- Support `cargo llvm-cov nextest --archive-file`. ([#266](https://github.com/taiki-e/cargo-llvm-cov/pull/266), thanks @magnusja)

- Add hint about cfgs. ([#330](https://github.com/taiki-e/cargo-llvm-cov/pull/330))

## [0.5.39] - 2023-12-16

- Remove dependency on `is-terminal`.

## [0.5.38] - 2023-12-13

- Fix panic when running tests at `/` such as in docker. ([#326](https://github.com/taiki-e/cargo-llvm-cov/pull/326), thanks @MikeDevresse)

## [0.5.37] - 2023-11-17

- Add `--fail-under-{functions,regions}` options. ([#323](https://github.com/taiki-e/cargo-llvm-cov/pull/323), thanks @CobaltCause)

## [0.5.36] - 2023-10-30

- Support `--doctests` flag in `cargo llvm-cov report` and `cargo llvm-cov show-env`.

## [0.5.35] - 2023-10-18

- Improve compile time.

## [0.5.34] - 2023-10-17

- Improve performance and reduce disc usage by passing `--no-deps` to `cargo metadata`.

## [0.5.33] - 2023-09-26

- Fix "The file was not recognized as a valid object file" error on WSL. ([#317](https://github.com/taiki-e/cargo-llvm-cov/pull/317))

## [0.5.32] - 2023-09-23

- Fix an issue where codes in the standard library are not being properly excluded from reports when using a custom toolchain. ([#311](https://github.com/taiki-e/cargo-llvm-cov/pull/311))

- Document a way to display coverage in VS Code.

## [0.5.31] - 2023-08-24

- Fix empty source path generated in cobertura.xml. ([#309](https://github.com/taiki-e/cargo-llvm-cov/pull/309), thanks @mstyura)

- Prepare for future branch coverage support. ([#308](https://github.com/taiki-e/cargo-llvm-cov/pull/308), thanks @Swatinem)

## [0.5.30] - 2023-08-23

- Fix an issue where coverage is not collected or fails to generate coverage on `cdylib` or proc-macro crate on Windows. ([#307](https://github.com/taiki-e/cargo-llvm-cov/pull/307))

- Escape values that are shown by `show-env` subcommand. ([#307](https://github.com/taiki-e/cargo-llvm-cov/pull/307))

## [0.5.29] - 2023-08-23

- Diagnostics improvements. ([#302](https://github.com/taiki-e/cargo-llvm-cov/pull/302))

## [0.5.28] - 2023-08-22

- Diagnostics improvements. ([#305](https://github.com/taiki-e/cargo-llvm-cov/pull/305), [#306](https://github.com/taiki-e/cargo-llvm-cov/pull/306))

## [0.5.27] - 2023-08-14

- Allow nightly to be specified by setting `RUSTC_BOOTSTRAP=1`, the same as for rustc and cargo. ([#298](https://github.com/taiki-e/cargo-llvm-cov/pull/298), thanks @RocketJas)

## [0.5.26] - 2023-08-12

- Fix support for `trybuild` 1.0.76+. ([#301](https://github.com/taiki-e/cargo-llvm-cov/pull/301))

## [0.5.25] - 2023-08-06

- Use `--show-missing-lines` logic in `--fail-uncovered-lines`. ([#277](https://github.com/taiki-e/cargo-llvm-cov/pull/277), thanks @michaelvlach)

- cargo-llvm-cov no longer sets the `CARGO_INCREMENTAL=0` environment variable. ([#297](https://github.com/taiki-e/cargo-llvm-cov/pull/297))

## [0.5.24] - 2023-07-28

- Update `cargo_metadata` to 0.17.

## [0.5.23] - 2023-07-07

- Inject additional contextual information about cargo-llvm-cov into the JSON output of llvm-cov. ([#289](https://github.com/taiki-e/cargo-llvm-cov/pull/289), thanks @dnaka91)

  It allows other programs, that rely on this output, to make certain assertions about the behavior of cargo-llvm-cov and can help to share common information.

## [0.5.22] - 2023-06-29

- Fix regression introduced in 0.5.21.

## [0.5.21] - 2023-06-29

**Note:** This release has been yanked due to regression fixed in 0.5.22.

- Fix "`-Z doctest-in-workspace` has been stabilized in the 1.72 release" warning on the latest nightly.

## [0.5.20] - 2023-06-02

- cargo-llvm-cov no longer sets the `RUST_TEST_THREADS` and `NEXTEST_TEST_THREADS` environment variables. cargo-llvm-cov now adopts another efficient way to workaround [rust-lang/rust#91092](https://github.com/rust-lang/rust/issues/91092). ([#279](https://github.com/taiki-e/cargo-llvm-cov/pull/279))

  This may greatly improve performance, [especially when using `cargo llvm-cov nextest`](https://github.com/taiki-e/cargo-llvm-cov/pull/279#issuecomment-1552058044).

## [0.5.19] - 2023-04-28

- Fix handling of `--cargo-profile` option for `cargo llvm-cov nextest`. ([#269](https://github.com/taiki-e/cargo-llvm-cov/pull/269))

## [0.5.18] - 2023-04-25

- Support `--ignore-run-fail` for `cargo llvm-cov nextest`. ([#263](https://github.com/taiki-e/cargo-llvm-cov/pull/263))

## [0.5.17] - 2023-04-21

- Set `CARGO_LLVM_COV` environment variable. ([#259](https://github.com/taiki-e/cargo-llvm-cov/pull/259), thanks @def-)

## [0.5.16] - 2023-04-18

- Improve the `--codecov` flag to match how region coverage is calculated to the HTML report. ([#255](https://github.com/taiki-e/cargo-llvm-cov/pull/255), thanks @andrewgazelka)

## [0.5.15] - 2023-04-15

- Fix version detection with dev build. ([#257](https://github.com/taiki-e/cargo-llvm-cov/pull/257), thanks @tofay)

## [0.5.14] - 2023-04-05

- Fix an issue where `--codecov` flag reports a fully covered line as only partially covered or not covered. ([#253](https://github.com/taiki-e/cargo-llvm-cov/pull/253), thanks @andrewgazelka)

## [0.5.13] - 2023-04-03

- Fix an issue where `--codecov` flag doesn't exclude files that should be excluded from the report. ([#251](https://github.com/taiki-e/cargo-llvm-cov/pull/251))

## [0.5.12] - 2023-04-02

- Add `--codecov` flag to support "Codecov Custom Coverage" format. This allows using region coverage on Codecov. ([#249](https://github.com/taiki-e/cargo-llvm-cov/pull/249), thanks @andrewgazelka)

## [0.5.11] - 2023-02-28

- Remove dependency on `tempfile`.

## [0.5.10] - 2023-02-23

- Update `lexopt` to 0.3.

- Update `cargo-config2` to 0.1.5.

## [0.5.9] - 2023-01-15

- Support `trybuild` 1.0.76+. ([#238](https://github.com/taiki-e/cargo-llvm-cov/pull/238))

## [0.5.8] - 2023-01-15

- Fix handling of cases where the target directory contains glob characters.

## [0.5.7] - 2023-01-11

- Fix "cannot satisfy dependencies so `std` only shows up once" error on `cargo llvm-cov nextest` introduced in 0.5.4.

## [0.5.6] - 2023-01-11

- Distribute prebuilt macOS universal binary.

## [0.5.5] - 2023-01-10

- Fix regression on doctests introduced in 0.5.4.

## [0.5.4] - 2023-01-09

- Use [`cargo-config2`](https://github.com/taiki-e/cargo-config2) to load Cargo configuration. ([#237](https://github.com/taiki-e/cargo-llvm-cov/pull/237))

  This brings the following improvements:

  - More accurate cargo configuration loading and resolution.
  - Fix installation failure on Rust 1.60 and 1.61 by removing dependency on `target-spec`.
  - Remove run-time dependency on unstable `cargo config get`. (Previously, this command was used in a form allowing failure, like `rust-analyzer` does.)

## [0.5.3] - 2022-12-15

- Fix an issue where coverage of binary targets containing hyphens was not collected correctly. ([#232](https://github.com/taiki-e/cargo-llvm-cov/pull/232))

- Fix help messages for `cargo llvm-cov report` subcommand.

## [0.5.2] - 2022-11-27

- Fix an issue where if `--cobertura` and `--output-path` are used simultaneously, then the saved file doesn't contain the cobertura-style output. ([#228](https://github.com/taiki-e/cargo-llvm-cov/pull/228), thanks @yuval-nextsilicon)

## [0.5.1] - 2022-11-27

- Add `--cobertura` flag to support [Cobertura](https://cobertura.github.io/cobertura)'s XML report format. ([#224](https://github.com/taiki-e/cargo-llvm-cov/pull/224), thanks @mike-kfed)

- Limit the number of test threads for `nextest` to work around [rust-lang/rust#91092](https://github.com/rust-lang/rust/issues/91092). ([#223](https://github.com/taiki-e/cargo-llvm-cov/pull/223))

  For subcommands other than `cargo llvm-cov nextest`, the same workaround has already been applied since 0.4.6.

- Replace `atty` with `is-terminal`. ([#226](https://github.com/taiki-e/cargo-llvm-cov/pull/226))

## [0.5.0] - 2022-09-10

- Improve handling of cases where `llvm-tools-preview` component is not installed. ([#219](https://github.com/taiki-e/cargo-llvm-cov/pull/219))

  **TL;DR:** You no longer need to install `llvm-tools-preview` before running cargo-llvm-cov in most cases.

  The new logic is based on the logic used by Miri when `rust-src` component or `xargo` is not installed.

  See [#219](https://github.com/taiki-e/cargo-llvm-cov/pull/219) for more.

- Fix various CLI-related bugs. ([#197](https://github.com/taiki-e/cargo-llvm-cov/pull/197), [#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217))

  This fixes various bugs related to subcommands (especially `nextest`). The following is a partial list:
  - Fix errors for `nextest`-specific options. ([#151](https://github.com/taiki-e/cargo-llvm-cov/issues/151), [#144](https://github.com/taiki-e/cargo-llvm-cov/pull/144#issuecomment-1072772281), [#213](https://github.com/taiki-e/cargo-llvm-cov/issues/213), etc.)
  - Fix problems where some options were ignored in `cargo llvm-cov run` and `cargo llvm-cov nextest` subcommands. ([#151](https://github.com/taiki-e/cargo-llvm-cov/issues/151), [#144](https://github.com/taiki-e/cargo-llvm-cov/pull/144#issuecomment-1072750780), [#198](https://github.com/taiki-e/cargo-llvm-cov/issues/198#issuecomment-1193305155), etc.)
  - Fix help messages for subcommands.

- Add `cargo llvm-cov report` subcommand. ([#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217)) This is equivalent to `cargo llvm-cov --no-run`, but it has a more obvious name and better diagnostics.

- Add `cargo llvm-cov test` subcommand. ([#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217)) This is equivalent to `cargo llvm-cov` without subcommand, except that test name filtering is supported.

- Deprecate `--no-run` in favor of `cargo llvm-cov report` subcommand. ([#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217))

- Add `--no-clean` flag to build without cleaning any old build artifacts. See [#214](https://github.com/taiki-e/cargo-llvm-cov/pull/214) for more.

- cargo-llvm-cov no longer redirects output from stdout to stderr if unnecessary. ([#206](https://github.com/taiki-e/cargo-llvm-cov/pull/206))

- Support shared `target` directory. ([#215](https://github.com/taiki-e/cargo-llvm-cov/pull/215))

- Support `--keep-going` (unstable), `--ignore-rust-version`. ([#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217))

- Support `--exclude-from-report` and `--ignore-run-fail` for `cargo llvm-cov run`. ([#217](https://github.com/taiki-e/cargo-llvm-cov/pull/217))

- Support relative path in `CARGO_LLVM_COV_TARGET_DIR`. ([#220](https://github.com/taiki-e/cargo-llvm-cov/pull/220))

- Add `LLVM_COV_FLAGS`/`LLVM_PROFDATA_FLAGS` environment variables to pass additional flags to llvm-cov/llvm-profdata in a space-separated list. ([#220](https://github.com/taiki-e/cargo-llvm-cov/pull/220))

- Deprecate `CARGO_LLVM_COV_FLAGS`/`CARGO_LLVM_PROFDATA_FLAGS` environment variables instead of `LLVM_COV_FLAGS`/`LLVM_PROFDATA_FLAGS` environment variables. ([#220](https://github.com/taiki-e/cargo-llvm-cov/pull/220))

- Document environment variables that cargo-llvm-cov reads. ([#220](https://github.com/taiki-e/cargo-llvm-cov/pull/220))

- Remove `cargo llvm-cov help` subcommand that was added automatically by clap. ([#197](https://github.com/taiki-e/cargo-llvm-cov/pull/197))

- cargo-llvm-cov no longer maps the `--jobs` (`-j`) option to llvm-cov/llvm-profdata's `-num-threads` option.

  This is to avoid confusion when using the `-j` option with `nextest`, which uses the `-j` option in a different sense than cargo.

- Improve compile time. ([#197](https://github.com/taiki-e/cargo-llvm-cov/pull/197))

- Diagnostics improvements.

## [0.4.14] - 2022-08-06

- Fix an issue where "File name or extension is too long" error occurs in Windows. ([#203](https://github.com/taiki-e/cargo-llvm-cov/pull/203), thanks @messense)

## [0.4.13] - 2022-08-01

- Fix an issue where merging of multiple `cargo llvm-cov run` coverage did not work.

## [0.4.12] - 2022-07-30

- Support `target.<cfg>.rustflags`. ([#200](https://github.com/taiki-e/cargo-llvm-cov/pull/200))

- Remove workaround for an old rustc bug on Windows if unnecessary. ([#199](https://github.com/taiki-e/cargo-llvm-cov/pull/199), thanks @ldm0)

## [0.4.11] - 2022-07-20

- Fix handling of existing CFLAGS/CXXFLAGS when `--include-ffi` flag is passed. ([#196](https://github.com/taiki-e/cargo-llvm-cov/pull/196))

## [0.4.10] - 2022-07-18

- Support coverage of C/C++ code linked to Rust library/binary. ([#194](https://github.com/taiki-e/cargo-llvm-cov/pull/194))

## [0.4.9] - 2022-07-07

- Fix an issue where some files were incorrectly ignored in reports. ([#191](https://github.com/taiki-e/cargo-llvm-cov/pull/191))

## [0.4.8] - 2022-06-16

- Correctly escape regular expressions passed to `-ignore-filename-regex`. ([#188](https://github.com/taiki-e/cargo-llvm-cov/pull/188), thanks @rhysd)

## [0.4.7] - 2022-06-13

- Pin clap to 3.1. ([#185](https://github.com/taiki-e/cargo-llvm-cov/pull/185))

## [0.4.6] - 2022-06-13

- Improve `--show-missing-lines` for multiple functions in a single line. ([#183](https://github.com/taiki-e/cargo-llvm-cov/pull/183), thanks @vmiklos)

- Limit the number of test threads to work around [rust-lang/rust#91092](https://github.com/rust-lang/rust/issues/91092). ([#184](https://github.com/taiki-e/cargo-llvm-cov/pull/184))

## [0.4.5] - 2022-06-02

- Fix handling of `RUSTC_WRAPPER`, `RUSTC`, and similar environment variables and configs. ([#180](https://github.com/taiki-e/cargo-llvm-cov/pull/180))

- Distribute prebuilt binaries for AArch64 macOS. ([#179](https://github.com/taiki-e/cargo-llvm-cov/pull/179))

## [0.4.4] - 2022-05-30

- Add `--fail-uncovered-{lines,regions,functions}` options to set the exit code based on uncovered {lines,regions,functions}. ([#173](https://github.com/taiki-e/cargo-llvm-cov/pull/173))

- Add `--ignore-run-fail` option to generate coverage even if tests fail. ([#174](https://github.com/taiki-e/cargo-llvm-cov/pull/174))

## [0.4.3] - 2022-05-29

- Fix metadata for cargo binstall. ([#176](https://github.com/taiki-e/cargo-llvm-cov/pull/176))

## [0.4.2] - 2022-05-29

- Add metadata for cargo binstall. ([#175](https://github.com/taiki-e/cargo-llvm-cov/pull/175), thanks @vmiklos)

## [0.4.1] - 2022-05-24

- Add `--coverage-target-only` flag to use rustflags only for target. ([#167](https://github.com/taiki-e/cargo-llvm-cov/pull/167), thanks @haraldh)

## [0.4.0] - 2022-05-12

- cargo-llvm-cov no longer changes the current directory when running cargo. ([#161](https://github.com/taiki-e/cargo-llvm-cov/pull/161))

- Exclude build script from report by default. ([#163](https://github.com/taiki-e/cargo-llvm-cov/pull/163))
  You can use `--include-build-script` flag to include build script in report.

- Set `cfg(coverage_nightly)` when nightly compiler is used. ([#164](https://github.com/taiki-e/cargo-llvm-cov/pull/164))

- Support short flags of `--release` (`-r`) and `--features` (`-F`). ([#165](https://github.com/taiki-e/cargo-llvm-cov/pull/165))

- Support [custom profiles](https://doc.rust-lang.org/cargo/reference/profiles.html#custom-profiles). ([#166](https://github.com/taiki-e/cargo-llvm-cov/pull/166))

## [0.3.3] - 2022-05-06

- Fix an issue where codes in the target directory are not being properly excluded from reports when using `show-env` subcommand. ([#156](https://github.com/taiki-e/cargo-llvm-cov/pull/156))

## [0.3.2] - 2022-05-05

- Alleviate an issue where "File name or extension is too long" error occurs in Windows. ([#155](https://github.com/taiki-e/cargo-llvm-cov/pull/155))

## [0.3.1] - 2022-05-01

- Calculate `--show-missing-lines` based on function regions. ([#150](https://github.com/taiki-e/cargo-llvm-cov/pull/150), thanks @vmiklos)

## [0.3.0] - 2022-04-08

- cargo-llvm-cov now always select the current toolchain. ([#148](https://github.com/taiki-e/cargo-llvm-cov/pull/148))

  Previously, if `-C instrument-coverage` is not available in the current toolchain, the nightly toolchain was used. (See [release note of 0.2.0](https://github.com/taiki-e/cargo-llvm-cov/releases/tag/v0.2.0) for more information on the previous behavior.)

- Make `--remap-path-prefix` optional. ([#141](https://github.com/taiki-e/cargo-llvm-cov/pull/141))

  Previously this flag was always used, but due to some bugs discovered we decided to disable it by default. If you were dependent on the behavior provided by this flag, you can use the same behavior by passing the `--remap-path-prefix` flag to cargo-llvm-cov.

- Stabilize a few unstable options.

## [0.2.4] - 2022-03-18

- Add support for `nextest`. ([#144](https://github.com/taiki-e/cargo-llvm-cov/pull/144), thanks @skyzh)

## [0.2.3] - 2022-03-05

- Add `--show-missing-lines` option to show uncovered lines in the command-line output. ([#143](https://github.com/taiki-e/cargo-llvm-cov/pull/143), thanks @vmiklos)

## [0.2.2] - 2022-03-01

- Add `--fail-under-lines` option to set the exit code based on coverage percentage. ([#139](https://github.com/taiki-e/cargo-llvm-cov/pull/139), thanks @vmiklos)

## [0.2.1] - 2022-02-18

- Update clap to 3.1. ([#136](https://github.com/taiki-e/cargo-llvm-cov/pull/136))

## [0.2.0] - 2022-02-06

- Update to stabilized `-C instrument-coverage`. ([#130](https://github.com/taiki-e/cargo-llvm-cov/pull/130))

  Support for `-Z instrument-coverage` in the old nightly will also be kept for compatibility.

  **Compatibility Note:** In 0.2, if `-C instrument-coverage` or `-Z instrument-coverage` is not available in the default toolchain, running `cargo llvm-cov` will find and use nightly (this is almost the same behavior as 0.1). This behavior is necessary because only the recent nightly currently supports `-C instrument-coverage` (and also for compatibility with 0.1). This behavior will be changed in 0.3 to always select the default toolchain. If you are likely to be affected by the change in 0.3, cargo-llvm-cov will emit a warning. 0.3 is planned to be released after `-C instrument-coverage` is available in the stable toolchain.

- Remove support of multiple values in `--package` and `--exclude`. ([#133](https://github.com/taiki-e/cargo-llvm-cov/pull/133))

  [This behavior was unintentionally enabled in the older version of 0.1 and was deprecated in the recent version of 0.1.](https://github.com/taiki-e/cargo-llvm-cov/pull/127#issuecomment-1018204521)

- Add `--exclude-from-test` option to exclude specific packages from the test but not from the report. ([#131](https://github.com/taiki-e/cargo-llvm-cov/pull/131))

- Add `--exclude-from-report` option to exclude specific packages from the report but not from the test. ([#131](https://github.com/taiki-e/cargo-llvm-cov/pull/131))

- Workspace members are now always included in the report unless specified by `--exclude` or `--exclude-from-report`. ([#131](https://github.com/taiki-e/cargo-llvm-cov/pull/131))

## [0.1.16] - 2022-01-21

- Alleviate an issue where "File name or extension is too long" error occurs in Windows. ([#126](https://github.com/taiki-e/cargo-llvm-cov/pull/126), thanks @aganders3)

- Re-enable multiple values for `--package` and `--exclude`. ([#127](https://github.com/taiki-e/cargo-llvm-cov/pull/127), thanks @aganders3)

  This behavior was unintentionally enabled in older versions and disabled in recent versions.

  We will support this again in 0.1.x for compatibility, but will remove it in 0.2.x.

- Distribute prebuilt binaries for AArch64 Linux (gnu and musl).

## [0.1.15] - 2022-01-06

- Fix bug in `show-env` subcommand. ([#121](https://github.com/taiki-e/cargo-llvm-cov/pull/121))

## [0.1.14] - 2022-01-06

- Add `show-env` subcommand. ([#115](https://github.com/taiki-e/cargo-llvm-cov/pull/115), thanks @davidhewitt)

- cargo-llvm-cov no longer sets `CARGO_TARGET_DIR`. ([#112](https://github.com/taiki-e/cargo-llvm-cov/pull/112), thanks @smoelius)

- cargo-llvm-cov can now properly exclude arbitrary `CARGO_HOME` and `RUSTUP_HOME` from reports.

## [0.1.13] - 2021-12-14

- Support custom-built rust toolchain. ([#111](https://github.com/taiki-e/cargo-llvm-cov/pull/111), thanks @tofay)

## [0.1.12] - 2021-11-15

- Exclude `CARGO_HOME` and `RUSTUP_HOME` used in the official rust docker image from reports. ([#105](https://github.com/taiki-e/cargo-llvm-cov/pull/105))

## [0.1.11] - 2021-11-13

- Fix ["conflicting weak extern definition" error](https://github.com/rust-lang/rust/issues/85461) on windows. ([#101](https://github.com/taiki-e/cargo-llvm-cov/pull/101))

## [0.1.10] - 2021-10-24

- Fix a compatibility issue with `cc`. ([#98](https://github.com/taiki-e/cargo-llvm-cov/pull/98))

## [0.1.9] - 2021-10-13

- Distribute statically linked binary on Windows MSVC. ([#95](https://github.com/taiki-e/cargo-llvm-cov/pull/95))

## [0.1.8] - 2021-10-04

- Fix an issue where some files were incorrectly ignored in reports. ([#94](https://github.com/taiki-e/cargo-llvm-cov/pull/94), thanks @larsluthman)

## [0.1.7] - 2021-09-19

- Add `--failure-mode` option. ([#91](https://github.com/taiki-e/cargo-llvm-cov/pull/91), thanks @smoelius)

## [0.1.6] - 2021-09-03

- Add `cargo llvm-cov run` subcommand to get coverage of `cargo run`. ([#89](https://github.com/taiki-e/cargo-llvm-cov/pull/89))

## [0.1.5] - 2021-09-01

- Add `--workspace` flag to `cargo llvm-cov clean` subcommand. ([#85](https://github.com/taiki-e/cargo-llvm-cov/pull/85))

- Fix bug around artifact cleanup. ([#85](https://github.com/taiki-e/cargo-llvm-cov/pull/85))

## [0.1.4] - 2021-08-29

- Improve heuristics around artifact cleanup. ([#79](https://github.com/taiki-e/cargo-llvm-cov/pull/79))
  This removes the need to recompile dependencies in most cases.

- Fix an issue where `--package` option could not handle package specifications containing the version such as `futures:0.3.16`. ([#80](https://github.com/taiki-e/cargo-llvm-cov/pull/80))

## [0.1.3] - 2021-08-26

- Add `--verbose` option to `cargo llvm-cov clean` subcommand. ([#75](https://github.com/taiki-e/cargo-llvm-cov/pull/75))

- Fix regressions introduced in 0.1.2. ([#74](https://github.com/taiki-e/cargo-llvm-cov/pull/74), [#76](https://github.com/taiki-e/cargo-llvm-cov/pull/76))

## [0.1.2] - 2021-08-26

**Note:** This release has been yanked due to regressions fixed in 0.1.3.

- Set `cfg(coverage)` to easily use `#[no_coverage]`. ([#72](https://github.com/taiki-e/cargo-llvm-cov/pull/72))

- Add `--quiet`, `--doc`, and `--jobs` options. ([#70](https://github.com/taiki-e/cargo-llvm-cov/pull/70))

- Add `cargo llvm-cov clean` subcommand. ([#73](https://github.com/taiki-e/cargo-llvm-cov/pull/73))

## [0.1.1] - 2021-08-25

- Add `--lib`, `--bin`, `--bins`, `--example`, `--examples`, `--test`, `--tests`, `--bench`, `--benches`, `--all-targets`, `--profile`, and `--offline` options. ([#67](https://github.com/taiki-e/cargo-llvm-cov/pull/67))

- Respect `BROWSER` environment variable and `doc.browser` cargo config. ([#66](https://github.com/taiki-e/cargo-llvm-cov/pull/66))

## [0.1.0] - 2021-08-15

- Update clap to fix build error. ([#59](https://github.com/taiki-e/cargo-llvm-cov/pull/59))

- Support latest version of trybuild. ([#54](https://github.com/taiki-e/cargo-llvm-cov/pull/54))

- Change output directory of `--html` and `--open` options from `target/llvm-cov` to `target/llvm-cov/html`. ([#62](https://github.com/taiki-e/cargo-llvm-cov/pull/62))

- You can now merge the coverages generated under different test conditions by using `--no-report` and `--no-run`. ([#55](https://github.com/taiki-e/cargo-llvm-cov/pull/55))

  ```sh
  cargo clean
  cargo llvm-cov --no-report --features a
  cargo llvm-cov --no-report --features b
  cargo llvm-cov --no-run --lcov
  ```

- Add environment variables to pass additional flags to llvm-cov/llvm-profdata. ([#58](https://github.com/taiki-e/cargo-llvm-cov/pull/58))

  - `CARGO_LLVM_COV_FLAGS` to pass additional flags to llvm-cov. (value: space-separated list)
  - `CARGO_LLVM_PROFDATA_FLAGS` to pass additional flags to llvm-profdata. (value: space-separated list)

- Fix "Failed to load coverage" error when together used with trybuild. ([#49](https://github.com/taiki-e/cargo-llvm-cov/pull/49))

- Fix bug in `--exclude` and `--package` options. ([#56](https://github.com/taiki-e/cargo-llvm-cov/pull/56))

- Fix bug in color-detection when both `--text` and `--output-dir` used. ([#62](https://github.com/taiki-e/cargo-llvm-cov/pull/62))

- `--html` and `--open` options no longer outputs a summary at the same time. ([#61](https://github.com/taiki-e/cargo-llvm-cov/pull/61))

- Respect rustflags and rustdocflags set by cargo config file. ([#52](https://github.com/taiki-e/cargo-llvm-cov/pull/52))

- Diagnostic improvements.

## [0.1.0-alpha.5] - 2021-08-07

- Support Windows. ([#41](https://github.com/taiki-e/cargo-llvm-cov/pull/41))

- Support trybuild. ([#44](https://github.com/taiki-e/cargo-llvm-cov/pull/44))

- Fix mapping error in `--doctests` option. ([#40](https://github.com/taiki-e/cargo-llvm-cov/pull/40))

- Fix bug in `--target` option. ([#46](https://github.com/taiki-e/cargo-llvm-cov/pull/46))

- Add `--package` option. ([#42](https://github.com/taiki-e/cargo-llvm-cov/pull/42))

## [0.1.0-alpha.4] - 2021-06-13

- cargo-llvm-cov no longer requires rustfilt. ([#29](https://github.com/taiki-e/cargo-llvm-cov/pull/29))

- Acknowledge that procedural macros are supported. ([#27](https://github.com/taiki-e/cargo-llvm-cov/pull/27))

- Fix support of testing binary crate. ([#23](https://github.com/taiki-e/cargo-llvm-cov/pull/23))

- Fix an issue where git dependencies were displayed in the coverage report. ([#19](https://github.com/taiki-e/cargo-llvm-cov/pull/19))

- Fix an issue where path dependencies that not included in the workspace were displayed in coverage report. ([#25](https://github.com/taiki-e/cargo-llvm-cov/pull/25))

- Fix bug in `--exclude` option. ([#30](https://github.com/taiki-e/cargo-llvm-cov/pull/30))

- Fix several bugs.

- Add `--output-path` option to specify a file to write coverage data into. ([#18](https://github.com/taiki-e/cargo-llvm-cov/pull/18))

- Add `--ignore-filename-regex` option to skip specified source code files from coverage report. ([#19](https://github.com/taiki-e/cargo-llvm-cov/pull/19))

- Add `--color` option. ([#15](https://github.com/taiki-e/cargo-llvm-cov/pull/15))

- Add `--no-fail-fast`, `--frozen`, and `--locked` option. ([#16](https://github.com/taiki-e/cargo-llvm-cov/pull/16))

- Add `--verbose` flag. ([#19](https://github.com/taiki-e/cargo-llvm-cov/pull/19))

- Improve diagnostics when the required tools are not installed. ([#17](https://github.com/taiki-e/cargo-llvm-cov/pull/17))

## [0.1.0-alpha.3] - 2021-06-04

- cargo-llvm-cov no longer requires cargo-binutils. ([#11](https://github.com/taiki-e/cargo-llvm-cov/pull/11))

- `--json` flag now exports all coverage data by default. ([#9](https://github.com/taiki-e/cargo-llvm-cov/pull/9))
  If you want to get only summary information, use `--summary-only` flag together.

- Enable `--html` flag automatically when `--open` flag is passed. ([#5](https://github.com/taiki-e/cargo-llvm-cov/pull/5))

- Add `--lcov` flag for exporting coverage data in "lcov" format. ([#9](https://github.com/taiki-e/cargo-llvm-cov/pull/9))

- Add `--output-dir` flag for specifying a directory to write coverage reports generated by `--html` or `--text` flag. ([#9](https://github.com/taiki-e/cargo-llvm-cov/pull/9))

- Fix a bug in cargo version detection. ([#7](https://github.com/taiki-e/cargo-llvm-cov/pull/7))

- Fix an issue where llvm-cov's auto-detection of color output doesn't work. ([#11](https://github.com/taiki-e/cargo-llvm-cov/pull/11))

- Fix several bugs.

- Documentation improvements.

## [0.1.0-alpha.2] - 2021-02-12

- Add `--text` option to output full report in plain text. ([#3](https://github.com/taiki-e/cargo-llvm-cov/pull/3), thanks @romac)

## [0.1.0-alpha.1] - 2021-01-23

Initial release

[Unreleased]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.24...HEAD
[0.6.24]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.23...v0.6.24
[0.6.23]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.22...v0.6.23
[0.6.22]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.21...v0.6.22
[0.6.21]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.20...v0.6.21
[0.6.20]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.19...v0.6.20
[0.6.19]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.18...v0.6.19
[0.6.18]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.17...v0.6.18
[0.6.17]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.16...v0.6.17
[0.6.16]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.15...v0.6.16
[0.6.15]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.14...v0.6.15
[0.6.14]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.13...v0.6.14
[0.6.13]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.12...v0.6.13
[0.6.12]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.11...v0.6.12
[0.6.11]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.10...v0.6.11
[0.6.10]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.9...v0.6.10
[0.6.9]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.8...v0.6.9
[0.6.8]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.7...v0.6.8
[0.6.7]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.6...v0.6.7
[0.6.6]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.5...v0.6.6
[0.6.5]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.4...v0.6.5
[0.6.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.3...v0.6.4
[0.6.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.2...v0.6.3
[0.6.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.1...v0.6.2
[0.6.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.6.0...v0.6.1
[0.6.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.39...v0.6.0
[0.5.39]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.38...v0.5.39
[0.5.38]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.37...v0.5.38
[0.5.37]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.36...v0.5.37
[0.5.36]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.35...v0.5.36
[0.5.35]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.34...v0.5.35
[0.5.34]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.33...v0.5.34
[0.5.33]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.32...v0.5.33
[0.5.32]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.31...v0.5.32
[0.5.31]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.30...v0.5.31
[0.5.30]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.29...v0.5.30
[0.5.29]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.28...v0.5.29
[0.5.28]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.27...v0.5.28
[0.5.27]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.26...v0.5.27
[0.5.26]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.25...v0.5.26
[0.5.25]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.24...v0.5.25
[0.5.24]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.23...v0.5.24
[0.5.23]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.22...v0.5.23
[0.5.22]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.21...v0.5.22
[0.5.21]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.20...v0.5.21
[0.5.20]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.19...v0.5.20
[0.5.19]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.18...v0.5.19
[0.5.18]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.17...v0.5.18
[0.5.17]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.16...v0.5.17
[0.5.16]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.15...v0.5.16
[0.5.15]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.14...v0.5.15
[0.5.14]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.13...v0.5.14
[0.5.13]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.12...v0.5.13
[0.5.12]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.11...v0.5.12
[0.5.11]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.10...v0.5.11
[0.5.10]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.9...v0.5.10
[0.5.9]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.8...v0.5.9
[0.5.8]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.7...v0.5.8
[0.5.7]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.6...v0.5.7
[0.5.6]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.5...v0.5.6
[0.5.5]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.4...v0.5.5
[0.5.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.3...v0.5.4
[0.5.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.2...v0.5.3
[0.5.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.14...v0.5.0
[0.4.14]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.13...v0.4.14
[0.4.13]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.12...v0.4.13
[0.4.12]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.11...v0.4.12
[0.4.11]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.10...v0.4.11
[0.4.10]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.9...v0.4.10
[0.4.9]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.8...v0.4.9
[0.4.8]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.7...v0.4.8
[0.4.7]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.6...v0.4.7
[0.4.6]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.5...v0.4.6
[0.4.5]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.4...v0.4.5
[0.4.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.3...v0.4.4
[0.4.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.2...v0.4.3
[0.4.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.1...v0.4.2
[0.4.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.3.3...v0.4.0
[0.3.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.3.2...v0.3.3
[0.3.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.3.1...v0.3.2
[0.3.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.3.0...v0.3.1
[0.3.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.2.4...v0.3.0
[0.2.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.2.3...v0.2.4
[0.2.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.2.2...v0.2.3
[0.2.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.16...v0.2.0
[0.1.16]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.15...v0.1.16
[0.1.15]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.14...v0.1.15
[0.1.14]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.13...v0.1.14
[0.1.13]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.12...v0.1.13
[0.1.12]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.11...v0.1.12
[0.1.11]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.10...v0.1.11
[0.1.10]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.9...v0.1.10
[0.1.9]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.8...v0.1.9
[0.1.8]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.7...v0.1.8
[0.1.7]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.6...v0.1.7
[0.1.6]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.5...v0.1.6
[0.1.5]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.4...v0.1.5
[0.1.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.3...v0.1.4
[0.1.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.2...v0.1.3
[0.1.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0-alpha.5...v0.1.0
[0.1.0-alpha.5]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0-alpha.4...v0.1.0-alpha.5
[0.1.0-alpha.4]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0-alpha.3...v0.1.0-alpha.4
[0.1.0-alpha.3]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0-alpha.2...v0.1.0-alpha.3
[0.1.0-alpha.2]: https://github.com/taiki-e/cargo-llvm-cov/compare/v0.1.0-alpha.1...v0.1.0-alpha.2
[0.1.0-alpha.1]: https://github.com/taiki-e/cargo-llvm-cov/releases/tag/v0.1.0-alpha.1
