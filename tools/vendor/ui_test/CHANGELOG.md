# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Fixed

### Changed

### Removed

## [0.25.0] - 2024-07-24

### Added

### Fixed

* panics when ui_test tried to show diagnostics on multi-byte chars

### Changed

### Removed


## [0.24.0] - 2024-07-11

### Added

* `Text::diff()` creates a text status emitter that does not do full dumps of test stderr/stdout, but only emits the diff of the changes
* Support `-Zbuild-std` by add
    * use `DependencyBuilder::build_std` to enable it

### Fixed

* Missing result dump if printing thread is too slow and the entire test exits before it is done.

### Changed

* Split up `Revisioned::mode` into `Revisioned::exit_status` and `Revisioned::require_annotations`
* `Config::output_conflict_handling` is now `Error` instead of `Bless`
* Rustfix tests now create multiple `.fixed` files if diagnostics contain multiple suggestions
* updated `prettydiff` from 0.6.4 to 0.7.0, which drops `ansi_term` and `winapi*` deps.

### Removed


## [0.23.0] - 2024-05-02

### Added

* `Config::custom_comments`
* `Revisioned::custom`
* `Flag` trait for custom `//@` flags
* `Build` trait for custom aux/dep build
    * `BuildManager` for deduplicating these builds on a per-`Config` basis

### Fixed

* folders and libraries linked by build scripts were ignored, causing linker failures

### Changed

* removed `Revisioned::no_rustfix` in favor of turning that into a rustc-specific custom flag
    * use `config.comment_defaults.base().set_custom("rustfix", RustFixMode::Everything);` to overwrite the `MachineApplicable` default
* removed `Revisioned::edition` in favor of turning that into a rustc-specific custom flag
* removed `Revisioned::needs_asm_support` in favor of turning that into a rustc-specific custom flag
* replaced `Mode::Run` with a rustc-specific run flag
* replaced rustfix with a rustc-specific rustfix flag
* replaced `rustfix` fields of `Mode::Fail` and `Mode::Yolo` by instead overwriting the rustc-specific custom flag
* aux builds and dependencies are now built *per* `Config` instead of being built just for the first `Config` and the result shared by the others
    * the configs could be different enough that aux builds built with a different config are incompatible (e.g. different targets).
* replaced `Revisioned::aux_builds` with a rustc-specific custom flag
* replaced `dependency_builder` and `dependency_manifest_path` with `DependencyBuilder` `Flag` that you an add to the default comments.
    * use `config.comment_defaults.base().set_custom("dependencies", DependencyBuilder::default());` to get the same behaviour as setting `Config.toml` as the `dependency_manifest_path`.
* updated `rustfix` from 0.6.1 to 0.8.1. This may cause additional suggestions to be applied that previously weren't.

### Removed

## [0.22.3] - 2024-04-05

### Added

* Reexporting `eyre::Result` at the root level

### Fixed

* Passing `--target` to build command when cross-compiling.

### Changed

### Removed

## [0.22.2] - 2024-02-27

### Added

### Fixed

### Changed

* `spanned` dependency bump to lower `bstr` to `1.6.0` to resolve windows linker issues with `1.7`

### Removed

## [0.22.1] - 2024-02-16

### Added

* Add `//~v` comments to put an error matcher above the error site.

### Fixed

* Give aux builds the default comment config, too

### Changed

### Removed

## [0.22.0] - 2024-01-24

### Added

* Started maintaining a changelog
* `Config::comment_defaults` allows setting `//@` comments for all tests
* `//~` comments can now specify just an error code or lint name, without any message. ERROR level is implied
* `Revisioned::diagnostic_code_prefix` allows stripping a prefix of diagnostic codes to avoid having to repeat `clippy::` in all messages

### Fixed

* report an error instead of panicking when encountering a suggestion that does not belong to the main file.
* number of filtered tests is now > 0 when things actually got filtered.

### Changed

* crate-private span handling was passed off to the `spanned` crate, improving some diagnostics along the way.
* `Config::output_conflict_handling` does not contain the bless command message anymore, it is instead available separately as `Config::bless_command`
* Updating `cargo_metadata` to `0.18`
* Updated `spanned` to `0.1.5`, giving more precise spans for more iterator operations
* `Config::cfgs` is now `Config::program::cfg_flag`
* Bumped `annotate-snippets` to `0.10`

### Removed

* `$DIR` and `RUSTLIB` replacements
* `Config::edition` (replaced by `config.comment_defaults.base().edition`)
* `Config::filter_stdout` (replaced by `config.comment_defaults.base().normalize_stdout`)
* `Config::filter_stderr` (replaced by `config.comment_defaults.base().normalize_stderr`)
* `Config::mode` (replaced by `config.comment_defaults.base().mode`)

## [0.21.2] - 2023-09-27
