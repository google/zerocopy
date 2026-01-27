# Changelog

## [0.17.24] - 2025-12-26

### Added

 - `Workspace::build_directory()` returns the build directory for intermediate build artifacts (requires Cargo 1.91+).
 - `Workspace::default_members()` and `Workspace::default_member_ids()` iterate over workspace default members (requires Cargo 1.71+; returns empty iterator for older Cargo versions).
 - `PackageLink::registry()` returns the registry URL for a dependency, if it uses a non-default registry.
 - `PackageLink::path()` returns the file system path for path dependencies.
 
## [0.17.23] - 2025-10-12

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.23.0.

## [0.17.22] - 2025-09-29

### Fixed

Replaced obsolete `doc_auto_cfg` with `doc_cfg`, to fix Rust nightly builds with the `doc_cfg` flag enabled.

## [0.17.21] - 2025-09-14

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.22.0.

## [0.17.20] - 2025-07-11

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.21.0.
  - As part of this update, restored compatibility with the unstable [bindeps feature](https://github.com/rust-lang/cargo/issues/9096) -- see [this commit](https://github.com/oli-obk/cargo_metadata/commit/73aaebb0770e1919a218dff564659f17da90067c).
- MSRV updated to Rust 1.86, as required by dependencies.

## [0.17.19] - 2025-05-29

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.20.0.
- Some older versions of Cargo, when the unstable [bindeps feature](https://github.com/rust-lang/cargo/issues/9096) is enabled, generate JSON output that is no longer supported by `cargo_metadata`. If you run into an error, please update your nightly toolchain. Nightly versions from at least 2024-07 do not appear to produce invalid metadata.
- MSRV updated to Rust 1.82.

## [0.17.18] - 2025-04-29

### Added

- `CargoSet::with_package_resolver` supports passing in a `PackageResolver` for additional dynamic filtering of dependency edges.
- `CargoSet::target_links` and `host_links` return the set of `PackageLink` instances followed on the target and host platforms, respectively.

Thanks to [anforowicz](https://github.com/anforowicz) for these contributions!

## [0.17.17] - 2025-02-21

### Added

- Add `PlatformEval::target_specs` to obtain the list of `TargetSpec` instances backing a platform evaluator. Thanks to [anforowicz](https://github.com/anforowicz) for the contribution!

## [0.17.16] - 2025-02-15

### Added

- `BuildTarget::test_by_default` returns true if tests are run for a build target by default.
- `BuildTarget::doc_by_default` returns true if documentation is enabled for a build target, respectively.

### Changed

- `BuildTarget::doc_tests` is now `BuildTarget::doctest_by_default`. The old name has been deprecated, but is kept around for compatibility.

## [0.17.15] - 2025-02-15

(This version was yanked due to incorrect documentation.)

## [0.17.14] - 2025-02-11

### Added

- `MetadataCommand::env` adds environment variables to the `cargo metadata` command.

  Thanks to [anforowicz](https://github.com/anforowicz) for your first contribution!

## [0.17.13] - 2025-02-08

### Changed

- Renamed `PlatformSpec::current` to `PlatformSpec::build_target` to indicate that it is determined at build time, not at runtime. The old method is still available but has been marked deprecated.

## [0.17.12] - 2025-01-05

### Added

Added support for custom sparse registries (`sparse+https://...`). Thanks to [jonhoo](https://github.com/jonhoo) for your first contribution!

## [0.17.11] - 2024-12-22

### Added

Added support for the upcoming [Cargo resolver version
3](https://doc.rust-lang.org/beta/cargo/reference/resolver.html#resolver-versions):
within guppy, `CargoResolverVersion::V3`. Resolver version 3 enables MSRV-aware
version resolution in Cargo.

The portion of dependency resolution that guppy works with (package and feature
resolution) happens after dependency versions have been resolved and
`Cargo.lock` is refreshed. This means that from guppy's perspective, resolver
version 3 is the same as version 2, and `CargoResolverVersion::V3` acts as an
alias for `CargoResolverVersion::V2`.

## [0.17.10] - 2024-12-03

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.19.1.
- MSRV updated to Rust 1.82.

## [0.17.9] - 2024-12-02

### Fixed

- Graphs can now be generated even if the workspace `Cargo.toml` is within a subdirectory of one
  of its members. (This is an uncommon situation, but one that is supported by Cargo.)

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.19.0.

## [0.17.8] - 2024-10-02

### Fixed

- Fixed a case of dependency matching with renamed packages ([#317]).

### Changed

- Update `target-spec` to 3.2.2.

[#317]: https://github.com/guppy-rs/guppy/pull/317

## [0.17.7] - 2024-07-31

### Changed

- Update `target-spec` to 3.2.1.

## [0.17.6] - 2024-07-29

### Changed

- MSRV updated to Rust 1.75.

### Fixed

- Fixed feature graph construction accidentally inserting self-loops in some cases ([#292]). This
  was causing cargo-hakari to crash in some workspaces.
- Fixed a small bug in Cargo resolution where packages were incorrectly being marked as activated on
  the host platform ([`8666ebc`]).

[#292]: https://github.com/guppy-rs/guppy/pull/292
[`8666ebc`]: https://github.com/guppy-rs/guppy/commit/8666ebce44e27dae3a59f22a5ce70b7bdb252183

## [0.17.5] - 2024-02-03

### Changed

- The `Debug` impl for `FeatureSet` is now more useful. (PRs welcome to make the `Debug` impls for
  types like `PackageSet` more useful as well.)
- MSRV updated to Rust 1.73.

### Fixed

- Cargo build simulations now consider dev-dependencies of proc-macro crates. Previously, we weren't
  doing so.

## [0.17.4] - 2023-11-29

### Fixed

- Attempted to address `PackageGraph` creation with artifact dependencies as supported by nightly Rust ([#174]). Note that this is not a complete fix, as documented at [#174].

[#174]: https://github.com/guppy-rs/guppy/issues/174

## [0.17.3] - 2023-11-16

### Fixed

- Fixed a `PackageGraph` creation edge case ([#158]).

[#158]: https://github.com/guppy-rs/guppy/issues/158

## [0.17.2] - 2023-11-14

### Fixed

- Improve `PackageGraph` creation algorithm to address issues like [nextest-rs/nextest#1090](https://github.com/nextest-rs/nextest/issues/1090).

### Changed

- MSRV updated to Rust 1.70.

## [0.17.1] - 2023-07-29

### Added

- `PackageMetadata::minimum_rust_version` provides the `rust-version` field of a package as a `Version`.
- `PackageMetadata::rust_version` has been deprecated because it returns a `VersionReq` even though
  it actually should be a `Version`. In the next major release of guppy, the current definition of
  `rust_version` will go away and be replaced with `minimum_rust_version`.

## [0.17.0] - 2023-06-25

### Changed

- `target-spec` updated to version 3.

### Fixed

- Proptest strategy creator names updated from `prop010_` to `proptest1_`.

## [0.16.0] - 2023-06-19

### Changed

- `target-spec` updated to version 2.
- MSRV updated to Rust 1.66.

## [0.15.2] - 2023-01-08

### Added

- `PackageMetadata::to_feature_set` converts a single package to a `FeatureSet`.

### Changed

- MSRV updated to Rust 1.62.

## [0.15.1] - 2022-12-04

### Added

- Detailed documentation about dependency cycles in Cargo, as part of the [`Cycles`](https://docs.rs/guppy/latest/guppy/graph/struct.Cycles.html) struct. Thanks [Aria](https://github.com/Gankra) for writing it!

## [0.15.0] - 2022-11-07

### Changed

- `guppy::Error::UnknownRegistryName` now boxes the internal `summary` and is smaller as a result.

## [0.14.4] - 2022-10-05

### Changed

- Internal dependency update: `cargo_metadata` updated to 0.15.1.

## [0.14.3] - 2022-09-30

### Changed

- Repository location update.
- MSRV updated to Rust 1.58.

Thanks to [Carol Nichols](https://github.com/carols10cents) for her contributions to this release!

## [0.14.2] - 2022-05-29

### Fixed

- On Windows, guppy now behaves correctly when a path dependency is on a different drive from the workspace ([#642]).

[#642]: https://github.com/facebookincubator/cargo-guppy/issues/642

### Changed

- Internal dependency updates.

## [0.14.1] - 2022-03-18

### Added

- `Workspace::target_directory` returns the target directory provided in the Cargo metadata.
- `Workspace::metadata_table` returns the freeform `workspace.metadata` table.

## [0.14.0] - 2022-03-14

### Added

Support for [weak dependencies and namespaced features]:

- Cargo build simulations now take into account weak dependencies and namespaced features.
- Optional dependencies (`"dep:foo"`) and namespaced features (`"foo"`) are now represented as separate nodes in a `FeatureGraph`, even with Rust versions prior to 1.60.
- Feature names are now represented as a new `FeatureLabel` enum.

[weak dependencies and namespaced features]: https://rust-lang.github.io/rfcs/3143-cargo-weak-namespaced-features.html

### Changed

- MSRV updated to Rust 1.56.

## [0.13.0] - 2022-02-13

### Added

- `doc_cfg`-based feature labels to rustdoc.
- `MetadataCommand::cargo_command` returns the underlying `std::process::Command` instance.

### Changed

- `guppy::graph::feature::CrossLink` renamed to `ConditionalLink`, and now covers some same-package
  features. For more, see the documentation for [`ConditionalLink`].
- Public dependency bump: `target-spec` updated to version 1.

### Fixed

- A small fix to Cargo build simulations ([#596](https://github.com/facebookincubator/cargo-guppy/issues/596)).

[`ConditionalLink`]: https://docs.rs/guppy/0.13/guppy/graph/feature/struct.ConditionalLink.html

## [0.12.6] - 2021-12-19

### Added

- `PackageMetadata::homepage`, `documentation` and `default_run`, exposed by newer versions of Cargo.

## [0.12.5] - 2021-12-17

### Added

- `guppy` now supports a "light" mode if `--no-deps` is passed in. This mode doesn't provide any information
  about third-party packages or dependency edges, but is much faster if the only information needed
  is workspace lookups.

## [0.12.4] - 2021-12-08

- Reverted change in 0.12.3 because of [#524](https://github.com/facebookincubator/cargo-guppy/issues/524).

## [0.12.3] - 2021-11-28

- Internal dependency `guppy-workspace-hack` updated to [`workspace-hack`](https://crates.io/crates/workspace-hack).

## [0.12.2] - 2021-11-25

### Added

- `PackageMetadata::link_between`, `link_from` and `link_to` look up a direct link from one package to another.

## [0.12.1] - 2021-11-23

### Changed

- The `toml` crate is now built with the `preserve_order` feature.
  - This feature ensures that the key ordering in metadata is preserved.

## [0.12.0] - 2021-11-23

This is a minor breaking change that should not affect most consumers.

### Fixed

- Summaries generated by old versions of `guppy` can now be parsed by this version, even if the metadata
  is in a different format.

### Changed

- Relative paths are now stored and presented with forward slashes on all platforms, including Windows.
- `guppy-summaries` updated to 0.6.0.

## [0.11.3] - 2021-11-20

### Added

- `PackageMetadata::rust_version` returns the `package.rust-version` field, if specified. Thanks [@foresterre](https://github.com/foresterre)!

## [0.11.2] - 2021-10-06

### Added

- Rudimentary support for alternate registries. This is a temporary workaround until [Cargo issue #9052](https://github.com/rust-lang/cargo/issues/9052)
  is resolved.
  - This is currently only hooked up to `hakari`.

## [0.11.1] - 2021-10-01

### Added

- A new abstraction `PlatformSpec` can represent the union of all platforms, the intersection
  of all platforms, or a single platform.
  - Methods like `EnabledStatus::required_on` and `EnabledStatus::enabled_on` have been switched
    to accepting a `&PlatformSpec` rather than a `&Platform`.
  - `CargoOptions::set_platform` and related methods now accept either a `Platform` or a `PlatformSpec`.
  - `EnabledStatus::enabled_on_any` is now `EnabledStatus::enabled_on(&PlatformSpec::Any)`.
- Omitted packages are now easier to describe while deserializing: they now take a `workspace-members`
  list of names, and a `third-party` list of specifiers such as `{ name = "serde", version = "1" }`.
  - The resolver will now also fail if any specifiers are unmatched.

### Changed

- Platform-related types have been moved into the new `platform` module at the top level.
- In Cargo options summaries, `version = "v1"` and `version = "v2"` have been renamed to `resolver = "1"` and
  `resolver = "2"` respectively, to align with Cargo.
  - The old specifiers will continue to work.
- Because of the changes to how omitted packages are represented, old-style `CargoOptionsSummary` instances
  may no longer parse correctly.
- MSRV updated to Rust 1.53.

## 0.11.0 - 2021-10-01

(This release was incorrectly made and was yanked.)

## [0.10.1] - 2021-09-13

### Changed

- Public dependency version bumps:
  - `target-spec` updated to 0.8.0.
    - As a result, `Platform` no longer has a lifetime parameter.
  - `guppy-summaries` updated to 0.5.0.
  - `semver` updated to 1.0.
- MSRV updated to Rust 1.51.

## [0.10.0] - 2021-09-13

(This release was yanked because `guppy-summaries` needed to be upgraded as well.)

## [0.9.0] - 2021-03-11

### Added

- `DependencyKind::VALUES` lists out all the values of `DependencyKind`.
- `DependencyReq::no_default_features()` returns the enabled status for a dependency when `default-features = false`.

### Changed

- `PackageMetadata::publish` now returns a new, more descriptive `PackagePublish` enum ([#320]).
- `PackageMetadata::readme` now returns `&Utf8Path` rather than `&Path`.
- `BuildTarget::path` now returns `&Utf8Path` rather than `&Path`.

[#320]: https://github.com/facebookincubator/cargo-guppy/issues/320

## [0.8.0] - 2021-02-23

### Changed

- `guppy` now uses [`camino`](https://crates.io/crates/camino) `Utf8Path` and `Utf8PathBuf` wrappers. These wrappers
  provide type-level assertions that returned paths are valid UTF-8.
- Public dependency version bumps:
  - `proptest` updated to version 1 and the corresponding feature renamed to `proptest1`.

## [0.7.2] - 2021-02-15

### Fixed

- Restored compatibility with Rust 1.48. (1.48 is the MSRV, and is now tested in CI.)

## [0.7.1] - 2021-02-14

### Changed

- Packages within a cycle are now returned in non-dev order. When the direction is forward,
  if package Foo has a dependency on Bar, and Bar has a cyclic dev-dependency on
  Foo, then Foo is returned before Bar. (This is not a breaking change because it is an additional
  constraint on guppy itself, not on its consumers.)

## [0.7.0] - 2021-02-03

### Added

- `PackageSource` now has support for parsing external sources through a new `parse_external` method.
- Cargo simulations have some new features:
  - New `CargoOptions::set_initials_platform` method can be used to simulate builds on exclusively the host
    platform.
  - `CargoSet::new` accepts an additional argument, `features_only`, which represents additional inputs that are only
    used for feature unification. This may be used to simulate, e.g. `cargo build --package foo --package bar`, when
    you only care about the results of `foo` but specifying `bar` influences the build.
  - New enum `graph::cargo::BuildPlatform` represents either the target platform or the host. New methods
    `CargoSet::platform_features` and `CargoSet::platform_direct_deps` accept the `BuildPlatform` enum.
- `FeatureSet::contains_package` returns true if a feature set has at least one feature in the given package.
- `semver::VersionReq` is now exposed in `guppy`.
- `FeatureGraph::resolve_ids` resolves feature IDs into a `FeatureSet`.

### Changed

- Feature filters `all_filter`, `default_filter` and `none_filter` have been combined into a single enum
  `StandardFeatures`.
- Cargo builds are now done through `FeatureSet` instances, not `FeatureQuery`. This is because Cargo builds always
  happen in the forward direction.
  - `FeatureQuery::resolve_cargo` has been renamed to `FeatureSet::into_cargo_set`.
- `CargoOptions::with_` methods have been renamed to begin with either `set_` or `add_`.
- `Obs` is now a type rather than a trait.
- `CargoOptions::set_proc_macros_on_target` was replaced with `InitialsPlatform::ProcMacrosOnTarget`.
- Public dependency version bumps:
  - `semver` updated to 0.11.
  - `target-spec` updated to 0.6.

## [0.6.3] - 2021-01-11

### Fixed

- Fix an unintentional use of `serde`'s private exports.

## [0.6.2] - 2020-12-09

### Fixed

- `FeatureGraph::is_default_feature` no longer follows cross-package links.

  Cyclic dev-dependencies can enable non-default features (such as testing-only features), and previously
  `is_default_feature` would have returned true for such features. With this change, `is_default_feature`
  returns false for such features.

  The `default_filter` feature filter, which uses `is_default_feature`, has been fixed as well.

## [0.6.1] - 2020-12-02

This includes all the changes from version 0.6.0, plus a minor fix:

### Fixed

- Removed "Usage" section from the README, the version number there keeps falling out of sync.

## [0.6.0] - 2020-12-02

(Version 0.6.0 wasn't released to crates.io.)

### Added

- New feature `rayon1`, which introduces support for parallel iterators with [Rayon](https://github.com/rayon-rs/rayon).
  Currently, only a few workspace iterators are supported. More methods will be added as required (if you need
  something, please file an issue or open a PR!)
- `PackageSet` and `FeatureSet` now have `PartialEq` and `Eq` implementations.
  - These implementations check for the graph being same through pointer equality. This means that sets that originate
    from different `PackageGraph` instances will always be unequal, even if they refer to the same packages.
- Added `PackageSet::to_package_query` to convert a `PackageSet` to a `PackageQuery` starting from the same
  elements.

### Changed

- Some methods have been renamed for greater fluency:
  - `FeatureGraph::query_packages` is now `PackageQuery::to_feature_query`.
  - `FeatureGraph::resolve_packages` is now `PackageSet::to_feature_set`.
- The `semver` dependency has been updated to 0.11.

## [0.5.0] - 2020-06-20

This includes the changes in version 0.5.0-rc.1, plus:

### Added

- Support for writing out _build summaries_ for `CargoSet` instances through the optional `summaries` feature.

### Changed

- `target-spec` has been upgraded to 0.4.

### Fixed

- `MetadataCommand::exec` and `build_graph` are now `&self`, not `&mut self`.

## [0.5.0-rc.1] - 2020-06-12

### Added

- `PackageGraph::query_workspace_paths` and `resolve_workspace_paths` provide convenient ways
  to create queries and package sets given a list of workspace paths.
- `PackageMetadata::source` provides the source of a package (a local path, `crates.io`, a `git` repository or a custom
  registry).
- `PackageQuery::initials` returns the initial set of packages specified in a package query.
- `FeatureQuery::initials` returns the initial set of features specified in a feature query.
- `FeatureQuery::initial_packages` returns the initial set of _packages_ specified in a feature query.
- Improvements to Cargo resolution:
  - `CargoSet` now carries with it the original query and information about
    direct third-party dependencies.
  - A number of bug fixes around edge cases.
- `Workspace::members_by_paths` and `Workspace::members_by_names` look up a list of workspace members
  by path or name, respectively.
- `FeatureGraph::all_features_for` returns a list of all known features for a specified package.

### Changed

- Lookup methods like `PackageGraph::metadata` now return `Result`s with errors instead of `Option`s.
- `target-spec` has been upgraded to 0.3.
- `proptest` has been upgraded to 0.10. The feature has accordingly been renamed to
  `proptest010`.
- `Workspace::members` is now `Workspace::iter_by_path`, and `Workspace::members_by_name` is now `Workspace::iter_by_name`.

### Fixed

- In `FeatureQuery<'g>` and `FeatureSet<'g>`, the lifetime parameter `'g` is now [covariant].
  Compile-time assertions ensure that all lifetime parameters in `guppy` are covariant.

[covariant]: https://github.com/sunshowers/lifetime-variance-example/blob/main/src/lib.rs

### Upcoming

- Support for _build summaries_ is currently in an experimental state.

## [0.4.1] - 2020-05-07

This is a small followup release with some APIs that were meant to be added to 0.4.0.

### Added

- `PackageGraph` now has some new `resolve_` methods:
  - `resolve_ids`: creates a `PackageSet` with the specified package IDs.
  - `resolve_workspace`: creates a `PackageSet` with all workspace packages (but no transitive dependencies).
  - `resolve_workspace_names`: creates a `PackageSet` with the specified workspace packages by name (but no transitive
    dependencies).

## [0.4.0] - 2020-05-06

This is a major overhaul of `guppy`, with many new features and several changed APIs.

### Added

- Support for graph analysis on a per-feature basis.
  - The APIs are contained in `guppy::graph::feature`, and are accessible through `PackageGraph::feature_graph`.
  - An almost complete set of queries and operations is available through `FeatureQuery` and `FeatureSet`.
- Support for simulating what packages and features would be built by Cargo.
  - The APIs are contained in `guppy::graph::cargo`, and are accessible by constructing a `FeatureQuery` and using its
    `resolve_cargo` method.
  - Both the current resolver and the upcoming [V2 resolver](https://github.com/rust-lang/cargo/pull/7820) are
    supported, and there are extensive property-based tests to ensure that `guppy` faithfully emulates `cargo`.
- `PackageQuery` (and `FeatureQuery`) can now be introspected with new methods `direction` and `starts_from`.
- `PackageMetadata` instances now have `has_build_script` and `is_proc_macro` methods.
- Add `PackageGraph::query_workspace_names` to make a `PackageQuery` by workspace name.

### Changed

- `PackageSet`'s consuming `into_` iterators have been turned into borrowing iterators.
  - `into_ids` is now `ids`, and `into_links` is now `links`.
- Direct dependency and reverse dependency queries now live on `PackageMetadata` instances.
- `PackageLink`, instead of having public `from`, `to` and `edge` fields, now has methods which return that data.
  - The functionality of `PackageEdge` has been subsumed into `PackageLink`.
- The data model for platform-specific statuses has been overhauled. See `EnabledStatus`, `PlatformStatus` and
  `PlatformEval`.
- `PackageResolver` (and `FeatureResolver`) improvements.
  - Resolver instances now have the query passed in, to make it easier to write stateless resolvers.
  - Resolver instances now take in `&mut self` instead of a plain `&self` (or `FnMut` instead of `Fn`).
- `MetadataCommand` has been reimplemented in `guppy`, and now has a `build_graph` method.
  - `Metadata` has been reworked as well, and renamed to `CargoMetadata`.

### Removed

- `PackageGraph::retain_edges` no longer exists: its functionality can be replicated through `PackageResolver`.

## [0.3.1] - 2020-04-15

### Added

- Support for listing and querying build targets (library, binaries, tests, etc) within a package.
  - `PackageMetadata::build_targets`: iterates over all build targets within a package.
  - `PackageMetadata::build_target`: retrieves a build target by identifier.

## [0.3.0] - 2020-04-14

This is a breaking release with some minor API changes.

### Added

- `PackageGraph::directly_depends_on`: returns true if a package directly depends on another.
- `Workspace` has new `member_by_name` and `members_by_name` methods for workspace lookups by name.

### Fixed

- `guppy` now checks for duplicate names in workspaces and errors out if it finds any.

### Changed

- `Workspace::members` and `Workspace::member_by_path` now return `PackageMetadata` instances, not `PackageId`.

## [0.2.1] - 2020-04-13

### Fixed

- Fixed a build issue on nightly Rust.

## [0.2.0] - 2020-04-13

This is a breaking release. There are no new or removed features, but many existing APIs have been cleaned up.

### Changed

- The `select_` methods have been renamed to `query_`.
  - `PackageSelect` is now `PackageQuery`.
- `select_all` is now `resolve_all` and directly produces a `PackageSet`.
- `DependencyLink` is now `PackageLink`, and `DependencyEdge` is now `PackageEdge`.
- `into_iter_links` is now `PackageSet::into_links`.
- `PackageId` is now custom to `guppy` instead of reusing `cargo_metadata::PackageId`.
- `PackageDotVisitor` now takes a `&mut DotWrite`.

### Removed

- All previously deprecated methods have been cleaned up.

## [0.1.8] - 2020-04-08

### Added

- Implemented package resolution using custom resolvers, represented by the `PackageResolver` trait.
  - Added new APIs `PackageSelect::resolve_with` and `PackageSelect::resolve_with_fn`.
  - A `PackageResolver` provides fine-grained control over which links are followed.
  - It is equivalent to `PackageGraph::retain_edges`, but doesn't borrow mutably and is scoped to a single selector.
- Added `PackageSet` to represent a set of known, resolved packages.
  - `PackageSet` comes with the standard set operations: `len`, `contains`, `union`, `intersection`, `difference` and
    `symmetric_difference`.
  - A `PackageSet` can also be iterated on in various ways, listed in the "Deprecated" section.

### Changed

- Updated repository links.

### Deprecated

- The following `into_` methods on `PackageSelect` have been deprecated and moved to `PackageSet`.
  - `select.into_iter_ids()` -> `select.resolve().into_ids()`
  - `select.into_iter_metadatas()` -> `select.resolve().into_metadatas()`
  - `select.into_root_ids()` -> `select.resolve().into_root_ids()`
  - `select.into_root_metadatas()` -> `select.resolve().into_root_metadatas()`

## [0.1.7] - 2020-04-05

### Added

- Support for [platform-specific dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies), including:
  - Querying whether a dependency is required or optional on the current platform, or on any other platform.
  - Evaluating which features are enabled on a platform.
  - Handling situations where the set of [target features](https://github.com/rust-lang/rfcs/blob/master/text/2045-target-feature.md) isn't known.

### Changed

- Internal improvements -- `into_iter_ids` is a further 10-15% faster for large graphs.
- Made several internal changes to prepare for feature graph support, coming soon.
- Sped up build times by removing some dependencies.

### Deprecated

- As part of support for platform-specific dependencies, `DependencyMetadata::target` has been replaced with the `_on` methods.
  - For example, to figure out if a dependency is enabled on a platform, use the `enabled_on` method.

## [0.1.6] - 2020-03-11

### Fixed

- Handle cyclic dev-dependencies properly. Previously, `guppy` could produce incomplete results if it encountered cycles.

### Changed

- As a result of algorithmic improvements to handle cycles, `into_iter_ids` is now around 60% faster for large graphs.

## [0.1.5] - 2020-03-06

### Fixed

- Fix a bug involving situations where different dependency sections depend on the same package with different versions:

```toml
[dependencies]
lazy_static = "1"

[dev-dependencies]
lazy_static = "0.2"
```

## [0.1.4] - 2020-01-26

### Added

- New selector `select_workspace` to select packages that are part of the workspace and all their transitive
  dependencies. In general, `select_workspace` is preferable over `select_all`.

### Fixed

- Fixed a bug in `into_root_ids` and `into_root_metadatas` that would cause it to return packages that aren't roots of
  another package.

### Changed

- Internal upgrades to prepare for upcoming feature graph analysis.

## [0.1.3] - 2019-12-29

### Added

- `PackageSelect::into_root_metadatas` returns package metadatas for all roots within a selection.
- New optional feature `proptest010` to help with property testing.

### Changed

- Upgrade to `petgraph` 0.5 -- this allows for some internal code to be simplified.

### Deprecated

- Package selectors have been renamed. The old names will continue to work for the 0.1 series, but will be removed in the 0.2 series.
  - `select_transitive_deps` → `select_forward`
  - `select_reverse_transitive_deps` → `select_reverse`
  - `select_transitive_deps_directed` → `select_directed`

## [0.1.2] - 2019-11-26

### Fixed

- Fixed the return type of `into_root_ids` to be `impl Iterator` instead of `impl IntoIterator`.

## [0.1.1] - 2019-11-22

### Fixed

- Fixed a publishing issue with version 0.1.0.

## [0.1.0] - 2019-11-22

### Added

- Initial release.

[0.17.24]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.24
[0.17.23]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.23
[0.17.22]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.22
[0.17.21]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.21
[0.17.20]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.20
[0.17.19]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.19
[0.17.18]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.18
[0.17.17]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.17
[0.17.16]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.16
[0.17.15]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.15
[0.17.14]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.14
[0.17.13]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.13
[0.17.12]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.12
[0.17.11]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.11
[0.17.10]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.10
[0.17.9]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.9
[0.17.8]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.8
[0.17.7]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.7
[0.17.6]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.6
[0.17.5]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.5
[0.17.4]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.4
[0.17.3]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.3
[0.17.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.2
[0.17.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.1
[0.17.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.17.0
[0.16.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.16.0
[0.15.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.15.2
[0.15.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.15.1
[0.15.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.15.0
[0.14.4]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.14.4
[0.14.3]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.14.3
[0.14.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.14.2
[0.14.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.14.1
[0.14.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.14.0
[0.13.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.13.0
[0.12.6]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.6
[0.12.5]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.5
[0.12.4]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.4
[0.12.3]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.3
[0.12.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.2
[0.12.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.1
[0.12.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.12.0
[0.11.3]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.11.3
[0.11.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.11.2
[0.11.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.11.1
[0.10.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.10.1
[0.10.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.10.0
[0.9.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.9.0
[0.8.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.8.0
[0.7.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.7.2
[0.7.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.7.1
[0.7.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.7.0
[0.6.3]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.6.3
[0.6.2]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.6.2
[0.6.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.6.1
[0.6.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.6.0
[0.5.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.5.0
[0.5.0-rc.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.5.0-rc.1
[0.4.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.4.1
[0.4.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.4.0
[0.3.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.3.1
[0.3.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.3.0
[0.2.1]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.2.1
[0.2.0]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.2.0
[0.1.8]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.1.8
[0.1.7]: https://github.com/guppy-rs/guppy/releases/tag/guppy-0.1.7

<!-- Previous releases were simply tagged "$VERSION", not "guppy-$VERSION". -->

[0.1.6]: https://github.com/guppy-rs/guppy/releases/tag/0.1.6
[0.1.5]: https://github.com/guppy-rs/guppy/releases/tag/0.1.5
[0.1.4]: https://github.com/guppy-rs/guppy/releases/tag/0.1.4
[0.1.3]: https://github.com/guppy-rs/guppy/releases/tag/0.1.3
[0.1.2]: https://github.com/guppy-rs/guppy/releases/tag/0.1.2
[0.1.1]: https://github.com/guppy-rs/guppy/releases/tag/0.1.1
[0.1.0]: https://github.com/guppy-rs/guppy/releases/tag/0.1.0
