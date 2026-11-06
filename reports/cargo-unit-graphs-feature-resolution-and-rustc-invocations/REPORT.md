# Cargo Unit Graphs, Contextual Feature Resolution, and `rustc` Invocation Assembly Across Rust 1.98–1.101

## Summary

Cargo does not identify a compilation subject by package name, manifest target, source path, feature list, target triple, or profile name alone. Internally, Cargo represents each planned compilation or custom-build execution as a deduplicated `Unit` (`UnitInner` in `src/cargo/core/compiler/unit.rs`), whose equivalence class incorporates the concrete package ID, Cargo target descriptor, effective `Profile`, host-versus-target `CompileKind`, `CompileMode`, contextual `features` vector, per-unit `rustflags` and `rustdocflags`, native `links_overrides`, standard-library status (`is_std`), artifact-dependency target state, and a post-construction dependency discriminator hash (`dep_hash`).

Because Resolver versions 2 and 3 key feature activation by both package ID and dependency context (`FeaturesFor::NormalOrDev`, `FeaturesFor::HostDep`, and `FeaturesFor::ArtifactDep`), the same dependency crate can be compiled multiple times in one command with distinct feature vectors (for example, once as a host build-dependency or procedural-macro dependency and once as a target library dependency). Stable `cargo metadata --format-version 1` serializes only a single package-wide `resolve.nodes[].features` union from the package-level resolve graph and omits `FeaturesFor`, making `cargo metadata` structurally insufficient to reconstruct active compilation units. Cargo's unstable `--unit-graph -Z unstable-options` JSON (`SerializedUnit`) exposes per-unit `features`, `platform`, `mode`, effective `profile`, `dependencies`, and `roots`, making it the closest machine-readable projection of planned compilation units, though it remains an unstable planning view that omits `rustflags`, `dep_hash`, and late build-script outputs.

Furthermore, a planned unit in `--unit-graph` is neither a complete `rustc` command line nor proof that `rustc` executed. Cargo constructs `rustc` invocations in two stages: static unit preparation (`prepare_rustc` and `build_deps_args`) followed by dynamic post-build-script augmentation (`BuildScriptOutputs` supplying `-L`, `-l`, `--cfg`, `--check-cfg`, custom flags, and `rustc-env` variables after `run-custom-build` units finish). When `BuildRunner` determines via unit fingerprints that an existing artifact is fresh, Cargo skips the `rustc` (and any `RUSTC_WRAPPER` / `RUSTC_WORKSPACE_WRAPPER`) invocation entirely.

Across four examined Cargo revisions—`1.98.0-nightly` (`fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, `nightly`), stable `1.98.1` (`797e8a9bca276c1c9f9f738d2a20f484fa4eea9d`), stable `1.99.0` (`5f94df4789f005f9a352888e8355ffc645b7ed0e`), and `1.101.0-nightly` (`3d7cf6e937d6127d0f49881bf689c560b36d35c4`, `nightly`)—the core `UnitInner` identity model, contextual `FeatureResolver` architecture, recursive unit-dependency expansion, and `cargo metadata` representation limits remain invariant, while specific manifest-inheritance rules, CI incremental defaults, `--unit-graph` serialized profile fields, and `rustc` command-line flags evolve across releases.

## Applicability

This report synthesizes source-level and execution-level evidence across four Cargo and Rust toolchain revisions, together with the downstream Anneal and Charon configurations that consume them:

1. **Anneal-Era Pinned Nightly (`nightly`)**:
   - `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` (`cargo 1.98.0-nightly`), integrated as the `src/tools/cargo` submodule of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`.
   - Selected by `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, `rustDate = "2026-05-31"`) and `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`rust-toolchain` channel `nightly`).
2. **Official Stable Rust `1.98.1`**:
   - `rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985` (peeled from annotated tag `1.98.1`), whose `src/tools/cargo` gitlink resolves to `rust-lang/cargo@797e8a9bca276c1c9f9f738d2a20f484fa4eea9d` (219 commits ahead of `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, 0 behind).
3. **Official Stable Rust `1.99.0`**:
   - `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` (peeled from annotated tag `1.99.0`, object `daa8d75bc715f77869fa06d80b6ea1a3fe52d38e`, released 2026-10-01), whose `src/tools/cargo` gitlink resolves to `rust-lang/cargo@5f94df4789f005f9a352888e8355ffc645b7ed0e`.
4. **Newer Nightly Comparison (`nightly`)**:
   - `rust-lang/cargo@3d7cf6e937d6127d0f49881bf689c560b36d35c4` (`cargo 1.101.0-nightly`), executed alongside `1.98.0-nightly` and stable `1.98.1` on macOS (`aarch64-apple-darwin`).

### Cross-Version Invariance vs. Version-Specific Behavior

| Dimension | Invariant Across Examined Versions | Version-Specific Differences |
| :--- | :--- | :--- |
| **`UnitInner` & `UnitGraph` Core Model** | `src/cargo/core/compiler/unit.rs`, `unit_graph.rs`, `unit_generator.rs`, and `unit_dependencies.rs` are byte-identical between `fbb61be30` (`1.98.0-nightly`) and `797e8a9bc` (`1.98.1`). | `1.101.0-nightly` (`3d7cf6e93`) adds `"trim_paths": "none"` to serialized `profile` objects in `--unit-graph` JSON. Stable `1.98.1` rejects `-Z unstable-options --unit-graph` with exit code `101`. |
| **Contextual Feature Resolution & `cargo metadata`** | `src/cargo/core/resolver/features.rs` and `src/cargo/ops/cargo_output_metadata.rs` are byte-identical between `1.98.0-nightly` and `1.98.1`. Across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`, `cargo metadata --format-version 1` emits identical package-level feature unions and omits per-unit `FeaturesFor` contexts. | In Cargo `1.99.0` (`5f94df478`, PR #17126), `src/workspace/parser/mod.rs` honors a member dependency's `default-features = false` in Edition 2024 when inheriting from a workspace dependency that enables or omits `default-features` (whereas `1.98.1` ignored it and errored in Edition 2024). |
| **`rustc` Process & Search-Path Assembly** | Two-stage command construction (static unit args + late `BuildScriptOutputs`) and wrapper nesting (`$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC`) hold across all examined versions. | Between `1.98.0-nightly` and `1.98.1`, `add_dep_arg` (`src/cargo/core/compiler/mod.rs`) stops adding build-script output directories to dependency `-L` paths, `deps_output` (`compilation.rs`) changes to `BTreeSet<PathBuf>`, and `trim-paths` build-script env vars (`custom_build.rs`) switch to `CARGO_TRIM_PATHS_SCOPE` / `CARGO_TRIM_PATHS_REMAP`. In `1.101.0-nightly` execution, `rustc` argv adds `-Z embed-metadata=no` and `--json=...unused-externs-silent`, and build-script/dependency paths move under `debug/build/<pkg>/<hash>/out`. |
| **Incremental Compilation Default in CI** | `CARGO_INCREMENTAL` and `build.incremental` take top precedence across all versions. | Cargo `1.99.0` (`src/workspace/profiles.rs`, PR #17220) inserts `.or_else(\|\| is_ci().then_some(false))` after `build.incremental`, disabling `rustc` incremental compilation by default when `CI` is set in the environment. |

## Findings

### 1. Compilation-Subject Identity (`Unit` and `UnitInner`)

**Basis: source + documentation + execution**

In `src/cargo/core/compiler/unit.rs` (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef` and `797e8a9bca276c1c9f9f738d2a20f484fa4eea9d`), `Unit` is a reference-counted handle to `UnitInner`, interned via `UnitInterner::intern` so that structurally equal units share a single instance. `UnitInner` derives `Hash`, `PartialEq`, `Eq`, `PartialOrd`, and `Ord` over the following identity-bearing fields:

- `pkg`: the concrete `Package` (identified externally by an opaque `PackageIdSpec` / `pkg_id` rather than a bare crate name);
- `target`: the manifest `Target` descriptor (`lib`, `bin`, `example`, `test`, `bench`, or `custom-build`), distinct from the target architecture triple;
- `profile`: the effective `Profile` struct (which can differ from the named `[profile.*]` table in `Cargo.toml`, e.g., when Cargo forces `panic = "unwind"` for test/benchmark harnesses or applies per-package profile overrides);
- `kind`: `CompileKind` (`CompileKind::Host` or `CompileKind::Target(CompileTarget)`), distinguishing host build scripts and procedural macros from target-architecture units;
- `mode`: `CompileMode` (`Build`, `Check`, `Test`, `Doc`, `Doctest`, `RunCustomBuild`, etc.);
- `features`: the sorted `Vec<InternedString>` of features activated specifically for this unit's dependency context;
- `rustflags` and `rustdocflags`: per-unit compiler and documentation flags (`Arc<[String]>`);
- `links_overrides`: native build-script override map;
- `is_std`: whether the unit is part of an unstable `-Z build-std` standard-library build;
- `dep_hash`: a `u64` hash computed in a post-construction graph pass to distinguish otherwise-identical units whose transitive dependencies differ (for example, when host and target contexts link differently configured instances of a shared dependency);
- `artifact` and `artifact_target_for_features`: unstable `-Z bindeps` artifact-dependency state; and
- `skip_non_compile_time_deps`: internal compile-time dependency filtering state.

Package and target selection (`src/cargo/ops/cargo_compile/packages.rs`, `compile_filter.rs`, `unit_generator.rs`) only selects the initial root units (`UserIntent::Build`, `Check`, `Test`, `Bench`, `Doc`, `Doctest`). A single manifest target routinely maps to multiple `Unit` instances in one command: for example, `cargo test` generates both a normal linkable library unit (`CompileMode::Build`) and a unit-test harness unit (`CompileMode::Test`) for the same `[lib]` target.

### 2. Unstable `--unit-graph` vs. Internal `UnitInner`

**Basis: source + documentation + execution**

Cargo's `-Z unstable-options --unit-graph` flag (`src/cargo/core/compiler/unit_graph.rs` and `src/doc/src/reference/unstable.md`) serializes the planned `UnitGraph` as JSON (`version: 1`) without executing the build. Each `SerializedUnit` entry exposes:

- `pkg_id`, `target`, `profile`, `platform` (`null` for `CompileKind::Host`, or the target triple string for `CompileKind::Target`), `mode`, `features`, `is_std`, and `dependencies` (array of `{ "index": usize, "extern_crate_name": InternedString, "public": bool, "noprelude": bool }`), along with top-level `roots` indices.

However, `SerializedUnit` is a projection rather than a lossless serialization of `UnitInner`: it omits `rustflags`, `rustdocflags`, `links_overrides`, `dep_hash`, artifact-dependency state, and the internal `unit_for` edge context. Consequently, an external verification tool that keys semantic artifacts by compilation subject must account for the full `UnitInner` discriminator dimensions (including compiler flags and dependency closure hashes) rather than assuming `(package, target)` or raw `--unit-graph` entries are canonical.

### 3. Contextual Feature Resolution (`ResolvedFeatures` and `FeaturesFor`) vs. `cargo metadata`

**Basis: source + documentation + execution**

Cargo separates lockfile dependency resolution from compile-time feature resolution (`src/cargo/ops/resolve.rs`, `src/cargo/core/resolver/features.rs`, `src/doc/src/reference/resolver.md`, `src/doc/src/reference/features.md`):

1. **Lockfile Pass vs. Active Feature Pass**: `resolve_ws_with_opts` first computes `resolved_with_overrides` across the workspace as if all features and optional dependencies of workspace members were enabled (populating `Cargo.lock`). It then constructs `FeatureOpts` and runs `FeatureResolver::resolve` for the selected package specs and command options, returning `WorkspaceResolve` with both a package-level `targeted_resolve` and contextual `SpecsAndResolvedFeatures`.
2. **Contextual Keying (`FeaturesFor`)**: `ResolvedFeatures` keys `activated_features` and `activated_dependencies` by `(PackageId, FeaturesFor)`, where `FeaturesFor` has three variants:
   - `FeaturesFor::NormalOrDev` (default normal and development dependencies);
   - `FeaturesFor::HostDep` (build dependencies and procedural macros compiled for the host);
   - `FeaturesFor::ArtifactDep(CompileTarget)` (artifact dependencies targeting a specific platform).
3. **Resolver 1 vs. Resolver 2 and 3**:
   - Under Resolver 1, `FeatureOpts::new` disables context decoupling, unifying features across normal, host/build, dev, and inactive-target edges for each package.
   - Under Resolver 2 and Resolver 3 (the Edition 2024 default, which shares Resolver 2's feature unification rules while adding MSRV-aware version selection), `FeatureOpts::new` enables `decouple_host_deps`, `decouple_dev_deps` (when `HasDevUnits::No`), and `ignore_inactive_targets` (when `ForceAllTargets::No`). If a command builds dev units (`cargo test` or `--all-targets`), `HasDevUnits::Yes` disables `decouple_dev_deps` for that command.
   - Optional dependencies (`ResolvedFeatures::is_dep_activated`) are tracked separately from ordinary edges and activated via implicit same-name features, explicit `dep:name` syntax, `name/feature`, or weak `name?/feature` syntax.
4. **Why `cargo metadata` Cannot Reconstruct Unit Features**:
   - In `src/cargo/ops/cargo_output_metadata.rs`, `cargo metadata --format-version 1` runs `resolve_ws_with_opts` across all workspace members with `HasDevUnits::Yes` and (unless `--filter-platform <triple>` is passed) `ForceAllTargets::Yes`.
   - Crucially, `build_resolve_graph_r` populates each `MetadataResolveNode.features` array from the package-level `ws_resolve.targeted_resolve` (`resolve.features(pkg_id)`), discarding `SpecsAndResolvedFeatures[*].resolved_features` and `FeaturesFor`.
   - In the 3-toolchain runtime probe (`support/cargo-subject-features-unit-graphs-to/results.json`), `cargo metadata` across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly` collapses `probe-dep` into a single node with `"features": ["dev", "host", "normal", "targeted"]` (even under `--filter-platform`), whereas `unit-build` on both nightlies emits two separate `probe-dep` units with `"features": ["host"]` (for the build script) and `"features": ["normal"]` (for the library/binary), and `unit-test` emits `["host"]` and `["dev", "normal"]`.

### 4. Recursive Unit-Graph Expansion and Two-Stage `rustc` Invocation Assembly

**Basis: source + documentation + execution**

From command-selected roots, `build_unit_dependencies` (`src/cargo/core/compiler/unit_dependencies.rs`) expands the recursive `UnitGraph` before `BuildRunner` schedules jobs (`src/cargo/ops/cargo_compile/mod.rs`, `src/cargo/core/compiler/mod.rs`, `compilation.rs`, `custom_build.rs`, `src/cargo/util/rustc.rs`):

- **Intra-Package and Host/Target Splitting**:
  - Non-library targets (`bin`, `test`, `example`, `bench`) automatically acquire a dependency edge to the same package's `[lib]` target via `maybe_lib`; integration tests and benchmarks also acquire edges to binary targets.
  - Procedural macros (`target.proc_macro()`) and build scripts force `CompileKind::Host` (`FeaturesFor::HostDep`), even when parent units are cross-compiled for `CompileKind::Target(triple)`.
  - Each build script splits into two graph nodes via `compute_deps_custom_build`: a host compilation unit (`CompileKind::Host`, `CompileMode::Build`) and a build-script execution unit (`CompileMode::RunCustomBuild`), wired to upstream native-link build scripts via `connect_run_custom_build_deps`. If a package with a build script is used in both normal and host contexts with different features, Cargo compiles and runs two distinct build-script unit pairs because the script may inspect `CARGO_FEATURE_*` environment variables at runtime.
- **Stage 1 (Static Unit Preparation)**:
  - `prepare_rustc` constructs the base compiler command with crate name, edition, source path, crate types, output mode, `--target`, effective profile/codegen flags, and configured `rustflags`.
  - `build_deps_args` translates `UnitDep` edges into `-L` search paths and `--extern <crate_name>=<artifact_path>` arguments, sets `OUT_DIR` when the package has a `RunCustomBuild` unit, and populates artifact-dependency environment variables.
- **Stage 2 (Late Build-Script Output Injection)**:
  - Because `RunCustomBuild` units have not executed when the unit graph is constructed, static preparation cannot produce the final `rustc` command line.
  - During job execution, after a unit's `RunCustomBuild` dependencies finish, the `rustc` job closure locks `BuildScriptOutputs` and invokes `add_native_deps`, `add_plugin_deps`, and `add_custom_flags`, injecting `cargo::rustc-link-search`, `cargo::rustc-link-lib`, `cargo::rustc-cfg`, `cargo::rustc-check-cfg`, `cargo::rustc-flags`, and `cargo::rustc-env` values discovered at runtime.
- **Compiler Wrapper Chain**:
  - `Rustc::process` (`src/cargo/util/rustc.rs`) and `Compilation::rustc_process` (`src/cargo/core/compiler/compilation.rs`) nest configured wrappers as:
    ```text
    $RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC <rustc-args...>
    ```
  - `RUSTC_WORKSPACE_WRAPPER` is inserted only for workspace-member units and participates in Cargo's unit filename hash, whereas `RUSTC_WRAPPER` wraps all `rustc` invocations (including Cargo's initial `rustc -vV` probe).
- **Planned Graph vs. Executed Processes**:
  - In the runtime probe (`support/cargo-subject-features-unit-graphs-to/results.json`), `unit-build` plans 6 units (5 Rust compilations + 1 `run-custom-build`). A cold `-vv` build executes all 6 actions and passes the build-script-emitted `PROBE_BUILD_TAG=host` environment variable to the downstream app `rustc` invocation. An immediate warm rebuild with unchanged inputs produces the same 6-unit `--unit-graph` plan but executes 0 `rustc` processes, reporting `Fresh` for both packages.

### 5. Cross-Version Source and Runtime Deltas (`1.98.0-nightly` $\to$ `1.98.1` $\to$ `1.99.0` $\to$ `1.101.0-nightly`)

**Basis: source + documentation + execution**

1. **Cargo `1.98.0-nightly` (`fbb61be30`) to Stable `1.98.1` (`797e8a9bc`)**:
   - Across 17 claim-mapped files (`support/cargo-r348-r349-r352-to-rust-1981-source-review/source-observation.json` and `support/cargo-r350-coverage-to-rust-1981-source-review/source-observation.json`), 12 complete files are byte-identical (`unit.rs`, `unit_graph.rs`, `features.rs`, `cargo_output_metadata.rs`, `unit_generator.rs`, `unit_dependencies.rs`, `rustc.rs`, and 5 reference docs), and the `## unit-graph` section of `src/doc/src/reference/unstable.md` is byte-identical.
   - The 4 changed implementation files (`support/cargo-r348-r349-r352-to-rust-1981-source-review/diffs/`) modify process/argument construction:
     - `src/cargo/core/compiler/mod.rs`: `add_dep_arg` skips custom-build output directories when collecting dependency `-L` search paths; adds optional `hint-msrv` and `trim-paths` remapping.
     - `src/cargo/core/compiler/compilation.rs`: changes `deps_output` from a single `PathBuf` per compile kind to `BTreeSet<PathBuf>` and updates host runner/linker target selection.
     - `src/cargo/core/compiler/custom_build.rs`: updates `trim-paths` build-script environment variables from `CARGO_TRIM_PATHS` to `CARGO_TRIM_PATHS_SCOPE` and `CARGO_TRIM_PATHS_REMAP`.
     - `src/cargo/ops/cargo_compile/mod.rs`: includes manifest parse-pass warnings in emitted diagnostics, narrows `compile_ws` visibility, and records invocation time for unit-graph logging.
2. **Stable `1.98.1` (`797e8a9bc`) to Stable `1.99.0` (`5f94df478`)**:
   - **Workspace-Inherited `default-features` in Edition 2024** (`support/rust-199-cargo-source-followup/cargo-1981-parser.rs` vs. `support/rust-199-cargo-source-followup/cargo-199-parser.rs`, Cargo PR #17126): At `1.98.1` (`src/cargo/util/toml/mod.rs`), if a workspace dependency enabled or omitted `default-features`, a member specifying `default-features = false` was ignored (raising a hard error in Edition 2024 and a warning in earlier editions). At `1.99.0` (`src/workspace/parser/mod.rs`), Edition 2024 applies the member's `default-features` setting first before falling back to the workspace setting, changing active feature sets for Edition 2024 workspace-inherited edges that disable default features.
   - **Default Incremental Compilation in CI** (`support/rust-199-cargo-source-followup/cargo-1981-profiles.rs` vs. `support/rust-199-cargo-source-followup/cargo-199-profiles.rs`, Cargo PR #17220): At `1.98.1` (`src/cargo/core/profiles.rs`), incremental compilation checked `CARGO_INCREMENTAL` then `build.incremental` then `profile.*.incremental`. At `1.99.0` (`src/workspace/profiles.rs`), Cargo inserts `.or_else(|| is_ci().then_some(false))` after `build.incremental`, disabling `rustc` incremental compilation by default when `CI` is present in the environment.
3. **Runtime Comparison up to `1.101.0-nightly` (`3d7cf6e93`, `nightly`)**:
   - In `support/cargo-subject-features-unit-graphs-to/results.json`, `1.101.0-nightly` adds `"trim_paths": "none"` to every unit's `profile` object in `--unit-graph` JSON, passes `-Z embed-metadata=no` and `--json=...unused-externs-silent` in cold `rustc` invocations, and places build-script/dependency outputs under `debug/build/<package>/<hash>/out` rather than `debug/deps`.

## Boundaries

- **Not Examined**:
  - Runtime execution of Cargo `1.99.0` (`5f94df4789f005f9a352888e8355ffc645b7ed0e`) on the Edition 2024 inherited `default-features` fixture or `CI=1` incremental profile fixture (those two `1.99.0` findings are established from commit-pinned Cargo source and upstream PRs #17126 / #17220).
  - Unstable `-Z bindeps` artifact dependencies and `-Z build-std` runtime execution (covered only where their fields appear in `UnitInner` and `FeaturesFor::ArtifactDep`).
  - `rustdoc` and doctest command-line assembly beyond their `CompileMode` presence in `UnitGenerator`.
  - Byte-for-byte reproducible-build provenance between official binary distribution archives and the Cargo Git submodule commits.
- **Known Not to Apply**:
  - `cargo metadata --format-version 1` cannot be used to determine per-unit feature sets when Resolver 2 or 3 compiles the same package under distinct `FeaturesFor` contexts (`NormalOrDev` vs. `HostDep` vs. `ArtifactDep`).
  - `--unit-graph` membership does not imply that `rustc` or a configured `RUSTC_WRAPPER` ran during a build, nor does `--unit-graph` contain late `BuildScriptOutputs` flags/environment variables, `rustflags`, or `dep_hash`.
- **Unsupported**:
  - Stable Cargo (`1.98.1` and `1.99.0`) rejects `-Z unstable-options --unit-graph` on the stable release channel with exit code `101`.

## Evidence

### Primary Upstream Source Coordinates

- **Cargo `1.98.0-nightly` (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, submodule of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) and Stable `1.98.1` (`rust-lang/cargo@797e8a9bca276c1c9f9f738d2a20f484fa4eea9d`, submodule of `rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985`)**:
  - `src/cargo/core/compiler/unit.rs` (blob `19376a97914bf15457a1a653fb7ef7ee3310eb3d`, identical at both commits): `Unit`, `UnitInner`, `UnitInterner::intern`, and `dep_hash`.
  - `src/cargo/core/compiler/unit_graph.rs` (blob `944b062cddf6cb617e93a31d72e9d4a8ccb7675a`, identical at both commits): `UnitGraph`, `UnitDep`, `SerializedUnit`, and JSON emission.
  - `src/cargo/core/resolver/features.rs` (blob `6d45edc669145a77c6eb554e29d48dd3781b10ca`, identical at both commits): `ResolvedFeatures`, `FeatureOpts`, `FeaturesFor`, `FeatureResolver::resolve`, `activate_pkg`, and `is_dep_activated`.
  - `src/cargo/ops/resolve.rs` (blob `722cefe5713c43834c27762485f88e973f3d01eb` at `fbb61be30`): `WorkspaceResolve`, `SpecsAndResolvedFeatures`, and `resolve_ws_with_opts`.
  - `src/cargo/ops/cargo_output_metadata.rs` (blob `929a4892e97a58e23ac8b48056e9355ddfe3edaa`, identical at both commits): `OutputMetadataOptions`, `MetadataResolveNode`, and `build_resolve_graph_r`.
  - `src/cargo/ops/cargo_compile/unit_generator.rs` (blob `c56b3b1012442be1800568208b069fa0615e0be6`, identical at both commits): `UnitGenerator`, `generate_root_units`, and root `FeaturesFor` selection.
  - `src/cargo/core/compiler/unit_dependencies.rs` (blob `2d0ea7c3c62bfa3bd76730dcfacf052d0e8268ef`, identical at both commits): `build_unit_dependencies`, `compute_deps`, `maybe_lib`, `compute_deps_custom_build`, and `connect_run_custom_build_deps`.
  - `src/cargo/util/rustc.rs` (blob `42c06ecabe6601a6002834f6b52c43987ca29d2d`, identical at both commits): `Rustc::process` and `workspace_process` wrapper chaining.
  - Changed process/orchestration files between `fbb61be30` and `797e8a9bc`: `src/cargo/ops/cargo_compile/mod.rs`, `src/cargo/core/compiler/mod.rs`, `src/cargo/core/compiler/compilation.rs`, `src/cargo/core/compiler/custom_build.rs`, and `src/doc/src/reference/unstable.md`.
- **Cargo `1.99.0` (`rust-lang/cargo@5f94df4789f005f9a352888e8355ffc645b7ed0e`, submodule of `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`)**:
  - `src/workspace/parser/mod.rs` (lines 1224–1251, compared against `1.98.1` `src/cargo/util/toml/mod.rs` lines 1209–1267): Edition 2024 workspace-inherited `default-features` resolution (PR #17126).
  - `src/workspace/profiles.rs` (lines 73–82, compared against `1.98.1` `src/cargo/core/profiles.rs` lines 69–75): `is_ci()` fallback disabling incremental compilation by default in CI environments (PR #17220).

### Preserved Package Support Artifacts

| Support Path | Contents |
| :--- | :--- |
| `support/cargo-unit-graphs-rustc-invocations/FINDINGS.md`, `support/cargo-unit-graphs-rustc-invocations/FINDINGS-INVOCATIONS.md`, `support/cargo-unit-graphs-rustc-invocations/BOUNDARIES.md`, `support/cargo-unit-graphs-rustc-invocations/EVIDENCE.md`, `support/cargo-unit-graphs-rustc-invocations/REVALIDATION.md` | Detailed breakdown of recursive unit-graph expansion and two-stage `rustc` command construction at `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`. |
| `support/cargo-r348-r349-r352-to-rust-1981-source-review/source-observation.json`, `support/cargo-r348-r349-r352-to-rust-1981-source-review/matrix.json`, `support/cargo-r348-r349-r352-to-rust-1981-source-review/check_matrix.py`, `support/cargo-r348-r349-r352-to-rust-1981-source-review/cargo-compare.json` | 17-file source snapshot inventory, blob SHA-1 / SHA-256 table, and offline verification script comparing `1.98.0-nightly` (`fbb61be30`) against `1.98.1` (`797e8a9bc`). |
| `support/cargo-r350-coverage-to-rust-1981-source-review/source-observation.json`, `support/cargo-r350-coverage-to-rust-1981-source-review/claim-matrix.json`, `support/cargo-r350-coverage-to-rust-1981-source-review/check_source.py`, `support/cargo-r350-coverage-to-rust-1981-source-review/reproduce.md` | 10-file coverage-claim source mapping and diffs between `fbb61be30` and `797e8a9bc`. |
| `support/cargo-subject-features-unit-graphs-to/probe.py`, `support/cargo-subject-features-unit-graphs-to/check.py`, `support/cargo-subject-features-unit-graphs-to/results.json`, `support/cargo-subject-features-unit-graphs-to/fixture/Cargo.toml` | 39-command runtime probe, offline checker, multi-package workspace fixture, and raw stdout/stderr logs across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`. |
| `support/rust-199-cargo-source-followup/cargo-1981-parser.rs`, `support/rust-199-cargo-source-followup/cargo-199-parser.rs`, `support/rust-199-cargo-source-followup/cargo-1981-profiles.rs`, `support/rust-199-cargo-source-followup/cargo-199-profiles.rs`, `support/rust-199-cargo-source-followup/provenance.json`, `support/rust-199-cargo-source-followup/check.py` | Preserved Cargo `1.98.1` and `1.99.0` parser and profile source snapshots, gitlink trees, and provenance checker. |

## Revalidation

1. **Offline Verification of Preserved Multi-Version Evidence**:
   - Run `python3 -B support/cargo-subject-features-unit-graphs-to/check.py` to verify the 39 captured command outputs, unit-graph projections, `cargo metadata` feature unions, and cold/warm build transcripts across `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`.
   - Inspect `support/cargo-r348-r349-r352-to-rust-1981-source-review/source-observation.json`, `support/cargo-r350-coverage-to-rust-1981-source-review/source-observation.json`, and `support/rust-199-cargo-source-followup/provenance.json` to verify the commit-pinned source snapshots and diffs across `fbb61be30`, `797e8a9bc`, and `5f94df478`.
2. **Revalidating Against a Newer Toolchain**:
   - Resolve the target Rust release commit and its `src/tools/cargo` submodule gitlink.
   - Diff `src/cargo/core/compiler/unit.rs` (`UnitInner` fields and `dep_hash`), `src/cargo/core/compiler/unit_graph.rs` (`SerializedUnit`), `src/cargo/core/resolver/features.rs` (`FeaturesFor` and `FeatureOpts`), `src/cargo/ops/cargo_output_metadata.rs` (`MetadataResolveNode`), `src/cargo/core/compiler/unit_dependencies.rs`, `src/cargo/core/compiler/mod.rs` (`prepare_rustc`, `build_deps_args`, `BuildScriptOutputs`), `src/workspace/parser/mod.rs`, and `src/workspace/profiles.rs`.
   - Execute `python3 -B support/cargo-subject-features-unit-graphs-to/probe.py` against the candidate Cargo and `rustc` binaries to compare `--unit-graph` JSON schemas, `cargo metadata` resolve nodes, and cold/warm `-vv` `rustc` invocations.
