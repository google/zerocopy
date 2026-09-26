# Cargo feature resolution and metadata at fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef

## Summary

At `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, the feature set used to compile a crate is not, in general, a single property of a package. Cargo's command-specific feature resolver can distinguish the same package when it is used as a normal/dev dependency, a host build-dependency or proc macro, or an artifact dependency for a particular target. Resolver versions 2 and 3 use those distinctions to avoid several kinds of feature unification that resolver 1 performs.

That distinction makes `cargo metadata` useful but insufficient for reconstructing every active compilation unit. Metadata format 1 emits manifest feature definitions, requested dependency features, and one `resolve.nodes[].features` list per package. It does not serialize Cargo's contextual `ResolvedFeatures` map or its `FeaturesFor` key. A package that must be compiled twice with different host and target feature sets can therefore have two unit-level feature configurations even though metadata has only one package-level resolved feature list.

Cargo's unit construction path consumes the contextual feature resolver directly. Root units select a `FeaturesFor` context, dependency units derive one from the dependency edge, and the resulting feature vector becomes part of the unit. The unstable unit-graph output serializes `unit.features`, so it is a closer representation of a command's planned compilation configurations than `cargo metadata`. It is still a planned graph, not proof that every unit was executed; Cargo may reuse a fresh artifact instead of invoking rustc.

Optional and target-specific dependencies are also command-sensitive. Optional dependencies are explicit activation state in `ResolvedFeatures`; target predicates are checked against the relevant host or target compile kind. Resolver 2/3 ignore features from target-specific dependencies for targets not being built, separate host-side build/proc-macro features from normal dependency features, and separate dev-dependency features when no dev unit is being built.

No fresh Cargo or rustc execution was performed. This report is based on exact pinned Cargo source and documentation. It establishes the feature-resolution and metadata representations at that revision, not an empirical transcript of a particular build.

## Applicability

The primary subject is Cargo commit `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.

The report covers:

- Cargo resolver versions 1, 2, and 3 as implemented at that revision;
- command-selected feature resolution through `resolve_ws_with_opts` and `FeatureResolver`;
- normal/dev, host build/proc-macro, and artifact-target feature contexts;
- optional and target-specific dependency activation;
- metadata output format version 1;
- the relationship between metadata feature fields and compilation-unit feature sets.

Resolver 3 has the same feature-decoupling behavior as resolver 2 in the examined implementation. Its documented additional change is the default handling of Rust-version incompatibility, not a new feature-unification algorithm.

Artifact dependencies are included because the pinned resolver has an explicit `FeaturesFor::ArtifactDep(CompileTarget)` context. This report does not attempt a complete behavioral study of the unstable artifact-dependency feature.

The report does not generalize to adjacent Cargo revisions without revalidation.

## Findings

### Lockfile dependency resolution and compile-time feature resolution are distinct passes

Cargo's resolver documentation distinguishes dependency resolution for the lockfile from the feature set used for a concrete compilation. For lockfile purposes, Cargo resolves the workspace as if all features of all workspace members are enabled so optional dependencies are available in the graph. It then resolves again for the selected command and requested features to determine what is actually active for compilation.

The implementation reflects that separation. `resolve_ws_with_opts` first obtains a `resolved_with_overrides` dependency graph. It then constructs `FeatureOpts` and runs `FeatureResolver::resolve` for each selected package-spec group. The returned `WorkspaceResolve` therefore contains both a package-level `targeted_resolve` and one or more `SpecsAndResolvedFeatures` values.

A future consumer should not treat "present in Cargo.lock" or "present in the package resolve graph" as evidence that a dependency or feature is active in a particular compilation unit.

Basis: **documentation** + **source**.

### Cargo keys active features by package and dependency context

`ResolvedFeatures` contains:

- `activated_features`, mapping a contextual package key to enabled feature names;
- `activated_dependencies`, mapping the same kind of key to enabled optional dependencies;
- the `FeatureOpts` that determine which contexts remain distinct.

The contextual discriminator is `FeaturesFor`:

- `NormalOrDev`;
- `HostDep` for build-dependencies and proc macros;
- `ArtifactDep(CompileTarget)` for an artifact dependency with an explicit target.

`FeatureResolver::activate_pkg` records features under a key containing both the package ID and the context after applying the active resolver options. `ResolvedFeatures::activated_features` later queries that same contextual key.

The important identity is therefore not merely "package X has features A and B." Under resolver 2/3, a more precise statement can be "package X, when used in host context, has A; the same package in the normal target context has B."

Basis: **source**.

### Resolver 1 collapses contexts that resolver 2 and 3 can keep separate

At this pin, `FeatureOpts::new` leaves all decoupling disabled for resolver 1. For resolver 2 and resolver 3, it enables:

- `decouple_host_deps`;
- `decouple_dev_deps`;
- `ignore_inactive_targets`.

The implementation can subsequently weaken those separations for the command being run. If any dev units are being built, Cargo disables dev-dependency decoupling. If `ForceAllTargets::Yes`, Cargo disables inactive-target filtering.

Upstream documentation describes the same three resolver-2 effects:

1. target-specific dependency features for targets not being built do not activate;
2. build-dependency and proc-macro features do not unify with normal-dependency features;
3. dev-dependency features do not unify with normal-dependency features unless dev dependencies are currently needed.

Resolver 3 follows the resolver-2 feature path in this source.

Basis: **documentation** + **source**.

### Dev-dependency separation depends on whether the command builds dev units

Resolver 2/3 do not assign an intrinsically permanent feature namespace to dev dependencies. `FeatureOpts::new` disables `decouple_dev_deps` when `HasDevUnits::Yes`.

This means the active feature set can depend on the command's target selection. A build with no tests/examples/other dev units can keep dev-enabled features out of the normal dependency instance; a command that needs dev units may unify them.

This is one reason a workspace-wide feature inventory is not enough to reconstruct a particular command's compilation configuration.

Basis: **source** + **documentation**.

### Target-specific dependency features are filtered against the relevant compile kind

When inactive-target filtering is enabled, the feature resolver tests a dependency's platform predicate against the context being resolved.

The pinned source distinguishes:

- build-dependencies and host-side dependency contexts, checked for the host compile kind;
- normal/dev dependency contexts, checked against the requested compilation targets;
- artifact dependencies, checked against their artifact target.

The unit-dependency builder later performs the corresponding platform check before creating dependency edges.

Thus a target-specific dependency can exist in the manifest and lockfile while contributing neither a unit nor features to a command that does not build its target.

Basis: **source**.

### Optional dependencies are separate activation state, not merely ordinary dependency edges

An optional dependency does not recurse automatically during feature resolution. The resolver records enabled optional dependencies in `ResolvedFeatures.activated_dependencies`, and unit-dependency construction checks `is_dep_activated` before adding an optional dependency.

Cargo's feature syntax supplies several ways to reach that state:

- an optional dependency normally creates an implicit same-name feature;
- `dep:name` explicitly enables the optional dependency and suppresses the implicit same-name feature when used in the feature table;
- `name/feature` enables a dependency feature and can activate an optional dependency;
- `name?/feature` defers that dependency feature until something else activates the optional dependency.

Consequently, reconstructing an active build requires both the enabled package features and the resulting optional-dependency activation, not only a list of manifest dependencies.

Basis: **documentation** + **source**.

### Feature unification is additive within each context

Cargo documents feature unification as taking the union of all features requested for the same dependency. If two selected roots request different features of one dependency, a unified dependency context receives both.

This also explains why `default-features = false` on one dependency edge is not a global guarantee that defaults are absent. Another edge to the same unified context can request defaults and thereby enable them for that context.

With resolver 2/3, the union is taken within the contexts that remain unified. Host and normal target uses, for example, can remain separate and therefore receive different unions.

Basis: **documentation** + **source**.

### Workspace command selection affects which root features are resolved together

`resolve_ws_with_opts` groups package specs according to Cargo's feature-unification policy, then invokes `FeatureResolver::resolve` for those groups. Upstream documentation notes that when multiple workspace packages are built in one invocation, their dependency features are unified; separate Cargo invocations are required when that cross-root unification is undesirable.

The command-line behavior also differs between resolver 1 and resolver 2/3. Under resolver 2, `--features` can address selected workspace packages, and `--no-default-features` applies to selected workspace members rather than only the current package.

The active configuration therefore includes package selection and feature flags as well as the manifest graph.

Basis: **documentation** + **source**.

### Compilation units receive contextual features directly

Cargo does not flatten `ResolvedFeatures` to one package-wide feature list before constructing units.

For a root target, `UnitGenerator` chooses a context with `FeaturesFor::from_for_host(target.proc_macro())`, then obtains that context's feature vector from `ResolvedFeatures::activated_features`.

For a dependency unit, `unit_dependencies.rs` derives the context from the dependency relationship with `unit_for.map_to_features_for`, obtains the corresponding feature vector, and passes it into the unit interner.

The unit is therefore the point where the command's package/target/profile/compile-kind state and its contextual feature set meet.

Basis: **source**.

### The unit-graph output preserves the feature vector of each planned unit

The pinned unit-graph serializer emits `features: &unit.features` for every unit. If the same package appears as multiple units because its contexts require different features, those feature lists are represented at unit granularity.

This makes `-Zunit-graph` a stronger source for reconstructing planned compile configurations than package-level metadata.

It is still a planning artifact. As established separately in the corpus's Cargo unit-graph report, Cargo may decide that a planned unit is fresh and reuse its artifact rather than run rustc. Unit-graph membership is therefore not execution evidence.

Basis: **source** + **derived** from the separately preserved unit-graph report.

### Cargo metadata exposes three different feature concepts

Metadata format 1 contains several fields named or related to "features" that answer different questions.

`packages[].features` is the package's feature-definition map from its manifest. It describes what each feature would enable; it is not the set enabled by the command.

`packages[].dependencies[].features`, together with `uses_default_features`, `optional`, and `target`, describes what that manifest dependency declaration requests.

`resolve.nodes[].features` is a list of features recorded on a package node in the package-level `Resolve` graph.

These fields should not be substituted for one another.

Basis: **documentation** + **source**.

### Metadata serializes one resolved feature list per package, not Cargo's contextual map

`MetadataResolveNode` contains a single `features: Vec<InternedString>`. `build_resolve_graph_r` populates it with `resolve.features(pkg_id)` from the package-level `Resolve`.

The metadata implementation does run `resolve_ws_with_opts`, but it serializes `ws_resolve.targeted_resolve`; it does not serialize the command-oriented `SpecsAndResolvedFeatures[*].resolved_features` map. The JSON schema also has no `FeaturesFor` discriminator.

Therefore metadata format 1 cannot represent two simultaneous feature sets for one package when resolver 2/3 cause separate host and target units, or separate artifact-target contexts, for that package.

Basis: **source**.

### Metadata resolution is workspace-oriented, not a transcript of a build command

`cargo metadata` resolves all workspace members. Its source invokes `resolve_ws_with_opts` with `HasDevUnits::Yes`.

Without `--filter-platform`, metadata also sets `ForceAllTargets::Yes`. The source explicitly contains a TODO noting that features are otherwise resolved with host as the requested-kind fallback and asks how that should work. The documentation describes the resulting resolve output as including all target platforms.

With `--filter-platform <triple>`, Cargo uses that target for filtering and does not force all targets. The option narrows the `resolve` graph, while the `packages` array remains a manifest inventory containing all dependencies.

This makes metadata appropriate for discovering the package graph and a broad resolved feature view, but not a drop-in replacement for the exact selection semantics of an arbitrary `cargo build`, `cargo test`, or cross-target invocation.

Basis: **source** + **documentation**.

### Exact active-build reconstruction needs unit-level context

For this Cargo revision, a future tool that needs the exact feature configuration of each planned compilation subject should retain at least:

1. the selected command roots and targets;
2. resolver version and command-line feature/default-feature settings;
3. the relevant host and requested target triples;
4. contextual feature resolution, including optional-dependency activation;
5. the resulting unit graph, including each unit's `features` and compile kind.

`cargo metadata` remains useful for package/manifests/dependency declarations and package IDs, but its one resolved feature list per package is insufficient whenever one package has multiple contextual feature sets.

This is a representation claim, not a recommendation that Anneal adopt `-Zunit-graph` as its permanent interface.

Basis: **derived** from the source relationships above.

## Boundaries

- No fresh Cargo, rustc, build-script, proc-macro, cross-target, or metadata command was executed.
- This report establishes the exact pinned implementation and documentation. It does not claim adjacent Cargo versions behave identically.
- It does not claim `cargo metadata` is wrong. The metadata schema represents a package-level resolve graph; the limitation arises only when a consumer needs command-specific unit-level feature identity.
- The report does not give a complete semantic model of unstable artifact dependencies. It records the explicit `ArtifactDep(CompileTarget)` feature context used by this source.
- It does not exhaustively document Cargo target-`cfg` evaluation. It establishes where target activation participates in feature and unit selection.
- It does not cover every unstable feature-resolver option or custom feature-unification policy.
- It does not establish that every unit in `-Zunit-graph` runs. Fingerprint freshness and artifact reuse are separate execution decisions.
- It does not treat `Cargo.lock` as active-build state. Lockfile resolution deliberately covers optional possibilities beyond one concrete command.
- It does not establish exact rustc argv or environment; that is covered by the separate Cargo unit-graph/rustc-invocation report.
- The source's own TODO around unfiltered metadata feature resolution is preserved rather than resolved by inference.
- No Anneal architecture decision is made here.

## Evidence

**Source — Cargo implementation.** Repository `rust-lang/cargo`, commit `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.

- `src/cargo/core/resolver/features.rs`, blob `6d45edc669145a77c6eb554e29d48dd3781b10ca`:
  - `ResolvedFeatures`;
  - `FeatureOpts`;
  - `FeaturesFor`;
  - `FeatureOpts::new` and `new_behavior`;
  - `ResolvedFeatures::activated_features` and `is_dep_activated`;
  - `FeatureResolver::resolve`, `activate_pkg`, `activate_fv`, `activate_dependency`, and `activate_dep_feature`;
  - target-context selection in feature dependency traversal.
- `src/cargo/ops/resolve.rs`, blob `722cefe5713c43834c27762485f88e973f3d01eb`:
  - `WorkspaceResolve`;
  - `SpecsAndResolvedFeatures`;
  - `resolve_ws_with_opts`, including package-spec grouping and the second `FeatureResolver::resolve` pass.
- `src/cargo/core/compiler/unit_dependencies.rs`, blob `2d0ea7c3c62bfa3bd76730dcfacf052d0e8268ef`:
  - dependency-unit `FeaturesFor` derivation;
  - contextual feature lookup;
  - target-platform and optional-dependency edge filtering.
- `src/cargo/ops/cargo_compile/unit_generator.rs`, blob `c56b3b1012442be1800568208b069fa0615e0be6`:
  - root-unit contextual feature lookup.
- `src/cargo/ops/cargo_output_metadata.rs`, blob `929a4892e97a58e23ac8b48056e9355ddfe3edaa`:
  - `OutputMetadataOptions`;
  - `MetadataResolveNode`;
  - `build_resolve_graph`;
  - `build_resolve_graph_r`;
  - package-level `resolve.features(pkg_id)` serialization.
- `src/cargo/core/compiler/unit_graph.rs`, blob `944b062cddf6cb617e93a31d72e9d4a8ccb7675a`: unit-graph serialization of `unit.features`.

**Documentation — same Cargo revision.**

- `src/doc/src/reference/features.md`, blob `d3fcd66fb63014f42d28f811cc46242fd02aef80`: optional dependencies, dependency features, feature unification, resolver-2 behavior, and command-line feature semantics.
- `src/doc/src/reference/resolver.md`, blob `26530990f4fe21015d44db5cbb261efcf4fd647c`: lockfile versus compile feature resolution, resolver-2 feature rules, workspace unification, and resolver-version semantics.
- `src/doc/src/commands/cargo-metadata.md`, blob `bb1c4da0b4cccc2dc65bf30a5269d1f8a0edb9d9`: metadata JSON fields, feature-selection options, and `--filter-platform`.

No evidence in this report is fresh **execution**.

## Revalidation

For a later Cargo revision, first perform a narrow source diff.

1. Find `ResolvedFeatures`, `FeaturesFor`, and `FeatureOpts). Check whether feature identity is still keyed by dependency context and whether resolver 2/3 still decouple host, dev, and inactive-target features in the same cases.
2. Inspect `resolve_ws_with_opts` and the unit generator/dependency builder. Confirm which resolved-feature object actually supplies each unit's feature vector.
3. Inspect metadata's resolve-node schema and construction. If metadata now serializes contextual feature sets or unit identities, the main insufficiency conclusion may no longer hold.
4. Inspect the unit-graph serializer and confirm that each unit still carries its resolved feature list.
5. Re-read the resolver and metadata documentation at that exact revision.

On an execution-capable surface, use one small workspace that forces the same dependency package into distinct contexts:

- use dependency `dep` normally with feature `normal`;
- use the same `dep` as a build-dependency with feature `host`;
- add a target-specific edge enabling feature `targeted`;
- add an optional dependency activated by one root feature;
- add a dev-dependency feature and both a non-dev and test command.

For the exact Cargo revision, preserve:

- `cargo metadata --format-version 1`;
- metadata with `--filter-platform` for the host and an alternate target;
- the equivalent command's `-Zunit-graph` output;
- verbose build output as an execution control;
- manifests, lockfile, exact toolchain, host/target triples, and hashes.

The decisive observation is whether one package has multiple unit-level feature vectors while metadata still has only one `resolve.nodes[].features` list. That establishes the representation gap for the tested revision. It does not prove that every unit graph node executes or that metadata is unsuitable for package-level dependency discovery.
