# Lake dependency resolution at Lean v4.30.0-rc2

## Summary

Lake at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) does **not** solve one global set of package-version constraints. It resolves one package per package base name while traversing the dependency graph. Once a package with that name is present in the workspace, later declarations with the same name are skipped. The resolver deliberately visits a package's direct dependencies in reverse declaration order before descending, so later `require`s and root-level requirements are encountered first. Lake's own help nevertheless says that if the graph requests multiple versions of one package, the materialized version is undefined; the traversal order is therefore an implementation fact, not a supported multi-version constraint-solving contract.

A dependency declaration reaches that graph through one of three source paths. An explicit path dependency is loaded from that relative path. An explicit Git dependency is cloned or updated at its requested revision. A dependency without `from`/source information is looked up in Reservoir using its scope and name. For a registry version range, Lake parses the range locally, asks Reservoir for the package's version array, and selects the **first** returned version that satisfies the range. Lake does not sort the returned versions or compute a maximum itself. With no requested registry version, Lake uses the registry Git source's `defaultBranch` when present; with `@ git <rev>`, it forwards that revision directly.

`lake-manifest.json` changes subsequent resolution from "choose a source/revision" to "materialize these locked package entries." A Git entry records both the exact checked-out commit (`rev`) and the input revision (`inputRev`); ordinary workspace loading uses those locked entries rather than re-running registry version selection. A path entry records the relative path. The manifest is therefore the important reproducibility boundary for dependency *selection*, although it does not by itself make package contents immutable or make builds reproducible.

Basis: pinned implementation source + same-revision Lake documentation + derived synthesis.

## Applicability

These findings apply to Lake as shipped in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The report covers package-source selection, version-range interpretation, graph traversal and same-name handling, `lake update` versus ordinary manifest-backed loading, inherited manifest entries, and package-entry overrides. It does not attempt to restate the full manifest schema, Git/path materialization behavior, relocation contract, or build-artifact invalidation rules; neighboring reference reports own those subjects.

Reservoir is treated as an external registry service. The pinned Lake client code establishes the request and response fields Lake consumes, but this investigation did not pin and reconstruct the Reservoir server revision that answered requests on 2026-09-27. In particular, the server's ordering guarantee for the versions array is not established here. The finding that Lake selects the first matching array element is a Lake implementation fact; whether Reservoir promises a particular order is separate.

No fresh Lake or Reservoir process was executed. The operational conclusions below come from the pinned implementation and same-revision documentation.

## Findings

### Lake resolves one package per base name, not one version per constraint set

`Dependency.name` is the package's graph identity. Its source comment requires the name to match the dependency package's declared name and to be unique across the dependency graph. `scope` is a registry qualifier, not an additional graph-identity component.

During recursive resolution, Lake scans each package's direct dependencies in reverse declaration order. Before loading a dependency, it checks whether any package already in the workspace has the same `baseName`; if so, that declaration is skipped. It also rejects a package requiring itself, or another package with the same name, along the current edge. Cycle detection is layered around the recursive fetch.

The traversal is breadth-first in the sense relevant to dependency priority: Lake loads all missing direct dependencies of a package before recursing into their dependencies. The source documents two reasons for reverse direct-dependency order: later `require`s should shadow earlier ones, and user/root requirements should take priority over inherited requirements.

This is not a global version solver. Lake does not gather all version predicates for a package name, intersect them, backtrack over candidate versions, or keep multiple versions of the same package name. Same-name declarations encountered after a package has been loaded do not trigger another version choice.

Lake's user-facing `lake update` help deliberately sets a stricter support boundary: if dependencies request multiple versions of the same package, "the version materialized is undefined." A future agent should therefore not use the current traversal order as a supported way to resolve incompatible version requirements, even though the pinned source explains which declarations are intentionally visited first.

Evidence:
- [`Dependency` graph-identity contract](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L41-L69)
- [`Workspace.resolveDepsCore`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L110-L140)
- [documented dependency traversal order](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L319-L352)
- [`lake update` help, including the multiple-version warning](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Help.lean#L195-L213)

### A declaration selects path, Git, or Reservoir resolution

`Dependency` separates four inputs that matter here: `name`, registry `scope`, optional textual `version?`, and optional explicit `src?`.

If `src?` is present, Lake bypasses Reservoir:

- `.path dir` resolves to the package at that relative filesystem location; or
- `.git url inputRev? subDir?` materializes the repository and optional package subdirectory at the requested Git revision.

If `src?` is absent, Lake requires a nonempty scope and uses Reservoir. The same-revision README describes this as the default behavior of `require <scope> / <name>` without a `from` clause.

For Reservoir dependencies, the textual `version?` has three modes:

1. no version: use the selected registry Git source's `defaultBranch` if one is provided;
2. `git#<rev>` (produced by Lean syntax `@ git <rev>` or TOML `rev` without an explicit source): use that Git revision directly; or
3. any other string: parse it as Lake's `VerRange` and select a matching registry version.

The registry package metadata can contain multiple sources. Lake's `RegistryPkg.gitSrc?` uses `Array.find?` and therefore takes the first source whose type is Git. Non-Git registry sources are not materializable by this code path; if no Git source exists, dependency materialization fails.

For the selected Git source, `LAKE_PKG_URL_MAP` can replace the repository URL by package name before the Git operation. This changes the physical endpoint Lake contacts without changing the dependency's graph name.

Evidence:
- [`Dependency` and `DependencySrc`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L24-L69)
- [`require` lowering](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/DSL/Require.lean#L18-L58)
- [TOML dependency decoding](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Toml.lean)
- [`Dependency.materialize`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L155-L223)
- [`RegistryPkg.gitSrc?`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Reservoir.lean#L84-L85)
- [`LAKE_PKG_URL_MAP` loading](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Env.lean#L163-L206)
- [same-revision dependency documentation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/README.md#L433-L512)

### Registry version ranges are local filters over Reservoir's returned order

When a registry dependency supplies a non-`git#` version string, Lake parses it as `VerRange`. At this revision the range language supports comparator predicates, comma-separated conjunction, `||` disjunction, wildcards, caret ranges, and tilde ranges. A bare fully specified version is rejected as a range; the parser tells the user to prefix an exact pin with `=` or use a broader comparator such as `≥`.

`VerRange.test` checks whether any disjunctive clause has all of its comparators satisfied. After parsing the range, `Dependency.materialize` calls Reservoir's `/versions` endpoint and then performs:

```text
vers.find? (ver.test ·.version)
```

The first matching `RegistryVer` supplies the Git revision. There is no Lake-side sort, maximum-version calculation, or second pass over the result array. Thus the user-facing phrase "latest version compatible" depends on the registry returning versions in the intended preference order; Lake itself only consumes the first match.

This matters for reproducibility. Re-running an unlocked range resolution can choose a different revision if the registry's returned version set or ordering changes. Once the resulting Git dependency has been written to the manifest, ordinary locked loading uses the manifest's exact `rev` instead of evaluating the range again.

Evidence:
- [`VerRange` parser and predicates](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Util/Version.lean#L352-L624)
- [Reservoir package-version response parsing](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Reservoir.lean#L144-L187)
- [first-match version selection in `Dependency.materialize`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L172-L207)

### No requested registry version means the registry's default branch, not the newest release

If a registry dependency has no `version?`, Lake does not fetch the registry version list. It reads the first Git source from the package metadata and uses that source's optional `defaultBranch` as the input Git revision.

If `defaultBranch` is absent, the input revision remains `none`; `cloneGitPkg` then clones without an explicit checkout, leaving Git's cloned default branch/HEAD as the selected source before Lake records the actual `HEAD` commit.

A versionless registry dependency therefore means "follow the registry Git source's default branch behavior at update time," not "choose the highest indexed semantic version." The exact commit becomes stable only after it is captured in the manifest.

Evidence:
- [registry source fields, including `defaultBranch`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Reservoir.lean#L22-L91)
- [versionless registry branch selection](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L172-L207)
- [`cloneGitPkg` behavior when no revision is supplied](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L28-L39)

### Updating and ordinary loading use different resolution paths

`Workspace.loadWorkspace` chooses between two high-level paths after loading the root package configuration:

- if `updateDeps` is true, call `updateAndMaterialize`, which resolves configuration declarations and writes a new manifest;
- otherwise, if `lake-manifest.json` exists, call `materializeDeps`, which uses the locked package entries; or
- otherwise, with no manifest, fall back to `updateAndMaterialize` and create one.

The same-revision README summarizes the user-facing consequence: after a dependency has been resolved and written to `lake-manifest.json`, ordinary commands do not update resolved dependencies; `lake update` is required to move them.

This distinction is more important than the original version syntax for repeatability. A declaration such as a branch, version range, or versionless Reservoir package controls **update-time selection**. The manifest's exact entry controls **ordinary locked materialization**.

Evidence:
- [`Workspace.loadWorkspace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Workspace.lean#L31-L42)
- [same-revision dependency documentation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/README.md#L433-L457)

### The manifest freezes a materialized Git commit while retaining the requested input revision

A Git `PackageEntry` stores:

- `url`: the materialization URL;
- `rev`: the exact Git commit observed after materialization;
- `inputRev`: the requested Git revision expression, when one exists; and
- optional `subDir`.

For a range-based Reservoir dependency, `inputRev` becomes the concrete registry-provided Git revision chosen for the matching version; the semantic version range itself is not stored in the manifest entry. For an explicit branch/tag/revision input, `inputRev` stores that input while `rev` stores the exact checked-out commit.

Ordinary `PackageEntry.materialize` uses `rev` as the checkout target. If the repository is already at that commit, Lake deliberately avoids a fetch; if it is absent or at another revision, the materializer may clone/fetch/checkout as described in the separate read-only/offline report.

The manifest therefore preserves the selected revision, not the reasoning that selected it. To understand *why* a range resolved to a particular release, a future investigation needs the package configuration plus the relevant registry response or registry history; `lake-manifest.json` alone does not retain the original range-to-version decision.

Evidence:
- [`PackageEntrySrc.git`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L64-L117)
- [configured dependency materialization and manifest-entry creation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L155-L223)
- [locked `PackageEntry.materialize`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L228-L265)

### `lake update` can refresh all root dependencies or preserve unselected root locks

The update path carries a `toUpdate : NameSet`.

A bare update has an empty set. In that case Lake does not seed the resolver with old manifest entries, so root dependency declarations are rematerialized from their current configuration and the new result is written to the manifest.

When `toUpdate` is nonempty, `reuseManifest` loads the existing manifest and retains package entries that are both:

- not marked `inherited`; and
- not named in `toUpdate`.

Those retained entries cause unselected root dependencies to materialize from their previous lock rather than re-running source/version selection. Selected root dependencies are resolved from their current declarations.

Transitive state is handled separately. After Lake loads a dependency, `addDependencyEntries` imports that dependency's own manifest entries, marks them inherited, and rebases inherited path entries under the containing package directory. If a dependency lacks a manifest, Lake warns and resolves its declared dependencies through the ordinary recursive update path instead.

This means Lake's update model is lock reuse plus ordered graph traversal, not a global re-solve of every transitive constraint. The implementation documentation describes `toUpdate` in terms of the root package's direct dependencies; the user-facing help should not be read as a promise that naming an arbitrary transitive package performs a package-manager-style global constraint update.

Evidence:
- [`reuseManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L144-L172)
- [`addDependencyEntries`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L174-L185)
- [`updateAndMaterializeDep`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L187-L207)
- [`Workspace.updateAndMaterializeCore`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L309-L391)
- [`lake update` CLI](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Main.lean#L880-L886)

### Locked loading is name-indexed and fails closed on missing manifest entries

`Workspace.materializeDeps` converts the manifest's package array into a map keyed by package name, then recursively walks the package dependency graph using the same name-oriented traversal as the update path.

For each dependency declaration, Lake looks up that name in the package-entry map. If no entry exists:

- a missing root dependency produces an error directing the user to `lake update <name>`; and
- a missing transitive dependency is treated as evidence that the manifest is corrupt and requires a full `lake update`.

When an entry exists, its source controls materialization. The current dependency declaration still contributes configuration options to `loadDepPackage`, but ordinary loading does not re-run Reservoir version selection for that name.

Before traversal, Lake validates the root package's current direct declarations against the manifest only for certain source changes. Git URL and requested Git revision changes produce out-of-date warnings, and a Git/path source-kind change produces a warning. A path-to-path change is not compared in this function. Full path-source staleness is covered by the separate Git/path dependency report.

Evidence:
- [`validateManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L429-L448)
- [`Workspace.materializeDeps`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L450-L494)

### Package-entry overrides replace locks by name after manifest validation

Locked loading has two override layers after it builds the initial name→entry map and validates the root manifest:

1. entries loaded from the workspace's `.lake/package-overrides.json`; then
2. entries supplied through `LoadConfig.packageOverrides`, including the CLI `--packages=<file>` mechanism.

Each layer inserts entries by package name, so later inserts replace earlier entries with the same name. Resolution then uses the resulting map.

These are materialization overrides, not a second dependency graph. They do not add a dependency that no package declares; they replace the package entry Lake will use when traversal reaches an existing dependency name. Because `validateManifest` runs before these insertions, its source-change warnings compare root declarations with the original manifest, not with the subsequent override entry.

This override mechanism is relevant to prepared environments: a consumer can redirect a locked package entry without rewriting the root manifest, but that redirection is an explicit input to workspace loading and must be included in any reproducibility claim.

Evidence:
- [workspace package-overrides location](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Workspace.lean#L170-L176)
- [`Workspace.materializeDeps` override insertion order](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L450-L494)
- [`--packages` loading](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Main.lean#L291-L295)

### Practical resolution model

For the pinned revision, the useful mental model is:

| Situation | What chooses the dependency source/revision? | Persistent result |
| --- | --- | --- |
| Explicit path during update/no-manifest load | configured relative path | manifest path entry |
| Explicit Git during update/no-manifest load | configured URL + requested Git revision | exact `rev` plus `inputRev` |
| Reservoir with `@ git <rev>` | first registry Git source + requested Git revision | exact `rev` plus `inputRev` |
| Reservoir with version range | first registry Git source + first returned version satisfying `VerRange` | exact `rev`; range reasoning is not retained in the entry |
| Reservoir with no version | first registry Git source + `defaultBranch`, or clone default HEAD if absent | exact `rev` plus branch input when present |
| Ordinary load with manifest | package entry keyed by dependency name | existing manifest remains selection authority |
| Ordinary load with package override | override entry keyed by dependency name | override affects this load; manifest file need not change |
| Same package name appears again in graph | already-loaded package wins; later declaration is skipped | no second package version |

The practical reproducibility rule follows directly: if an Anneal workflow cares which dependency revision is consumed, preserve and validate the locked manifest and any override inputs. Re-evaluating a branch, registry default, or range is a new resolution event, not a replay of the old one.

## Boundaries

This report does not establish Reservoir's server-side ordering guarantee for package versions or sources. Lake consumes the first matching version and first Git source it receives; the registry contract behind that ordering requires separate pinned Reservoir research. Do not infer that an arbitrary API response order is sorted merely because `lake update` help says "latest version compatible."

No runtime probe established the exact network transcript, response ordering, or behavior under a deliberately adversarial registry response. The implementation path is direct enough to establish Lake's local selection algorithm, but an execution fixture would strengthen the observable-service boundary.

This report does not claim that `lake-manifest.json` alone gives byte-reproducible dependencies or builds. A Git checkout can be dirty, path dependencies are not content-addressed, environment/configuration can affect package loading, and build products have separate trace/hash/cache state. Those subjects are covered elsewhere in the corpus.

The report does not define a supported strategy for graphs that require incompatible versions of one package name. Lake's help explicitly calls that result undefined. The source traversal order is recorded so agents can understand observed behavior and precedence, not so they can depend on multi-version resolution.

The targeted-update discussion is intentionally limited to what the pinned `toUpdate`/manifest-reuse implementation establishes. This investigation did not execute `lake update <transitive-name>` against competing transitive manifests, so it does not claim a stronger user-facing contract for arbitrary transitive update names.

The version-range section records the parser and selection behavior relevant to dependency resolution, not every edge case of `StdVer` suffix ordering. Adjacent Lake releases may change both the range language and registry protocol.

## Evidence

The primary source revision is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned source blobs inspected:

- `src/lake/Lake/Config/Dependency.lean` — `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`
- `src/lake/Lake/DSL/Require.lean` — `53a2193ce8636f1974330a9b344dce6b00d6981e`
- `src/lake/Lake/Load/Toml.lean` — `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`
- `src/lake/Lake/Load/Materialize.lean` — `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`
- `src/lake/Lake/Load/Resolve.lean` — `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`
- `src/lake/Lake/Load/Workspace.lean` — `9f25dd62bc752ede695a25fc20371157eb65d64b`
- `src/lake/Lake/Load/Manifest.lean` — `760eb81419762fb0ab11393e93082930645e2b6d`
- `src/lake/Lake/Reservoir.lean` — `20789b581b8f9d7361f8844d8978a64b5a6da9bb`
- `src/lake/Lake/Util/Reservoir.lean` — `ab19b5e5c7927835ee6565fdfc6a755e2de0ea1f`
- `src/lake/Lake/Util/Version.lean` — `7d89bda7ac1abc6d8c07d6e48e50ed20cfeb74c1`
- `src/lake/Lake/Config/Env.lean` — `eed315c538de746a891d18f72564e88aea64e969`
- `src/lake/Lake/Config/Workspace.lean` — `b9c01f130240ae7c65ee298778351ddbe312374e`
- `src/lake/Lake/CLI/Main.lean` — `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`
- `src/lake/Lake/CLI/Help.lean` — `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb`
- `src/lake/README.md` — `2bc9c7832db61b10e78d33cd5e980449e4da13a0`

The same-revision README was used as descriptive upstream documentation for the user-facing dependency/update contract. The implementation files above are the primary evidence for the resolver algorithm, local range selection, manifest-lock transition, update reuse, and override precedence.

Neighboring corpus reports were inspected to avoid duplicating their stronger subjects:

- `lake-manifest-schema-locking-v4-30-0-rc2`
- `lake-git-path-dependencies-v4-30-0-rc2`
- `lake-readonly-relocation-offline-concurrency-v4-30-0-rc2`
- `lake-state-model-v4-30-0-rc2`

No fresh execution evidence was acquired.

## Revalidation

After a Lake revision change, the cheapest source revalidation is to inspect these boundaries in order:

1. `Lake/Config/Dependency.lean` and the Lean/TOML loaders: dependency identity, source variants, scope, and version-input encoding.
2. `Lake/Load/Materialize.lean`: explicit-source handling, Reservoir lookup, range selection, selected revision, and manifest-entry construction. In particular, search for the current equivalent of `vers.find?`; a sort or solver introduced here would materially change this report.
3. `Lake/Reservoir.lean`: registry source and version response shapes and how a Git source is selected.
4. `Lake/Util/Version.lean`: the range grammar and `VerRange.test` semantics.
5. `Lake/Load/Resolve.lean`: traversal order, same-name deduplication, targeted manifest reuse, inherited-entry import, root-manifest validation, override precedence, and missing-entry failures.
6. `Lake/Load/Workspace.lean`: when normal loading uses a manifest versus performs an update.
7. `Lake/CLI/Help.lean` and `README.md`: whether the public contract still disclaims multiple versions and still describes ordinary commands as preserving locked resolution.

A compact execution probe can then distinguish the facts most likely to change without recreating a large ecosystem project:

- serve a tiny fake registry endpoint with one package, two Git sources, and deliberately ordered matching versions; point `RESERVOIR_API_URL` at it and record which source/version Lake chooses;
- reverse only the returned version order and confirm whether the selected commit changes;
- create root and transitive dependencies with the same package base name but different source/revision requests and record the selected package plus warnings;
- run ordinary `lake build` twice around a registry change while preserving the manifest to confirm the locked `rev` prevents re-resolution;
- delete the manifest and repeat to show the resolution event happens again;
- exercise bare `lake update`, `lake update <direct-dependency>`, and a named transitive dependency while preserving before/after manifests; and
- supply a package override entry for a locked dependency and record the materialized source while confirming the root manifest remains unchanged.

Preserve the fake-registry response bytes, package fixtures, before/after manifests, and command logs. That probe would cheaply verify both the local algorithm and the service-boundary assumptions that source inspection alone cannot establish.
