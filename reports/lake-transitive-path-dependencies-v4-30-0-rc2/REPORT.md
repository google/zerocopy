# Transitive path dependencies in Lake v4.30.0-rc2

## Summary

Lake v4.30.0-rc2 interprets a path dependency relative to the package that declares it, but it does not preserve that nested coordinate system in the root lockfile. During update, Lake flattens the dependency closure into the root `lake-manifest.json`. A path entry inherited from package `P` is rewritten from `child/path` to `P`'s root-workspace-relative directory joined with `child/path`, then marked `inherited`. A Git entry is also marked inherited but is not path-rebased because its repository identity is independent of the parent's filesystem location.

That flattening is not cosmetic. Ordinary locked workspace loading builds one name-indexed map from the root manifest and resolves every direct and transitive dependency from it. A locked path entry is materialized as `workspace_root / recorded_dir`, with no parent-package context available. If a transitive dependency is absent from the root manifest, Lake reports the manifest as corrupt rather than consulting the parent's manifest to reconstruct the edge.

The `inherited` bit primarily records ownership/update provenance. On update, inherited entries from the previous root manifest are not reused as root-owned locks; Lake rederives them from dependency manifests or from the dependency configuration it is traversing. The resolver visits direct dependencies before descending, in reverse declaration order, so later user requirements shadow earlier ones and root requirements take priority over inherited requirements. Since package names are globally unique in the workspace graph, a flattened transitive path entry and a root requirement with the same package name do not coexist as independent nodes.

This model explains Anneal's current prepared-archive transformation. Anneal reads Aeneas's already-flattened manifest, requires every inherited package to be a path dependency, rebases each path from Aeneas-workspace coordinates into the generated verification workspace, marks those entries inherited, and adds Aeneas itself as the direct non-inherited path dependency. The generated manifest therefore contains a complete root-relative closure without requiring Lake to write into or rediscover the read-only Aeneas tree.

Basis: pinned Lake implementation source + checked-in Anneal V2 archive construction + derived synthesis.

## Applicability

These findings apply to Lake as shipped in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The Anneal-specific observations apply to `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, where the V2 archive-cache integration fixture constructs a generated Lake workspace from the Aeneas archive.

The report focuses on transitive **path** dependencies: how their relative coordinates are interpreted, flattened, inherited, reused, and consumed. Git entries appear only where the contrast explains why path rebasing is necessary. General Git-versus-path behavior, whole-manifest schema, read-only execution, and package identity after vendoring are separate reports.

No fresh Lake process was executed. The traversal, rebasing, lockfile, and precedence conclusions below come from exact pinned source. Runtime revalidation is specified where it would strengthen operational confidence.

## Findings

### A path dependency starts in the declaring package's coordinate system

`DependencySrc.path dir` means a package at a fixed path relative to the dependent package's directory. When Lake materializes a live dependency declaration, `Dependency.materialize` receives the declaring package's root-workspace-relative directory as `relParentDir`, computes `relPkgDir := relParentDir / dir`, and loads the package from `wsDir / relPkgDir`.

For a root package, the parent coordinate is effectively the workspace root. For a transitive package, the same spelling therefore denotes a different physical path. If root `R` loads `A` at `deps/A` and `A` declares `require B from "../B"`, Lake resolves `B` through `A`'s coordinate system before recording a root-relative result.

The source contains a normalization specifically for non-root parents. Before materializing a new dependency declaration, `updateAndMaterializeDep` uses `pkg.relDir / "."` for a non-root package. Its comment explains the reason: a path entry inherited from another package's manifest already carries an explicit `./` form after rebasing, while the no-manifest route would otherwise store a superficially different path. The inserted `.` makes the two routes converge on the same effective workspace-relative form.

Evidence:
- [`DependencySrc.path`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L25-L34)
- [`Dependency.materialize`, path branch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L151-L167)
- [non-root path normalization in `updateAndMaterializeDep`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L186-L205)

### Dependency manifests are flattened into root-workspace coordinates

A package manifest's path entries are defined relative to the package directory that contains that manifest. `PackageEntry.inDirectory pkgDir` converts such an entry into the enclosing coordinate system by prefixing `pkgDir` to `.path dir`. It deliberately leaves non-path source variants unchanged.

During update, `addDependencyEntries` reads the just-loaded dependency's manifest. For each package entry not already present by package name, it performs two transformations before storing the entry in the update-state map:

1. `setInherited` marks it as inherited; and
2. `inDirectory pkg.relDir` rebases a path source through the loaded dependency's root-workspace-relative directory.

The root manifest itself is flat: it contains one `packages : Array PackageEntry`, not a tree of nested manifests. `Workspace.writeManifest` later emits entries in resolved workspace-package order from the single name-indexed update map.

The resulting invariant is operationally useful: every path entry in the root manifest is already expressible from the root workspace, even if its original `require` was nested several packages deep. Repeating the update recursively compounds the rebasing at each declaring package boundary until the path is root-relative.

Evidence:
- [`PackageEntrySrc.path` relative-path contract](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L64-L80)
- [`setInherited` and `inDirectory`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L152-L165)
- [`addDependencyEntries`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L173-L184)
- [`Workspace.writeManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L384-L400)

### Git entries are inherited without filesystem rebasing

`PackageEntry.inDirectory` only changes `.path dir`; every other source is returned unchanged. In this Lake revision, the other relevant source is Git.

That asymmetry follows the source models. A path entry denotes a relationship in a package's local filesystem coordinate system, so moving the declaration into the root manifest requires a coordinate conversion. A Git entry contains a repository URL, exact recorded revision, requested input revision, and optional subdirectory. Those fields do not become more correct by prefixing the parent package's path.

Consequently, `inherited` and "rebased" are not synonyms. All imported dependency-manifest entries are marked inherited. Only inherited path entries need their source location rewritten.

Evidence:
- [`PackageEntry.inDirectory`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L157-L165)
- [`PackageEntrySrc`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L64-L81)

### Locked loading consumes the root manifest as a complete flattened closure

Ordinary workspace loading uses an existing root `lake-manifest.json` unless update is requested. `Workspace.materializeDeps` folds `manifest.packages` into one `NameMap PackageEntry`, then recursively walks the package graph.

For every dependency edge—whether it originates at the root or inside another dependency—the resolver looks up `pkgEntries.find? dep.name`. If present, the stored `PackageEntry` is materialized. For a path entry, `PackageEntry.materialize` simply loads `wsDir / relPkgDir`; it does not receive the declaring package's directory and cannot reinterpret the path relative to that parent.

If an entry is missing, the error distinguishes the two cases. A missing root dependency tells the user to add it with `lake update <name>`. A missing dependency of a non-root package says the manifest is corrupt and instructs the user to regenerate a complete manifest.

This proves the important lockfile boundary: nested manifests are update inputs, not a hierarchy consulted during ordinary locked dependency resolution. A prepared root manifest must already contain the complete transitive closure in root-relative coordinates.

Evidence:
- [`Workspace.loadWorkspace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Workspace.lean#L47-L60)
- [`Workspace.materializeDeps`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L446-L490)
- [`PackageEntry.materialize`, path branch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L225-L265)

### `inherited` controls update ownership, not a second locked-load algorithm

An inherited entry is not materialized through a special parent-relative path during ordinary load. Its already-flattened source is consumed from the same root manifest map as a direct entry.

The distinction appears during update. `reuseManifest` can seed update state from the old root manifest, but on a selective update it skips entries marked `inherited`. Those entries are expected to be reconstructed from the packages that own the dependency declarations rather than treated as root-owned locks. The update walk then loads packages and invokes `addDependencyEntries` on their manifests, restoring inherited entries in current parent coordinates.

This prevents a transitive path entry's old root-relative path from becoming authoritative independently of the parent package that introduced it. If the parent moves, changes its own manifest, or is selected differently by graph precedence, the next update can rederive the child path from the parent's current state.

The boundary is still lockfile-driven between updates. Ordinary loading does not rederive inherited entries from nested manifests, so a stale but syntactically valid flattened entry can remain in effect until update.

Evidence:
- [`reuseManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L140-L171)
- [`addDependencyEntries`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L173-L184)
- [update traversal and manifest rewrite](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L310-L423)

### Traversal order gives root and later requirements precedence over inherited ones

Lake's resolver is breadth-first. For each package, it visits direct dependencies in reverse declaration order before descending into dependencies' dependencies. The source documents both reasons:

1. later `require` declarations should shadow earlier ones; and
2. requirements written by the user should take priority over those inherited from dependencies.

The mechanism is package-name deduplication. Before loading a dependency, `resolveDepsCore` checks whether a package with the same `baseName` is already in the workspace. During update, `addDependencyEntries` similarly inserts a dependency-manifest entry only if the name is not already present in the update-state map.

Thus a transitive path dependency is not an independently namespaced object just because it came from another package or a different relative path. Package names are the graph identity boundary. If root and transitive declarations both name `foo`, the traversal/precedence rules choose one `foo`; Lake does not maintain separate `root/foo` and `A/foo` nodes.

This is especially important for vendoring. A prepared flattened manifest must preserve the package names and the precedence-selected closure. Rewriting only paths while accidentally changing names or traversal-selected membership changes the workspace graph, not merely its storage layout.

Evidence:
- [`Workspace.resolveDepsCore`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L90-L129)
- [documented traversal order and precedence](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L310-L352)
- [`addDependencyEntries` name guard](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L173-L184)

### A package without a nested manifest can still produce a flattened transitive path lock

`Dependency.materialize` attempts to load the materialized package's default manifest and includes the result in `MaterializedDep`. `addDependencyEntries` uses that nested manifest when available, but a missing manifest is only a warning.

The resolver still loads the package configuration. When it later traverses that package's `depConfigs`, `updateAndMaterializeDep` resolves each dependency declaration directly. For a path dependency it passes the declaring package's `relDir` (with the `/.` normalization described above), and stores the resulting root-relative `PackageEntry` in update state.

Therefore the flattening model does not require every dependency package to ship a nested `lake-manifest.json`. A nested manifest is a reusable source of locked child entries; absent one, Lake can reconstruct the child closure from live package configuration during update. The root manifest produced at the end is still complete and flat.

Evidence:
- [materialization's optional nested-manifest load](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L209-L223)
- [missing-manifest handling in `addDependencyEntries`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L173-L184)
- [recursive update/load path](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L353-L382)

### Path staleness is not detected by comparing configured path strings

Before ordinary locked materialization, `validateManifest` compares the root package's current direct dependency declarations with the root manifest. Git entries get URL and requested-revision checks. A source-kind change gets a warning. But `.path .., .path ..` returns success without comparing path strings.

For a transitive path dependency, the boundary is even more indirect: ordinary locked loading does not validate a nested package's current path declaration against the flattened inherited entry before selecting that entry by package name. The root manifest remains the dependency-location authority until update.

This does not make the manifest incorrect; it defines the lock boundary. It does mean that editing a dependency package's transitive `require ... from <new path>` is not sufficient by itself to make a prepared locked workspace follow the new path. The root manifest needs regeneration or an equivalent deliberate transformation.

Evidence:
- [`validateManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L425-L445)
- [locked recursive lookup from the root package-entry map](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L450-L490)

### Anneal's generated manifest is a manual root-relative flattening step

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Anneal's archive-cache fixture creates a fresh generated workspace that requires `aeneas` from the prepared archive's `backends/lean` directory.

It does not ask Lake to update that generated workspace against the read-only dependency tree. Instead, `write_relative_archive_manifest` constructs a complete root manifest itself:

1. it canonicalizes the Aeneas Lean package and generated workspace;
2. it reads Aeneas's existing `lake-manifest.json`;
3. it adds Aeneas itself as a direct path entry with `inherited: false`;
4. for every Aeneas manifest package entry, it requires `type == "path"`;
5. it interprets that entry's directory in Aeneas-workspace coordinates;
6. it rewrites the directory relative to the generated workspace;
7. it sets `inherited: true`; and
8. it otherwise preserves the entry object and writes the complete generated manifest.

This transformation is the same coordinate change that Lake's update machinery performs conceptually, but it starts from an already-flattened Aeneas manifest. The generated workspace becomes a new root coordinate system, so each inherited path needs one more rebase from `aeneas_lean` into that workspace.

The explicit rejection of non-path inherited entries is a useful contract, not a Lake requirement. Lake itself can materialize Git entries. Anneal's archive fixture chooses the stronger condition that the prepared dependency closure is already local and path-addressable; if Aeneas later introduces a Git entry into its manifest, this code fails instead of silently adding a network-capable materialization path.

Evidence:
- [generated workspace and `require aeneas from ...`](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/src/main.rs#L143-L188)
- [`write_relative_archive_manifest`](https://github.com/google/zerocopy/blob/41f5b37afe7060fd9fe08c00b200672cd76d77b9/anneal/src/main.rs#L220-L287)

### The prepared-archive invariant is stronger than "all dependencies are paths"

For Anneal's generated manifest to be correct, several properties must hold together:

- the Aeneas manifest must already describe the complete precedence-selected transitive closure;
- every inherited package used by this transformation must be materialized inside the prepared archive and represented as a path entry;
- rebasing must preserve each package entry's name and configuration/manifest-file metadata while changing only the coordinate-dependent fields;
- the generated root must add Aeneas as the direct package, not accidentally mark it inherited;
- all rewritten paths must still land in the intended immutable archive trees; and
- the resulting root manifest must agree with the generated `require aeneas from ...` declaration.

The current code implements this shape. "Path dependency" alone, however, does not prove any of those archive-level properties. Lake does not content-pin a path source. The archive construction and its validation are what supply provenance, completeness, and read-only placement.

## Boundaries

This report does not repeat the full `lake-manifest.json` schema or general Git-versus-path semantics. It isolates the transitive path coordinate and flattening rules needed to reason about a prepared dependency closure.

It does not establish:

- byte-for-byte integrity of the trees reached by path entries;
- whether a moved prepared archive leaves every non-manifest artifact relocatable;
- whether generated build traces or configuration `.olean`s contain absolute paths;
- whether ordinary `lake --offline` or another command prevents all networking;
- correctness of arbitrary manually edited manifests;
- equivalence of build outputs before and after a Git-to-path vendoring transformation;
- behavior of future Lake path-copy/vendor features; or
- a stable external API for constructing manifests by hand.

The path normalization containing `/.` is an implementation detail that currently aligns two update routes. Consumers should rely on the semantic location, not on byte-for-byte preservation of that syntactic path form across Lake versions.

The resolver's name-based precedence also means a flattened manifest is not merely a multiset of all syntactically mentioned dependencies. It represents the single workspace graph selected by Lake's traversal and package-name uniqueness rules.

## Evidence

Primary Lake revision: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned Lake source blobs inspected:

- `src/lake/Lake/Config/Dependency.lean` — `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`
- `src/lake/Lake/Load/Manifest.lean` — `760eb81419762fb0ab11393e93082930645e2b6d`
- `src/lake/Lake/Load/Materialize.lean` — `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`
- `src/lake/Lake/Load/Resolve.lean` — `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`
- `src/lake/Lake/Load/Workspace.lean` — `9f25dd62bc752ede695a25fc20371157eb65d64b`

Anneal observation revision: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

Pinned Anneal source blob inspected:

- `anneal/src/main.rs` — `b947700606677ea89c7a205f3ffcc75493508f63`

Neighboring durable reports were used to keep scope boundaries clean. The Git-versus-path report owns the general source-model comparison; the package-identity-after-vendoring report owns Lake package identity across source substitution; the manifest and read-only reports own broader locking and prepared-environment behavior. The transitive-specific claims here are independently grounded in the pinned source above.

## Revalidation

After a Lake version change, source revalidation should start with four boundaries:

1. `Lake/Load/Manifest.lean`: whether path entries are still relative to the containing manifest's package, whether `inherited` still exists, and how `inDirectory` transforms source variants;
2. `Lake/Load/Materialize.lean`: how a live path dependency combines `relParentDir` with its configured path and how a locked path entry is materialized;
3. `Lake/Load/Resolve.lean`: traversal order, name deduplication, inherited-entry reuse, nested-manifest ingestion, root-manifest writing, validation, and locked recursive lookup; and
4. Anneal's generated-manifest construction: whether it still consumes an already-flattened Aeneas manifest, enforces path-only entries, rebases directories, and preserves metadata.

A compact exact-pin runtime fixture should then test the operational edges:

- create `R -> A -> B`, where both edges are path dependencies, and verify the root manifest records `B` relative to `R`, not relative to `A`;
- give `A` its own manifest, repeat without that manifest, and compare the resulting root path for `B` after normalizing filesystem semantics;
- move `A` while preserving its internal `B` relationship, run update, and verify the inherited root entry for `B` is rederived under the new parent coordinate;
- keep the old root manifest while changing `A`'s configured path to `B`, then verify ordinary locked loading continues to use the old flattened entry until update;
- delete `B` from the root manifest while leaving `A`'s nested manifest intact, then confirm ordinary locked load reports an incomplete/corrupt root manifest rather than reconstructing `B` from `A`;
- introduce a root `B` and an inherited `B` at different paths and confirm root/later-require precedence;
- relocate the complete `R/A/B` tree while preserving root-relative topology and confirm the flattened path closure still resolves; and
- run Anneal's archive-manifest transformation on a synthetic Aeneas manifest containing a nested path entry, then verify the rewritten path lands on the same package from the generated workspace.

For the Anneal path-only contract, add a negative fixture with one inherited Git entry and preserve the expected construction failure. If a future design deliberately permits Git there, replace that test with explicit network/materialization and immutability requirements rather than silently weakening the prepared-archive guarantee.