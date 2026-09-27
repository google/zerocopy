# Lake manifest schema and dependency locking at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `lake-manifest.json` is the root workspace's persisted dependency-materialization record. Its current schema version is `1.2.0`. A manifest stores workspace-relative Lake/package locations plus one entry per resolved dependency. A path entry records a relative directory. A Git entry records both the exact checked-out commit in `rev` and, separately, the requested revision in `inputRev` when one exists. This distinction is the core of Lake's lock behavior: ordinary manifest-based materialization uses the recorded `rev`, while `inputRev` lets Lake detect that the dependency declaration has changed and should be updated.

Ordinary dependency loading treats the manifest as authoritative rather than silently re-resolving changed requirements. Lake warns when a root Git dependency's configured URL or requested revision differs from the manifest, but it still materializes the manifest entry. A root dependency absent from the manifest is an error. For a materialized Git dependency, Lake avoids fetching when the existing checkout is already at the locked `rev`; otherwise it updates or clones to that `rev`.

`lake update` is the operation that constructs a new lock state. A selective update reuses non-inherited manifest entries whose package names were not selected, while resolving selected entries again. A bare update reuses none of the old locked entries and can rebuild even from an otherwise unreadable old manifest. Transitive entries inherited from dependency manifests are not frozen by the selective-reuse step; Lake reconstructs them from the dependency graph. After resolution, Lake rewrites the root manifest from the resulting workspace and lock-entry map.

The format is versioned, but compatibility is intentionally broader than exact equality. This revision reads manifest versions from `0.5.0` upward, has a compatibility decoder for pre-`0.7.0` package entries, and rejects versions with major version greater than `1`. It does not reject a future `1.x` minor merely because it is newer than the writer's `1.2.0`; the format comment defines post-`1.0` minor increments as backward-compatible extensions. Checked-in tests confirm that `0.4.0` is rejected, `0.5` through `1.2.0` are accepted, and running an update rewrites accepted older formats into the current form.

The manifest write path itself is not a filesystem transaction protocol. `Manifest.save` pretty-prints JSON and calls `IO.FS.writeFile` on the destination directly; the examined update path does not wrap that call in a temporary-file rename or a manifest-level inter-process lock. Therefore the source establishes lock-*file semantics* for dependencies, but not atomic replacement or cross-process serialization of concurrent manifest writers. Those stronger filesystem/concurrency properties require separate evidence.

Basis: source + checked-in test source + derived conclusions.

## Applicability

This report applies to the Lake implementation shipped in Lean `v4.30.0-rc2`, repository `leanprover/lean4`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

The report uses **locked revision** for a Git manifest entry's exact `rev` field and **input revision** for its `inputRev` field. The first is the concrete commit Lake obtained after materialization; the second preserves the revision expression supplied by configuration or registry resolution, such as a branch, tag, or commit-like input. For path dependencies, the manifest stores a relative directory instead of a revision.

This report is narrower than a full dependency-resolver report. It documents the serialized schema, what the persisted fields mean, how ordinary loading consumes them, how update reuses or replaces them, version compatibility, and the write boundary. It does not reconstruct Reservoir's full version-selection algorithm, registry precedence, or all Git/path source-selection rules.

No fresh Lake process was executed for this report. Checked-in tests are evidence about what upstream intended and continuously tests, but they are still inspected source rather than execution performed by this investigation.

## Findings

### The current manifest schema is `1.2.0`

`Lake.Manifest.version` is `{major := 1, minor := 2}`. The serializer emits these top-level fields:

- `version`: the current manifest format version;
- `fixedToolchain`: whether the root package's selected toolchain is fixed;
- `name`: the root package name;
- `lakeDir`: the root package's Lake directory, normally relative to the workspace;
- `packagesDir`: the dependency-package directory, represented as an optional path in the in-memory structure;
- `packages`: the ordered array of dependency entries.

A package entry contains common fields `name`, `scope`, `inherited`, `configFile`, and `manifestFile`, plus one of two source variants. A path entry has `type: "path"` and `dir`. A Git entry has `type: "git"`, `url`, `rev`, `inputRev`, and `subDir`.

The source explicitly describes a path entry's `dir` as relative to the directory of the package containing the manifest. During update, inherited path entries are rebased with `PackageEntry.inDirectory`; the resolver includes an explicit normalization step so an inherited path retains the same serialized form whether it came from a dependency manifest or was reconstructed because that dependency lacked one.

Basis: source. `src/lake/Lake/Load/Manifest.lean`, `Manifest.version`, `PackageEntrySrc`, `PackageEntry`, `Manifest`, and the `ToJson` instances; `src/lake/Lake/Load/Resolve.lean`, `updateAndMaterializeDep`.

### A Git entry separates the requested revision from the resolved commit

When Lake freshly materializes a Git dependency, it passes the requested revision to Git, then reads the repository's actual HEAD with `repo.getHeadRevision`. The resulting manifest entry stores:

- `rev`: that exact HEAD revision;
- `inputRev`: the revision expression that drove materialization, if any.

This split lets a branch or tag-like input produce a concrete lock. It also lets Lake compare future configuration against the request that produced the lock without discarding the exact commit needed to reproduce the old state.

When Lake later materializes a manifest entry, it uses `rev`, not `inputRev`, as the checkout target. If the local repository already exists and its HEAD equals `rev`, Lake deliberately skips the remote update/fetch; it only warns if the checkout has local changes. If the repository is missing or at a different revision, Lake clones or updates it to the recorded `rev`.

Derived consequence: a present checkout at the locked commit can be consumed without contacting the Git remote through this path. This is a narrow property of `PackageEntry.materialize`, not a complete offline guarantee for Lake as a whole.

Basis: source. `src/lake/Lake/Load/Materialize.lean`, `Dependency.materialize` and `PackageEntry.materialize`.

### Ordinary manifest loading preserves the lock even when configuration drifts

`Workspace.materializeDeps` converts the manifest's package array into a name-indexed map and validates the root package's declared dependencies against it. For Git dependencies it warns if either the configured URL or configured requested revision differs from the manifest's URL/`inputRev`; it warns if the source kind changes between Git and path. A path-to-path declaration does not trigger a path-value comparison in `validateManifest`.

After those warnings, dependency materialization still looks up the package by name in the manifest map and materializes that entry. Lake does not silently replace it with the changed declaration. If a root dependency is not present in the manifest, loading fails with an instruction to run `lake update <name>`. If a transitive dependency is missing, Lake treats the manifest as corrupt and directs the user to regenerate it with `lake update`.

This means a warning is not an automatic re-resolution signal. For Git dependencies, configuration drift is surfaced while the previous locked `rev` remains the materialization source until an update is performed. For path dependencies, the source-level validator at this revision is even weaker: once the dependency remains of path kind, it does not compare the newly configured directory to the stored `dir` before materializing the manifest entry.

Basis: source. `src/lake/Lake/Load/Resolve.lean`, `validateManifest` and `Workspace.materializeDeps`.

### Selective update preserves some root locks and reconstructs the rest

The update path carries a `NameMap PackageEntry` explicitly described as a map of locked dependencies. `reuseManifest` seeds this map from the old root manifest only for a selective update: when `toUpdate` is non-empty, Lake reuses entries that are neither inherited nor named in `toUpdate`.

The consequences are important:

- `lake update foo` can keep other root dependency locks while resolving `foo` again;
- inherited entries are not directly preserved by this selective-reuse step, because they must follow the dependency graph that results from the retained/updated direct dependencies;
- a bare update, represented by an empty `toUpdate`, reuses none of the old entries and resolves the lock state afresh.

While traversing dependencies, Lake first consults the lock-entry map by package name. A hit materializes the existing entry. A miss materializes from the current dependency declaration and stores the resulting entry. Dependency manifests can contribute inherited entries; first insertion wins according to the resolver's traversal/shadowing rules.

After dependency resolution, `Workspace.writeManifest` walks the resolved workspace packages, looks up their entries, fills in each package's actual relative config/manifest paths, constructs a new root `Manifest`, and saves it to `ws.manifestFile`.

Basis: source. `src/lake/Lake/Load/Resolve.lean`, `UpdateT`, `reuseManifest`, `addDependencyEntries`, `updateAndMaterializeDep`, `Workspace.updateAndMaterializeCore`, and `Workspace.writeManifest`.

### A bare update is the recovery path for an unreadable old manifest

`reuseManifest` treats old-manifest errors differently depending on the update mode. During a selective update, a load error is rethrown because Lake would need the old lock entries to preserve unselected packages. During a bare update, Lake warns that it is ignoring the old manifest and constructs new state from scratch.

The checked-in manifest test exercises this distinction for the unsupported `0.4.0` format: `resolve-deps` fails, `update bar` fails, but a bare `update` succeeds and produces the expected current manifest.

Basis: source + checked-in test source. `src/lake/Lake/Load/Resolve.lean`, `reuseManifest`; `tests/lake/tests/manifest/test.sh`.

### Version compatibility is asymmetric by design

`Manifest.getVersion` accepts either the historical numeric encoding or a semantic-version string. It rejects versions below `0.5.0` and versions whose major component is greater than `1`. For versions before `0.7.0`, it decodes the old `PackageEntryV6` representation and converts it to the current entry type. The version comment states that, after `1.0.0`, minor increments are backward-compatible extensions and that prerelease suffixes do not affect feature compatibility.

The implementation does not compare a `1.x` minor against the writer's current `1.2.0`; therefore a future same-major manifest is accepted by this gate. Unknown JSON fields are not serialized back unless represented in the current structures, so successful reading of a future compatible extension does not imply round-trip preservation of every field an even newer writer might add.

The checked-in test suite copies manifests from `0.5`, `0.6`, `0.7`, `1.0.0`, `1.1.0`, and `1.2.0`, loads them, runs update, and compares the result with the current expected form. It separately checks that `0.4.0` is incompatible.

Basis: source + checked-in test source + derived conclusion about future-minor acceptance/round-trip limits. `src/lake/Lake/Load/Manifest.lean`, `Manifest.getVersion`, `getPackages`, `Manifest.fromJson?`; `tests/lake/tests/manifest/test.sh` and `lake-manifest-latest.json`.

### The manifest is a lock record, not a transactional lock protocol

`Manifest.save` calls `Json.pretty` and then `IO.FS.writeFile manifestFile`. In the examined update path, `Workspace.updateAndMaterialize` completes dependency resolution, calls `writeManifest`, and only then runs package `post_update` hooks.

Two useful boundaries follow from that ordering:

1. resolution failure before `writeManifest` prevents this path from writing the new manifest, although dependency repositories or other materialized state may already have changed;
2. a failure in a post-update hook occurs after the new manifest has been written.

The save path contains no temporary-file/rename step and no manifest-level inter-process lock around the write. Source inspection therefore does not justify claims that replacing `lake-manifest.json` is crash-atomic or that concurrent writers are serialized. A later report or execution probe should treat those as separate questions rather than inferring them from the word "lock".

Basis: source + derived boundary. `src/lake/Lake/Load/Manifest.lean`, `Manifest.save`; `src/lake/Lake/Load/Resolve.lean`, `Workspace.updateAndMaterialize` and `Workspace.writeManifest`.

## Boundaries

- **Not a full resolver model.** This report does not reconstruct Reservoir lookup/version solving, package-shadowing beyond what is necessary to explain persisted entries, or every Git/path source-selection rule. Those belong in the separate dependency-resolution subject.
- **No fresh execution.** The test behavior described here comes from checked-in test scripts and fixtures at the pinned revision, not a test run performed for this report.
- **No whole-Lake offline claim.** Skipping a fetch when a Git checkout already matches the locked `rev` does not prove that no other Lake path can access the network.
- **No filesystem concurrency guarantee.** The examined save/update path provides no manifest-level locking or atomic-replace mechanism. This report does not claim how two concurrently running Lake processes race in practice.
- **No adjacent-version generalization.** The schema and update rules are pinned to `v4.30.0-rc2`. Later Lake changes must be rechecked, especially because manifest semantics are explicit versioned state.
- **No guarantee that future `1.x` extensions round-trip.** This reader accepts same-major future minor versions at the version gate, but the current in-memory types and serializer only preserve fields they know about.
- **Root validation is not full semantic equality.** At this revision, `validateManifest` checks Git URL/requested revision and source-kind changes, but does not compare two path-source directory values.

## Evidence

All source evidence is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- **Source:** `src/lake/Lake/Load/Manifest.lean` (`760eb81419762fb0ab11393e93082930645e2b6d`), especially lines 29–55 (`Manifest.version` and compatibility policy), 64–180 (`PackageEntrySrc`, `PackageEntry`, and `Manifest`), 188–230 (serialization/version decoding), and 257–260 (`Manifest.save`).
- **Source:** `src/lake/Lake/Load/Materialize.lean` (`e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`), especially `Dependency.materialize` and `PackageEntry.materialize`: a fresh Git materialization records `repo.getHeadRevision` as `rev`, while replay uses the stored `rev` and avoids a fetch if the checkout already matches.
- **Source:** `src/lake/Lake/Load/Resolve.lean` (`ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`), especially lines 131–205 (`UpdateT`, `reuseManifest`, inherited entries, selective reuse), 346–400 (`updateAndMaterializeCore`, `writeManifest`), and 430 onward (`validateManifest`, `materializeDeps`).
- **Source / checked-in tests:** `tests/lake/tests/manifest/test.sh` (`817b708067aed85a9b204725d5f362bd0d6521ba`) and `tests/lake/tests/manifest/lake-manifest-latest.json` (`0f0bf56074594e083f45978b5904b5295d22d21d`). The test script distinguishes unsupported `0.4.0`, supported historical versions, selective-update failure on an unreadable manifest, and bare-update recovery.
- **Documentation source:** `src/lake/README.md` at the same repository revision states the user-facing rule: after a dependency is first resolved, the specific revision is saved in `lake-manifest.json`, future builds use it, and `lake update` is required to update the dependency.

No execution evidence was gathered.

## Revalidation

For another Lean/Lake revision, the cheapest useful source revalidation is:

1. inspect `Lake/Load/Manifest.lean` for `Manifest.version`, the `Manifest`/`PackageEntry` structures, `getVersion`, `getPackages`, and `Manifest.save`;
2. inspect `Lake/Load/Materialize.lean` for where fresh Git materialization obtains `rev` and how `PackageEntry.materialize` replays it;
3. inspect `Lake/Load/Resolve.lean` for `reuseManifest`, `updateAndMaterializeDep`, `Workspace.writeManifest`, `validateManifest`, and `Workspace.materializeDeps`;
4. diff `tests/lake/tests/manifest/` and run that test on a capable surface.

A compact execution probe should add one direct Git dependency and one path dependency, generate a manifest, then verify separately that: (a) the Git entry records exact `rev` plus requested `inputRev`; (b) changing the requested Git revision produces a warning but ordinary manifest loading still uses the prior locked commit; (c) `lake update <dep>` changes only the selected direct lock when possible; (d) bare `lake update` recovers from an incompatible manifest; and (e) changing a path declaration without updating demonstrates the pinned validator/materialization behavior. A separate two-process/crash probe is required for any claim about atomic manifest replacement or concurrent writers.