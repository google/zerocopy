# Git dependencies versus path dependencies in Lake v4.30.0-rc2

## Summary

Lake v4.30.0-rc2 gives Git and path dependencies deliberately different source and identity semantics.

A **path dependency** is a package already present at a filesystem path relative to the package that requires it. Lake does not copy it into the workspace package store or attach a revision identity to it. The manifest records the path, rebased into the root workspace when necessary. Ordinary manifest loading then uses that recorded path in place. Source changes at that path are therefore source changes to the dependency itself.

A **Git dependency** is repository materialization state managed by Lake. Lake clones it under the workspace packages directory, resolves the configured revision expression to an actual checkout, records the exact Git commit as `rev`, separately records the requested expression as `inputRev`, and can later fetch, checkout, clean, delete, or reclone that package directory. An already-materialized locked checkout at the recorded commit can be consumed without fetching; a missing or wrong-revision checkout can require Git mutation or network access.

Both source kinds are still the *same kind of Lake package once loaded*. The package graph is keyed by package name, not by `(source kind, source location)`. A Git package and a path package with the same package name do not coexist as distinct graph nodes merely because their source identities differ.

The manifest boundary also differs in a subtle way. For a root Git dependency, Lake warns if the current configured URL or requested revision differs from the locked manifest entry, but continues to use the locked entry until update. For a path dependency, the pinned `validateManifest` code treats any path→path combination as acceptable without comparing the configured and recorded paths. Changing a path dependency's `from` path can therefore leave ordinary manifest-based loading silently pointed at the old manifest path until `lake update` rewrites the lock state.

For Anneal, the practical distinction is: **use Git when the dependency identity is an exact repository revision that Lake may materialize; use path when the dependency identity is a relative filesystem relationship whose source tree is already supplied by the enclosing prepared environment.** Neither source kind by itself establishes whole-build reproducibility, read-only safety, or artifact equivalence.

Basis: pinned implementation source + same-revision Lake documentation + derived synthesis.

## Applicability

These findings apply to Lake as shipped in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The report compares explicit Lake `DependencySrc.path` and `DependencySrc.git` dependencies, plus the manifest entries that persist those resolutions. Registry/Reservoir dependencies are discussed only where the pinned implementation ultimately materializes them through Git. Full Reservoir version selection is a separate dependency-resolution subject.

The report does not claim that every file reached through a path dependency is relocatable, immutable, or build-equivalent after copying. It also does not claim that an exact Git commit makes a Lean package reproducible across toolchains, environments, configuration options, submodules, external tools, or generated state. Those are distinct state and build questions.

No fresh Lake process was executed. The materialization, locking, traversal, and validation conclusions below come from the exact pinned implementation. Runtime probes are specified under Revalidation where execution would add materially stronger evidence.

## Findings

### The configuration model makes source kind explicit

Lake's dependency configuration has one `DependencySrc` sum type with two explicit cases at this revision:

- `path dir`: a package located at a fixed path relative to the dependent package's directory; and
- `git url rev subDir`: a package cloned from a fixed Git URL, optionally at a requested revision and optionally using a package in a repository subdirectory.

The `require` macro lowers the two source syntaxes directly into those cases. Same-revision documentation describes path dependencies as loading a package at a fixed path relative to the requiring package and Git dependencies as cloning the repository, checking out a commit/branch/tag, and then loading either the repository root or `subDir`.

A dependency without an explicit source is a third configuration path: Lake resolves it through the configured registry/Reservoir. At this pin, successful Reservoir materialization still requires the registry record to supply a Git source, after which the materialization path becomes the same Git mechanism. Thus "Git versus path" is also the important physical-materialization split underneath registry resolution.

Evidence:
- [`DependencySrc` and `Dependency`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L25-L69)
- [`require` source expansion](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/DSL/Require.lean#L20-L52)
- [Lake dependency syntax documentation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/README.md#L468-L512)
- [`Dependency.materialize`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L151-L223)

### Path dependencies are borrowed in place

For a configured path dependency, `Dependency.materialize` computes

`relPkgDir := relParentDir / dir`

and loads the dependency from `wsDir / relPkgDir`. It does not create a copy in the workspace packages directory, invoke Git, resolve a revision, or synthesize another source tree. The resulting manifest entry is simply `.path relPkgDir`.

Locked materialization is equally direct. `PackageEntry.materialize` handles a path entry by loading `wsDir / relPkgDir`. There is no existence-to-copy fallback and no revision check.

This makes the dependency's filesystem tree itself the source identity that Lake consumes. Editing that tree changes the dependency source without any dependency-source update step. Any reproducibility or immutability property must come from how the enclosing environment supplies and protects that tree, not from Lake pinning a path dependency to content.

Evidence:
- [`Dependency.materialize`, path branch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L155-L167)
- [`PackageEntry.materialize`, path branch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L225-L265)

### Git dependencies are managed checkouts with two revision identities

A configured Git dependency is materialized under the workspace packages directory using the dependency package name. Lake creates or updates a Git repository there, resolves the requested revision, reads the repository's actual `HEAD`, and stores both values in the manifest:

- `rev`: the exact checked-out Git commit; and
- `inputRev`: the requested revision expression, such as a branch, tag, or commit-like input.

These fields answer different questions. `inputRev` records what the configuration asked Lake to follow; `rev` records the concrete checkout that ordinary locked loading can reproduce.

When updating an existing Git materialization, Lake compares the configured remote URL with the repository remote. If the URL changed, non-Windows builds delete and reclone the repository; on Windows Lake logs that manual deletion may be necessary and proceeds through the update path. When moving to another revision, Lake performs a detached checkout and cleans untracked files from tracked directories. The source calls out stale `.hash` files as one reason for that cleanup.

Evidence:
- [`cloneGitPkg`, `updateGitPkg`, and `updateGitRepo`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L25-L87)
- [configured Git materialization and manifest-entry creation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L210-L223)
- [`PackageEntrySrc.git`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L68-L82)

### Locked Git and locked path entries have different recovery behavior

Ordinary workspace loading uses `lake-manifest.json` when present. It constructs a package-entry map from the manifest and materializes each dependency from the corresponding entry.

For a path entry, locked materialization only resolves the recorded relative path.

For a Git entry, locked materialization reconstructs the expected package repository directory under the workspace packages directory and then:

1. if the directory is absent, clones the repository at the recorded exact `rev`;
2. if the repository exists at another revision, updates it to the recorded `rev`; or
3. if it is already at the recorded `rev`, avoids a fetch and only warns if the checkout has local changes.

The code comment explicitly cites offline operation as the reason for the exact-revision fast path. A complete manifest can therefore make a *prepared* Git dependency network-independent when the exact checkout already exists, but the same manifest still authorizes clone/fetch when that local materialization is absent or wrong. A path dependency has no corresponding network/materialization fallback; the referenced filesystem package simply has to exist.

Evidence:
- [`Workspace.loadWorkspace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Workspace.lean#L46-L64)
- [`Workspace.materializeDeps`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L446-L490)
- [locked Git materialization fast path](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L228-L265)

### The manifest validates Git source changes more strongly than path changes

`validateManifest` compares the root package's current direct dependency declarations against locked manifest entries before ordinary materialization.

For Git→Git, it compares both the configured URL and configured requested revision with the manifest's URL and `inputRev`; mismatches produce an "out of date" warning directing the user to `lake update`.

For path→path, the pinned function returns `pure ()`. It does **not** compare the configured path with the manifest's recorded path.

For a source-kind transition, such as Git→path or path→Git, it warns that the source kind changed.

Because `materializeDeps` subsequently materializes the *manifest entry*, not the source location from the live dependency declaration, a changed configured path can remain silently ineffective until the manifest is updated. The current dependency declaration still contributes package configuration options passed to `loadDepPackage`; the locked source location comes from the manifest.

This asymmetry is important for generated workspaces. Rewriting a path dependency in `lakefile.lean` without regenerating or updating the matching manifest does not establish that Lake will follow the new path.

Evidence:
- [`validateManifest`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L425-L444)
- [manifest-entry materialization using current dependency options](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L450-L490)

### Local modifications are source-kind-specific too

Path dependencies have no repository cleanliness concept in Lake's dependency materializer. The files at the path are the dependency.

A locked Git dependency at the correct commit is different but not fully immutable: if the repository has local changes, Lake warns and continues. It does not reset the checkout merely because the manifest names an exact commit. Consequently, `rev == HEAD` is not equivalent to "working tree bytes exactly equal the commit."

When an update actually changes Git revision, `updateGitPkg` checks out the new revision and runs Git cleanup for untracked files in tracked directories. The stronger cleanup belongs to the mutation/update path, not ordinary consumption of an already-at-rev checkout.

For an immutable prepared dependency universe, Anneal therefore needs a filesystem/read-only or content-validation contract in addition to the manifest's Git revision if it wants to exclude local working-tree differences.

Evidence:
- [locked Git local-diff warning](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L240-L255)
- [revision-change cleanup](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Materialize.lean#L25-L40)

### Transitive path identities are rebased; Git identities remain repository identities

Lake flattens dependency-manifest entries into the root workspace manifest. `addDependencyEntries` marks inherited entries and calls `inDirectory pkg.relDir`. `PackageEntry.inDirectory` prefixes only path entries with the containing package directory; Git entries are returned unchanged.

That difference follows the source models:

- a transitive path dependency means "this package at this relative filesystem relationship to its declaring package," so Lake must rebase the path when expressing it from the root workspace;
- a transitive Git dependency already carries its repository identity independently of the parent package's location, so no path rebasing is needed.

The update resolver contains an additional normalization for path dependencies when the declaring package lacks a manifest. It inserts `.` in the relative package directory so the stored path has the same effective form as the inherited-manifest route.

This is why vendoring a dependency tree by changing Git sources into paths is not merely a URL rewrite. It changes the identity model from repository revision to enclosing filesystem topology, and the complete root manifest must reflect the new path relationships.

Evidence:
- [`PackageEntry.inDirectory`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Manifest.lean#L157-L166)
- [inherited manifest-entry rebasing](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L173-L204)

### Source kind does not become package graph identity

`Dependency.name` is required to match the package's declared configuration name, and the source documents that the name must be unique across packages in the dependency graph. Resolution checks the workspace for an already-loaded package with the same base name and skips another dependency with that name.

Traversal order determines which declaration wins. Lake resolves direct dependencies in reverse declaration order before descending transitively; its source says this makes later `require`s shadow earlier ones and makes user/root requirements take priority over inherited requirements.

Therefore two dependencies named `foo`, one from Git and one from a path, do not form two independent packages in one workspace graph merely because their sources differ. Source selection and package graph identity are separate layers.

Evidence:
- [`Dependency.name` uniqueness contract](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Dependency.lean#L41-L69)
- [package-name deduplication during traversal](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L100-L129)
- [documented resolver precedence](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Resolve.lean#L330-L351)

### The two source kinds imply different Anneal preparation contracts

For a prepared Anneal environment, the direct comparison is:

| Property | Path dependency | Git dependency |
| --- | --- | --- |
| Source location | Existing tree relative to requiring package | Lake-managed repository under packages directory |
| Persistent source identity | Relative path | URL + exact `rev` + requested `inputRev` + optional `subDir` |
| Content pin supplied by source kind | None | Exact commit for checkout, but not working-tree cleanliness |
| Normal materialization write | None to create the source tree | Can clone/fetch/checkout/clean/reclone |
| Network requirement | None from path resolution itself | None only when prepared checkout already satisfies locked state; otherwise possible |
| Relocation primitive | Preserve relative topology | Preserve workspace package location/manifest plus a usable checkout, or rematerialize |
| Transitive flattening | Path is rebased under parent package | Repository identity is not path-rebased |
| Config-vs-manifest stale-source warning | No path comparison for path→path | URL and requested-revision comparison |
| Repository subdirectory | Express by pointing path at desired package directory | Native `subDir` field |

This table is about dependency-source semantics. Build outputs remain governed by Lake's separate configuration, trace, hash, setup, and artifact state.

## Boundaries

This report does not duplicate the full `lake-manifest.json` schema report. It uses only the manifest fields required to distinguish Git and path semantics.

It also does not establish:

- Reservoir's complete version-selection and registry-precedence algorithm;
- whether arbitrary path dependency files are unchanged, read-only, or content-addressed;
- whether an exact Git checkout including submodules or external generated files is reproducible;
- whether changing a path or Git source causes the same target rebuilds after the dependency has been loaded;
- whole-environment relocation;
- artifact-cache equivalence;
- concurrency safety for shared source/build trees; or
- absence of network access during all Lake operations.

The pinned source has no path-dependency `copy` flag in `DependencySrc`; later Lake revisions add behavior in this area. Do not project current Lake path-copy semantics backward onto v4.30.0-rc2.

The Git checkout's exact `rev` is not a cryptographic commitment to every file Lake may observe. A dirty worktree can be accepted with a warning, package configuration can depend on environment/options, and build products have separate identities.

## Evidence

The primary source revision is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned source blobs inspected:

- `src/lake/Lake/Config/Dependency.lean` — `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`
- `src/lake/Lake/DSL/Require.lean` — `53a2193ce8636f1974330a9b344dce6b00d6981e`
- `src/lake/Lake/Load/Manifest.lean` — `760eb81419762fb0ab11393e93082930645e2b6d`
- `src/lake/Lake/Load/Materialize.lean` — `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`
- `src/lake/Lake/Load/Resolve.lean` — `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`
- `src/lake/Lake/Load/Workspace.lean` — `9f25dd62bc752ede695a25fc20371157eb65d64b`

Same-revision documentation was inspected at `src/lake/README.md`; the pinned documentation's path/Git dependency descriptions agree with the implementation boundary above.

Neighboring durable reference work was used only to avoid duplicating broader conclusions: the manifest-schema report owns full manifest locking/version semantics, while the read-only/relocation report owns the stronger prepared-environment execution contract. The claims in this report are independently grounded in the pinned Lake source listed above.

## Revalidation

After a Lake version change, the cheapest source revalidation is to compare these exact boundaries:

1. `Lake/Config/Dependency.lean`: source variants and any new path-copy/vendor option;
2. `Lake/Load/Materialize.lean`: path resolution, Git clone/update/clean behavior, and manifest-entry materialization;
3. `Lake/Load/Manifest.lean`: path/Git entry fields and `inDirectory` rebasing;
4. `Lake/Load/Resolve.lean`: resolver precedence, inherited-entry flattening, `validateManifest`, and locked materialization; and
5. `Lake/Load/Workspace.lean`: whether ordinary loading still prefers the existing manifest.

A compact exact-pin runtime fixture should then exercise the semantics that source inspection cannot make concrete by itself:

- create one path dependency and one Git dependency with equivalent tiny package contents;
- run `lake update`, preserve the manifest, and record physical package locations;
- change only the path dependency declaration while keeping the old manifest, then confirm which directory is loaded and whether any warning is emitted;
- change only the Git URL and requested revision while keeping the old manifest, then record warnings and the checkout actually used;
- dirty an already-at-`rev` Git checkout and confirm ordinary loading warns but does not reset it;
- delete the locked Git checkout under hard network denial and confirm the attempted rematerialization fails;
- relocate the complete tree while preserving relative path topology and confirm path lookup follows the manifest's rebased path;
- add a transitive path dependency and inspect the root manifest's rebased inherited entry; and
- introduce same-name Git/path dependencies at different graph levels and confirm the documented precedence rule.

Preserve the fixture, generated manifest, command output, and filesystem/network traces. Those observations would strengthen the operational claims while keeping the durable source model pinned and reviewable.