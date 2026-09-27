# Lake source materialization and prebuilt dependency trees at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a prebuilt Lake dependency tree does **not** by itself suppress dependency source materialization. Lake loads and materializes the workspace before ordinary build execution. What Lake does next is controlled primarily by the manifest entry for each dependency.

For a locked **Git** manifest entry, Lake expects the dependency directory to be a Git repository. If the directory exists and its `HEAD` is already the manifest's exact locked revision, Lake does not fetch the remote; it only warns if the worktree has changes. If the directory is absent, Lake clones it. If it exists but is not at the locked revision, Lake enters the update path, which fetches the remote before resolving/checking out the requested revision. A copied source directory without usable `.git` metadata therefore is not an adequate pre-materialized Git dependency: on non-Windows systems Lake will normally treat the repository as mismatched, remove it, and clone it again.

For a locked **path** manifest entry, Lake directly resolves the declared filesystem path. That path materialization performs no Git clone or fetch and makes no source copy. This is the key mechanism used by current Anneal. Anneal first obtains ordinary Lake packages while constructing its archive, then removes their `.git` directories and rewrites dependency declarations and manifests from Git/registry sources to vendored relative path dependencies. Generated verification workspaces likewise write a root manifest containing only relative path entries and reject an archived Aeneas manifest containing a non-path dependency. The absence of Git metadata is therefore deliberate and sound relative to Anneal's rewritten path-dependency universe.

The practical rule is: **prebuilt artifacts and pre-existing source directories are not the source-materialization contract; the manifest/source kind is.** A Git-locked dependency needs an acceptable Git checkout at the locked revision to avoid fetch/clone. A vendored path dependency needs the declared directory to exist and load as a Lake package. Current Anneal avoids source-network activity by changing the dependency model to the latter before packaging, not merely by shipping a populated `.lake/packages` directory.

No fresh Lake process or network experiment was run for this report. The Lake control-flow conclusions come from exact pinned source and its checked-in clone test; the Anneal conclusions come from current `main` source at the revision above.

## Applicability

This report covers two currently separate #3720 inventory questions because they share one control-flow boundary:

- **Lake source-materialization behavior.** What source state Lake expects for path and Git dependencies and what operations materialization performs.
- **When Lake clones/fetches despite a prebuilt dependency tree.** Which pre-existing trees avoid network operations and which still enter Git materialization.

It applies to:

- Lake in Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`;
- Anneal V2 at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

This report does not redefine Lake dependency **selection**. Version/range selection, manifest precedence, and package-name conflict rules belong to the dependency-resolution report. It also does not claim that eliminating source clone/fetch eliminates all possible network access: package release archives, artifact caches, arbitrary Lake scripts, or user package configuration can have separate network behavior.

## Findings

### Ordinary build loads and materializes dependencies before running build jobs

The `lake build` CLI constructs a load configuration and calls `loadWorkspace` before parsing and running target build jobs. `loadWorkspace` first loads the root package and then either:

- calls `updateAndMaterialize` when dependency updating is requested;
- loads an existing manifest and calls `materializeDeps`; or
- if no manifest exists, falls back to `updateAndMaterialize`.

Thus a complete `.lake/build` tree does not bypass source dependency loading. If the manifest/source tree is not consumable, Lake can fail or perform materialization before it reaches the build graph whose outputs were prebuilt.

This also explains why omitting `lake-manifest.json` is materially different from shipping a locked manifest. With dependencies configured but no manifest, ordinary workspace loading enters update/materialization and can resolve or clone remote dependencies.

Basis: **source** in `Lake/CLI/Main.lean` and `Lake/Load/Workspace.lean`.

### A path manifest entry is a filesystem reference, not a package copy

`PackageEntry.materialize` handles a manifest `.path` entry by computing `wsDir / relPkgDir`, loading any declared nested manifest from that package location, and returning the materialized dependency description. It does not call Git and does not copy the package into `packagesDir`.

Configuration-level path dependencies behave the same way conceptually: their path is rooted relative to the requiring package and becomes a path manifest entry. The same-revision CLI documentation says that `lake update` makes no copy of local dependencies.

Consequences:

1. A vendored package tree can live anywhere addressable by the manifest's relative path; it need not be under `.lake/packages` for path semantics.
2. `.git` metadata is irrelevant to path materialization.
3. Prebuilt build products can be colocated with those sources, but they are not what causes Lake to regard the dependency as materialized; the path entry does.
4. If the declared path is missing or does not contain a loadable package configuration, the later package-load step fails rather than silently consulting Git.

Basis: **source** in `Lake/Load/Materialize.lean`, `Lake/Load/Resolve.lean`, and `Lake/Load/Manifest.lean`; **documentation** in `Lake/CLI/Help.lean`.

### A locked Git dependency avoids fetch only when the existing checkout is already at the locked revision

For a manifest Git entry, Lake chooses a directory under the manifest's packages directory using the package name. It then applies this exact branch:

- if the directory exists **and** `getHeadRevision?` equals the manifest's exact `rev`, Lake does not call the remote; it only checks for local diffs and may warn;
- if the directory exists but `HEAD` differs, Lake calls `updateGitRepo`;
- if the directory does not exist, Lake calls `cloneGitPkg`.

The checked-in `tests/lake/tests/clone/test.sh` exercises the first case. It deliberately changes the dependency's remote URL to `https://example.com/hello.git`, then runs `lake build`; the build succeeds because Lake does not fetch when the local checkout is already at the locked revision.

This is a strong, narrow offline property: **locked revision already at `HEAD` suppresses the Git fetch path during source materialization**. It does not prove the rest of a build is network-free.

Basis: **source** in `Lake/Load/Materialize.lean`; **checked-in test** in `tests/lake/tests/clone/test.sh`.

### A wrong Git `HEAD` enters a fetch even when the requested revision may already exist locally

When an existing repository is from the same URL but not already at the manifest revision, `updateGitRepo` calls `updateGitPkg`. That function asks `findRemoteRevision` for the desired revision. At this pin, `findRemoteRevision` unconditionally performs:

`git fetch --tags --force <remote>`

before resolving the requested revision and checking it out.

That ordering matters for offline/prebuilt consumers. Merely retaining the desired commit object somewhere in the repository is not enough to guarantee no fetch if `HEAD` is different. The fast path is specifically equality between the current `HEAD` and the locked revision before the update helper is entered.

A source archive intended for offline consumption as a Git dependency should therefore preserve the repository with `HEAD` already at the exact manifest revision. If it cannot preserve that invariant, using path dependencies is the cleaner contract.

Basis: **source** in `Lake/Load/Materialize.lean` and `Lake/Util/Git.lean`.

### A copied Git dependency with no `.git` metadata is not an already-materialized Git dependency

For a manifest Git entry, Lake tests whether the dependency **directory** exists before asking Git for its `HEAD`. A plain copied source directory therefore takes the “repository exists” branch, but `getHeadRevision?` cannot establish the locked revision without Git metadata. Lake then enters `updateGitRepo`.

On non-Windows systems, a repository whose remote cannot be shown to match is removed and freshly cloned from the configured URL. On Windows, the implementation avoids recursive deletion because of filesystem reliability concerns and instead warns that manual deletion may be needed before proceeding through the update path.

Therefore this packaging shape is unsafe for an offline Git-locked consumer:

- manifest says `type = git`;
- `.lake/packages/foo` contains source files;
- `.lake/packages/foo/.git` was removed.

The directory's presence does not satisfy Lake's Git materialization invariant. This conclusion follows directly from the pinned control flow; no destructive fixture was executed during this report.

Basis: **source** in `Lake/Load/Materialize.lean` and `Lake/Util/Git.lean`.

### Manifest entries, not current `require` text alone, drive ordinary locked materialization

With an existing manifest, `Workspace.materializeDeps` builds a name map from manifest package entries, overlays workspace package overrides and explicit overrides, validates root `require` source changes, and then recursively materializes dependencies from those selected entries.

`validateManifest` warns if a root Git URL/revision or source kind differs from the current configuration, but ordinary manifest-driven materialization still uses the selected manifest/override entry. Updating the lock requires `lake update` or an update-mode load.

This distinction is useful for reproducible prebuilt trees: the persisted manifest can lock exact Git revisions or path locations, while source configuration can be checked for drift. It also means a packaging system must inspect both manifests and any active override layer when determining whether a consumer will attempt Git operations.

Basis: **source** in `Lake/Load/Resolve.lean`.

### Transitive dependencies are materialized before their package configuration can participate in the loaded workspace

Lake recursively resolves the package graph breadth-first by package name. For each missing direct dependency it first materializes the dependency, then loads that dependency's package configuration, then recurses into newly loaded packages.

A prebuilt child package therefore cannot defer its own source-location requirements until after build setup. Its manifest entry must already lead Lake to a usable source directory/repository so Lake can load the child configuration and discover/validate the rest of the graph.

This is one reason “the compiled `.olean`s are present” is not a substitute for a coherent source/package graph. Lake still needs package configuration during workspace construction.

Basis: **source** in `Lake/Load/Resolve.lean`.

### Current Anneal intentionally converts the dependency universe from Git to path before deleting Git metadata

Current Anneal's Nix pipeline initially invokes ordinary Lake/Mathlib machinery to obtain package sources and cache artifacts. During this producer phase the package directories are genuine Git clones.

Before those packages become the offline archive dependency universe, Anneal changes the contract:

1. the Mathlib-cache download derivation copies `.lake/packages` into its output;
2. it removes all `.git` directories from the copied packages;
3. the Aeneas compilation derivation copies those packages into a vendored `packages` tree;
4. `rewrite-lake-vendor.py` rewrites known `require` declarations and every traversed `lake-manifest.json` entry for a vendored package to `{type: "path", name, dir, inherited}` and removes remote-source fields;
5. Anneal then performs an offline verification build against that rewritten tree.

The order is important. Removing `.git` would be incompatible with a retained Git manifest as described above. Anneal is not relying on directory presence to fool Git materialization; it deliberately changes Lake's source model to path dependencies.

Basis: **current Anneal source** in `anneal/flake.nix` and `anneal/rewrite-lake-vendor.py` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

### Generated Anneal workspaces preserve the path-only invariant

When Anneal creates a verification workspace from the archive, `write_relative_archive_manifest` reads the archived Aeneas manifest and requires every inherited entry to have `type == "path"`; a non-path entry is an error. It adds Aeneas itself as another path dependency, rewrites every package directory relative to the fresh workspace, and writes a root manifest containing those path entries.

The same test path then runs:

- `lake --keep-toolchain --old build Generated`; and
- `lake --keep-toolchain env lean --json generated/Generated.lean`.

The source comments state the intended contract directly: the Nix archive must support fresh generated workspaces without reconfiguring packages or rebuilding read-only Lake artifacts.

This makes the consumer invariant explicit. If a future archive accidentally reintroduces a Git manifest entry, current Anneal fails while constructing the fresh workspace rather than silently accepting a package that could trigger a clone/fetch later.

Basis: **current Anneal source** in `anneal/src/main.rs` at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

### “Prebuilt” has three independent dimensions

For Anneal and similar packaging systems, three states should be kept separate:

| Dimension | Question | Relevant Lake mechanism |
| --- | --- | --- |
| Source materialization | Can Lake load every package source/configuration without obtaining another checkout? | manifest entry type; path existence; Git `HEAD`/remote/update path |
| Build reuse | Can Lake accept existing `.olean`/trace/native outputs without rebuilding? | traces, hashes, mtimes/old mode, artifact cache |
| Network freedom | Can all invoked commands complete without network access? | source materialization **plus** cache/release/package hooks/scripts and external tools |

A system can satisfy one and fail another. For example, a locked Git repository already at `HEAD == rev` can satisfy source materialization without a fetch while still causing a build. Conversely, a complete build cache next to a Git dependency stripped of `.git` can fail during source materialization before those cached outputs matter.

This separation should be retained in Anneal tests and documentation. It prevents cache-success evidence from being misread as source-vendoring evidence.

## Boundaries

**No fresh execution.** The report did not run Lake, remove a test repository, or simulate an unavailable remote. The no-fetch behavior has checked-in exact-pin test coverage; the missing-`.git` behavior is a direct control-flow consequence that should still receive a minimal regression fixture if Anneal comes to depend on it explicitly.

**Path dependencies can execute arbitrary package configuration.** “No Git operation in `PackageEntry.materialize`” does not imply a hostile or custom package configuration cannot perform network I/O when loaded.

**Other Lake network features are separate.** Release-build downloads, artifact-cache services, Reservoir resolution during update, custom scripts, and package hooks are outside the narrow source-materialization claim. The corpus's offline-operation and artifact-cache reports own those paths.

**Existing repository validity is narrower than directory existence.** Lake's fast no-fetch Git path depends on a readable Git `HEAD` equal to the locked revision. This report does not attempt to catalogue every way a corrupt repository can fail later.

**Windows update behavior differs.** When a repository URL appears changed, the non-Windows path removes and reclones the directory. Windows logs a manual-deletion warning and enters the update behavior instead because recursive repository deletion is treated as unreliable.

**Package overrides can change the source kind.** The effective manifest entry map includes `lake-packages.json`/workspace overrides and explicit overrides. A caller using those features must include them in source-materialization analysis.

**Anneal's current path-only invariant is revision-specific.** It is established for `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`; future packaging changes require revalidation.

## Evidence

Primary Lake subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned Lake files inspected:

- `src/lake/Lake/Load/Materialize.lean`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b` — path/Git package materialization, exact-HEAD fast path, clone/update behavior.
- `src/lake/Lake/Load/Resolve.lean`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928` — recursive resolution, manifest reuse/update, override precedence, manifest-driven materialization.
- `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b` — manifest versus update choice during workspace loading.
- `src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d` — persisted path/Git entry schema.
- `src/lake/Lake/Config/Dependency.lean`, blob `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1` — configuration source kinds.
- `src/lake/Lake/Util/Git.lean`, blob `e60d7e27924551cd495f9ef9adec4c7e45bdd47d` — clone, fetch, revision resolution, checkout.
- `src/lake/Lake/CLI/Main.lean`, blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78` — `lake build` loads the workspace before build execution.
- `src/lake/Lake/CLI/Help.lean`, blob `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb` — update/materialization user contract.
- `src/lake/README.md`, blob `2bc9c7832db61b10e78d33cd5e980449e4da13a0` — same-revision package-dependency documentation.
- `tests/lake/tests/clone/test.sh`, blob `b3ba81f1f56337186a812435bd70e505923ed78f` — checked-in no-fetch test when the local Git dependency is already at the manifest revision.

Current Anneal files inspected at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`:

- `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba` — producer-stage package copying, `.git` removal, vendoring, and offline build preparation.
- `anneal/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c` — conversion of known dependencies and manifests to relative path entries.
- `anneal/src/main.rs`, blob `b947700606677ea89c7a205f3ffcc75493508f63` — fresh-workspace relative path manifest construction and rejection of non-path archived entries.

No execution transcript was produced in this investigation.

## Revalidation

After changing Lake or Anneal's dependency packaging, revalidate in this order:

1. **Workspace load order.** Confirm `lake build` still calls full workspace dependency materialization before target build execution.
2. **Git fast path.** Inspect manifest Git materialization and confirm whether exact `HEAD == locked rev` still suppresses fetch.
3. **Git update path.** Inspect whether a wrong `HEAD` still invokes `git fetch` before local resolution and whether URL-mismatch behavior still deletes/reclones.
4. **Path semantics.** Confirm a manifest path entry still resolves directly without copying/fetching.
5. **Manifest fallback.** Check what an absent or unreadable manifest causes ordinary build to do.
6. **Overrides.** Include all workspace/package override layers in the effective source-kind calculation.
7. **Anneal producer.** Verify every archived dependency manifest/configuration that can participate in the consumer graph has been rewritten to path form before `.git` metadata is removed.
8. **Anneal consumer.** Preserve the current explicit rejection of non-path inherited entries or replace it with an equally strong invariant.

A minimal exact-pin execution matrix should then cover:

| Case | Setup | Expected source-materialization result |
| --- | --- | --- |
| Locked Git, exact `HEAD` | valid repo; remote unreachable; `HEAD == manifest rev` | succeeds without fetch |
| Locked Git, wrong `HEAD` | desired object present locally; remote unreachable | attempts update/fetch and fails offline |
| Locked Git, no `.git` | copied source dir only; remote unreachable | does not accept directory as materialized Git repo; non-Windows path attempts reclone |
| Locked path | relative path source present; no `.git`; network disabled | loads without Git clone/fetch |
| Missing manifest | configured remote dependency; populated build outputs | enters update/materialization rather than treating outputs as sufficient |
| Anneal archive | path-only manifest; `.git` absent; network denied | generated workspace loads and builds using shipped sources/artifacts |

Preserve command lines, stdout/stderr, manifest bytes, package directory state, and a process/network trace if available. The final Anneal test should distinguish “no Git fetch/clone” from the stronger “no network syscall by any process.”
