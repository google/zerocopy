# Lake Dependency Resolution, Manifest Locking, Path Flattening, and Vendoring

## Summary

Across Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52`, `Lake version 5.0.0-src+5045d00`), Lake does **not** solve a global system of package-version constraints. Instead, it resolves at most one package per package base name (`Dependency.name`) during a breadth-first traversal of the dependency graph (`Workspace.resolveDepsCore`). Within each package, direct dependencies are visited in reverse declaration order before descending transitively, so later `require` declarations shadow earlier ones and root-level requirements take priority over transitive requirements. Once a package with a given `baseName` is present in the workspace, subsequent dependency declarations sharing that `baseName` are skipped. Lake's user-facing `lake update` documentation nevertheless declares that if a graph requests multiple versions of the same package, the materialized version is undefined; the traversal precedence is an implementation property rather than a multi-version constraint-solving guarantee.

Dependency declarations enter the workspace graph through three source channels (`DependencySrc` and Reservoir lookup):
1. **Explicit path dependencies** (`.path dir`) borrow an existing filesystem directory relative to the declaring package without copying files into `.lake/packages` or attaching a revision digest.
2. **Explicit Git dependencies** (`.git url inputRev? subDir?`) materialize a Git repository under the workspace packages directory (`.lake/packages/<name>`), recording both the resolved checkout commit (`rev`) and the requested revision expression (`inputRev`).
3. **Reservoir registry dependencies** (`src? = none` with non-empty `scope`) query the Reservoir API (`RESERVOIR_API_URL`), select the first Git source from the registry response (`RegistryPkg.gitSrc?`), and resolve `version?` in one of three ways: no version uses the source's `defaultBranch` (or the cloned remote's default `HEAD` when absent); `git#<rev>` forwards `<rev>` directly; and any other string is parsed locally as a `VerRange` and matched via `vers.find? (ver.test ·.version)` against the server-returned version array without client-side sorting.

The root `lake-manifest.json` (schema version `1.2.0`) separates update-time selection from ordinary locked workspace loading (`Workspace.loadWorkspace` and `Workspace.materializeDeps`):
- **Flattened root-relative coordinates**: During `lake update`, Lake imports each dependency's manifest via `addDependencyEntries`, marks those entries `inherited := true`, and rebases inherited `.path` entries through `PackageEntry.inDirectory pkg.relDir` so all path entries in the root manifest are expressed relative to the root workspace. Inherited `.git` entries retain their repository coordinates unchanged. During ordinary locked loading, Lake indexes the root manifest by package name and resolves every direct and transitive dependency from that single flat map; a missing root dependency fails with a prompt to run `lake update <name>`, while a missing transitive dependency fails closed as a corrupt manifest.
- ** Asymmetric configuration-drift validation**: `validateManifest` warns when a root Git dependency's URL or `inputRev` drifts from the manifest or when a dependency switches between Git and path kinds, while still materializing the locked manifest entry. For path-to-path declarations, `validateManifest` returns `pure ()` without comparing the configured path against the manifest's `dir`.
- **Source materialization vs. prebuilt artifacts**: A prebuilt `.lake/build` tree does not bypass workspace dependency materialization. A locked Git manifest entry skips network `git fetch` only when `.lake/packages/<name>` exists as a valid Git repository whose `HEAD` already equals `rev`; if `.git` metadata is stripped while the manifest entry remains `type: "git"`, Lake treats the directory as mismatched, deletes it on non-Windows hosts, and attempts to reclone. Converting a prepared dependency tree from Git to offline vendored form therefore requires rewriting `require` declarations and `lake-manifest.json` entries to `type: "path"` before removing `.git` metadata, while preserving `Dependency.name` (`baseName`), the package's self-declared `origName` (`Package.id?`), and the topological load index (`wsIdx`, which forms `keyName := baseName.num wsIdx`).
- **`v4.30.0-rc2` to `v4.34.1` configuration-cache delta**: While manifest schema `1.2.0`, single-name graph resolution, and Git/path materialization rules remain invariant from `v4.30.0-rc2` to `v4.34.1` (with `PackageEntry.materialize` moving into `Lake/Load/Resolve.lean` in `v4.34.1`), compiled configuration caching changed starting in `v4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): `LoadConfig.configDir` (`Lake/Load/Config.lean` line 83) hoists compiled `lakefile` artifacts from `<pkgDir>/.lake/config/<pkgName>/` into the consumer workspace's `<wsDir>/.lake/config/<pkgIdx>/`, eliminating configuration-compilation writes inside read-only vendored path dependencies.

Basis: source + documentation + derived synthesis across `leanprover/lean4` (`v4.30.0-rc2` and `v4.34.1`) and `google/zerocopy` (`41f5b37afe7060fd9fe08c00b200672cd76d77b9`).

## Applicability

The findings in this report apply to the following pinned subjects recorded in `REPORT.json` and cross-version revalidation baselines:
- **Lean 4 and Lake `v4.29.0`**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740` (historical comparison baseline for Lake `5.0.0-src+98dc76e` workspace and manifest loading).
- **Lean 4 and Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`Lake version 5.0.0-src+3dc1a08`), the baseline toolchain selected by Anneal's Aeneas backend.
- **Lean 4 and Lake `v4.31.0`**: `leanprover/lean4` revision `68218e876d2a38b1985b8590fff244a83c321783` (the intermediate release that hoisted `LoadConfig.configDir` into the root workspace).
- **Lean 4 and Lake `v4.34.1`**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52` (`Lake version 5.0.0-src+5045d00`), the revalidation target release.
- **Anneal V2 archive workspace construction**: `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/src/main.rs`, `anneal/flake.nix`, and `anneal/rewrite-lake-vendor.py`).

### Relationship Among Subjects and Scope Boundaries

This package synthesizes six closely coupled facets of Lake's dependency and manifest subsystem:
1. **Graph resolution and Reservoir version selection** (`Dependency`, `VerRange`, `RegistryPkg`, `Workspace.resolveDepsCore`).
2. **Git versus path dependency semantics** (`DependencySrc.git` vs. `DependencySrc.path` and `PackageEntrySrc`).
3. **Transitive path coordinate flattening and `inherited` provenance** (`PackageEntry.inDirectory`, `addDependencyEntries`, `write_relative_archive_manifest`).
4. **Manifest schema `1.2.0`, compatibility gates, selective updates, and non-transactional saving** (`Manifest`, `Manifest.getVersion`, `reuseManifest`, `Manifest.save`).
5. **Four-layer package identity across Git-to-path vendoring** (`Dependency.name`, `Package.baseName`, `Package.keyName`, and `Package.origName` / `Package.id?`).
6. **Prebuilt source materialization and `.git`-stripping invariants** (`PackageEntry.materialize`, `updateGitRepo`, `findRemoteRevision`).

 behaviors shared across `v4.30.0-rc2` and `v4.34.1` are distinguished from version-specific module refactoring (`Lake/Load/Materialize.lean` into `Lake/Load/Resolve.lean`) and the `v4.31.0` / `v4.34.1` workspace-local `.lake/config/<pkgIdx>` hoisting. Reservoir server-side ordering guarantees are outside the scope of the pinned client code and are documented under **Boundaries**.

## Findings

### 1. Single-Package-Per-BaseName Graph Resolution and Traversal Precedence

In both `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `Dependency.name` is the package's graph identity. Its source documentation requires `name` to match the dependency package's declared name and to be unique across the dependency graph. `Dependency.scope` is a Reservoir registry qualifier rather than a graph-namespace component.

During recursive resolution (`Workspace.resolveDepsCore`, at lines 110–140 and 319–352 of `src/lake/Lake/Load/Resolve.lean` in `v4.30.0-rc2`, and lines 195 and 505 of `src/lean/lake/Lake/Load/Resolve.lean` in `v4.34.1`), Lake traverses each package's direct dependencies in **reverse declaration order** before descending into transitive dependencies:
- Before loading a dependency, Lake checks whether any package already loaded in the workspace has the same `baseName`; if so, the later declaration is skipped without re-evaluating its version or source.
- Lake rejects direct self-dependencies (`dep.name == pkg.baseName`) and detects cycles along the active dependency chain.
- Because all missing direct dependencies of a package are loaded before recursing into their children (breadth-first priority) and direct dependencies are scanned in reverse order, later `require` statements in the same file shadow earlier ones, and root-package requirements take priority over transitive requirements.

Lake does not collect version predicates across the graph, intersect `VerRange` constraints, backtrack, or instantiate multiple versions of a package name. Moreover, Lake's `lake update` CLI help (`src/lake/Lake/CLI/Help.lean` lines 195–213) explicitly warns that if dependencies request multiple versions of the same package, "the version materialized is undefined." Consumers must therefore treat reverse-declaration breadth-first winning as an implementation mechanism rather than a supported multi-version solver.

Basis: source + documentation.

### 2. Source Selection: Path, Git, and Reservoir First-Match Filtering

`Dependency` (`src/lake/Lake/Config/Dependency.lean` lines 24–69) separates `name : Name`, `scope : String`, `version? : Option String`, `src? : Option DependencySrc`, and `opts : NameMap String`. Both the Lean DSL (`src/lake/Lake/DSL/Require.lean` lines 18–58) and the TOML loader (`src/lake/Lake/Load/Toml.lean`) lower `require` declarations into this structure.

When `src?` is present, Lake bypasses Reservoir:
- **`.path dir`**: resolves directly to the package at `relParentDir / dir` relative to the declaring package.
- **`.git url inputRev? subDir?`**: materializes the Git repository at `url` (after optional URL substitution from the JSON environment variable `LAKE_PKG_URL_MAP`, parsed in `Lake/Config/Env.lean` lines 163–206), checks out `inputRev?`, and loads the package from the repository root or `subDir?`.

When `src?` is `none`, Lake requires a non-empty `scope` and queries Reservoir (`Lake/Reservoir.lean` lines 22–91 and 144–187):
1. `RegistryPkg.gitSrc?` uses `Array.find?` to pick the **first** source entry whose type is Git. Non-Git registry sources cannot be materialized by this path.
2. `version?` is interpreted in three modes during update/materialization (`Dependency.materialize`):
   - **`none` (versionless declaration)**: Lake does not fetch Reservoir's `/versions` endpoint. It uses the selected Git source's optional `defaultBranch` as `inputRev?`. If `defaultBranch` is `none`, `cloneGitPkg` clones without an explicit revision checkout, leaving the remote's default `HEAD` branch checked out before recording `HEAD` as `rev`.
   - **`some "git#<rev>"` (from Lean `@ git <rev>` or TOML `rev` without explicit `git`/`path` source)**: strips the `git#` prefix and uses `<rev>` directly as the requested Git revision.
   - **Any other string**: parsed locally via `VerRange.parse` (`src/lake/Lake/Util/Version.lean` lines 352–624), which supports comparator predicates (`<`, `<=`, `>`, `>=`, `=`), comma-separated conjunctions, `||` disjunctions, wildcards, caret (`^`) ranges, and tilde (`~`) ranges (rejecting bare exact versions unless prefixed with `=`). Lake fetches the Reservoir `/versions` array and evaluates:
     ```lean
     vers.find? (ver.test ·.version)
     ```
     Lake selects the **first** array element satisfying `VerRange.test`. Lake performs no local sorting or maximum-version computation over `vers`; "latest version compatible" depends entirely on the ordering returned by the Reservoir server. Once materialized into `lake-manifest.json`, the chosen version's `rev` becomes the locked `inputRev` and resolved `rev`, and the original semantic range expression is not preserved in `lake-manifest.json`.

| Resolution Scenario | Selection Authority | Persistent Manifest Result |
| --- | --- | --- |
| Explicit `path` during update or missing-manifest load | Configured relative `dir` joined to declaring package's `relDir` | `.path relPkgDir` (workspace-relative) |
| Explicit `git` during update or missing-manifest load | Configured `url` (or `LAKE_PKG_URL_MAP` override) + `inputRev?` | `.git url rev inputRev? subDir?` with exact `HEAD` in `rev` |
| Reservoir with `@ git <rev>` | First registry Git source + `<rev>` | `.git url rev (some <rev>) subDir?` |
| Reservoir with `VerRange` string | First registry Git source + first `/versions` entry matching `VerRange.test` | `.git url rev (some ver.revision) subDir?`; range string is not stored |
| Reservoir with `version? = none` | First registry Git source + `defaultBranch` (or remote default `HEAD`) | `.git url rev defaultBranch subDir?` |
| Ordinary load with existing `lake-manifest.json` | Package entry looked up by `dep.name` in root manifest | Existing manifest remains selection authority |
| Ordinary load with `.lake/package-overrides.json` or `--packages` | Override entry keyed by `dep.name` (inserted after `validateManifest`) | Override controls materialization for that run without rewriting `lake-manifest.json` |
| Duplicate `dep.name` encountered later in graph | First-loaded package in breadth-first reverse-`require` order wins | Later declaration is skipped; single node per `baseName` |

Basis: source + documentation + derived synthesis.

### 3. Git vs. Path Dependency Semantics and Transitive Coordinate Flattening

Git and path dependencies have fundamentally different physical ownership, coordinate systems, and validation rules:

| Property | Path Dependency (`DependencySrc.path` / `PackageEntrySrc.path`) | Git Dependency (`DependencySrc.git` / `PackageEntrySrc.git`) |
| --- | --- | --- |
| Physical location | Borrowed in place at `wsDir / relPkgDir` | Managed repository under `wsDir / packagesDir / name` |
| Persistent manifest identity | Workspace-relative `dir : FilePath` | `url`, exact checked-out `rev`, requested `inputRev?`, optional `subDir?` |
| Content pin in Lake | None (filesystem contents are consumed directly) | Exact commit hash `rev` for `HEAD`, but dirty worktrees only log a warning |
| Materialization writes | None to create the source tree | Clones if missing; fetches, detaches checkout, and runs `git clean` on revision change; deletes and reclones on URL mismatch (non-Windows) |
| Network requirement | None during path resolution | Zero network fetch **only** when local repository exists and `HEAD == rev` |
| Transitive manifest flattening | Rebased via `PackageEntry.inDirectory pkg.relDir` (`pkgDir / dir`) | Unchanged by `inDirectory`; repository URL/revision is parent-location-independent |
| `validateManifest` drift check | Path-to-path returns `pure ()` without comparing path strings | Warns if `url` or `inputRev?` differs from current root `require` declaration |
| Subdirectory support | Expressed directly in the target path `dir` | Dedicated optional `subDir : Option FilePath` field |

#### Coordinate Rebasing and `inherited` Ownership

When a non-root package `P` at workspace-relative directory `pkg.relDir` declares `require B from "<dir>"`, `<dir>` is written in `P`'s coordinate system. During `lake update`, Lake flattens the entire dependency closure into the root workspace's single `lake-manifest.json`:
- If `P` has its own `lake-manifest.json`, `addDependencyEntries` (`Lake/Load/Resolve.lean` lines 173–185 in `v4.30.0-rc2`) loads `P`'s entries, marks each entry with `setInherited` (`inherited := true`), and transforms its source via `PackageEntry.inDirectory pkg.relDir` (`Lake/Load/Manifest.lean` lines 152–166), which prefixes `pkg.relDir` onto `.path dir` while leaving `.git` entries untouched.
- If `P` lacks a `lake-manifest.json`, Lake logs a warning and resolves `P`'s declared dependencies live in `updateAndMaterializeDep` (`Lake/Load/Resolve.lean` lines 186–207), passing `pkg.relDir / "."` as the parent directory so the resulting path string includes the `./` normalization matching inherited manifest entries.

During ordinary locked loading (`Workspace.materializeDeps`), Lake folds `manifest.packages` into a single `NameMap PackageEntry` and looks up every dependency—direct or transitive—by `dep.name` in that root map. `PackageEntry.materialize` loads `.path relPkgDir` directly as `wsDir / relPkgDir` without consulting parent manifests. If a root dependency is missing from the root manifest, Lake errors with instructions to run `lake update <name>`; if a transitive dependency is missing, Lake reports the root manifest as corrupt and requires a full `lake update`.

The `inherited : Bool` flag governs **selective updates**, not locked loading: when `lake update <pkg>` is invoked with a non-empty `toUpdate : NameSet`, `reuseManifest` (`Lake/Load/Resolve.lean` lines 144–172) retains only existing root manifest entries where `!entry.inherited && !toUpdate.contains entry.name`. Inherited entries are always discarded from the initial lock seed and re-derived from the updated dependency graph.

Basis: source + derived synthesis.

### 4. Manifest Schema `1.2.0`, Version Compatibility, Overrides, and Non-Transactional Saving

In both `v4.30.0-rc2` (`src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d`) and `v4.34.1` (`src/lean/lake/Lake/Load/Manifest.lean`, 313 lines, SHA-256 `8b01bdff19b7e4cb...`, with `Manifest.load` at line 258 and `Manifest.tryLoadEntries` at line 301), `Manifest.version` is `{major := 1, minor := 2, patch := 0}` (`"1.2.0"`):
- **Top-level JSON fields**: `version` (`"1.2.0"`), `fixedToolchain` (`Bool`), `name` (`Name`), `lakeDir` (`FilePath`), `packagesDir` (`FilePath`), and `packages` (`Array PackageEntry`).
- **Per-package common JSON fields**: `name`, `scope`, `inherited`, `configFile`, `manifestFile`, plus variant fields `type: "path"` (`dir`) or `type: "git"` (`url`, `rev`, `inputRev`, `subDir`).
- **Asymmetric version compatibility (`Manifest.getVersion`)**: Lake accepts integer legacy versions or semantic-version strings from `0.5.0` upward (converting pre-`0.7.0` entries via `PackageEntryV6`), rejects versions below `0.5.0` (such as `0.4.0`), and rejects major versions `> 1`. It accepts any `1.x` minor version without comparing `minor <= 2`, treating post-`1.0` minor bumps as backward-compatible extensions (checked-in test coverage in `tests/lake/tests/manifest/test.sh`, blob `817b708067aed85a9b204725d5f362bd0d6521ba`).
- **Recovery from unreadable manifests**: In `reuseManifest`, a corrupt or incompatible manifest rethrows its error during a selective update (`lake update <pkg>`) because unselected root locks cannot be recovered, whereas a bare `lake update` (`toUpdate.isEmpty`) logs a warning, ignores the unreadable manifest, and reconstructs `lake-manifest.json` from scratch.
- **Package-entry override precedence**: After `validateManifest` checks root declarations against `lake-manifest.json`, `Workspace.materializeDeps` overlays entries from `<wsDir>/.lake/package-overrides.json` and then from `LoadConfig.packageOverrides` (`--packages=<file>`, parsed in `Lake/CLI/Main.lean` lines 291–295). Later insertions replace earlier entries by package name without adding undeclared dependencies or re-running `validateManifest`.
- **Non-transactional save ordering**: `Manifest.save` formats JSON with `Json.pretty` and calls `IO.FS.writeFile manifestFile` directly without a temporary-file rename or cross-process file lock. In `Workspace.updateAndMaterialize`, `writeManifest` runs after dependency materialization completes and **before** `post_update` hooks execute, so a failing `post_update` hook leaves the new `lake-manifest.json` already written on disk.

Basis: source + checked-in test source.

### 5. Four-Layer Package Identity and Git-to-Path Vendoring Invariants

Converting a dependency graph from Git checkouts to vendored path dependencies preserves Lake behavior only when four distinct package identities are respected (`src/lake/Lake/Config/Package.lean` lines 24–93 and 149–165, `src/lake/Lake/Load/Config.lean` lines 20–45, `src/lake/Lake/Load/Lean/Elab.lean` lines 57–89, `src/lake/Lake/Load/Toml.lean` lines 470–499, and `src/lake/Lake/Build/Info.lean` lines 31–40):

1. **Dependency source identity (`DependencySrc` / `PackageEntrySrc`)**: Where files come from (`.git` vs. `.path`). Changing `.git` to `.path` removes Git commit provenance (`rev`) from Lake's manifest layer; external packaging must supply content integrity.
2. **Assigned workspace package name (`Dependency.name` -> `Package.baseName`)**: The name declared in `require <name>` and used as the deduplication and manifest-lookup key across the workspace graph.
3. **Internal workspace key (`Package.keyName := baseName.num wsIdx`)**: Combines `baseName` with the package's topological load index `wsIdx : Nat`. `Package` equality (`BEq`) compares `wsIdx`, `Hashable` hashes `keyName`, `Workspace.packageMap` is keyed by `keyName`, and `BuildKey` variants (`package`, `packageModule`, `packageTarget`) embed `keyName`. A vendoring transformation that alters dependency declaration order or inserts/removes intermediate packages changes `wsIdx` and `keyName` even if `baseName` is preserved.
4. **Author-declared package name (`Package.origName` -> `Package.id?`)**: The name declared inside the dependency's own `package <origName>` statement. For non-bootstrap packages, `Package.id?` returns `origName` as the `PkgId` passed to `lean` for native C symbol mangling and module build traces (`Module.recBuildLean` hashes `mod.pkg.id?`, whereas `Package.version` is not part of `Package.id?`).

#### Prebuilt Source Materialization and `.git` Stripping

As mapped in [`support/lake-source-materialization/source-map.json`](support/lake-source-materialization/source-map.json), `lake build` always executes `loadWorkspace` and materializes dependencies before running target build jobs (`Lake/CLI/Main.lean` and `Lake/Load/Workspace.lean`):
- For a locked **Git** entry, `PackageEntry.materialize` checks whether `.lake/packages/<name>` exists. If it exists and `repo.getHeadRevision?` equals the locked `rev`, Lake skips `git fetch` (verified by `tests/lake/tests/clone/test.sh`, blob `b3ba81f1f56337186a812435bd70e505923ed78f`). If `HEAD` differs from `rev`—even if the target commit object already exists in the local object database—`updateGitRepo` calls `updateGitPkg` -> `findRemoteRevision` (`Lake/Util/Git.lean`), which unconditionally executes `git fetch --tags --force <remote>` before checkout. If `.git` was stripped from `.lake/packages/<name>` while the manifest entry remained `type: "git"`, `getHeadRevision?` fails, remote URL comparison fails, and on non-Windows systems Lake deletes the directory and attempts a fresh `git clone`.
- Anneal V2 (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`) satisfies this boundary in two coordinated steps:
  1. During archive construction (`anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`, and `anneal/rewrite-lake-vendor.py`, blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`), Anneal strips `.git` directories from copied packages and rewrites `require` declarations and `lake-manifest.json` entries to `{type: "path", name, dir, inherited}` without remote fields.
  2. When constructing a fresh verification workspace (`anneal/src/main.rs` lines 143–188 and `write_relative_archive_manifest` at lines 220–287, blob `b947700606677ea89c7a205f3ffcc75493508f63`), Anneal reads the archived Aeneas `lake-manifest.json`, rejects any inherited entry whose `type != "path"`, rebases each inherited `dir` relative to the generated workspace with `inherited: true`, and prepends Aeneas itself as a direct path entry (`inherited: false`).

### 6. Version Deltas: `v4.30.0-rc2` vs. `v4.31.0` and `v4.34.1`

Comparing `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) against `v4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) establishes two structural changes alongside invariant manifest locking:

1. **Module consolidation (`Lake/Load/Resolve.lean` and `Lake/Load/Manifest.lean`)**:
   - In `v4.34.1`, `src/lean/lake/Lake/Load/Manifest.lean` (313 lines, SHA-256 `8b01bdff19b7e4cb...`) defines `Manifest.load` (line 258) and `Manifest.tryLoadEntries` (line 301), while `src/lean/lake/Lake/Load/Resolve.lean` (627 lines, SHA-256 `f90d1e01f6ee9d60...`) consolidates `PackageEntry.materialize` (lines 32 and 310) and `Workspace.resolveDepsCore` (lines 195 and 505). The manifest schema version (`1.2.0`), single-`baseName` deduplication, reverse-`require` breadth-first traversal, and Git/path materialization rules remain unchanged.
2. **Hoisting of compiled `lakefile` configuration caches out of path dependencies (`v4.31.0` and `v4.34.1`)**:
   - In `v4.30.0-rc2`, `importConfigFile` (`src/lake/Lake/Load/Lean/Elab.lean` lines 165–279, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`) stored compiled configuration artifacts under `<pkgDir>/.lake/config/<pkgName>/lakefile.{olean,olean.trace,olean.lock}` inside each dependency's own package directory. Because `ConfigTrace` records `idx : Nat` and `name : Name`, loading a read-only path dependency from a consumer workspace where its `wsIdx` or cache state was unprimed caused Lake to attempt creating `lakefile.olean.lock` inside the read-only dependency tree.
   - Starting in `v4.31.0` (`68218e876d2a38b1985b8590fff244a83c321783`) and preserved in `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `LoadConfig.configDir` (`src/lean/lake/Lake/Load/Config.lean` line 83, 84 lines, SHA-256 `7292223420baa665...`) is defined as:
     ```lean
     cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx
     ```
     and `importConfigFile` (`src/lean/lake/Lake/Load/Lean/Elab.lean` lines 180–185, 299 lines, SHA-256 `5b3d30d5a9001514...`) writes `.olean`, `.olean.private`, `.olean.server`, `.olean.trace`, and `.olean.lock` under the **consumer workspace's** `.lake/config/<pkgIdx>/` directory. Consequently, in `v4.31.0` and `v4.34.1`, elaborating or re-elaborating a Lean-authored `lakefile.lean` in a read-only vendored path dependency never writes configuration cache or lock files into the dependency's own directory.

Basis: source across `v4.30.0-rc2`, `v4.31.0`, and `v4.34.1`.

## Boundaries

- **Reservoir server-side version ordering — `not examined` / `unknown`**: Lake's `Dependency.materialize` selects the first element of the `/versions` array matching `VerRange.test`. Whether the Reservoir backend service guarantees descending semantic-version order across all endpoints and historical states was **not examined** in this client-source study.
- **Multi-version dependency graphs — `unsupported`**: Graphs requiring two distinct versions of the same `Dependency.name` are **unsupported** by Lake; `lake update` help explicitly marks the materialized version as undefined.
- **Content immutability from `lake-manifest.json` alone — `known not to apply`**: A locked manifest is **known not to apply** as a cryptographic commitment to working-tree bytes. Path dependencies carry no content digest in Lake, and locked Git dependencies at `HEAD == rev` with local uncommitted modifications only emit a warning rather than resetting the worktree.
- **Path-to-path configuration drift warnings — `known not to apply`**: `validateManifest` is **known not to apply** to path-value changes when both the `lakefile` declaration and the manifest entry have `type: "path"`; Lake silently continues using the manifest's `dir` until `lake update` is run.
- **Crash-atomic or concurrent manifest writes — `unsupported`**: `Manifest.save` uses `IO.FS.writeFile` directly without a temporary file rename or lockfile; concurrent writers to the same `lake-manifest.json` are **unsupported**.
- **Retroactive `copy` flag projection — `known not to apply`**: `DependencySrc.path` at `v4.30.0-rc2` has no `copy` flag; path dependencies are borrowed in place.

## Evidence

### 1. Pinned Upstream `leanprover/lean4` Sources (`v4.30.0-rc2` @ `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`)

All `v4.30.0-rc2` blobs below were inspected on 2026-09-27:
- `src/lake/Lake/Config/Dependency.lean` (blob `a06fad9cd1da3df2ab1b2c6aaaba38535e64a0f1`, lines 24–69): `DependencySrc` (`.path`, `.git`) and `Dependency` graph-identity contract (`name`, `scope`, `version?`, `src?`, `opts`).
- `src/lake/Lake/Config/Package.lean` (blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`, lines 24–93, 149–165): `Package` structure (`wsIdx`, `baseName`, `keyName := baseName.num wsIdx`, `origName`, `dir`, `relDir`, `id?`, `version`).
- `src/lake/Lake/Config/Workspace.lean` (blob `b9c01f130240ae7c65ee298778351ddbe312374e`, lines 170–205): `packageOverridesFile` (`.lake/package-overrides.json`), `packages` array ordering, and `packageMap` indexed by `keyName`.
- `src/lake/Lake/Config/Env.lean` (blob `eed315c538de746a891d18f72564e88aea64e969`, lines 163–206): `LAKE_PKG_URL_MAP` and Reservoir API URL environment parsing.
- `src/lake/Lake/DSL/Require.lean` (blob `53a2193ce8636f1974330a9b344dce6b00d6981e`, lines 18–58) & `src/lake/Lake/DSL/Package.lean` (blob `91169e3d688711a5caf24491daa4f3f6d53d740d`, lines 21–46): macro lowering for `require` and `package`.
- `src/lake/Lake/Load/Config.lean` (blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`, lines 20–45), `src/lake/Lake/Load/Lean.lean` (blob `b38ee619b42d8293fc9e4ffb4b8e2f4b1508c1e7`, lines 24–42), `src/lake/Lake/Load/Lean/Elab.lean` (blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`, lines 57–89, 165–279), and `src/lake/Lake/Load/Toml.lean` (blob `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`, lines 470–499): package configuration loading, `nameExt`, and `.lake/config` trace caching.
- `src/lake/Lake/Load/Manifest.lean` (blob `760eb81419762fb0ab11393e93082930645e2b6d`, lines 29–260): `Manifest.version` (`1.2.0`), `PackageEntrySrc`, `PackageEntry`, `setInherited`, `inDirectory`, `Manifest.getVersion`, and `Manifest.save`.
- `src/lake/Lake/Load/Materialize.lean` (blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`, lines 25–87, 145–265): `cloneGitPkg`, `updateGitPkg`, `updateGitRepo`, `Dependency.materialize` (`vers.find?`), and `PackageEntry.materialize` (`HEAD == rev` fast path).
- `src/lake/Lake/Load/Resolve.lean` (blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`, lines 90–230, 309–494): `Workspace.resolveDepsCore`, `reuseManifest`, `addDependencyEntries`, `updateAndMaterializeDep`, `Workspace.updateAndMaterializeCore`, `Workspace.writeManifest`, `validateManifest`, and `Workspace.materializeDeps`.
- `src/lake/Lake/Load/Workspace.lean` (blob `9f25dd62bc752ede695a25fc20371157eb65d64b`, lines 31–64): `Workspace.loadWorkspace` selection between `updateAndMaterialize` and `materializeDeps`.
- `src/lake/Lake/Reservoir.lean` (blob `20789b581b8f9d7361f8844d8978a64b5a6da9bb`, lines 22–187), `src/lake/Lake/Util/Reservoir.lean` (blob `ab19b5e5c7927835ee6565fdfc6a755e2de0ea1f`), `src/lake/Lake/Util/Version.lean` (blob `7d89bda7ac1abc6d8c07d6e48e50ed20cfeb74c1`, lines 352–624), and `src/lake/Lake/Util/Git.lean` (blob `e60d7e27924551cd495f9ef9adec4c7e45bdd47d`): Reservoir API decoding, `VerRange`, and `findRemoteRevision` (`git fetch --tags --force`).
- `src/lake/Lake/Build/Info.lean` (blob `6c723e06c58ce54b0aff43217847b45ed364434f`, lines 31–40), `src/lake/Lake/Build/Infos.lean` (blob `e7761bb5b29ef84a187e64c6c76b4274b5111261`, lines 24–33), `src/lake/Lake/Build/Module.lean` (blob `21c5f343112a1690390188642a05d6092432ab84`, lines 884–896), `src/lake/Lake/Config/LeanLib.lean` (blob `077efb6c244fd53bab5dead6c850d40161c96e7f`, lines 58–69), and `src/lake/Lake/Config/Module.lean` (blob `f8b938e16fe53ada616364033b8d8353baa733ee`, lines 151–163): `keyName` in `BuildKey` and `origName` (`Package.id?`) in native symbol generation and module traces.
- `src/lake/Lake/CLI/Main.lean` (blob `65b0e7fd0d6cd21d512edb49a276bcc65ae31c78`, lines 291–295, 880–886), `src/lake/Lake/CLI/Help.lean` (blob `aa96ac1b5fa65178418d4292b49d8086f0d6a9bb`, lines 195–213), `src/lake/README.md` (blob `2bc9c7832db61b10e78d33cd5e980449e4da13a0`, lines 433–512), `tests/lake/tests/manifest/test.sh` (blob `817b708067aed85a9b204725d5f362bd0d6521ba`), `tests/lake/tests/manifest/lake-manifest-latest.json` (blob `0f0bf56074594e083f45978b5904b5295d22d21d`), and `tests/lake/tests/clone/test.sh` (blob `b3ba81f1f56337186a812435bd70e505923ed78f`).

### 2. Pinned `leanprover/lean4` Sources (`v4.31.0` @ `68218e876d2a38b1985b8590fff244a83c321783` and `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`)

Inspected for multi-version revalidation on 2026-11-05:
- `src/lean/lake/Lake/Load/Manifest.lean` (313 lines, SHA-256 `8b01bdff19b7e4cb...`): `Manifest.load` (line 258), `Manifest.tryLoadEntries` (line 301).
- `src/lean/lake/Lake/Load/Resolve.lean` (627 lines, SHA-256 `f90d1e01f6ee9d60...`): `PackageEntry.materialize` (lines 32, 310), `Workspace.resolveDepsCore` (lines 195, 505).
- `src/lean/lake/Lake/Load/Config.lean` (84 lines, SHA-256 `7292223420baa665...`): `LoadConfig.configDir` at line 83 (`cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx`).
- `src/lean/lake/Lake/Load/Lean/Elab.lean` (299 lines, SHA-256 `5b3d30d5a9001514...`): `importConfigFile` at lines 180–185 writing `.olean`, `.olean.private`, `.olean.server`, `.olean.trace`, and `.olean.lock` under the root workspace's `.lake/config/<pkgIdx>/`.
- `src/lean/lake/Lake/Config/Env.lean` (344 lines, SHA-256 `bc976a2f9ae48066...`) & `src/lean/lake/Lake/Config/Workspace.lean` (435 lines, SHA-256 `80ae4168ce567b92...`).

### 3. Pinned `google/zerocopy` Sources (`41f5b37afe7060fd9fe08c00b200672cd76d77b9`) and Support Material

- `anneal/src/main.rs` (blob `b947700606677ea89c7a205f3ffcc75493508f63`, lines 143–188, 220–287): `write_relative_archive_manifest` and generated workspace manifest construction.
- `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`) & `anneal/rewrite-lake-vendor.py` (blob `e61fc992837435a43b3e434ddd3b07aa7d13b48c`): `.git` removal and Git-to-path manifest/configuration rewriting.
- Preserved package support mapping: [`support/lake-source-materialization/source-map.json`](support/lake-source-materialization/source-map.json).

## Revalidation

To revalidate these findings against a newer Lean/Lake revision or an updated Anneal archive pipeline:

1. **Diff the core Lake loader and resolver modules**:
   - Inspect `Lake/Config/Dependency.lean`, `Lake/Config/Package.lean`, and `Lake/Load/Config.lean` for changes to `DependencySrc`, `keyName` (`baseName.num wsIdx`), `origName` (`Package.id?`), and `LoadConfig.configDir`.
   - Inspect `Lake/Load/Manifest.lean` and `Lake/Load/Resolve.lean` (plus `Lake/Load/Materialize.lean` if split) for `Manifest.version`, `Manifest.getVersion`, `PackageEntry.inDirectory`, `Workspace.resolveDepsCore` traversal order, `vers.find?` in Reservoir range resolution, `reuseManifest`, `validateManifest`, and `PackageEntry.materialize`'s `HEAD == rev` check.
2. **Run a minimal discriminating execution matrix**:
   - **Fake Reservoir range ordering**: Serve a local JSON fixture via `RESERVOIR_API_URL` with two matching versions, reverse their array order, and confirm whether `lake update` selects the new first element.
   - **Transitive path flattening and drift**: Create `R -> A -> B` using relative path dependencies, run `lake update`, verify `B`'s entry in `R/lake-manifest.json` is rebased to `R`'s root and marked `inherited: true`, then edit `A`'s path to `B` without running `lake update` to confirm ordinary `lake build` still uses the locked root manifest entry.
   - **Offline Git vs. path materialization**: Verify that a locked Git dependency with `HEAD == rev` succeeds when the remote URL is unreachable, fails when `HEAD != rev` (even if the target commit is present locally) or when `.git` is removed, and succeeds without `.git` once rewritten to `type: "path"`.
   - **Vendoring identity verification**: Compare pre- and post-vendoring resolved package arrays to verify that every package retains its `baseName`, `origName`, and `wsIdx` (`keyName`).
