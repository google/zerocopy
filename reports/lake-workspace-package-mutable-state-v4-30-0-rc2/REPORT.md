# Workspace-owned versus package-owned mutable Lake state at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does **not** put all mutable state for a workspace under one workspace-private directory. The important boundary is the `Package.dir` of each loaded package.

Three ownership classes matter:

1. **Workspace-root state.** The root package determines the workspace directory, the default remote-package directory (`.lake/packages`), the root manifest (`lake-manifest.json`), and the package-overrides file (`.lake/package-overrides.json`). `lake update` writes the root manifest and can rewrite the root `lean-toolchain`. Git dependencies are normally cloned or updated under the root workspace's package directory.
2. **Package-local state.** Every package, including a dependency, has its own `dir` and computes its default build directory as `<package>/.lake/build`. Module outputs, build traces, cached file hashes, native intermediates, libraries, and executables are written under that package build directory. At this revision, Lean-authored package configuration is also compiled under the package's own `.lake/config/...` directory. A path dependency outside the root workspace is therefore not merely read from its source directory: ordinary configuration and build operations can write into that dependency's tree.
3. **Lake cache state.** Lake may use a cache outside both the workspace and dependency trees, selected by `LAKE_CACHE_DIR`, an Elan toolchain cache, or a system cache. If no such cache exists, the workspace cache falls back to the root package's `.lake/cache`. Artifact-cache behavior is a separate subsystem; this report records only the ownership boundary needed to distinguish it from package build state.

This distinction explains why two workspaces can safely have independent manifests and Git dependency clones yet still interfere if they both refer to the same path dependency and let Lake use that dependency's default `.lake/build` or `.lake/config`. Conversely, ordinary Git dependencies materialized into each workspace's own `.lake/packages` are normally isolated because the package-local state lives inside each workspace-local clone.

Lake does not provide one general process lock that serializes package builds. The pinned source explicitly says Lake no longer uses its old build lock file. Individual subsystems use narrower techniques—build traces, `.hash` files, cache-specific race handling, and configuration-cache locks—but those mechanisms do not establish that arbitrary concurrent writers to one shared package build directory are safe. The source evidence is enough to locate the shared mutable paths; a concurrent-process probe is still required to characterize every race outcome.

No fresh Lake process was run for this report. Findings are source-level facts at the exact pinned revision, with derived concurrency and isolation consequences stated separately from unmeasured execution behavior.

## Applicability

This report applies to Lake as shipped in Lean `v4.30.0-rc2`, repository revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

It answers the #3720 inventory question **Workspace-owned versus package-owned mutable state**. “Owned” here means where Lake reads or writes persistent filesystem state, not who conceptually authored a configuration value. A package can be a member of one workspace while still storing build or configuration state under its own physical source directory.

The findings cover the ordinary workspace/package model, default paths, Git and path dependency materialization, build artifacts and traces, manifest/toolchain updates, and the local Lake cache location. Package options can override several paths, especially `buildDir` and `packagesDir`; where an option is configurable, the report describes the default and the rule used to derive the effective path rather than assuming the default is mandatory.

The report does not attempt to replace the dedicated reports for `.lake/config` invalidation, the artifact cache, or read-only/relocation behavior. Those subjects require more detailed validity, keying, or execution analysis. This report instead identifies which mutable locations belong to which package or workspace so those mechanisms can be reasoned about without treating `.lake` as a single workspace-global namespace.

## Findings

### The workspace directory is exactly the root package directory

`Workspace.dir` returns `Workspace.root.dir`, and `Workspace.lakeDir` returns `Workspace.root.lakeDir`. The workspace therefore has no independent filesystem root distinct from the root package. Workspace-root files are rooted through the root `Package`.

The workspace object separately holds all loaded packages, but adding a dependency package to `Workspace.packages` does not re-root that package's own paths. Each `Package` retains its own absolute `dir` and a `relDir` describing its location relative to the workspace.

Basis: **source** — `src/lake/Lake/Config/Workspace.lean`, `Workspace.dir` and `Workspace.lakeDir`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `src/lake/Lake/Config/Package.lean`, `Package.dir`, `Package.relDir`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`.

### The remote-package directory and manifest are workspace-root state

The root package's workspace configuration supplies `packagesDir`; its default is `.lake/packages`. `Workspace.pkgsDir` is `Workspace.root.pkgsDir`, so ordinary remotely materialized dependencies live beneath the root workspace by default.

Likewise, `Workspace.manifestFile` is the root package's manifest path. Its conventional name is `lake-manifest.json`. `Workspace.writeManifest` serializes the resolved entries to that root manifest. A dependency may have its own manifest which Lake reads while resolving inherited dependencies, but the top-level update operation writes the consolidated manifest for the current root workspace rather than rewriting every dependency's manifest.

Basis: **source** — `src/lake/Lake/Config/WorkspaceConfig.lean`, `WorkspaceConfig.packagesDir`, blob `e6074ad0e0b1f2660294a5771b34ce1d42d12e20`; `src/lake/Lake/Config/Defaults.lean`, `defaultPackagesDir` and `defaultManifestFile`, blob `03033b5a032e450540ad99cc7c3be73544ad7416`; `src/lake/Lake/Config/Workspace.lean`, `Workspace.pkgsDir` and `Workspace.manifestFile`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `src/lake/Lake/Load/Resolve.lean`, `addDependencyEntries` and `Workspace.writeManifest`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`.

### Git dependency source state is normally workspace-local and mutable

For a Git dependency, `Dependency.materialize` chooses a relative package directory under the workspace's `relPkgsDir`; with defaults, this is `.lake/packages/<assigned-name>`. `materializeGitRepo` clones there if the directory does not exist or updates the existing checkout otherwise.

Updating can check out a different revision, clean untracked files from tracked folders, delete and reclone a checkout when its URL changes on non-Windows hosts, and otherwise mutate the repository. Loading a manifest entry also clones or updates the workspace-local checkout when its recorded revision is not already present.

Thus a normal Git dependency is not immutable source owned elsewhere: its checkout is persistent mutable state owned by this workspace's materialization area. Two separate root workspaces using their default package directories normally receive separate Git checkouts and therefore separate package-local build/config state inside those checkouts.

Basis: **source** — `src/lake/Lake/Load/Materialize.lean`, `updateGitPkg`, `cloneGitPkg`, `updateGitRepo`, `materializeGitRepo`, `Dependency.materialize`, and `PackageEntry.materialize`, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`.

### Path dependencies keep their referenced directory; Lake does not copy them into the workspace package store

For a path dependency, `Dependency.materialize` computes the dependency directory from the declaring package's relative location plus the dependency path and returns that path as the materialized package. A locked manifest path entry is likewise resolved directly as `wsDir / relPkgDir`. There is no clone/copy step analogous to Git materialization.

This difference is the key ownership hazard for shared dependency universes. If two workspaces resolve the same physical path dependency, both `Package` values can point at that one directory. Any package-local mutable state described below is then shared unless configuration redirects it elsewhere or the operation is constrained not to write.

Basis: **source** — `src/lake/Lake/Load/Materialize.lean`, `Dependency.materialize` path case and `PackageEntry.materialize` path case, blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`; **derived** — because package-local paths are defined from the retained physical `Package.dir`, two package objects that resolve to the same directory name the same default mutable locations.

### Build state is package-local, not workspace-root state

`Package.buildDir` is `Package.dir / PackageConfig.buildDir`. The default `buildDir` is `.lake/build`. The same package object derives its Lean library, native library, executable, and intermediate directories from that build directory.

This applies to dependencies as well as the root package. A dependency loaded from `<dir>` therefore defaults to writing build products below `<dir>/.lake/build`; Lake does not redirect dependency outputs into the root workspace merely because the dependency is a member of that workspace.

`Package.clean` reinforces this ownership rule: it removes that package's `buildDir`, not a single workspace-wide build-output directory.

Basis: **source** — `src/lake/Lake/Config/PackageConfig.lean`, `PackageConfig.buildDir`, `leanLibDir`, `nativeLibDir`, `binDir`, and `irDir`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`; `src/lake/Lake/Config/Package.lean`, `Package.buildDir`, derived output-directory accessors, and `Package.clean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`.

### Lean module artifacts, traces, and hash sidecars inherit the package build directory

A `Module` derives `.olean`, `.ilean`, generated C/bitcode/object paths, and its `.trace` path from package-owned library/intermediate directories. Building modules can remove old outputs, write new outputs, write build traces, and create or clear `.hash` sidecars used to cache content hashes.

The important ownership conclusion is independent of the particular module facet: these mutable files live in the package's effective build directory. A shared path dependency with the default build directory therefore shares these files across consumers.

Basis: **source** — `src/lake/Lake/Config/Module.lean`, module output and trace path accessors, blob `f8b938e16fe53ada616364033b8d8353baa733ee`; `src/lake/Lake/Build/Module.lean`, module artifact removal, `.hash` caching, trace writing, and build operations, blob `21c5f343112a1690390188642a05d6092432ab84`; `src/lake/Lake/Build/Common.lean`, `BuildMetadata.writeFile`, `buildAction`, `buildFileUnlessUpToDate'`, and file-hash helpers, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`.

### Lean-authored configuration cache is also package-local at this revision

The package/workspace split is not limited to ordinary build products. At v4.30.0-rc2, a package's Lean configuration is compiled under that package's own `.lake/config/<assigned-name>/` directory. Dependency loading passes both the root workspace directory and the dependency's physical package directory, and the configuration loader uses the package directory for this cache.

That means a path dependency can be mutated before its normal Lean modules are built. The dedicated configuration-ownership and `.lake/config` reports cover the trace identity, invalidation, and locking rules; the ownership fact needed here is simply that the cache lives beneath the dependency package directory rather than the root workspace.

Basis: **source** — `src/lake/Lake/Load/Config.lean`, `LoadConfig.lakeDir`, blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`; `src/lake/Lake/Load/Resolve.lean`, `loadDepPackage`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`; `src/lake/Lake/Load/Lean/Elab.lean`, `importConfigFile`, blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`.

### `lake update` also owns selected root-workspace files outside `.lake`

Dependency update is not confined to `.lake`. `Workspace.updateToolchain` can rewrite the root package's `lean-toolchain` file when it selects a different toolchain, and `Workspace.writeManifest` writes the root `lake-manifest.json`.

A consumer that needs its source checkout to remain byte-for-byte immutable must therefore distinguish ordinary build/setup commands from update/reconfiguration operations. “Make `.lake` writable” is not by itself a complete write-isolation rule for `lake update`.

Basis: **source** — `src/lake/Lake/Load/Resolve.lean`, `Workspace.updateToolchain`, `Workspace.writeManifest`, and `Workspace.updateAndMaterialize`, blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`.

### The package-overrides file is root-workspace state

`Workspace.packageOverridesFile` is `<workspace lakeDir>/package-overrides.json`, where `workspace lakeDir` is the root package's `.lake`. It controls workspace-level automatic package overrides and is not stored in each dependency's package directory.

Basis: **source** — `src/lake/Lake/Config/Workspace.lean`, `Workspace.packageOverridesFile`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`.

### The local Lake cache is a third ownership domain

Lake's `Env` can select a cache through `LAKE_CACHE_DIR`, an Elan toolchain cache, or a system cache. `Workspace.computeLakeCache` uses that environment cache for the workspace; only when no appropriate environment cache exists does it fall back to `<root-package>/.lake/cache` (with a separate system-cache preference for bootstrap packages).

The cache contains artifact content and input-to-output mappings under its own directory. It is therefore neither the ordinary package build directory nor, in the common environment/toolchain-cache case, workspace-local state. Multiple local copies can intentionally share it.

This report does not characterize artifact-cache keying, publication/restoration, or concurrency. Those questions belong to the dedicated artifact-cache subject. The ownership fact is that “build outputs for a package” and “cache entries reusable across package copies” are different persistent stores.

Basis: **source** — `src/lake/Lake/Config/Env.lean`, `Env.computeCache?` and `Env.compute`, blob `eed315c538de746a891d18f72564e88aea64e969`; `src/lake/Lake/Config/Workspace.lean`, `computeLakeCache`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `src/lake/Lake/Config/Cache.lean`, `Cache.artifactDir`, `Cache.outputsDir`, and related path definitions, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`.

### The root workspace does not imply one shared build-output namespace

The workspace's aggregate search paths are assembled from its packages' individual binary/library/source directories. This is consistent with the underlying ownership model: a workspace coordinates multiple package-local build trees rather than assigning every package a subdirectory of one root build tree.

A prepared environment can therefore combine a writable root workspace with dependency build trees elsewhere, or conversely make a dependency source read-only and fail when Lake needs to configure/build it. Whether an arrangement works depends on the effective paths of every loaded package, not only on the permissions of the root `.lake` directory.

Basis: **source** — `src/lake/Lake/Config/Workspace.lean`, workspace `binPath`, `leanPath`, and `srcPath` accessors, blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `src/lake/Lake/Config/Package.lean`, package output path accessors, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`; **derived** — the workspace combines paths that remain rooted at their owning packages.

### Lake has no general build lock that makes a shared package build directory a serialized resource

`Lake.Util.Lock` documents an old build lock-file facility but states that Lake does not currently use a lock file; the prior build lock was removed. Build code independently writes or removes target files, `.trace` files, and `.hash` files. Some local-cache writes use create-if-new operations specifically to tolerate races, while configuration compilation has its own narrower locking protocol.

The source therefore does **not** justify treating a shared `<package>/.lake/build` as a process-serialized database. It establishes overlapping mutable filenames and the absence of a general build lock. It does not, by itself, establish that a particular pair of concurrent identical builds will corrupt artifacts or fail; some operations may be naturally idempotent or separately race-tolerant. That behavioral question requires execution probes for the commands and artifacts of interest.

Basis: **source** — `src/lake/Lake/Util/Lock.lean`, module documentation and lock helpers, blob `78f109574faedcfedd6d142ed51b5b700082aa63`; `src/lake/Lake/Build/Common.lean`, trace/hash/cache write paths including race-tolerant cache-file creation, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`; **derived** — no general serialization guarantee follows from narrower per-subsystem mechanisms.

### Practical isolation follows source ownership, not dependency graph membership

For the default layout, the source evidence yields this useful map:

| State | Default/effective owner | Typical location | Shared when two workspaces share one path dependency? |
| --- | --- | --- | --- |
| Root manifest | root workspace | `<root>/lake-manifest.json` | No, unless the roots themselves are shared |
| Root toolchain file updated by Lake | root workspace | `<root>/lean-toolchain` | No, unless the roots themselves are shared |
| Remote Git dependency clones | root workspace | `<root>/.lake/packages/<pkg>` | Normally no |
| Package overrides | root workspace | `<root>/.lake/package-overrides.json` | No, unless the roots themselves are shared |
| Package build outputs/traces/hashes | each package | `<pkg>/.lake/build/...` by default | **Yes** |
| Lean package-configuration cache | each package | `<pkg>/.lake/config/...` | **Yes** |
| Local Lake artifact cache | environment/toolchain/system cache, else root fallback | e.g. toolchain/system cache, or `<root>/.lake/cache` | Often intentionally shared; separate cache semantics apply |

The last column assumes both workspaces resolve the same physical path dependency directory. It does not apply to two independent Git clones that merely contain identical source bytes.

Basis: **derived** from the source-backed ownership rules above.

## Boundaries

- **No fresh execution.** This report did not run Lake against read-only trees or simultaneous processes. Filesystem write locations are established from exact source; particular failure modes and race outcomes are not.
- **Artifact-cache concurrency is separate.** The local cache is identified as a distinct ownership domain, but its keying, atomicity, publication/restoration, and multi-process behavior are not characterized here.
- **`.lake/config` validity is separate.** This report records that the cache is package-local. Its precise trace fields, invalidation predicate, and locking behavior belong to the dedicated configuration-cache report.
- **Custom paths change physical locations.** `buildDir` and `packagesDir` are configurable. The ownership rule remains: `Package.buildDir` is rooted at that package, while the workspace package store is rooted at the root package.
- **External scripts can write elsewhere.** Lake scripts, custom facets, external build systems, and tools invoked by package configuration can perform arbitrary I/O. This report inventories Lake's built-in state paths, not every path user code could mutate.
- **No claim of safe concurrent package builds.** Absence of a general build lock plus shared filenames is an isolation concern, not execution evidence that every concurrent build pair fails or corrupts output.
- **No post-v4.30 continuity claim.** The issue inventory separately calls out Lake configuration-ownership changes after this release. This report must be revalidated rather than projected to v4.31 or later.

## Evidence

Primary source was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), inspected on 2026-09-26.

Relevant immutable source locations:

- `src/lake/Lake/Config/Package.lean` — blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`; `Package.dir`, `lakeDir`, `pkgsDir`, `manifestFile`, `buildDir`, output-directory accessors, `clean`.
- `src/lake/Lake/Config/Workspace.lean` — blob `b9c01f130240ae7c65ee298778351ddbe312374e`; `computeLakeCache`, `Workspace.dir`, `lakeDir`, `pkgsDir`, `manifestFile`, `packageOverridesFile`, aggregate search paths.
- `src/lake/Lake/Config/WorkspaceConfig.lean` — blob `e6074ad0e0b1f2660294a5771b34ce1d42d12e20`; `WorkspaceConfig.packagesDir`.
- `src/lake/Lake/Config/Defaults.lean` — blob `03033b5a032e450540ad99cc7c3be73544ad7416`; `defaultPackagesDir`, `defaultManifestFile`.
- `src/lake/Lake/Config/PackageConfig.lean` — blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`; package build/output directory configuration and artifact-cache options.
- `src/lake/Lake/Config/Module.lean` — blob `f8b938e16fe53ada616364033b8d8353baa733ee`; module artifact and trace paths.
- `src/lake/Lake/Load/Materialize.lean` — blob `e098e5adbbf33a641fa5cf7d37d0bbd371956f4b`; Git clone/update and direct path-dependency materialization.
- `src/lake/Lake/Load/Resolve.lean` — blob `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`; dependency loading, inherited manifest entries, package-directory migration, root toolchain update, root manifest write.
- `src/lake/Lake/Load/Workspace.lean` — blob `9f25dd62bc752ede695a25fc20371157eb65d64b`; full-workspace loading and update/materialization entry points.
- `src/lake/Lake/Load/Config.lean` — blob `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`; package-local Lake directory during package configuration.
- `src/lake/Lake/Load/Lean/Elab.lean` — blob `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`; compiled Lean configuration cache paths and writes.
- `src/lake/Lake/Build/Module.lean` — blob `21c5f343112a1690390188642a05d6092432ab84`; module build outputs, traces, and `.hash` sidecars.
- `src/lake/Lake/Build/Common.lean` — blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`; generic artifact, trace, hash, and local-cache writes.
- `src/lake/Lake/Config/Env.lean` — blob `eed315c538de746a891d18f72564e88aea64e969`; environment/toolchain/system cache selection.
- `src/lake/Lake/Config/Cache.lean` — blob `607e6b92108f30e0a57d0de682f7faa283d7d470`; local cache directory structure.
- `src/lake/Lake/Util/Lock.lean` — blob `78f109574faedcfedd6d142ed51b5b700082aa63`; explicit statement that Lake no longer uses the historical general build lock.

No execution artifacts are included because this investigation did not run Lake.

## Revalidation

For another Lake revision, first diff the small ownership-defining surface before repeating broader archaeology:

1. Check `Package.buildDir`, `Package.lakeDir`, `Workspace.pkgsDir`, `Workspace.manifestFile`, and `Workspace.computeLakeCache`.
2. Check `Dependency.materialize` and `PackageEntry.materialize` to see whether path dependencies remain direct references and where Git dependencies are cloned.
3. Check package-configuration loading to determine whether dependency configuration caches still live under the dependency package directory.
4. Check module/output path accessors and generic build helpers to determine whether build artifacts, traces, and hash sidecars remain package-local.
5. Check update code for root manifest and `lean-toolchain` writes.
6. Check whether a new cross-process build-locking mechanism has been introduced.

A compact execution probe can then validate the source-derived filesystem model:

- create two minimal root workspaces that both `require` the same path dependency;
- snapshot the shared dependency tree and each root before any Lake command;
- run workspace loading/setup and a build separately, recording every changed path;
- repeat with the dependency read-only to identify the first required package-local write;
- run the two consumers concurrently with private roots but the same dependency directory, and record failures plus final trace/hash/artifact bytes;
- repeat with distinct dependency copies to distinguish workspace interaction from ordinary package-local mutation;
- if artifact caching is enabled, place `LAKE_CACHE_DIR` in a separately monitored directory so cache writes are not mistaken for package-build writes.

That probe would establish concrete command-level behavior. It should not be replaced by merely checking that one prebuilt tree happens to work once: the important invariant is which paths Lake is permitted or required to mutate for each operation and whether concurrent consumers can do so safely.