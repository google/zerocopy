# Findings

## 1. Relative manifest path entries move with the workspace

Lake's manifest model represents a path dependency as a path relative to the package directory containing the manifest. During materialization, Lake joins that stored relative path to the current workspace directory. The dependency configuration model uses the same rule for declared path dependencies.

This gives Lake a relocation-friendly dependency identity at the manifest layer: if a prepared workspace and dependency tree move together while preserving the relative topology encoded in `lake-manifest.json`, Lake can resolve the same path packages from the new root. Anneal V1 uses this property when it rewrites the installed Aeneas archive's manifest entries into paths relative to a fresh generated workspace.

This result is narrower than whole-environment relocation. Build traces, generated setup files, native artifacts, package configuration, environment-dependent options, and other build inputs can still invalidate prepared outputs after a move. The source facts here establish how path dependencies are located, not that every compiled artifact is path-independent.

## 2. A complete manifest separates locked consumption from mutating dependency update

Ordinary `loadWorkspace` has two materially different paths. When `lake-manifest.json` exists and dependency updates were not requested, Lake calls `materializeDeps` using the locked entries. When the manifest is missing, it calls `updateAndMaterialize` instead.

The update path is allowed to create or replace dependency state and to write a new manifest. Toolchain-update paths can also update `lean-toolchain`. A read-only prepared environment therefore should not depend on Lake reconstructing missing dependency state on first use.

The historical Anneal V1 work reached the same boundary from execution: PR #3450 records that without a root manifest Lake reconfigured path dependencies and attempted writes in read-only package configuration trees. The resulting design generated a complete relative manifest before consumption.

For Anneal, the practical rule is simple: if a prepared dependency universe is supposed to be immutable at verification time, record enough manifest state that ordinary loading stays on the locked materialization path. Do not rely on Lake to infer or update that state inside the immutable tree.

## 3. Locked Git checkouts can avoid fetches, but missing or mismatched checkouts cannot

For a Git entry from a manifest, Lake first checks whether the expected repository directory exists. If it exists and its current HEAD is exactly the manifest's locked revision, Lake checks for a local diff and does not fetch. The source comment explicitly identifies offline operation as a reason for this fast path.

If the repository is absent, Lake clones it. If the repository exists at a different revision, Lake updates it, which can fetch from the configured remote before checkout. Dependency resolution outside an already-complete manifest can also consult Reservoir.

This means offline dependency consumption is state-dependent. A locked manifest plus already-materialized exact-revision checkouts can avoid dependency network access. A manifest alone cannot: it still permits clone/fetch when the locked source is missing or stale.

Anneal V1 eventually converted transitive Lean dependencies into filesystem-local Git remotes. That did not make Lake stop cloning; it changed the clone/fetch source from the internet to a local filesystem source. This is a useful distinction for prepared toolchains: local source materialization can preserve Lake's Git semantics while removing network dependence.

## 4. `--offline` does not make ordinary `lake build` offline at this revision

The Lake CLI parses an `offline` option. However, `LakeOptions.mkLoadConfig` does not include that field, and the ordinary `build` command constructs `LoadConfig`, calls `loadWorkspace`, and then runs the build. By contrast, `new` and `init` pass `opts.offline` directly to their initialization functions.

Therefore `lake build --offline` is not, at v4.30.0-rc2, a general switch that prevents dependency or artifact network access.

`LAKE_NO_CACHE` / `--no-cache` is different again. Lake documents that setting as disabling build-cache downloads. It does not disable Git clone/fetch or Reservoir access. Treating it as a global network-denial mode would conflate artifact-cache policy with dependency resolution.

A strong offline claim for Anneal must instead be established from the complete prepared state plus an execution probe that denies network access and verifies that no network attempt occurs.

## 5. A read-only dependency tree works only if the chosen path needs no package-local writes

Lake writes more than compiled outputs. At this revision, ordinary build machinery may create or update:

- `lake-manifest.json` and dependency materialization state on the update path;
- package build products and generated setup files;
- `.trace` metadata after successful build actions;
- adjacent `.hash` files when hashes are missing or not trusted;
- restored artifacts copied or hard-linked from the artifact cache into package build directories; and
- cache output mappings when the package/cache configuration permits writes.

Even a command intended only to reuse prepared outputs can therefore fail against a read-only package if some trace, hash, package configuration, or build result is considered stale or missing.

The historical Anneal V1 archive contract made this explicit. Its regression test asserts that every non-symlink path below the installed Aeneas archive lacks write bits. It then consumes that archive from a separate writable generated workspace. V1 also runs the build with `--old`; PR #3450 records that old mode alone was insufficient when input mtimes were too fresh, so the archive preparation was changed to make inputs older than prebuilt artifacts and to prime or rewrite other cache/trace state.

The important lesson is not “use `--old`.” It is that read-only consumption is a theorem about a specific prepared state and command path. Every fallback that writes or rebuilds must be excluded.

## 6. Lake's artifact cache separates some shared immutable artifacts from local package builds

Lake's package configuration distinguishes artifact-cache reads from artifact-cache writes. With no explicit `enableArtifactCache` setting, packages can read the local artifact cache by default but do not write to it by default. `restoreAllArtifacts` defaults to false.

The cache stores artifacts by content hash. When saving an artifact, Lake makes the local/cache copy read-only where possible. Competing cache creators are handled narrowly: cache insertion uses hard links with `alreadyExists` tolerance or “write if new” helpers. Some cache-map files are protected by shared/exclusive file locks.

These mechanisms support a useful architecture for many independent workspaces: prepopulate a cache, expose it read-only for consumers, and keep mutable package/workspace state separate. Anneal V1 moved in this direction specifically to avoid per-test clones; PR #3305 records that the prior clone-pool design could consume roughly 100 GB with around 100 parallel worker threads.

The cache does not eliminate all local writes. A cache hit may still cause Lake to write a fetch trace, restore an artifact into a package-local path, or write a `.hash` file. A missing cached artifact may trigger a remote cache-service download when the cached output metadata names a service. Cache availability therefore must be tested together with the package-local state and command being used.

## 7. Lake has no global lock that serializes concurrent builds

`Lake.Util.Lock` is unusually direct: Lake does not currently use a lock file. The source explains that an earlier build lock was removed because interruption made the lock too disruptive.

This makes the concurrency boundary important. Lake has local synchronization mechanisms, but there is no process-wide guarantee that two `lake` processes mutating the same workspace or build tree are serialized. The content-addressed artifact cache handles several creator races, and cache-map file operations can lock individual files. Those facts are not a general concurrent-writer protocol for manifests, dependency checkouts, trace files, package build directories, or all cache output files.

A design with concurrent Anneal workers should therefore prefer **concurrent readers of immutable prepared state plus private writable workspaces**. If several processes must write the same Lake state, that sharing needs a separate proof or an outer coordination mechanism tailored to the exact files involved.

## 8. Preserved Anneal V1 tests establish one read-only prepared-archive design, not a universal Lake guarantee

Current `google/zerocopy` still contains the V1 regression test introduced by the historical archive work. The test:

1. resolves the installed toolchain archive;
2. asserts that the Aeneas archive tree has no write bits;
3. creates a fresh writable generated workspace;
4. writes a Lakefile requiring Aeneas from the installed archive;
5. writes a complete manifest whose Aeneas and transitive package entries are relative to the generated workspace;
6. runs `lake --keep-toolchain --old build Generated`; and
7. runs `lake --keep-toolchain env lean --json generated/Generated.lean`.

The checked-in test is strong evidence about the intended V1 contract and about regressions that V1 maintainers considered important. PR #3453 says the purpose was specifically to catch read-only archive/cache reuse regressions.

It is not fresh execution evidence for this report. The test's actual toolchain archive, build environment, mtimes, cache contents, operating system, and historical Lake revision matter. The current report therefore uses the test as preserved historical evidence and requires a fresh exact-pin probe before promoting the behavior to a v4.30.0-rc2 guarantee.

## 9. Relocation, read-only use, offline use, and concurrency should be tested independently

The source model shows why a single “prepared Lake environment works” test is too coarse.

- **Relocation** can fail because a path or trace embeds an old root even when every file is present.
- **Read-only use** can fail because Lake wants to refresh a hash, trace, manifest, checkout, or restored artifact even when no network is needed.
- **Offline use** can fail because a dependency or cache artifact is missing even when all local paths are writable.
- **Concurrency** can fail because two writers target the same mutable state even when one writer succeeds alone.

Anneal should keep these dimensions separate in its regression suite. A prepared-toolchain contract is easier to reason about when each test changes one axis and records the exact filesystem/network effects.