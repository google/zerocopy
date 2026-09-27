# What Lake's artifact cache does not cache at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake's artifact cache is **not** a snapshot of a package, workspace, build directory, or process state. It stores only outputs that a cache-aware build path explicitly serializes into artifact descriptions and associates with an input hash. Other Lake state can still be required for a successful build or reuse path.

Several important classes sit outside that contract. Source files and configuration inputs are traced as inputs rather than copied into the artifact store. Package dependency source trees are managed through Lake's package/dependency machinery, not by the per-target artifact cache. Ordinary `.trace` and `.hash` sidecars are local build metadata rather than independently recoverable artifact-cache entries, even though some higher-level archives can intentionally package trace state. Lake also has local-only build helpers: for example, the built-in shared-library facet for an `extern_lib` uses `buildFileUnlessUpToDate'`, not the artifact-cache-aware wrapper. Package build archives from Reservoir or GitHub releases are another separate reuse channel.

The built-in Lean-module path illustrates the narrower positive boundary. Its cacheable output set includes `.olean`, `.olean.server`, `.olean.private`, `.ilean`, IR, generated C, optional bitcode, and an optional `.ltar` archive. When a module cache hit is used, Lake may restore only the artifacts that must exist at conventional build paths. Files used only to set up or drive the build are not automatically part of that cached output set.

For Anneal, the practical consequence is that seeding `LAKE_CACHE_DIR` cannot by itself reconstruct an arbitrary prepared Lake tree. A cache-dependent workflow must separately account for sources, manifests/configuration, package materialization, local metadata or archives needed by the selected path, and any uncached target products. Cache completeness is target-specific, not workspace-wide.

## Applicability

This report covers Lake as shipped in Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

"Artifact cache" means the Lake content-addressed artifact store plus its package-scoped input-to-output mappings, as described by the adjacent `lake-artifact-cache-architecture-v4-30-0-rc2` candidate. "Does not cache" means a file or state class is not automatically preserved as an output of that artifact-cache mechanism merely because Lake uses it during a build.

This report does not claim that an excluded file can never appear inside some other cached archive. In particular, module `.ltar` archives intentionally package a trace file alongside module artifacts. The distinction is between **standalone artifact-cache coverage** and **incidental inclusion inside a separately cached compound artifact**.

The report also separates Lake's artifact cache from Lake's package build-archive mechanism. A Reservoir barrel or GitHub release build archive can repopulate a package build directory, but that is a different protocol with different identifiers, paths, and freshness logic.

Evidence is exact pinned source plus an adjacent durable architecture candidate used to delimit terminology. No fresh Lake or Lean execution was performed.

## Findings

### Only cache-aware build paths participate

The core local helper `buildFileUnlessUpToDate'` implements ordinary local freshness. It compares the current dependency trace with a neighboring `.trace` file, builds the target when necessary, and records file hash/trace metadata. It does not consult Lake's artifact output mappings or save the result into the content-addressed artifact store.

`buildArtifactUnlessUpToDate` is the cache-aware wrapper. When artifact-cache use is enabled, it queries the package-scoped input-to-output mapping, resolves an artifact, and can save a newly built file through `Cache.saveArtifact`. Otherwise it falls back to `buildFileUnlessUpToDate'`.

The distinction means "Lake built this file" does not imply "the artifact cache can reproduce this file." Participation is a property of the chosen build helper and output serialization.

Basis: **source** in `Lake.Build.Common`.

### A built-in external shared-library path is local-only

`buildLeanSharedLibOfStatic`, used by the built-in `ExternLib.sharedFacet`, constructs a dynamic library from a static library. It adds the Lean trace, selected arguments, and platform trace, then calls:

```lean
buildFileUnlessUpToDate' dynlib do
  ...
  compileSharedLib dynlib args lean.cc
```

That path uses ordinary local `.trace`/`.hash` freshness rather than `buildArtifactUnlessUpToDate`. The resulting shared library is therefore a concrete built-in example of an output that is not automatically inserted into or recovered from the per-target artifact cache through this facet.

This is narrower than saying "shared libraries are uncached." Other shared-library builders in `Lake.Build.Common` do use the artifact-cache-aware wrapper. Cache coverage depends on the exact target/facet path.

Basis: **source** in `Lake.Build.ExternLib` and `Lake.Build.Common`.

### Source files are traced inputs, not artifact-cache outputs

Lake represents source/data files with input jobs such as `inputTextFile`, `inputBinFile`, and `inputFile`. Those jobs compute a `BuildTrace` from the existing file and propagate the trace to dependent jobs. They do not call `Cache.saveArtifact` merely because a file is an input.

This is expected: the artifact cache maps a build-input identity to outputs. It does not serve as a general source-content store for every input used to derive that identity.

As a result, a cache hit does not by itself materialize a missing source checkout. A workflow that needs Lake to discover modules, resolve package configuration, or otherwise read source/config files must make those inputs available separately unless the selected cached artifact path has eliminated that need.

Basis: **source** in `Lake.Build.Common`; the workflow consequence is **derived**.

### Package dependency source materialization is a separate subsystem

Lake's package build logic has a distinct concept of a **package build archive**. For dependencies, `maybeFetchBuildCache` can fetch a Reservoir barrel or GitHub release archive when configured and unpack it into the package build directory.

`Package.fetchBuildArchive` uses ordinary `buildUnlessUpToDate?` state for the downloaded archive and then untars it into `self.buildDir`. This path does not use the local per-target artifact-cache output mapping.

Similarly, a package's dependency source checkout is managed by Lake's dependency/package materialization machinery rather than by the artifact cache. The artifact cache can reuse products *after* an applicable target identity is known; it is not a replacement for the package source/store layer.

For Anneal, this distinction matters when asking whether an offline or read-only run can rely on a seeded artifact cache. Missing package source state may still force package-resolution/materialization work even if matching compiled artifacts exist elsewhere.

Basis: **source** in `Lake.Build.Package`; the dependency-source implication is **derived** and should be combined with the separate source-materialization report when available.

### Local `.trace` and `.hash` sidecars are not general standalone cache entries

Lake writes `.trace` files beside ordinary targets and `.hash` sidecars beside files whose content hashes it has cached locally. Those files support freshness checks and avoid repeated hashing.

The generic artifact store does not automatically save every `.trace` or `.hash` sidecar as an independent content-addressed output. On a normal artifact-cache hit, Lake resolves the output artifact description, and restoration writes the target file plus a `.hash` sidecar for the restored content.

Module handling adds an important exception. `Module.packLtar` deliberately includes the module trace file in the `.ltar` archive together with module artifacts. When Lake later unpacks such an archive, it can read that reconstructed trace to resolve the module outputs. The trace is recoverable there because a higher-level compound artifact explicitly included it, not because `.trace` files are globally cached.

This distinction should prevent two opposite mistakes: deleting all local trace state on the assumption that the artifact store contains it independently, or assuming no cache path can ever restore trace state.

Basis: **source** in `Lake.Build.Common` and `Lake.Build.Module`.

### The Lean-module cache has an explicit output inventory

The module builder's `ModuleOutputArtifacts` covers a defined set of products. At this revision the source computes artifact descriptions for:

- `.olean`;
- `.olean.server` when the input is a module;
- `.olean.private` when the input is a module;
- `.ilean`;
- generated IR when applicable;
- generated C;
- bitcode when the LLVM backend is available; and
- optionally an `.ltar` archive.

`Module.cacheOutputArtifacts` and `Module.packLtar` operate on that set. The setup files, source files, package manifest/configuration, and arbitrary files that happen to coexist in the package build tree are not added merely because they are nearby.

A module cache hit can also restore only the subset required at conventional build paths. `restoreNeededArtifacts` restores the `.ilean` while other cached products may remain referenced by their cache paths. `restoreAllArtifacts` is a separate placement choice.

The module path is therefore evidence against treating `.lake/build` as the unit of caching. Lake caches a typed output set selected by the target implementation.

Basis: **source** in `Lake.Build.Module`.

### Module setup/intermediate state can be local-only even when module outputs are cacheable

The module build contains local setup and IR-control files used to prepare compilation. For example, the Lean-IR setup path uses `buildUnlessUpToDate?` with `mod.irFile`, writes `mod.irSetupFile`, and tracks its own local trace/freshness state.

Separately, the final module output set can be represented as cacheable `ModuleOutputArtifacts`.

This split matters operationally: target outputs can be cacheable while setup/control state used to build them is not itself part of the artifact-cache output mapping. If Lake can satisfy the target directly from the cache, the local setup path may not need to run. If it cannot, having the cache populated does not guarantee that all local setup state needed for a rebuild has been preserved.

Basis: **source** in `Lake.Build.Module`; the control-flow consequence is **derived**.

### Package build archives are not the same thing as the artifact cache

Lake's `Package.maybeFetchBuildCache` terminology is easy to conflate with the artifact cache. It can download a prebuilt package archive from Reservoir or a GitHub release and unpack the archive into the package's build directory. The URL can depend on package revision and Lean toolchain.

That mechanism is distinct from:

```text
<lake-cache>/outputs/<package-scope>/<input-hash>.json
<lake-cache>/artifacts/<content-hash>.<ext>
```

used by the local artifact cache. A package build archive may contain broad build-tree state that the per-target artifact cache does not. Conversely, an artifact-cache entry can exist without a package release/barrel archive.

Anneal should therefore name these channels separately in diagnostics and prepared-state contracts. "Cache present" is ambiguous unless it says which cache.

Basis: **source** in `Lake.Build.Package`, `Lake.Config.Cache`, and **derived** comparison.

### The artifact cache does not preserve the workspace/package control plane

Workspace manifests, dependency declarations, package configuration, override state, package stores, and toolchain-discovery state participate in deciding *what* Lake will build and *where* it will find dependencies. The artifact cache stores output mappings and content-addressed output bytes; it does not serialize the whole loaded `Workspace`/`Package` graph as an artifact-cache entry.

That means the cache cannot be treated as a self-describing build environment. Lake still needs enough control-plane state to select a package, target/facet, dependency graph, configuration, and input hash before it can ask whether a matching output mapping exists.

Some of that state can be captured by other Lake mechanisms, and some build products can be reached without replaying every ordinary preparation step. The important boundary is that no generic artifact-cache operation reconstructs the complete workspace model from cached artifact bytes.

Basis: **derived** from `Lake.Config.Workspace`, `Lake.Config.Package`, and the cache lookup API; use the separate package/source-materialization reports for exact preparation requirements.

### Arbitrary custom targets are not automatically cacheable

The artifact-cache primitives are reusable, but custom target code chooses what helpers to invoke and what outputs to serialize. A custom target that only uses `buildUnlessUpToDate?`, `buildFileUnlessUpToDate'`, raw `IO`, or another local mechanism does not become artifact-cache-aware just because the package has artifact-cache reading enabled.

Conversely, custom code can explicitly use cache-aware primitives and output descriptions.

This is why a package-level setting such as artifact-cache readability is a permission/policy boundary rather than a declaration that every target has a cache representation.

Basis: **source** from the generic build/cache helper separation; custom-target consequence is **derived**.

### A seeded artifact cache is not equivalent to a prepared build tree

Combining the boundaries above yields a useful Anneal rule. A seeded artifact cache may supply many expensive module/native outputs, but it does not by itself establish the presence of:

- source and package configuration needed to resolve the build;
- dependency source/checkouts or package-store state;
- every local `.trace`/`.hash` sidecar;
- local-only target/facet outputs;
- setup/control files needed when a cache miss forces rebuilding;
- workspace manifest/override state; or
- package build archives from the separate Reservoir/release mechanism.

Which of these are required depends on the exact build path. If an artifact cache hit occurs before some local preparation path, that state may be unnecessary for that invocation. If a miss occurs, the missing non-cached state can become observable immediately.

Therefore a prepared Anneal environment should validate the selected **consumer path**, not merely count cache files.

Basis: **derived** synthesis from the pinned source.

## Boundaries

**No fresh execution.** This report did not run Lake, Lean, or Anneal. It establishes source-level coverage boundaries and concrete local-only paths but does not enumerate filesystem accesses of an actual cache-hit run.

**Not an exhaustive negative enumeration.** Lake is extensible. Custom targets and facets can use arbitrary build logic. This report identifies the governing mechanism and representative built-in exclusions rather than proving a closed world of every uncached file.

**Module archives can carry otherwise-local metadata.** The `.ltar` path explicitly includes the module trace file. Statements about traces being outside the artifact cache mean they are not generically stored as standalone artifact-cache outputs.

**Package build archives are separate.** This report distinguishes them from the artifact cache; it does not fully specify Reservoir/GitHub archive formats or publication policy.

**Source materialization is adjacent.** The artifact cache does not substitute for dependency source management, but the exact conditions under which Lake clones, fetches, or can consume an already-materialized checkout are separate inventory work.

**No claim that all native outputs are uncached.** The `ExternLib.sharedFacet` is a concrete local-only shared-library path, while other shared-library/object/executable builders use cache-aware helpers.

**No claim that a cache hit requires all ordinary local state.** A successful hit can bypass rebuild/setup work. The point is that the artifact cache does not itself preserve that state if a later miss or alternate target needs it.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27 against `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: local-only freshness helpers, artifact-cache-aware wrapper, input-file jobs, hash/trace sidecars, artifact restoration.
- `src/lake/Lake/Build/ExternLib.lean`, blob `9ed94d229d3ca5d41173941e157d31f9b9f6b814`: built-in `ExternLib.sharedFacet` path through `buildFileUnlessUpToDate'`.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: explicit module output-artifact set, cache/restore path, `.ltar` packing including trace state, module setup/local-control paths.
- `src/lake/Lake/Build/Package.lean`, blob `2f55a2a5fde4280b2b61945f88c4e0b31d1b0ce3`: separate package build-archive fetch/unpack path and dependency extra-target integration.
- `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`: artifact content identity.
- `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`: artifact store and package-scoped output mappings.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: package/build/cache scope and package state.
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: workspace/package/cache organization.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: environment-selected Lake cache and toolchain/cache state.

The adjacent durable candidate `5a2f45ab-5124-4cc2-9a11-a9266e7ce215` for Lake artifact-cache architecture was used to preserve terminology and avoid redoing its broader architecture research. The negative-boundary claims above were rechecked against the pinned source.

Evidence roles are **source** and **derived**. No fresh **execution** evidence was produced.

## Revalidation

For another Lake revision, begin with the helper boundary rather than searching for cache-directory paths:

1. inspect `buildArtifactUnlessUpToDate` and the ordinary local freshness helpers;
2. find every built-in caller that goes through an artifact-cache-aware helper;
3. inspect custom output serializers such as `ModuleOutputArtifacts`;
4. identify built-in paths that remain on `buildFileUnlessUpToDate'`, `buildUnlessUpToDate?`, or raw build logic;
5. compare package build-archive/release machinery with the per-target artifact-cache code;
6. inspect whether trace/hash metadata has become independently cacheable.

For this exact revision, the strongest execution probe is a **cache-only consumer matrix**. Build a small package once with artifact-cache writes enabled, preserve the cache, and create new consumer roots that delete one state class at a time:

- source files;
- `lake-manifest.json` / package configuration;
- dependency source checkout;
- target `.trace` files;
- `.hash` sidecars;
- module setup/control files;
- conventional build outputs;
- `ExternLib.sharedFacet` output.

Run narrowly selected targets under verbose Lake output and record whether each case is a cache hit, local replay, rebuild, source-resolution failure, or missing-local-output failure. Repeat the module case with both individual cached artifacts and an `.ltar`-only cache entry.

A second fixture should compare the same package with a Reservoir/GitHub package build archive available versus only the local artifact cache available. Preserve exact filesystem manifests before and after each run. That evidence would establish which non-cached state Lake actually requires on the Anneal consumer path rather than only what the source makes possible.
