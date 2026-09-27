# Lake artifact-cache architecture at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake's artifact cache has two distinct local layers:

1. a content-addressed artifact store, where an artifact is identified by its content hash plus extension and normally lives under `artifacts/{hash}.{ext}`; and
2. an input-to-output mapping store, where a package-scoped build input hash maps to structured JSON that names one or more artifact descriptions under `outputs/<package-scope>/<input-hash>.json`.

The build system uses the current dependency trace's hash as the lookup key. A cache hit resolves the stored output descriptions to content-addressed artifacts. A build that is permitted to populate the cache can save newly built files into the artifact store and write the corresponding input-to-output mapping. This is separate from the ordinary per-target `.trace` file: a saved trace can itself carry output descriptions, and Lake can use those descriptions to reconstruct a missing cache mapping.

Cache readability and writability are deliberately different defaults. When no package or workspace override is set, `Package.isArtifactCacheReadable` is `true` while `Package.isArtifactCacheWritable` is `false`. This lets a package consume an existing shared cache without silently growing it. In the non-writable path, a cache hit is restored into the package's normal build location; in the writable path, Lake can return the cache-resident artifact directly unless restoration is explicitly requested.

The local cache can also carry remote-origin metadata. A cached output may name a cache service and remote scope; if the content-addressed file is missing locally, `resolveArtifact` can download it, verify its content hash, and then use it. Thus the architecture separates build identity, output descriptions, local artifact bytes, and remote transport metadata rather than treating a cache entry as one opaque archive.

No fresh Lake or Lean execution was performed. These findings come from exact pinned Lake source. Runtime performance, filesystem-specific hard-link behavior, cache concurrency under real contention, and remote service behavior remain execution questions.

## Applicability

The findings apply to Lake as shipped in Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

"Input hash" means the hash of the current Lake dependency trace at the point where `buildArtifactUnlessUpToDate` performs the cache lookup. "Artifact description" means `ArtifactDescr`, which contains a content hash and extension. "Artifact" means the runtime `Artifact` value, which adds a preferred filesystem path, display name, and modification time. "Output mapping" means the package-scoped mapping from input hash to structured output JSON.

This report describes the architecture that ties those pieces together. Separate inventory items should answer the exact semantics of `LAKE_ARTIFACT_CACHE`, `LAKE_CACHE_DIR`, cache keys, publication/restoration, concurrent writers, and which build products participate in the cache. This report uses those mechanisms only where needed to explain the architecture.

## Findings

### The cache separates build-input identity from artifact-content identity

`ArtifactDescr` contains two fields: a Lake `Hash` over artifact contents and a file extension. Its cache-relative path is `{hash}.{ext}`. The serialized artifact description is that relative path, not the runtime filesystem path.

`Artifact` extends the description with a preferred `path`, a human-facing `name`, and an `mtime`. This distinction lets the same content identity be represented either by the content-addressed file inside Lake's cache or by a restored file in a package build directory.

The input side is stored separately. `Cache.outputsFile` places a mapping at:

`outputs/<scope>/<input-hash>.json`

and `Cache.writeOutputs` writes structured output data there. The cache therefore does not infer which artifact belongs to a build input by scanning artifact filenames. The input hash selects an output description; that description selects content-addressed artifact bytes.

Basis: **source**.

### Lake's core artifact-build path looks up by the current dependency-trace hash

`buildArtifactUnlessUpToDate` captures the current `depTrace` and defines `inputHash := depTrace.hash`. Cache lookup then calls `getArtifacts? inputHash savedTrace pkg`.

`getArtifacts?` first tries the package-scoped local input-to-output mapping. If that does not yield usable outputs, it tries output descriptions stored in the target's saved trace file. A matching saved trace therefore serves two roles: ordinary build freshness metadata and a possible source of artifact descriptions.

If Lake recovers outputs from a saved trace and the package is allowed to write the artifact cache, it writes those outputs into the local input-to-output mapping. This can repair or seed the mapping layer without rebuilding the underlying target.

Basis: **source**.

### Saving an artifact is content-addressed and race-tolerant at the artifact-file layer

`Cache.saveArtifact` hashes the file, derives the artifact description, and targets `cache.artifactDir / descr.relPath`. Binary artifacts are hashed as raw bytes. Text artifacts are normalized from CRLF to LF before hashing and caching.

For binary files Lake first tries to hard-link the built file into the cache. If that fails for a reason other than an already-created destination, it falls back to a race-tolerant create using the bytes it already read. Text artifacts use a corresponding write-if-new path. The implementation explicitly anticipates another process racing to create the same content-addressed destination.

Lake also makes source and cached files unwritable where possible. The source comments explain the reason: a hard-linked local file that remains mutable could corrupt the shared cache.

After saving, the returned `Artifact.path` normally points at the cache file. With `useLocalFile`, the returned artifact retains the local build path while preserving the same content identity.

Basis: **source**.

### Read and write policy have different defaults

`Package.isArtifactCacheReadable` resolves package configuration, then workspace configuration, and defaults to `true`. `Package.isArtifactCacheWritable` follows the same override chain but defaults to `false`.

The package configuration documentation states the intended policy: absent overrides, a package can use artifacts from the cache but cannot write to it. The same configuration also warns that targets using the artifact cache may not leave their products at the traditional build-directory path.

This difference is visible in `buildArtifactUnlessUpToDate`:

- In the writable path, Lake tries the cache first. If it must build and the result is cacheable, it saves the artifact and writes the input-to-output mapping.
- In the non-writable path, Lake first accepts an ordinary up-to-date local result. Otherwise, if reading is enabled, it may fetch a matching cache entry before building.

The non-writable cache-hit path requests restoration into the target's normal local path. The writable path can instead use the cache-resident path directly unless the caller or package asks for restoration.

Basis: **source**.

### Restoration is a separate operation from cache lookup

`restoreArtifact` makes a cached artifact available at a requested local path. If the local file is absent, Lake first tries a hard link from the cache and falls back to copying. It writes a `.hash` sidecar for the restored file and returns the same artifact identity with the preferred path changed to the local file.

`restoreAllArtifacts` is therefore not a second cache: it is a placement policy for bytes already identified by the artifact cache. The default is `false`. A project that needs conventional build-directory paths can ask Lake to restore cache hits there.

Basis: **source**.

### The normal local mapping stores structured outputs, not only single files

Lake's `CacheOutput` wraps arbitrary output JSON together with optional remote-cache service and scope metadata. `ResolveOutputs` turns that structured data back into the output type expected by a build target. `CacheMap.collectOutputDescrs` recursively walks arrays and objects to recover all embedded artifact descriptions.

This design allows a single build input to describe compound outputs rather than requiring a one-file cache model. It also explains why `ToOutputJson Artifact` serializes only the artifact description: runtime paths and mtimes are reconstructed when Lake resolves the output.

The exact JSON shape is target-dependent. Custom output types can serialize structure that is not an artifact at all, including booleans and nested objects. The cache architecture supplies the mapping and artifact primitives; it does not require every cached target to have one flat file result.

Basis: **source**.

### Missing local bytes can be recovered through remote-origin metadata

`resolveArtifact` computes the expected local content-addressed path from the artifact description. If the file exists, Lake returns it with its current modification time. If it is absent and the cached output carries both a cache service and scope, Lake resolves the configured service and downloads the artifact.

The download path verifies the bytes against the expected content hash. A mismatch is reported and the downloaded file is removed. Successfully downloaded artifacts are made read-only where possible before use.

A local output mapping can therefore act as an index to a remote artifact, but only when the mapping contains the service/scope provenance required to locate it. A purely local mapping without remote metadata fails closed when its content-addressed file is missing.

Basis: **source**.

### The cache root is selected independently of a package's build directory

A `Cache` is structurally just a root directory. `Workspace.computeLakeCache` chooses the environment-provided cache when available; otherwise it falls back to the package's `.lake/cache`. The environment loader lets `LAKE_CACHE_DIR` provide an explicit cache root; without it, Lake can select an Elan toolchain cache or a system cache.

This separation is what permits artifacts to be shared across local copies of packages. It also means that a cache-resident artifact path is not generally a path inside the current package build directory.

The exact cache-root precedence and empty-`LAKE_CACHE_DIR` behavior are separate configuration subjects and should be revalidated independently when those details matter.

Basis: **source**.

### The ordinary `.trace` file and artifact cache are complementary state

A normal target trace records the build dependency hash and may store serialized output descriptions. The artifact cache separately stores a package-scoped input-hash mapping and content-addressed artifact bytes.

This yields three useful recovery cases:

1. The local target is up to date: Lake can use the local file and compute or recover its artifact identity without consulting shared cache output mappings.
2. The local target is stale or absent but the package mapping is present: Lake can resolve the mapping to cache bytes and avoid rebuilding.
3. The package mapping is absent but an applicable saved trace still contains output descriptions: Lake can resolve those outputs, and, when writes are allowed, repopulate the package mapping.

A prepared environment that preserves only one of these state classes should therefore not assume it has preserved all of Lake's reuse machinery.

Basis: **source** + **derived**.

## Boundaries

- No fresh Lean or Lake execution was performed. Filesystem behavior such as hard-link success, permission enforcement, and observed reuse/rebuild decisions was not measured.
- The report does not fully specify the input-hash key. `buildArtifactUnlessUpToDate` uses the current dependency trace hash, but the exact constituents of that trace differ by target and belong in the separate artifact-cache key-semantics inventory item.
- The report does not claim that every Lake target uses the artifact cache. Only targets routed through compatible cache-aware build helpers and output encodings participate; the complete non-cached surface is a separate inventory item.
- The report does not characterize concurrent writes to output-mapping files, remote transfer races, or end-to-end multi-process cache safety. The artifact-file save path is explicitly race-aware, but that does not establish whole-cache concurrency semantics.
- The report does not establish remote service availability, authentication behavior, retry policy, or server-side consistency. It only follows the pinned client-side architecture.
- The report does not establish cache portability across operating systems, architectures, or Lean toolchains. Lake has platform/toolchain concepts elsewhere in the cache implementation; cross-platform semantics are separate work.
- The report does not treat a Lake content hash as a cryptographic integrity commitment. Other pinned Lake source identifies `Hash` as a `UInt64`-based non-cryptographic hash.
- The report does not equate `restoreAllArtifacts` with cache validity. Restoration changes where an already-resolved artifact is exposed, not whether its input mapping is applicable.
- Adjacent Lean/Lake versions may change cache schemas, path selection, read/write defaults, mapping semantics, or restoration behavior. No continuity is inferred.

## Evidence

All primary evidence is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). Evidence was acquired on 2026-09-27.

- **Artifact identity — source.** `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`: `artifactPath`, `ArtifactDescr`, `ArtifactDescr.relPath`, JSON serialization, `Artifact`, `Artifact.useLocalFile`, and `Artifact.trace`.
- **Local mapping and cache layout — source.** `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`: `Cache`, `artifactDir`, `artifactPath`, `outputsDir`, `outputsFile`, `writeOutputs`, `readOutputs?`, `CacheOutput`, and cache-map machinery.
- **Remote artifact resolution — source.** The same `Cache.lean` blob: cache-service/scope types, artifact URLs, `downloadArtifactCore`, `downloadArtifact`, and transfer hash verification.
- **Build/cache integration — source.** `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: `ToOutputJson Artifact`, `Cache.saveArtifact`, `getArtifactsUsingCache?`, `getArtifactsUsingTrace?`, `getArtifacts?`, `resolveArtifact`, `restoreArtifact`, and `buildArtifactUnlessUpToDate`.
- **Read/write/restore policy — source.** `src/lake/Lake/Config/Monad.lean`, blob `59e032d7c516298a494c070abb948eafe2474184`: `Package.restoreAllArtifacts`, `Package.isArtifactCacheReadable`, and `Package.isArtifactCacheWritable`.
- **Package configuration contract — source.** `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: `enableArtifactCache?` and `restoreAllArtifacts?` documentation and defaults.
- **Package mapping scope — source.** `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: `Package.cacheScope`, based on the package base name.
- **Cache-root selection — source.** `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: `computeLakeCache`, workspace cache configuration, and environment propagation.
- **Environment cache-root discovery — source.** `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: `LAKE_CACHE_DIR`, Elan/system cache discovery, `lakeCache?`, and `cacheToolchain`.

No evidence above is fresh **execution**. Source establishes the control flow and persistence model. Runtime consequences are marked as derived or left open.

## Revalidation

For another Lake revision, first compare the narrow source boundaries that define this architecture:

1. `ArtifactDescr` serialization and the `artifacts/{hash}.{ext}` layout;
2. `Cache.outputsFile`, `CacheOutput`, and the input-to-output mapping format;
3. `Cache.saveArtifact`, including text normalization, hard-link/copy behavior, and race handling;
4. `getArtifactsUsingCache?`, `getArtifactsUsingTrace?`, and `resolveArtifact`;
5. `Package.isArtifactCacheReadable`, `isArtifactCacheWritable`, and `restoreAllArtifacts`;
6. `buildArtifactUnlessUpToDate`, especially which path is used for writable versus read-only consumers;
7. cache-root discovery in `Env` and `Workspace`.

On an execution-capable surface, construct two independent copies of one small package plus one dependency under different absolute roots. Point both at one controlled `LAKE_CACHE_DIR`. For a cache-aware target, preserve after each step:

- the target `.trace` and `.hash` sidecars;
- `outputs/<scope>/<input-hash>.json`;
- the referenced `artifacts/{hash}.{ext}` file;
- the target's ordinary build-directory file, if present; and
- verbose Lake build output showing whether the action was build, fetch, or replay.

Run four cases: writer enabled, second-copy read-only consumer, `restoreAllArtifacts=true`, and an intentionally removed local artifact. Then repeat the read-only case after deleting only the package output mapping but preserving a compatible target trace to test trace-based recovery. Record hard-link versus copy behavior and inode identity where the platform supports it.

For the remote branch, use a controlled cache service or recorded fixture. Remove the local content-addressed file while keeping an output mapping carrying service/scope metadata, then verify that the downloaded bytes are checked against the expected hash before becoming usable. A separate concurrency probe should exercise simultaneous writers to both artifact files and output mappings; the source-level race handling for artifact files alone is not sufficient evidence for whole-cache concurrency safety.
