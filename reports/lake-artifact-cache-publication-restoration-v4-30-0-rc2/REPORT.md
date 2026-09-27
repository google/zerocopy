# Lake artifact-cache publication and restoration at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake publishes a cacheable build result in two logically separate layers: it first makes the output bytes available under a content-derived artifact name, then writes a package-scoped input-to-output JSON mapping that points to that artifact description. These steps are ordered, but they are not one transaction.

Artifact-file creation is deliberately tolerant of competing creators. Binary outputs prefer a hard link from the built file and fall back to create-if-absent byte publication; text outputs normalize CRLF to LF and use create-if-absent publication. A pre-existing content-addressed path is accepted rather than rewritten. The input-to-output mapping has weaker publication mechanics: `Cache.writeOutputsCore` writes the JSON file directly with `IO.FS.writeFile`. The inspected path has no temporary-file rename, compare-and-swap, or explicit filesystem sync. A crash or competing mapping writer is therefore outside the guarantees established by this source inspection. A malformed mapping is detected on read, warned about, and treated as a cache miss.

Restoration is placement, not cache-key validation. Given an already-resolved `Artifact`, `restoreArtifact` leaves an existing destination alone; otherwise it tries to hard-link the cached artifact to the requested local path and falls back to copying it. It then writes the local `.hash` sidecar and returns an `Artifact` whose preferred path is the local file. In the ordinary cache-aware build path, writable packages may consume cache-resident paths directly unless restoration is requested, while non-writable but readable packages restore cache hits into the conventional build location.

The saved per-target `.trace` is a second recovery route. If the package mapping is absent but a matching saved trace contains output descriptions, Lake can resolve those artifacts. A writable package then attempts to backfill the missing input-to-output mapping; failure of this particular backfill is only a warning. This makes trace state and cache mapping complementary, but it does not make their updates atomic.

No fresh Lake execution was performed. These conclusions come from exact pinned source. Filesystem-specific hard-link behavior, power-loss durability, whole-cache multi-process safety, and remote cache service behavior remain outside the established result.

## Applicability

The findings apply to Lake shipped in Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. They describe the cache-aware artifact path centered on `buildArtifactUnlessUpToDate`, `Cache.saveArtifact`, `Cache.writeOutputs`, cache/trace lookup, and `restoreArtifact`.

The report assumes a build target routed through these artifact-cache-aware helpers. It does not claim that every Lake target uses the artifact cache. It also does not restate the exact cache-key composition, cache-root selection, remote cache protocol, or full concurrent-writer behavior; those are separate subjects. Where concurrency matters here, the report states only what the publication primitives themselves establish.

“Publication” means making a local build result recoverable through Lake's local artifact cache. It has two layers:

1. **artifact publication** — place content under `artifacts/<content-hash>.<ext>`; and
2. **mapping publication** — write `outputs/<package-scope>/<input-hash>.json` describing the output artifact or structured outputs.

“Restoration” means making an already-resolved cached artifact available at a target's conventional local build path. It is distinct from choosing the input hash, resolving a mapping, or downloading a missing remote artifact.

## Findings

### Lake publishes artifact bytes before it publishes the input-to-output mapping

For a cache-writable package, `buildArtifactUnlessUpToDate` computes `inputHash := depTrace.hash` and first tries to recover matching output from the cache or saved trace. If it must use or produce a local output and the status is cacheable, it calls `cacheArtifact`, which delegates to `Cache.saveArtifact`. Only after that call returns does it call `Cache.writeOutputs pkg.cacheScope inputHash art.descr`.

The order matters. In the normal direct publication path, Lake does not intentionally install an input mapping before `Cache.saveArtifact` has produced or accepted the referenced content-addressed artifact. The reverse failure is possible: artifact publication can succeed and the subsequent mapping write can fail, leaving artifact bytes that are not reachable through that new package mapping.

A fresh rebuild also writes the target's build trace before `Cache.saveArtifact` and `Cache.writeOutputs`: `buildAction` writes the dependency trace and serialized output description when the build completes successfully. That saved trace can later serve as an alternate source of artifact descriptions.

Basis: **source** + **derived** from the ordered calls in `Build.Common`.

### Content-addressed artifact creation is deliberately race-tolerant at the file-creation step

`Cache.saveArtifact` derives an `ArtifactDescr` from the output's content hash and extension. For binary artifacts it reads the full file, computes the hash, marks the local file unwritable where possible, and targets `cache.artifactDir / descr.relPath`.

If the cache path does not already exist, Lake first tries to hard-link the built file into the cache. An `alreadyExists` failure is accepted as another creator winning the race. Other hard-link failures fall back to `writeBinFileIfNew`; that helper opens the destination with `IO.FS.Mode.writeNew` and likewise treats `alreadyExists` as success. Text artifacts use the same create-if-new pattern after normalizing CRLF to LF before hashing and storage.

This is a narrow race guarantee: two processes trying to create the same content-addressed artifact path need not fail merely because one wins creation. It is not a transaction for the whole cache, and it does not establish semantics for simultaneous writers of the input-to-output mapping.

Basis: **source**.

### A pre-existing local artifact path is trusted by name/existence in these paths

`Cache.saveArtifact` skips artifact-file creation when the content-addressed cache path already exists. `resolveArtifact` similarly accepts a local artifact path when its modification time can be read. Neither inspected local path rehashes pre-existing bytes before returning the artifact.

This means content-addressing is an identity convention used by the local cache, not evidence here of an adversarial or corruption-detecting local store. Remote-download resolution has a separate hash-verification path; this report does not generalize that remote check to already-present local cache files.

Basis: **source**.

### Output-map publication is a direct overwrite, not a source-established atomic commit

The output mapping for one package scope and input hash is:

`outputs/<scope>/<input-hash>.json`

`Cache.writeOutputsCore` creates parent directories and then calls `IO.FS.writeFile file (toJson out).pretty`. The inspected function does not use a temporary sibling plus rename, exclusive create, expected-old-value guard, lock, or explicit filesystem synchronization.

Consequently, this source inspection does **not** establish crash-atomic or multi-writer-serializable mapping publication. An interrupted or competing write may leave state whose behavior depends on filesystem/runtime details not proven here. Lake does have a defined recovery behavior for syntactically bad mapping contents: `readOutputs?` logs an “invalid JSON” warning and returns `none`, so the bad mapping is treated as unavailable rather than as a valid hit.

Basis: **source** + **derived** negative guarantee from the actual write primitive.

### Direct mapping-write failure is fatal after artifact publication; trace backfill failure is only a warning

There are two distinct mapping-write sites.

On the normal writable build path, after `cacheArtifact` succeeds, `buildArtifactUnlessUpToDate` directly awaits `writeOutputs`. There is no local catch around that call. An I/O error therefore aborts this build action after the artifact may already have been installed in the content-addressed store.

By contrast, `getArtifactsUsingTrace?` handles the case where a matching saved trace contains usable output descriptions. If the package is writable, Lake attempts to backfill the package mapping, but converts a failed `writeOutputs` to a warning and still returns the resolved artifacts.

The asymmetry is intentional in the source shape even though no design rationale is claimed here: direct publication treats inability to publish the mapping as an error; recovery from an already-usable trace treats mapping repair as opportunistic.

Basis: **source**.

### The saved trace can recover a missing mapping, but the two state classes are not one transaction

`getArtifacts?` checks the package's input-to-output mapping first. If that does not yield usable output, it checks the saved target trace. A trace qualifies when its dependency hash equals the current input hash and it contains output descriptions that resolve successfully.

For a writable package, successful trace-based recovery attempts to write those descriptions back into the package cache mapping. This lets a saved trace repair a missing mapping without rebuilding the target. It also means preserving only the mapping store or only `.trace` files does not preserve exactly the same recovery state.

Nothing in these calls atomically commits the trace, artifact file, and output mapping as one record. A later consumer must tolerate partial persistence among those layers according to the lookup and fallback rules.

Basis: **source** + **derived**.

### Cache-readable and cache-writable packages use different restoration policies

The default package policy is asymmetric: artifact-cache readability defaults to `true`, while writability defaults to `false`. `restoreAllArtifacts` defaults to `false`.

When a package is writable, `buildArtifactUnlessUpToDate` tries the cache before local replay/build. A cache hit is restored only if the caller requested `restore` or the package/workspace enables `restoreAllArtifacts`; otherwise the returned `Artifact.path` can remain the cache-resident path.

When a package is not writable, Lake first accepts an up-to-date local file. If the local target needs work and cache reading is enabled, a cache hit is requested with `restore := true`, so the conventional local target path is materialized. If cache reading is disabled or lookup fails, Lake builds the local output without publishing it to the artifact cache.

Thus “cache hit” does not imply “file appears in the package build directory.” Placement depends on write policy and restoration configuration.

Basis: **source**.

### Restoration hard-links first, then copies; it does not replace an existing destination

`restoreArtifact file art` first checks `file.pathExists`. If the destination already exists, the function skips both hard-link/copy materialization and the `.hash` sidecar write, then returns `art.useLocalFile file`.

If the destination is absent, Lake creates parent directories and tries `IO.FS.hardLink art.path file`. On failure it copies the cached artifact bytes to `file` and marks that copied file unwritable where possible. After either successful hard-link or copy, it writes the local file-hash sidecar and returns an `Artifact` whose preferred path and display name refer to the local destination.

At this function boundary, restoration therefore does not mean “replace local bytes with cached bytes.” It means “ensure a missing destination is materialized, otherwise use the destination that already exists.” The ordinary build path has its own trace and removal logic around this helper; callers outside that context must not infer stronger replacement semantics from `restoreArtifact` itself.

Basis: **source**.

### A cache fetch can rewrite the local target trace when the saved dependency identity no longer matches

The cache-hit helper checks `savedTrace.replayOrFetchIfUpToDate inputHash`. That method considers the saved trace current for this purpose when its recorded dependency hash equals the current input hash; otherwise it selects a fetch action.

When the helper does not accept the saved trace, it removes the local target file if present and writes a synthetic fetch trace containing the current input hash and fetched artifact description before restoration. This makes the newly fetched artifact's provenance visible to subsequent Lake reuse logic.

When the saved dependency hash already matches, Lake replays the trace instead and does not rewrite it merely because the artifact came from the cache path.

Basis: **source**.

### Cache publication deliberately excludes results accepted only by modification-time fallback

`SavedTrace.replayIfUpToDate'` distinguishes hash-up-to-date, modification-time-up-to-date, and out-of-date states. `OutputStatus.isCacheable` is false only for the modification-time-up-to-date case.

In the writable path, Lake publishes with `cacheArtifact`/`writeOutputs` only when `status.isCacheable` is true. Therefore a target accepted solely through old-mode modification-time fallback is usable locally but is not promoted by this path into the shared artifact cache as though its content identity had been established by the hash-based path.

Basis: **source** + **derived**.

## Boundaries

- No fresh Lake execution was performed. The report does not measure whether hard links succeed on any particular filesystem, what errors a specific platform returns, or how permissions behave under unusual mounts.
- The source paths inspected here contain no explicit `fsync`, `fdatasync`, directory sync, journal transaction, or equivalent durability protocol for artifact/mapping/trace publication. This report therefore does not claim power-loss durability merely because a write call returned.
- Whole-cache concurrency is a separate inventory item. The report establishes race-tolerant artifact-file creation and observes direct mapping overwrite mechanics; it does not claim a complete concurrent-writer model for mappings, traces, remote downloads, cache cleanup, or mixed operations.
- Artifact-cache key semantics are separate. This report uses `inputHash := depTrace.hash` only to describe where publication/restoration fits in the control flow.
- The report does not claim cryptographic integrity for Lake's local content hash and does not characterize deliberate cache tampering. It only records that already-present local content-addressed paths are not rehashed in the inspected resolution/publication paths.
- Remote cache services are outside scope except for the distinction that local `resolveArtifact` may download a missing artifact when mapping metadata names a service/scope. Remote transport, authentication, retries, and server consistency are not established here.
- `restoreArtifact`'s existing-destination behavior is a function-level fact. Whether a particular caller has already proved or repaired that destination is a caller-specific question.
- Ordinary `IO.FS.writeFile` and copy semantics depend on Lean's runtime and the host filesystem. The report does not infer stronger atomicity than the source explicitly constructs around those primitives.

## Evidence

All primary evidence was acquired on 2026-09-27 from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). The package's `source-map.json` preserves the exact source paths, blobs, symbols, and line ranges used below.

- **Artifact identity — source.** `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`: `artifactPath`, `ArtifactDescr`, `ArtifactDescr.relPath`, and `Artifact.useLocalFile`.
- **Artifact save, lookup, restoration, and build integration — source.** `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: trace read/write and replay functions; `buildAction`; `Cache.saveArtifact`; cache/trace lookup; `restoreArtifact`; and `buildArtifactUnlessUpToDate`.
- **Mapping layout and publication — source.** `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`: `Cache.outputsFile`, `Cache.writeOutputsCore`, `Cache.writeOutputs`, and `Cache.readOutputs?`.
- **Package read/write/restore policy — source.** `src/lake/Lake/Config/Monad.lean`, blob `59e032d7c516298a494c070abb948eafe2474184`: `Package.restoreAllArtifacts`, `Package.isArtifactCacheReadable`, and `Package.isArtifactCacheWritable`.
- **Create-if-absent and copy primitives — source.** `src/lake/Lake/Util/IO.lean`, blob `35f92bf0053f3fca99f771f1b268f35760667d40`: `writeFileIfNew`, `writeBinFileIfNew`, and `copyFile`.

No claim above is based on fresh **execution**. The ordering and failure conclusions are **derived** only where they follow directly from the inspected call order and uncaught/caught I/O operations.

## Revalidation

For another Lake revision, first diff the small publication/restoration boundary rather than repeating broad Lake research:

1. `Cache.saveArtifact` and the create-if-new helpers: content normalization, hard-link fallback, pre-existing-artifact treatment, and permission changes;
2. `Cache.outputsFile`, `writeOutputsCore`, and `readOutputs?`: mapping path, serialization, and whether publication gains an atomic-replace or locking primitive;
3. `getArtifactsUsingCache?`, `getArtifactsUsingTrace?`, and `getArtifacts?`: lookup order and trace-to-mapping backfill;
4. `restoreArtifact`: existing-destination behavior, hard-link/copy fallback, and sidecar update;
5. `buildArtifactUnlessUpToDate`: publication order, writable/readable branches, restoration policy, and cacheability gating; and
6. `buildAction` plus fetch-trace writing: when output descriptions become durable relative to artifact/mapping publication.

On an execution-capable surface, a compact probe can test the source-derived boundaries without a large workspace. Use one cache-aware target and a controlled `LAKE_CACHE_DIR`, then preserve the cache tree and target tree after each step:

- build with cache writing enabled and record the order/presence of the target trace, content-addressed artifact, output mapping, local file, and `.hash` sidecar;
- delete the local target but preserve the mapping and artifact, then compare `restoreAllArtifacts=false` with `true`;
- disable cache writing while keeping reading enabled and confirm that a cache hit restores the conventional local target path;
- delete only the package output mapping while preserving a matching saved trace and artifact, then verify trace-based recovery and mapping backfill;
- corrupt the mapping JSON and verify that Lake warns and falls back rather than accepting the entry; and
- separately inject failures between artifact creation and mapping publication, and during mapping replacement, to characterize crash behavior that source inspection alone does not establish.

A concurrency probe should be kept separate: race two writers with the same and different input hashes, inspect both `artifacts/` and `outputs/`, and preserve any malformed or last-writer-wins mapping evidence. Passing artifact-file races would not by itself establish safe mapping concurrency.
