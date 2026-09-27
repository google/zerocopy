# Lake artifact-cache key semantics at v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does not derive one universal cache key by hashing a package directory, command line, or target declaration. The local artifact cache instead maps a **package cache scope plus the current build job's dependency-trace hash** to one or more output artifact descriptions. The output artifact descriptions are a separate identity layer: each names the output by its content hash and extension.

The distinction is central to cache correctness. A target's cache key changes only when its `BuildTrace` changes. Built-in Lake targets deliberately mix selected semantic inputs into that trace: source or dependency artifact hashes, the Lean git hash, host-platform identity for native outputs, module identity, selected options, and arguments classified as `traceArgs`. They also deliberately exclude some inputs. In particular, path-shaped `weakArgs` such as `-I` and `-L` flags are passed to compiler/linker invocations without being mixed into the dependency trace, so relocation can preserve cache identity when only those paths move.

This makes cache-key completeness a property of each target's trace construction. The generic artifact-cache API does not independently discover every semantic input to a build command. A built-in or custom target that omits a semantically relevant value from its trace can reuse an artifact under an insufficient key; adding irrelevant or location-specific values reduces reuse. `platformIndependent = true` is another explicit narrowing operation: the module setup path omits native-library and platform traces that it otherwise retains.

Anneal should therefore treat a Lake artifact-cache key as a target-specific semantic contract, not as proof that two build environments are equivalent. For any cache path Anneal intends to rely on, the durable evidence should identify the exact target, the traces it mixes, the values it intentionally omits, and the conditions under which any cached `.hash` metadata is trusted.

## Applicability

This report covers Lake as selected by Lean `v4.30.0-rc2`, revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. It focuses on the identity used for local artifact-cache lookup and the built-in trace construction that feeds that identity.

The adjacent `lake-artifact-cache-architecture-v4-30-0-rc2` report covers cache layout, artifact restoration, cache read/write policy, and remote-origin metadata. This report narrows the question to **what determines the input hash** and what Lake intentionally does not place in that hash. Publication/restoration semantics, whole-cache concurrency, remote service consistency, and cross-platform artifact portability remain separate subjects.

Evidence here is pinned source inspection. No fresh Lake or Lean execution was performed. The source is sufficient to identify the key construction and built-in trace plumbing, but execution remains useful for detecting accidental inputs, stale `.hash` behavior, or target-specific paths not obvious from a static call graph.

## Findings

### Lake uses two identity layers: an input trace hash and an output content hash

`Lake.Build.Common.buildArtifactUnlessUpToDate` first reads the current job trace:

```lean
let depTrace ← getTrace
...
let inputHash := depTrace.hash
```

It uses that `inputHash` to query `getArtifacts?` and, when a cacheable build completes, stores the output mapping through:

```lean
(← getLakeCache).writeOutputs pkg.cacheScope inputHash art.descr
```

`Cache.outputsFile` stores the mapping at:

```text
<cache>/outputs/<package-scope>/<input-hash>.json
```

The package scope is `Package.cacheScope`, which is the package's `baseName` rendered as a string.

The value in that mapping is not the build path. `ArtifactDescr` identifies an artifact using its content hash plus extension and serializes as `{hash}.{ext}`. Artifact bytes live separately in the content-addressed artifact directory. Thus a cache lookup has two conceptually distinct identities:

1. **input identity:** package cache scope + dependency-trace hash;
2. **output identity:** content hash + extension.

This separation lets many input identities point at content-addressed output bytes and lets the same output content be reused without making the output path part of its identity.

Basis: **source** in `Lake.Build.Common`, `Lake.Config.Cache`, `Lake.Config.Package`, and `Lake.Config.Artifact`.

### The input hash is exactly the hash accumulated in the target's `BuildTrace`

`BuildTrace` carries a caption, nested input traces, a hash, and an mtime. `BuildTrace.mix` combines two traces by applying `Hash.mix` to their hashes. `JobM.addTrace` updates the current job trace by mixing another trace into it. Job-state merging similarly combines traces.

`BuildMetadata.ofBuild` persists the final dependency hash as `depHash` and serializes the nested input traces separately. On a subsequent normal-mode build, `SavedTrace.replayIfUpToDate'` considers the dependency hash equal only when the newly constructed trace hash matches the stored one.

This has two consequences.

First, the cache key is not derived from the human-readable trace captions. A file trace may use the path as its caption while its hash comes from file contents. The persisted `inputs` list is useful provenance, but the cache lookup is driven by the composed `depTrace.hash`.

Second, input participation is explicit. A value affects the cache key only if the target or a dependency contributes a trace whose hash depends on that value. The artifact-cache layer does not inspect the later build command and add missing command-line arguments on its own.

Basis: **source** in `Lake.Build.Trace`, `Lake.Build.Job.Monad`, `Lake.Build.Job.Basic`, and `Lake.Build.Common`.

### File inputs are content-based, with deliberate text normalization

Lake's built-in file input jobs distinguish binary and text inputs. Binary input hashes are sensitive to byte differences. Text inputs normalize line endings before hashing, so CRLF/LF differences do not force different content hashes.

`fetchFileHash` can also reuse a sidecar `.hash` file when Lake's `trustHash` setting is active. With rehashing requested, it recomputes the content hash instead. This does not change the logical key model—file content hashes are still what enter the trace—but it changes how Lake obtains those hashes operationally.

For a prepared cache, this makes `.hash` coherence a correctness precondition whenever hashes are trusted. Moving a tree with stale sidecars can preserve an incorrect trace value until a rehash path recomputes it. Anneal should not equate “same Lake input hash” with “freshly rehashed same contents” unless the hash-trust state is known.

Basis: **source** in `Lake.Build.Common`; the operational implication is **derived** from the `trustHash` branch.

### The Lean toolchain contribution is the Lean git hash, not the toolchain path

Built-in targets call `addLeanTrace` when their output depends on the Lean toolchain. The build context's Lean trace is constructed from:

```lean
.ofHash (pureHash ws.lakeEnv.leanGithash)
```

Its caption includes the Lean version string and git hash, but the trace hash itself is the hash of the Lean git hash value.

This is intentionally different from hashing an absolute Lean installation path. Relocating an otherwise identical Lean installation does not change this trace merely because the sysroot path moved. Conversely, changing the selected Lean git hash changes this contribution even if some filesystem paths remain the same.

The boundary is worth stating precisely: this trace captures the Lean revision identifier Lake selected. It does not by itself prove that two locally built Lean installations with the same reported git hash are bit-for-bit or configuration-equivalent.

Basis: **source** in `Lake.Build.Run`, `Lake.Build.Context`, and `Lake.Build.Common`.

### Native targets explicitly add the host platform

`addPlatformTrace` mixes a hash of `System.Platform.target` into the current trace. Built-in object, shared-library, and executable builders call it.

For example, `buildO` and `buildLeanO` add the platform trace before calling `buildArtifactUnlessUpToDate`. The shared-library and Lean-executable builders do the same. The resulting cache key therefore distinguishes the platform identifier for these native artifacts even when source and other traced inputs match.

This is a positive inclusion, not a general proof of binary compatibility. The platform trace is only the platform string Lake chose to mix. Other ABI-relevant toolchain details must enter through other traced inputs or target-specific assumptions.

Basis: **source** in `Lake.Build.Common`.

### Path-shaped weak arguments are intentionally excluded from native cache keys

Lake's object-builder API separates `weakArgs` from `traceArgs`. Both are passed to the compiler. Only `traceArgs` are hashed into the dependency trace with `addPureTrace`.

The source comment explains the intended use: system-dependent options such as `-I` and `-L` should be weak so that path changes do not cause a rebuild. `buildLeanO`, the shared-library builders, and the executable builder preserve the same distinction. Absolute include or library locations can therefore change without changing the cache key when they arrive only through the weak-argument channel.

This is a deliberate relocation feature and a correctness boundary. It assumes that changing those weak path spellings without changing the traced semantic inputs does not change the meaning of the build. If two different include paths resolve to different headers, or two different library paths resolve to different libraries without the dependency traces changing, the weak-argument exclusion is insufficient.

For Anneal, the important rule is not “paths are ignored.” The rule is narrower: **values passed through `weakArgs` are ignored by that builder's trace hash**. Other paths can still affect a trace through file contents, dependency artifacts, explicit pure traces, or custom target logic.

Basis: **source** in `Lake.Build.Common`; the correctness condition is **derived** from the distinction between invocation arguments and traced arguments.

### Lean module keys include source/dependency state plus selected semantic configuration

`Module.recBuildLean` constructs a richer trace before looking in the cache. At the selected revision it mixes:

- the Lean trace;
- the source job's trace;
- traced Lean options;
- whether the input is a module;
- the module name;
- the package ID;
- module-specific Lean arguments;
- the setup/dependency trace produced by module dependency resolution.

`traceOptions` hashes the effective `-Dname=value` option strings. `Package.id?` is the original package name for non-bootstrap packages. The module name and package ID therefore participate independently of source contents.

The dependency setup path includes import information and, depending on `platformIndependent`, native-library traces and an explicit platform trace. This means the module input hash is not just a source-file hash. It represents a target-specific composition chosen by Lake's module builder.

Basis: **source** in `Lake.Build.Module` and `Lake.Config.Package`.

### `platformIndependent` deliberately narrows the module dependency trace

During module setup, Lake separates a general dependency trace from a library trace. Its behavior is:

- if `platformIndependent` is unspecified, mix both dependency and library traces;
- if explicitly `false`, mix both plus the platform trace;
- if explicitly `true`, mix only the general dependency trace.

The `true` case therefore omits information that other cases retain. Later root-output tracking can also mark the packed module artifact as platform-independent.

This is not automatic platform-independence detection. It is target/package configuration changing what participates in the key. A project using `platformIndependent = true` is asserting that omitted native-library and platform distinctions are irrelevant for the cached module output.

Anneal should preserve that assertion as provenance rather than inferring platform equivalence from a cache hit.

Basis: **source** in `Lake.Build.Module`.

### Package version and repository revision are not generic top-level key fields

The local output mapping is namespaced by `Package.cacheScope`, which is the package `baseName`. The generic `buildArtifactUnlessUpToDate` path then keys the mapping by the target's dependency-trace hash.

Neither API automatically appends a package version, Git revision, repository URL, absolute package directory, or output filename to that tuple. Those values matter only if the target's constructed trace depends on them indirectly or explicitly.

For built-in Lean modules, source content, dependencies, Lean revision, module identity, package ID, options, arguments, and configuration-specific dependency traces provide substantial disambiguation. That is different from saying the package's source-control revision is itself a generic cache-key component.

This distinction matters when evaluating a reused cache across checkouts. The safe question is “do all semantically relevant differences flow into this target's trace?” rather than “did Lake hash the commit SHA?”

Basis: **source** in `Lake.Config.Cache`, `Lake.Config.Package`, `Lake.Build.Common`, and `Lake.Build.Module`; the checkout implication is **derived**.

### Output paths do not automatically participate in `buildArtifactUnlessUpToDate`

`buildArtifactUnlessUpToDate` receives the output `file`, but the cache lookup's `inputHash` is the current dependency trace hash captured before the build. The output path is used to find the `.trace` file, restore artifacts, remove stale local outputs, and select where a build writes. It is not automatically mixed into `inputHash`.

As a result, moving an otherwise identical target output location can preserve the artifact-cache key if the target's upstream trace construction is unchanged. That can be useful for relocation. It also means that a custom build whose semantics depend on its output pathname must explicitly trace the relevant distinction rather than relying on the generic artifact-cache wrapper.

Basis: **source** in `Lake.Build.Common`.

### Saved traces and artifact-cache mappings share the same input-hash contract

A saved build trace records `depHash`. Artifact-cache lookup with `getArtifactsUsingTrace?` accepts saved outputs only when the saved `depHash` equals the current `inputHash`. The local cache mapping is queried with the same `inputHash`.

This alignment is important: the `.trace` replay path and the artifact-cache mapping path are two representations of the same dependency identity. A saved trace can seed a missing cache mapping when the cache is writable, but it cannot legitimately do so under a different dependency hash.

The cache architecture therefore has several layers of state, but it does not define independent semantic keys for trace replay and artifact lookup in this path.

Basis: **source** in `Lake.Build.Common`.

### Trace completeness is part of target correctness

The generic artifact-cache machinery cannot know whether a custom target's trace is complete. It only consumes the `BuildTrace` the target has assembled. Lake's built-ins demonstrate the intended discipline: add dependency traces, hash semantically relevant options, add Lean/platform traces where appropriate, and intentionally classify relocatable path arguments as weak.

That discipline creates two symmetric failure modes:

- **under-keying:** omit a semantic input and a stale or incompatible artifact can be reused;
- **over-keying:** include location-specific or irrelevant values and equivalent builds miss the cache.

A cache hit therefore establishes equality of Lake's target-specific traced identity, not full semantic equivalence of arbitrary environments. Anneal should treat the traced-input inventory as part of the evidence for every cache-dependent workflow.

Basis: **derived** from the generic key path and built-in target implementations.

## Boundaries

**No fresh execution.** This report did not run Lake or Lean. It establishes key construction from exact pinned source, not observed cache-hit behavior in an Anneal fixture.

**Not an exhaustive audit of every Lake target.** The report examines the generic artifact-cache path and representative built-in Lean-module/native builders that matter to Anneal. Custom facets and uncommon built-ins can construct different traces.

**Not a remote-cache protocol report.** Remote publication, revision-map semantics, service scopes, authentication, and restoration policy are adjacent subjects. This report follows the input hash through local lookup and the root-output tracking path only far enough to establish identity semantics.

**Not a platform-portability proof.** Adding a platform trace or setting `platformIndependent` changes key construction; neither action proves that a produced native or Lean artifact is portable.

**Not a package-revision equivalence proof.** The absence of a generic commit-SHA field does not mean revision changes are invisible. Source/dependency hashes normally carry many revision effects. The point is only that revision identity is target-trace-derived rather than an unconditional top-level cache-key field.

**Hash sidecars are an operational trust boundary.** The source permits cached `.hash` values to be reused. This report does not measure how Anneal currently creates, validates, relocates, or invalidates those sidecars.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27 against `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`: `BuildTrace`, `compute`, `mix`, hash/mtime/caption separation.
- `src/lake/Lake/Build/Job/Monad.lean`, blob `7321de72c6283e5af458b19bd2988d99f906745d`: current-job trace state and `addTrace`.
- `src/lake/Lake/Build/Job/Basic.lean`, blob `1f0066910478137341388422d8d593ddffbaca18`: job-state trace merging and completed-job trace propagation.
- `src/lake/Lake/Build/Job/Register.lean`, blob `700ecf9be3b0628952f0cc9b32ce9cac99a07607`: registration renewal preserves the trace hash while dropping nested-input detail.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: generic artifact-cache lookup/write key; saved trace metadata; file hashing; Lean/platform/pure traces; `weakArgs`/`traceArgs`; native builders.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: built-in module trace composition, cache lookup/write, `platformIndependent` behavior, output tracking.
- `src/lake/Lake/Build/Library.lean`, blob `6cb600d16b99f31d29e13dccc6cdfccef6a8b23a`: static-library build dependencies and generic artifact-cache wrapper use.
- `src/lake/Lake/Build/Context.lean`, blob `8f2eda8d462334f933f112d7ebc4acd3e9553568`: build-context Lean trace.
- `src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`: Lean trace constructed from the selected Lean git hash.
- `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`: output content identity and `{hash}.{ext}` serialization.
- `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`: input-to-output cache maps, output mapping paths, artifact-cache storage.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: package cache scope, package ID, and package configuration fields.
- `src/lake/Lake/Config/Env.lean`, blob `eed315c538de746a891d18f72564e88aea64e969`: cache and toolchain-related environment state.

The adjacent durable candidate `5a2f45ab-5124-4cc2-9a11-a9266e7ce215` for Lake artifact-cache architecture was used as an evidence index and scope boundary. Exact key semantics were re-read from the pinned source rather than inferred from that candidate's summary.

Evidence roles are **source** and **derived**. No fresh **execution** evidence was produced.

## Revalidation

For another Lake revision, revalidate the key contract in this order:

1. inspect `ArtifactDescr` and cache output-map paths to confirm the separation between input identity and output content identity;
2. inspect `BuildTrace.mix`, job trace propagation, and `BuildMetadata` to identify the actual hash used for freshness;
3. inspect `buildArtifactUnlessUpToDate` and module-specific cache paths to verify which trace hash becomes `inputHash`;
4. inspect `Package.cacheScope` and any remote cache scope changes;
5. inspect representative built-in module/object/library/executable builders for `addLeanTrace`, `addPlatformTrace`, `addPureTrace`, `weakArgs`, and `traceArgs`;
6. inspect file hash trust/rehash behavior.

For this exact revision, a useful execution suite would vary one input dimension at a time and record the resulting `outputs/<scope>/<input-hash>.json` path plus target trace metadata:

- change a source file semantically and confirm a new input hash;
- change only CRLF/LF line endings for a text-traced input and confirm the normalized hash remains stable;
- relocate an include/library directory supplied only through `weakArgs` and confirm the input hash remains stable;
- change a value supplied through `traceArgs` and confirm the input hash changes;
- change the selected Lean git hash and confirm targets using `addLeanTrace` change identity;
- compare platform-dependent and explicitly `platformIndependent` module configurations;
- deliberately stale a `.hash` sidecar, compare trusted-hash and rehash modes, and record whether the resulting input identity follows the sidecar or recomputed content.

Preserve the exact trace JSON, cache mapping path, command line, package configuration, and generated artifact hashes for each probe. Those fixtures would turn the source-level contract into executable regression evidence for Anneal's cache assumptions.
