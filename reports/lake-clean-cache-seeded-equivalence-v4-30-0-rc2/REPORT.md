# Clean-build versus cache-seeded equivalence in Lake v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), a Lake artifact-cache hit is a **same-traced-input substitution**, not proof that a fresh clean build would reproduce the same bytes.

Lake computes an input `BuildTrace` for a build action. It uses that trace's hash as the local artifact-cache lookup key. A cache entry maps that input hash to content-addressed output descriptors. On a hit, Lake can resolve those descriptors and reuse producer-created output bytes without running the producer action. This design gives a precise reuse contract, but it leaves a separate empirical question: would a fresh producer run under the intended equivalent conditions emit the same `.olean`, `.ilean`, generated/native artifacts, and other outputs?

Clean and cache-seeded trees also differ intentionally in state that should **not** be required to match byte-for-byte. A clean build writes ordinary build metadata containing its dependency-input tree and log. A cache fetch can write synthetic metadata with the same dependency hash and output descriptors but an empty input tree/log and `synthetic = true`. Cache restoration can place some artifacts at content-addressed cache paths and restore others into the build tree. Modification times, hard-link topology, permissions, build-action labels, and raw file paths can therefore differ while the cached output identity remains the same.

For Anneal, the useful equivalence contract has three layers:

1. **Producer-input identity:** compare the effective traced values that are supposed to identify the build—toolchain identity, source content, options, logical module/package identity, dependency artifact traces, and other traced inputs. Treat intentionally weak or untraced inputs separately rather than assuming the Lake key covers them.
2. **Output identity:** compare the bytes of every artifact that matters to later compilation, elaboration, linking, or analysis. Lake's own content hashes are useful navigation data, but they are non-cryptographic 64-bit hashes; an equivalence probe should use direct byte comparison or a cryptographic digest and should not merely trust existing `.hash` sidecars.
3. **Consumer behavior:** compare the behavior that Anneal depends on—ordinary reuse, import/elaboration, `setup-file`, and representative server preparation. Raw path-bearing `ModuleSetup` JSON need not be textually identical if both setups identify the same module/package/options and resolve to byte-identical imported artifacts.

This source inspection therefore establishes **what equivalence must mean and which state is intentionally allowed to differ**. It does not establish that clean and cache-seeded builds are actually equivalent at this revision. Closing that stronger claim requires a paired execution on the exact pinned toolchain and inputs.

The current Anneal pipeline on `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` is an important boundary. It downloads and unpacks Mathlib's precompiled cache, then rewrites Git dependencies to vendored path dependencies. The source explicitly says that this rewrite changes Lake dependency hashes even though the source content and cached artifacts came from the same upstream revisions. Anneal therefore verifies that archive with `lake --old build`, using mtime-based acceptance after making rewritten inputs older than the unpacked artifacts. That pipeline is **not** evidence that current hash-mode clean and cache-seeded states are equivalent.

## Applicability

The Lake findings apply to the implementation shipped at Lean commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`. This is the Lean version selected by the examined Anneal configuration.

"Clean build" means an ordinary hash-mode Lake build in which the target outputs cannot be satisfied by a preexisting artifact-cache entry and the relevant producer actions actually run. "Cache-seeded build" means a separate state with equivalent intended inputs in which Lake satisfies some or all producer actions from seeded artifact-cache mappings and content-addressed artifacts.

The strongest comparison holds the host/target platform, Lean toolchain, source revisions, effective build configuration, and semantically relevant environment constant unless the experiment is specifically testing one of those dimensions. Cross-platform portability and relocation are separate questions. A path relocation can be part of a later equivalence experiment, but path changes must then be classified according to whether Lake traces them, deliberately treats them as weak inputs, or exposes them only through consumer-facing path fields.

Unless stated otherwise, the findings concern ordinary hash-based freshness, not `lake --old`. Old mode can accept an output based on modification times after a dependency-hash mismatch or missing trace, and Lake deliberately treats an mtime-only up-to-date result as non-cacheable. An old-mode acceptance is therefore not evidence that the normal artifact-cache input key is equivalent.

The report examines two subjects for different purposes. The pinned Lean/Lake source defines the cache and build-state mechanism. Current `google/zerocopy` `main` shows how Anneal presently seeds Mathlib build products and why its existing archive verification uses old mode. The Anneal source is not used to generalize Lake behavior beyond the pinned Lean implementation.

## Findings

### A cache hit identifies a traced input and producer output, not a hypothetical rebuild

For ordinary artifact-backed build actions, Lake computes the current dependency trace and takes `depTrace.hash` as the `inputHash`. Its cache lookup first asks for the output mapping associated with that input hash. The mapping points to output descriptors; resolving those descriptors returns cached artifacts. If no usable mapping/artifact exists, Lake falls back to saved local state or to the producer action.

For a generic artifact build, `buildArtifactUnlessUpToDate` implements this sequence directly. Module compilation uses the same concept through `Module.recBuildLean`: the module's current dependency trace is the cache input identity, and the resulting `ModuleOutputDescrs` are the cached output description.

This design establishes a **Lake reuse equivalence class**:

> the current traced input hash selects an output descriptor set that Lake is willing to reuse for that input.

It does not establish a **rebuild reproducibility theorem**:

> running the producer action again under the intended same conditions necessarily emits the same bytes.

The producer never runs on a successful cache hit, so the cache path cannot itself compare cached output bytes with hypothetical newly generated output bytes.

Basis: **source + derived**.

### The module input identity covers selected effective inputs, not all process state

A module's `leanArts` job builds its dependency trace before deciding whether to reuse, fetch, or rebuild. At this revision, the traced inputs include:

- the selected Lean toolchain trace;
- the module's source trace;
- effective Lean options;
- module-system mode;
- logical module name;
- package identity passed to Lean;
- traced Lean arguments; and
- setup/dependency traces, including imported artifact/transitive traces and selected dependency-library/plugin state.

This is the right starting point for a clean/cache experiment because the cache key is derived from these values. It is not a claim that every input to every underlying tool is present in the trace.

Lake explicitly supports **weak arguments**. For native compilation/link helpers, `traceArgs` enter the dependency trace while `weakArgs` do not. The source explains that system-dependent options such as path-bearing `-I` or `-L` arguments should be weak so that a path change does not by itself invalidate a build artifact. Module compilation similarly passes `weakLeanArgs` to Lean without adding them to the module dependency trace.

A same-key cache hit can therefore cross a weak-input difference by design. That may be correct under Lake's intended weak-input contract, but it does not logically imply that a fresh producer invocation with different weak inputs would be byte-identical. An equivalence experiment must either hold weak inputs constant or explicitly test and justify the intended weak-input variation.

Basis: **source + derived**.

### Output descriptors are content-based and do not encode preferred filesystem paths

`ArtifactDescr` contains a Lake `Hash` and an extension. Its cache-relative path is derived as `{hash}.{ext}`. The descriptor does not include a preferred build-tree path, modification time, or producer log.

For a Lean module, `ModuleOutputDescrs` records descriptors for the output classes produced by that module build:

- `.olean`;
- `.olean.server`, when present;
- `.olean.private`, when present;
- `.ilean`;
- `.ir`, when present;
- generated `.c`;
- optional `.bc`; and
- optional `.ltar`.

`ModuleOutputArtifacts.descrs` reduces each concrete `Artifact` to this descriptor-only representation before Lake writes the input-to-output mapping.

This separation matters for equivalence. Two states can name the same content-addressed output descriptors while exposing different preferred paths or mtimes. Conversely, equality of descriptor strings is weaker evidence than direct byte equality because Lake's `Hash` is only a 64-bit, explicitly non-cryptographic hash.

For a high-confidence Anneal probe, the primary artifact comparison should therefore be the actual output bytes, or a cryptographic digest computed from those bytes. The Lake descriptor set should be recorded as the implementation's own identity layer, not treated as cryptographic proof.

Basis: **source + derived**.

### Clean and cache-fetched trace files are intentionally not byte-equivalent

Lake's persisted `BuildMetadata` contains:

- `depHash`;
- serialized dependency inputs;
- output description;
- build log; and
- a `synthetic` bit.

A successful producer action writes ordinary build metadata with the dependency trace's input tree, output description, build log, and `synthetic = false`.

A cache fetch can instead call `BuildMetadata.ofFetch`. That metadata preserves the requested `inputHash` as `depHash` and the fetched output description, but it records an empty input tree, an empty log, and `synthetic = true`. `SavedTrace.replayOrFetchIfUpToDate` recognizes that synthetic provenance and marks the action as a fetch when appropriate.

Therefore exact `.trace` byte equality would reject an intended cache hit. The useful semantic comparison is narrower:

- the current dependency identity should correspond to the same `depHash`;
- the output descriptors should identify the intended output content;
- a later unchanged build should treat the result as current under ordinary hash-mode rules; and
- differences that encode **provenance of build versus fetch** should remain classified as expected differences.

The same reasoning applies to build logs and action labels. A clean producer should be observable as a build. A seeded consumer should be observable as a fetch or replay. Their difference proves that the experiment exercised different paths; it is not evidence of semantic inequivalence.

Basis: **source + derived**.

### Cache restoration can produce different layouts while preserving artifact identity

A resolved cache artifact initially lives under Lake's cache artifact directory, keyed by its content descriptor. `restoreArtifact` can then make it available at a requested local build path, preferring a hard link and falling back to a copy. The restored local file receives a `.hash` sidecar and is made unwritable where possible.

Module restoration is deliberately selective. `Module.restoreNeededArtifacts` restores `.ilean` to the module's build directory but can leave other module outputs at their cache paths. `Module.restoreAllArtifacts` restores the full module output set, including `.olean`, server/private oleans, `.ilean`, IR, generated C/bitcode, and an archive when present.

A clean build and a cache-seeded build can consequently have:

- different preferred artifact paths;
- different hard-link/copy topology;
- different modification times;
- different permissions inherited or applied during restoration; and
- a different set of materialized build-tree files.

None of those differences, by itself, disproves equivalence of the artifact content consumed by Lean/Lake.

The experiment should instead identify every path that consumers can observe, resolve it to content, and compare the content identity and role. If a consumer requires a specific local path rather than merely the content, that path requirement becomes part of the consumer-behavior contract and must be tested separately.

Basis: **source + derived**.

### `.hash` sidecars are useful state, but they are not independent proof of equivalence

Lake can cache a file's content hash in a neighboring `.hash` file. With normal hash trust enabled, `fetchFileHash` may reuse that sidecar without rereading the artifact bytes. `--rehash` disables that shortcut and forces recomputation.

The local artifact-cache resolver similarly returns an existing cache file using the descriptor and file metadata; it does not recompute the artifact's content hash on every local hit. By contrast, a newly downloaded remote artifact passes through `downloadArtifactCore`, which computes its hash and rejects a mismatch.

This gives an equivalence probe two important controls:

1. do not compare only preexisting `.hash` sidecars; and
2. either force Lake to rehash where relevant or compute an independent cryptographic digest of every compared artifact.

A seeded tree with corrupt local bytes plus a stale trusted sidecar is not an acceptable equivalence witness merely because Lake's metadata strings line up.

Basis: **source + derived**.

### Server preparation should be compared semantically, not as raw path-bearing JSON

Lean's `ModuleSetup` contains the module name, optional package identity, module-system mode, imports, pre-resolved imported artifacts, dynamic-library paths, plugin paths, and Lean options.

Lake's `setup-file` path computes this structure for an edited document after building or fetching the required dependencies. Because imported artifacts, dynamic libraries, and plugins are represented by filesystem paths, two semantically equivalent environments can produce different raw `ModuleSetup` JSON when one environment references content-addressed cache paths and another references restored build-tree paths.

For Anneal's interactive/server use, a stronger and more useful comparison is:

- the same module and package identity;
- the same effective options and import relation;
- each imported artifact path resolves to byte-identical content of the same artifact class;
- dynamic-library/plugin paths resolve to the intended byte-identical binaries for the fixed host platform; and
- representative server preparation and elaboration produce the same success/failure and semantic query results.

This comparison deliberately does not require raw path strings to match. If the server itself embeds or exposes a path in a way that changes relevant behavior, that observation is a separate path-sensitivity finding rather than a reason to define all path differences as inequivalent.

Basis: **source + derived**.

### Producer state and consumer state are related but not identical

The source supports a useful producer/consumer distinction.

A producer can leave:

- output artifact bytes;
- content-hash sidecars;
- an ordinary build trace containing the full dependency-input tree and build log;
- input-hash-to-output-descriptor cache mappings; and
- package/build-tree placement of outputs.

A cache-seeded consumer fundamentally needs enough state to:

1. compute the same intended current input identity;
2. find the corresponding output mapping;
3. resolve the referenced artifact bytes; and
4. materialize any paths that the downstream consumer requires.

During that process, Lake can synthesize a fetch trace and recreate local `.hash` sidecars or restored files. It need not reproduce the producer's exact trace provenance, log, mtimes, or filesystem topology.

This distinction explains why copying an entire producer workspace is neither necessary nor a particularly precise definition of cache equivalence. The useful contract is the producer identity and output content required to reconstruct a valid consumer state.

Basis: **source + derived**.

### A practical equivalence matrix separates required equality from expected difference

For a fixed host/target and exact toolchain, the following matrix is a useful acceptance contract for Anneal:

| State or observation | Clean vs seeded requirement | Rationale |
| --- | --- | --- |
| Effective traced source/config/toolchain inputs | Equal, except for an explicitly tested equivalence transformation | These values determine the normal cache input identity. |
| Current Lake `depHash` / input cache key | Equal in a hash-mode same-input experiment | A different key means Lake itself sees different traced inputs. |
| `.olean`, `.olean.server`, `.olean.private` bytes | Byte-identical when present and semantically consumed | These are compiler outputs consumed by import/server paths. |
| `.ilean` bytes | Byte-identical | `.ilean` is a distinct module output and is explicitly restored for consumers. |
| IR / generated C / bitcode used by the workflow | Byte-identical for the fixed platform/toolchain | These feed meta/native compilation paths. |
| Native object/library/executable bytes | Byte-identical if the tested workflow claims native-output equivalence | They are separate artifact-producing actions and can include platform/linker inputs. |
| Lake artifact descriptors | Equal when the compared bytes are intended to be the same | Descriptors encode Lake content identity, but are only 64-bit hashes. |
| Existing `.hash` sidecar bytes | Recompute or independently verify; do not trust equality alone | Lake may trust stale sidecars. |
| `.trace` file bytes | **Not required equal** | Clean traces and synthetic fetch traces intentionally encode different provenance. |
| Trace `depHash` and referenced outputs | Semantically equal for the same-input comparison | These are the reuse-relevant identities. |
| Trace `inputs`, `log`, `synthetic` | May differ | Fetch provenance intentionally differs from build provenance. |
| Artifact/cache/build-tree paths | May differ if consumers resolve to the same intended content | Cache artifacts are content-addressed; restoration is selective. |
| mtimes, permissions, hard-link topology | Not required equal | They are placement/provenance state, not content identity; old mode is a separate case. |
| Build action/log | Expected to differ: build versus fetch/replay | The difference proves that both paths were exercised. |
| `ModuleSetup` raw JSON | Not necessarily textually equal | It contains paths. |
| `ModuleSetup` module/package/options + resolved artifact identities | Equal | These are the semantic server-preparation inputs relevant to the fixed environment. |
| Representative import/elaboration/server behavior | Equal | This is the end-to-end consumer check. |

The matrix should be treated as a test specification, not as evidence that the equalities already hold.

Basis: **derived from source**.

### Current Anneal deliberately falls outside ordinary hash-mode equivalence during cache verification

Current `anneal/flake.nix` downloads Mathlib's precompiled cache into a fixed-output derivation and later unpacks its `.ltar` archives into an ordinary `.lake/build` tree. The Aeneas compilation derivation copies those products into vendored package trees before building the Lean backend.

The same derivation then rewrites Git dependencies to final vendored path dependencies. Its comment records the consequence directly: this transformation changes Lake dependency hashes even though the source content and cached artifacts originated from the same upstream revision.

Anneal therefore does not ask ordinary hash-mode Lake to prove that the rewritten consumer state has the same key as the producer state. Instead, it:

1. makes rewritten source/configuration inputs older than the prebuilt outputs; and
2. invokes `lake --old build`.

The derivation later primes an Aeneas package configuration for generated workspaces and rewrites trace paths for relocation.

This is a deliberate compatibility strategy, not a clean/cache equivalence proof. A future Anneal v2 design that wants hash-mode reusable artifacts should avoid treating this old-mode success as evidence that the underlying producer and consumer states have equal dependency identities.

Basis: **source** (`google/zerocopy` current Anneal configuration) + **derived**.

## Boundaries

- **No paired execution was performed.** This report does not establish that a clean producer and a seeded consumer generate or consume byte-identical `.olean`, `.ilean`, IR, generated C/bitcode, native objects, archives, libraries, or executables.
- **No whole-workspace reproducibility claim is made.** Source inspection identifies Lake's identity and substitution mechanism but cannot prove deterministic output of Lean, C/C++ compilers, linkers, archivers, or external generators.
- **Lake content hashes are not cryptographic commitments.** The pinned `Hash` type is a `UInt64`, and the implementation contains an explicit TODO to use a secure hash. Equal Lake descriptors are not sufficient evidence against collision or stale-local-cache corruption.
- **Weak-input differences require their own justification.** Lake intentionally omits some weak arguments from dependency traces. Same-key reuse across such a change reflects Lake's policy, not proof that a hypothetical rebuild would produce the same bytes.
- **Old mode is excluded from hash-mode equivalence.** An mtime-based old-mode reuse can succeed after dependency hashes diverge. Current Anneal uses exactly this mechanism after vendoring/rewrite changes.
- **Relocation is not established here.** The report explains why path-bearing placement state is not automatically part of artifact identity, but it does not prove that every consumer remains correct after relocation.
- **Cross-platform equivalence is not established.** Several native build paths explicitly mix the platform into their traces. Compare native outputs only for a fixed platform unless a separate portability investigation proves a broader contract.
- **Raw server setup equality is intentionally not required.** Path-bearing `ModuleSetup` values can differ. The report proposes a semantic comparison but does not execute one.
- **The #3720 clean-build/cache-seeded equivalence question remains empirically open.** This source-only result can define a rigorous experiment and the meaning of "semantically relevant equivalence"; it cannot substitute for the experiment.

## Evidence

All Lean/Lake source evidence is from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

- **Source:** `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`.
  - `BuildMetadata`, `BuildMetadata.ofBuild`, and `BuildMetadata.ofFetch` define ordinary versus synthetic trace metadata.
  - `SavedTrace.replayIfUpToDate'` and `replayOrFetchIfUpToDate` define ordinary freshness and fetch/replay behavior.
  - `fetchFileHash` defines `.hash` trust and recomputation.
  - `Cache.saveArtifact`, `resolveArtifact`, `restoreArtifact`, and `buildArtifactUnlessUpToDate` define content-addressed cache storage, resolution, restoration, and cache-vs-build selection.
  - `buildO`, `buildLeanO`, `buildSharedLib`, `buildLeanSharedLib`, and `buildLeanExe` show the distinction between weak and traced arguments and platform/toolchain traces.
- **Source:** `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`.
  - `Hash` is a non-cryptographic 64-bit content hash.
  - `BuildTrace` separates trace hash, mtime, caption, and input tree.
- **Source:** `src/lake/Lake/Config/Artifact.lean`, blob `41d6af1a9aa52d6888d3f245df38b4cd76a4dd5d`.
  - `ArtifactDescr` contains content hash plus extension and derives the content-addressed cache path.
  - `Artifact` adds preferred path and mtime; `Artifact.trace` carries content hash and mtime into a build trace.
- **Source:** `src/lake/Lake/Config/Cache.lean`, blob `607e6b92108f30e0a57d0de682f7faa283d7d470`.
  - `CacheMap` maps input hashes to output descriptions.
  - `Cache.writeOutputs` / `readOutputs?` store and retrieve per-package input-to-output mappings.
  - `downloadArtifactCore` verifies the content hash of a remote artifact after download.
- **Source:** `src/lake/Lake/Build/ModuleArtifacts.lean`, blob `9863290328250c33d9933b1569387d96ec244da8`.
  - `ModuleOutputDescrs` enumerates the cached module-output descriptors.
  - `ModuleOutputArtifacts.descrs` discards preferred paths and mtimes when constructing output descriptions.
- **Source:** `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`.
  - `Module.recBuildLean` constructs the module dependency trace and selects cache/local/rebuild paths.
  - `Module.buildLean` runs the producer and computes output artifacts.
  - `Module.restoreNeededArtifacts` and `restoreAllArtifacts` show selective versus complete local materialization.
  - `Module.computeExportInfo` propagates artifact identities into downstream import traces.
- **Source:** `src/Lean/Setup.lean`, blob `38e7f619e852e8ae17d13c94de35a25d279387b6`.
  - `ModuleSetup` exposes module/package identity, imports, path-bearing imported artifacts, dynamic libraries, plugins, and options to consumers such as the language server.

The Anneal-specific evidence is from `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- **Source:** `anneal/flake.nix`, blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`.
  - The derivation at lines 293–350 downloads Mathlib's precompiled cache and preserves its archive/cache material.
  - The derivation at lines 353–386 unpacks `.ltar` files into the build tree.
  - The Aeneas compilation derivation at lines 390–490 copies those products into vendored path packages.
  - Its comments at lines 438–447 state that rewriting Git dependencies to vendored path dependencies changes Lake dependency hashes and therefore verifies the archive with `lake --old build`.
  - The later steps prime package configuration and rewrite traces for the installed archive.

Related current reference reports provide narrower same-revision context but are not substituted for the primary-source evidence above:

- `reports/lean-lake-trace-hash-artifacts-v4-30-0-rc2/REPORT.md` records Lake's Lean identity, output-hash, and trace boundary.
- `reports/lake-olean-invalidation-v4-30-0-rc2/REPORT.md` records module-specific invalidation inputs.
- `reports/lake-server-preparation-v4-30-0-rc2/REPORT.md` records the `serve`/`setup-file` preparation graph and its distinction from ordinary builds.

No fresh **execution** evidence was gathered for this report.

## Revalidation

A capable surface can turn this source-level contract into a direct clean/cache equivalence result with a paired experiment.

1. **Freeze the subject.** Use Lean `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, a fixed platform, exact source revisions, exact package configuration, and a recorded environment. Record weak arguments separately from traced arguments.
2. **Run a genuine clean producer.** Use an isolated workspace/cache in which the target cannot be satisfied from an artifact cache. Run the chosen build in ordinary hash mode. Preserve verbose build-action output, module traces, output mappings, `.hash` sidecars, and all relevant output bytes.
3. **Construct an independent seeded consumer.** Seed only the intended cache mappings/artifact bytes into a fresh state. Remove local target outputs/traces that could turn the test into ordinary local replay. Run the same target in ordinary hash mode and preserve the same evidence.
4. **Prove the two paths were different.** The producer should show producer actions; the consumer should show cache fetch/replay for the intended targets. A seeded run that silently rebuilt does not test cache equivalence.
5. **Compare producer identities.** Confirm that the current normal-mode dependency hashes/cache keys match. If they do not, classify the exact differing traced input instead of falling back to mtime acceptance.
6. **Compare output bytes.** Compute a cryptographic digest for every relevant `.olean`, server/private olean, `.ilean`, IR, generated C/bitcode, and any native object/archive/library/executable in scope. Compare the actual bytes, not only Lake descriptors or preexisting `.hash` sidecars.
7. **Recompute cached hashes.** Use Lake's rehash path where applicable or independently hash the files. This discriminates genuine byte identity from stale trusted sidecars or a corrupted local cache entry.
8. **Compare trace semantics, not trace bytes.** Record `depHash`, output descriptors, and synthetic/build provenance. Expect clean and fetched trace metadata to differ in input-tree/log/synthetic fields.
9. **Compare server preparation.** Run `setup-file` for a representative generated/edited module in both states. Canonicalize artifact/dynlib/plugin paths to their resolved content identities before comparing. Then run a representative server/elaboration query that depends on the prepared imports.
10. **Add discriminating controls.** Change one traced source/config input and verify the normal cache key changes or the cached result is rejected. Separately vary a deliberately weak path input if Anneal intends to rely on that equivalence class, and verify both artifact bytes and consumer behavior rather than assuming the weak-input contract is harmless.
11. **Keep old mode out of the primary witness.** If current Anneal's `--old` archive path is also tested, report it as a distinct compatibility experiment. Its success demonstrates mtime-based acceptability, not equality of ordinary dependency hashes.

If all required artifact bytes and consumer behaviors match, the result can support the broad clean/cache equivalence claim for the exact tested configuration. If only the source-level identity model is revalidated, retain the stronger execution claim as open.
