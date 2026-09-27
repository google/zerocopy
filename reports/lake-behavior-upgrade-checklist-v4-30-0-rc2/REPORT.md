# Lake behavior upgrade checklist for Anneal

## Summary

Lake is part of Anneal's Lean toolchain contract, not just a command wrapper around `lean`. At the current baseline, Lake is the implementation shipped from `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`). It loads and materializes the Aeneas/Mathlib dependency graph, compiles package configuration, owns build keys and traces, decides when outputs are reusable, interacts with local and remote artifact caches, prepares language-server files, and chooses where several classes of mutable state live.

Those behaviors matter directly to Anneal's prepared-environment design. At the current pin, a complete manifest can make already-materialized Git dependencies avoid fetching, but `lake build --offline` is not itself a network-denial contract. Lean-authored dependency configuration can write into the dependency's own `.lake/config`. Package build state can live inside path dependencies. There is no process-wide build lock. Lake's artifact cache can substitute producer-created bytes for a matching traced input, but that does not prove that a clean rebuild would reproduce those bytes. `lake setup-file` also remains a distinct per-document preparation step even when ordinary build artifacts already exist.

A Lake upgrade therefore needs a behavior checklist, not merely a successful `lake --version` or `lake build`. `lake-upgrade-checklist.json` records twelve gates covering implementation identity, dependency resolution and manifests, configuration and mutable-state ownership, build invalidation, artifact caching, relocation/read-only/offline operation, concurrency, server preparation, native artifacts, clean/cache equivalence, and an integrated behavior probe suite.

Several of these gates intentionally require execution evidence. The current source corpus is strong enough to define what must be tested, but it does not convert source inspection into claims about whole-environment relocation, network silence, contention behavior, or clean/cache equivalence.

## Applicability

The baseline is Lean/Lake `v4.30.0-rc2` at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Aeneas `nightly-2026.06.03` at `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, and current Anneal at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

The Aeneas Lean workspace supplies a concrete `lake-manifest.json` dependency graph. Anneal packages the matching Lean toolchain and prepares/prunes dependency state for later use. The checklist applies when Anneal changes Lean/Lake revisions, changes a prepared-tree or cache policy in a way that depends on Lake internals, or intentionally relies on behavior not established at the current exact pin.

This is narrower than a general Lake release checklist. It focuses on the behaviors that affect Anneal's reproducibility, isolation, offline packaging, parallelism, and interactive-proof plans. A source change in an unrelated Lake command need not trigger every gate.

## Findings

### 1. Pin Lake by the Lean/Lake revision and execution environment

At this baseline, Lake and Lean are developed and shipped together. The exact Lake behavior described by the reference corpus belongs to Lean revision `3dc1a088…`, not to an abstract command name. A new Lean archive can therefore also be a new Lake implementation even when Anneal's Rust/Aeneas inputs are unchanged.

For an upgrade, record the immutable Lean/Lake revision, the platform archive bytes Anneal will execute, and the launch environment that selects the `lake` binary. Adjacent-version source observations are hypotheses to revalidate, not inherited guarantees.

Basis: direct toolchain **source** plus the exact-pin Lake corpus.

### 2. Revalidate manifest and dependency-resolution semantics before trusting a prepared graph

At `v4.30.0-rc2`, Lake resolves one package per base name rather than globally solving one version-constraint system. Git, path, and Reservoir dependencies follow different materialization paths. Once a root manifest exists, ordinary loading treats its locked entries as authoritative; a Git entry records both the exact checked-out `rev` and the requested `inputRev`. Update operations intentionally have different semantics from ordinary loading.

The manifest format is versioned as well. The current writer uses schema `1.2.0`, accepts a range of older versions, and rewrites accepted older formats on update. Ordinary manifest saving is a direct file write, not a general transaction protocol.

A Lake upgrade should diff the manifest schema/compatibility policy, dependency resolution, and update rules, then load the exact Aeneas/Mathlib graph and verify the intended revisions are materialized. Do not assume that an unchanged `lake-manifest.json` has unchanged semantics under a new Lake.

Basis: pinned dependency-resolution and manifest-schema **source analysis**.

### 3. Treat configuration compilation as mutable package state

Lake's package configuration model has a behavior boundary that is easy to miss in read-only designs. At the current pin, Lean-authored `lakefile.lean` configuration is compiled into `<package>/.lake/config/...` state. That is true for dependency packages as well as the root. The cache trace includes package index/name, platform, Lean Git hash, configuration hash, and persisted options; the ordinary validity test compares only a subset of those fields. A stale cache can cause re-elaboration and rewrites inside the dependency tree.

TOML-authored package configuration follows a different path and does not use this compiled Lean-configuration cache. The distinction should be revalidated after a Lake upgrade rather than generalized from one package type to another.

If Anneal expects immutable shared dependency sources, test the exact configured package graph under read-only permissions. A prepared source tree is not read-only merely because no source file is edited intentionally.

Basis: pinned configuration-ownership and config-cache reports.

### 4. Re-map mutable state before reasoning about parallelism

The current state model separates root-workspace state, package-local state, and cache state. A root package normally owns the manifest and Git dependency materialization under its `.lake/packages`. Every loaded package can own its own `.lake/build`, and Lean-authored packages can own `.lake/config`. A path dependency outside the root can therefore receive build/configuration writes in its own tree.

This ownership map is the prerequisite for safe concurrency. Two workers with separate root workspaces can still interfere if they share a path dependency and allow Lake to write the dependency's package-local state. Conversely, immutable dependency sources plus per-worker writable build/workspace state give a much stronger isolation story.

An upgrade should reconstruct the state map from the proposed Lake and test the topology Anneal will actually deploy. Do not rely on directory names alone; ask which package/workspace object owns each write.

Basis: pinned Lake state-model and mutable-state reports.

### 5. Revalidate build-trace inputs and invalidation, not only output timestamps

Current Lake build reuse is trace-driven. Module compilation hashes include the setup/dependency trace, Lean identity, normalized source contents, effective Lean options, module/package identity, selected arguments, and relevant imported/plugin/platform traces. Persisted build metadata records the dependency hash and can carry inputs, logs, and output descriptions. `--old` or missing traces introduce separate modification-time behavior.

That means both under-invalidation and over-invalidation can change across a Lake revision. An upgrade should diff the construction of traces for artifact classes Anneal relies on and identify weak or omitted inputs explicitly. If a new Lake begins tracing an input that was previously untraced, cache reuse may become more conservative without being incorrect. If a formerly traced semantic input disappears, that is higher risk.

Basis: pinned state-model and `.olean` invalidation reports.

### 6. Revalidate the artifact-cache contract separately from ordinary build traces

At the current pin, Lake's artifact cache separates a content-addressed artifact store from package-scoped input-hash-to-output mappings. A cache hit starts from the current dependency-trace hash, resolves output descriptions, and can restore or directly use cached artifacts depending on writability/restoration policy. Cache readability defaults differently from cache writability. Remote-origin metadata can cause a missing content artifact to be downloaded and verified.

This is not the same state as an ordinary target `.trace` file. An upgrade should revalidate key construction, output descriptions, local storage, restoration, writable/readable defaults, and any remote fetch path. If Anneal promises offline execution, a readable cache that can lazily fetch remote bytes is materially different from a fully local cache.

Basis: pinned artifact-cache architecture **source analysis**.

### 7. Keep relocation, read-only operation, and offline operation as separate claims

The current source corpus establishes no single Lake mode that provides all three. Relative manifest paths can relocate with a preserved topology. Already-materialized locked Git dependencies can avoid fetches. But ordinary Lake operations may write manifests, dependencies, configuration caches, build products, traces, hashes, restored artifacts, and cache metadata. The current `lake build --offline` flag is also not a complete network-denial contract because the parsed flag is not propagated through every ordinary build-loading path.

Trace rewriting adds another limit. In ordinary `BuildMetadata`, path-bearing input captions and logs can be explanatory while `depHash` carries freshness identity, but output descriptions are operational state. Compiled-configuration `*.olean.trace` files have another schema whose options can affect later re-elaboration. A blanket textual rewrite of all `*.trace` bytes is therefore not a schema-independent relocation rule.

An upgrade should run relocation, read-only, and network-denial probes independently and then in composition. Observe filesystem writes and network attempts instead of inferring from option names.

Basis: pinned read-only/relocation/offline and trace-rewrite reports.

### 8. Do not infer arbitrary concurrent-writer safety from narrow locks

Lake `v4.30.0-rc2` has no process-wide build lock. Individual subsystems use narrower mechanisms: configuration-cache locks, cache-map locks, race-tolerant insertion of content-addressed artifacts, and similar local protections. Those mechanisms do not serialize arbitrary concurrent mutations of one package build directory, manifest, configuration cache, or output mapping.

This distinction matters for Anneal's parallel testing plans. A shared immutable package/dependency universe can be useful; a shared writable build universe is a stronger and separately testable claim. After an upgrade, re-audit which locks exist and stress the intended topology with multiple consumers/writers.

Basis: pinned mutable-state and read-only/concurrency reports.

### 9. Revalidate `lake serve` and `lake setup-file` as a distinct interactive path

A normal prepared build is not the whole language-server contract. At the current pin, `lake serve` starts the Lean server in a workspace-aware environment, while an open document's worker later invokes `lake setup-file` using the document's current import header. That operation resolves/builds or fetches imports and returns file-specific `ModuleSetup` state: import artifacts, dynamic libraries/plugins, package/module identity, and server options.

`setup-file` can also be asked not to build or use caches; current failure behavior explicitly reports imports out of date in that path. A Lake upgrade can therefore affect interactive operation without changing ordinary `lake build` success.

If Anneal will expose interactive Lean, replay preserved `setup-file` specimens and verify the semantic fields the client/server consumes. A batch-only smoke test is not enough.

Basis: pinned server-preparation report.

### 10. Revalidate host-native artifacts independently of Lean module artifacts

Lake can build more than `.olean` and `.ilean`: generated C/bitcode, host objects, static/shared libraries, plugins, and executables have their own facets and platform-sensitive traces. Some cache hits can leave preferred artifact paths in a cache; other build helpers restore conventional package-local paths because linkers/loaders require them.

Anneal's prepared-tree and pruning logic must therefore classify native products separately from source-level/module artifacts. A Lake upgrade should inventory the native facets actually consumed, verify platform tracing/restoration behavior, and exercise the packaged tree on required host classes.

Basis: pinned native-artifact report.

### 11. Preserve the distinction between cache substitution and clean-build equivalence

A Lake artifact-cache hit at the current pin means: the current traced input hash selected a cached output description and those producer-created bytes were reused. It does **not** prove that rerunning the producer action in a clean tree would emit the same bytes. Build metadata can also differ intentionally between clean and cached paths while the relevant output artifacts remain equivalent.

For Anneal, an equivalence probe should compare three layers: traced producer inputs, byte identity of consumer-relevant outputs, and behavior of consumers such as imports and `setup-file`. Weak/untraced inputs must be considered explicitly. Cryptographic byte comparisons are stronger evidence than reusing Lake's non-cryptographic artifact hashes as proof of equality.

A new Lake may change the cache key or restoration protocol legitimately. The upgrade gate is therefore behavioral: does the new clean/cache composition satisfy Anneal's needed equivalence, not does it reproduce internal metadata verbatim?

Basis: pinned clean/cache-seeded equivalence report.

### 12. End with a compact behavior-probe suite over the packaged environment

The source reports above identify the state and invariants that can drift. The final upgrade gate should exercise them together using Anneal's exact packaged environment. A compact matrix should cover:

- locked dependency materialization with and without already-present checkouts;
- relocation of a prepared tree;
- read-only dependency/package state;
- explicit network denial;
- multiple concurrent consumers and, separately, any intended shared writers;
- ordinary build reuse and stale-input invalidation;
- cache-seeded restoration versus clean build;
- `lake setup-file`/server preparation for a generated Lean file.

Record filesystem topology and permissions, commands, environment variables, network/write observations, trace/artifact hashes, diagnostics, and expected failures. These probes should be small enough to carry forward to later Lake revisions. They are more valuable as a stable compatibility harness than as a one-off benchmark.

Basis: **derived** from exact-pin source findings; the stronger whole-environment claims require **execution**.

## Boundaries

- No newer Lean/Lake revision was selected or evaluated. This report defines upgrade gates from `v4.30.0-rc2`; it does not approve adjacent behavior.
- No fresh Lake/Lean/Aeneas/Nix execution was performed for this report.
- Source inspection establishes the state model and candidate invariants to test. It does not establish network silence, filesystem permission behavior, race freedom under contention, relocation success, or clean/cache equivalence for an arbitrary packaged tree.
- `lake-manifest.json` locks dependency materialization; it is not build-freshness state.
- A build `.trace`, a configuration `.olean.trace`, an artifact-cache mapping, and a module `.hash` are different state classes. Their filenames do not justify one generic rewrite or migration rule.
- Read-only, relocatable, offline, and concurrent are independent properties. Passing one does not imply the others.
- A cache hit is not proof that a clean producer run would generate identical bytes.
- A process-local or subsystem lock is not evidence of general multi-process build serialization.
- Server preparation is a separate consumer path from ordinary batch build and must be tested only if Anneal relies on it.
- The machine-readable checklist is an aid to revalidation. Current Anneal authority and newer precisely scoped evidence remain controlling.

## Evidence

**Direct environment source.** `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`:

- `backends/lean/lean-toolchain` (blob `6c7e31fffe3e03be3e0d7021acd9cd848e44db26`) selects the Lean/Lake toolchain;
- `backends/lean/lake-manifest.json` (blob `1a5af703163d8b39f4311aafe22ae171788179ee`) records the concrete dependency graph used by the generated Lean project.

**Direct Anneal packaging source.** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, `anneal/flake.nix` (blob `433fcf5c64da4f51b9fac471f1faf45c1f730cba`), packages the Lean/Lake environment whose behavior Anneal consumes.

**Published exact-pin Lake evidence.** Current `google/zerocopy` reference state `b59ccc6a33c219354126ab524ad4c503ea0e8d0b` contains focused reports for:

- Lake's workspace/package/build/trace state model;
- dependency resolution and manifest schema/locking;
- package configuration ownership and config-cache invalidation;
- module invalidation inputs;
- artifact-cache architecture;
- trace relocation/rewrite boundaries;
- read-only, relocation, offline, and concurrency source behavior;
- server preparation;
- clean-build versus cache-seeded equivalence criteria;
- mutable-state ownership; and
- Lean-package native artifacts.

`lake-source-map.json` records the exact report blobs. Those reports preserve the underlying pinned implementation paths and source evidence; this checklist composes their version-sensitive boundaries and preserves the places where execution is still required.

## Revalidation

When Anneal considers a new Lean/Lake revision or changes a Lake-dependent packaging assumption, copy `lake-upgrade-checklist.json` and attach evidence to the applicable gates.

A narrow efficient sequence is:

1. **Resolve the implementation and graph.** Record the exact Lean/Lake revision, archive bytes, Aeneas manifest, and package materialization identities.
2. **Diff state ownership and invalidation first.** Changes here determine whether later probes are testing isolated workspaces or accidentally sharing mutable state.
3. **Diff manifest, trace, configuration-cache, and artifact-cache schemas/semantics.** Update any path transformation or prepared-state logic field-by-field; do not mass-rewrite by filename suffix.
4. **Run relocation/read-only/offline/concurrency probes.** Use filesystem permissions and network denial that make violations observable.
5. **Run clean/cache and stale-input probes.** Compare exact consumer-relevant bytes and behaviors, not only internal trace metadata.
6. **Replay `setup-file`/server preparation if interactive use is in scope.** Verify imported artifact identities and expected no-build failure behavior.
7. **Run the integrated packaged matrix.** Use the exact paths, permissions, caches, dependency tree, and platform environment Anneal will ship.
8. **Preserve the result.** Store immutable revisions, manifests, commands, topology, observed writes/network use, artifact digests, and diagnostics so the same matrix can distinguish the next Lake revision.

If the upgrade changes only one subsystem, rerun the smallest transitive set of gates that depends on it. For example, an artifact-cache implementation change need not force a new manifest-resolution study, but it does require cache, offline/network, restoration, clean/cache-equivalence, and any consumer paths that use restored artifacts. A Lean/Lake revision change that touches configuration or build-state code can reach substantially more of the matrix.
