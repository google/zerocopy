# Boundaries

- No fresh `lake`, Lean compiler, server, cache, or filesystem experiment was run.
- This package establishes the source-level state model and ordinary freshness logic at Lean/Lake `v4.30.0-rc2`; it does not establish observed behavior for a concrete Anneal workspace.
- It does not establish that every Lake command uses exactly the same trace/reuse helper. The report follows the shared build machinery and representative module path rather than exhaustively proving every target implementation.
- It does not inventory every field of `PackageConfig`, `WorkspaceConfig`, `BuildConfig`, cache configuration, artifact-store configuration, or every built-in facet.
- It does not establish all source/configuration changes that invalidate every Lean artifact. The module path shows important traced inputs, but the detailed invalidation matrix remains a separate inventory subject.
- It does not establish relocation behavior. Absolute paths are present in loaded package values, but whether a serialized prepared environment can be moved safely requires inspection and execution across manifests, traces, artifacts, and setup commands.
- It does not establish read-only behavior. The source shows writes to manifests, trace files, hash sidecars, build directories, and caches on relevant paths, but a read-only consumer may avoid some producer paths. Which writes are attempted by a concrete command needs a dedicated report/probe.
- It does not establish offline behavior. Dependency materialization and artifact fetching can involve remote services; exact network triggers are separate.
- It does not establish concurrency safety for shared package trees, build products, trace files, or artifact caches.
- It does not establish clean-build versus cache-seeded semantic equivalence.
- It does not treat Lake's 64-bit build hashes as cryptographic integrity guarantees; the source explicitly notes they are not secure hashes.
- It does not assume adjacent Lean/Lake releases preserve the same manifest schema, trace format, package ownership, or build algorithm.
