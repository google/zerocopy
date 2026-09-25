# Lake package, workspace, build, and trace state at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake separates several kinds of state that are easy to conflate.

A **package** is a loaded package configuration plus concrete filesystem identity: its package directory, configuration file, manifest path, build directory, declared dependencies, targets, and related settings. A **workspace** is rooted at one package and adds the resolved package set, package-name map, facet configurations, detected toolchain/environment, and system Lake configuration. The root package's `lake-manifest.json` records how remote and path dependencies should be materialized; it is dependency-resolution/materialization state, not a record of whether compiled artifacts are current.

Lake's build graph uses typed build keys. A target names something buildable such as a module, package target, or package module. A facet names a projection or build product of another target. Fetching a target or facet resolves a build function through the build index and produces a `Job`. Jobs execute asynchronously and carry a `BuildTrace`, build action, log, rebuild status, and timing.

Artifact freshness is tracked separately from the manifest. A `BuildTrace` combines a dependency hash with the maximum relevant modification time and retains a tree of input traces for explanation. Successful build actions can persist `BuildMetadata` in target-specific trace files. At this revision, when such a trace exists, the ordinary up-to-date check compares the current dependency hash with the saved dependency hash. With old mode enabled, a hash mismatch can fall back to modification time. If no saved trace exists, Lake falls back to output-versus-input modification times. File hashes can themselves be cached in adjacent `.hash` files and trusted unless the configured mode requests rehashing.

The result is a layered state model: configuration determines package/workspace structure; the manifest determines dependency materialization; build keys/facets identify requested build products; jobs execute the graph; artifacts hold outputs; and traces/hashes decide whether outputs can be reused. These layers have different ownership and invalidation rules. Treating `lake-manifest.json`, `.lake/build`, or a trace file as interchangeable "Lake cache state" loses distinctions that matter for reproducibility and prepared-environment design.

No fresh Lake or Lean execution was performed. This report establishes the source-level state model and ordinary reuse decision at the exact pin. It does not establish relocation, read-only consumption, offline behavior, concurrent sharing, or clean-build versus cache-seeded equivalence; those require separate source study and, for the stronger claims, execution.

## Applicability

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- release: `v4.30.0-rc2`
- component: Lake sources shipped in this Lean tree
- Anneal context: current Anneal selects this Lean release through its pinned Aeneas toolchain.

This report uses "configuration" for the package/workspace values loaded from Lake configuration files and related environment/system configuration. It uses "manifest" for the serialized dependency-materialization record. It uses "trace" for Lake build dependency/freshness state. Those terms name different source-level types at this revision.

Adjacent Lean/Lake releases are not assumed to share this behavior. In particular, later changes to package configuration ownership, trace formats, cache behavior, or server setup require separate reports.

## Findings

See [`FINDINGS.md`](FINDINGS.md).

## Boundaries

See [`BOUNDARIES.md`](BOUNDARIES.md).

## Evidence

See [`EVIDENCE.md`](EVIDENCE.md) for exact source files and blob identities. The evidence is pinned **source** and source documentation. There is no fresh **execution** evidence.

## Revalidation

See [`REVALIDATION.md`](REVALIDATION.md) for the cheapest source diff and a minimal capable-surface probe that distinguishes manifest state, build artifacts, saved traces, hash reuse, and old-mode fallback.
