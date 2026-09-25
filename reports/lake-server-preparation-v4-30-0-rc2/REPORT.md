# Lake language-server preparation versus ordinary builds at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), launching the Lean server and preparing an individual open file are separate Lake operations.

`lake serve` loads the workspace far enough to construct the augmented environment and root-package global server arguments, then spawns `lean --server`. It does not precompute one immutable project-wide setup object for every document. After an individual file worker parses that file's current import header, the worker invokes `lake setup-file <path> -`, sends the parsed header as JSON on stdin, and receives a `ModuleSetup` JSON object for that file.

`setup-file` is not the same operation as an ordinary `lake build` of the edited module. Its top-level build deliberately does not construct a proper trace state for the edited file. Instead, it resolves the file to a workspace module when possible, follows the current in-memory import header, builds or fetches the imports and other dependencies needed for elaboration, computes pre-resolved transitive import artifacts, dynamic libraries, plugins, package/module identity, and server-specific Lean options, and returns those values as `ModuleSetup`. The current edited file remains the language server worker's job to elaborate.

This distinction explains why an ordinary prepared build tree is necessary but not by itself the complete language-server preparation contract. The server still needs a file-specific setup step to map the current document header to import artifacts and server options. Conversely, `setup-file` reuses Lake's normal dependency build/fetch machinery for imports; it is not an independent second compiler pipeline.

The language server can be configured not to build missing/stale dependencies. In that mode the worker invokes `setup-file` with `--no-build --no-cache`; Lake exit code 3 becomes the explicit worker result `importsOutOfDate`, and the worker reports that imports must be rebuilt rather than silently elaborating against an incomplete setup.

No fresh server or Lake execution was performed. The report establishes the exact source-level preparation graph and output contract. It does not establish that a particular prebuilt Anneal archive can satisfy `setup-file` read-only, relocatably, offline, or without rebuilding; those stronger claims require the separate Lake behavior probes.

## Applicability

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- release: `v4.30.0-rc2`
- components: Lake `serve` and `setup-file`; Lean language-server file-worker initialization; `ModuleSetup`.

Current Anneal selects this Lean release through its pinned Aeneas toolchain. This report records behavior of that exact revision. Later Lake changes to package ownership, setup-file output, server bootstrapping, or dependency build policy need separate validation.

"Ordinary build" below means Lake target/module building through the ordinary build graph, not a claim that every invocation of bare `lake build` selects the same targets. The useful contrast is between building persistent module artifacts and the file-specific top-level `setup-file` operation that prepares an edited document for server elaboration.

## Findings

See [`FINDINGS.md`](FINDINGS.md).

## Boundaries

See [`BOUNDARIES.md`](BOUNDARIES.md).

## Evidence

See [`EVIDENCE.md`](EVIDENCE.md). Evidence consists of pinned **source**, upstream source documentation, and checked-in test material; no fresh **execution** occurred.

## Revalidation

See [`REVALIDATION.md`](REVALIDATION.md) for a minimal capable-surface experiment that compares ordinary build state, `setup-file` output, no-build behavior, edited import headers, and server startup.
