# Compact Lake/cache execution probes and Mathlib boundaries at v4.30.0-rc2

## Summary

The compact synthetic Lake suite supports four practical distinctions: seed a complete relative manifest before a workspace's first Lake load; keep shared dependency sources/build products immutable while consumers use separate workspace state; treat artifact-cache writers separately from shared package-directory writers; and compare clean versus cache-seeded output across more than `.olean` bytes. One small cache experiment observed successful concurrent consumers and successful concurrent artifact-cache publication, while concurrent writers rebuilt the same shared package outputs. Mathlib source identifies a platform-sensitive artifact contract, but no cross-architecture archive comparison was run.

## Applicability

Lake/Lean source is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`); Mathlib is `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Executions ran on macOS arm64 against tiny synthetic packages. This package condenses the probe suite; existing package-config and cache-architecture reports provide the fuller source traces.

## Findings

### Read-only use, relocation, setup-file, and offline qualification

A fresh consumer with a complete relative `lake-manifest.json` present before first invocation consumed a relocated read-only producer. Without the consumer manifest, Lake attempted to create a configuration lock beneath the producer package. The same setup path affected `setup-file` and `lake env lean --json`. A prepared fixture ran under `--offline`, but that option was not verified as a network-denying harness; do not claim a proven zero-network build. A source-only producer failed `--no-build`, then rebuilt successfully with a normal build.

Basis: execution; detailed table and command output in `lake-execution/RESULTS.md` and `lake-probes-runs.json`.

### Cache environment, clean/cache equivalence, and outputs that matter

With `LAKE_ARTIFACT_CACHE=true` the fixture populated eight entries in its configured cache; with `LAKE_CACHE_DIR=''` no custom cache was used. Clean, cache-seeded, and rebuilt fixture outputs had byte-identical `Generated.olean`, `.ilean`, and generated `.c` hashes, and the downstream theorem was accepted. Trace files differed because they include absolute paths even though the observed depHash and output descriptors matched. `setup-file` and `lean --json` also need comparison; equal OLean bytes alone do not prove equivalent package context.

Basis: execution + Lake source. Additional dimensions for `.olean.server`, `.olean.private`, hashes, native outputs, references, diagnostics, and traces are tabulated in `lake-execution/RESULTS.md`.

### Concurrency boundaries

Two separate consumers concurrently read a frozen producer and both passed without changing its file inventory. Two consumers concurrently building against the same writable source-only producer both reported building the same `Dep` outputs. Two independent source-identical packages writing to a shared `LAKE_ARTIFACT_CACHE` both succeeded and a third consumer fetched the artifact; this one run is a successful concurrent publication specimen, not a stress or crash-consistency proof. Preserve workspace-local mutable `.lake` state per consumer and serialize or isolate shared producer writes.

Basis: execution + source. Results in `lake-concurrency/`.

### Package-config and server trace priming

At this Lake revision the package configuration cache is under the dependency's `.lake/config/<assigned-name>/` and its trace identity includes assigned package index/name, config hash, platform, and Lean hash. A read-only package-config primer must run in the intended consumer identity before freezing the dependency. `setup-file` is a useful direct check that Lake's server-facing import artifacts resolve, but a fresh manifest/config miss may attempt writes before the server can start. This package preserves the execution distinction; the existing `lake-package-config-priming-v4-30-0-rc2` report contains the precise source algorithm and Anneal primer identity.

Basis: source + execution.

### Mathlib cache/platform architecture

At the pinned Mathlib revision, each module's `.ltar` is named from Mathlib's module hash; its header carries a separate Lake depHash checked against the installed trace. The logical packed set requires trace, OLean/hash, ILean/hash, and generated C/hash, with server/private OLean, IR, and extra outputs optional when present. Mathlib redirects dependency package paths during extraction. Its behavior and the Nix packaging source select host-specific tool/cache assets, so treat archives/build products as toolchain/platform-specific until directly compared. No AArch64-vs-x86_64 or Linux-vs-macOS `.ltar` was fetched or compared in this run.

Basis: source; see `mathlib-cache-artifact-format-v4-30-0-rc2` for pinned paths and details.

## Boundaries

Synthetic two-module Lake fixtures are not a Mathlib-sized or real Aeneas generated environment. Concurrent cache publication was one small successful schedule. Concurrent shared package build writes are not established safe by successful completion. `--offline` was not enforced by firewall. No cross-platform cache artifact equivalence, Mathlib download/reconstruction, or native plugin equivalence was tested. The test covers an observed set of semantically relevant artifact dimensions, not every possible Lean/Lake state.

## Evidence

- Lean/Lake: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Mathlib: `leanprover-community/mathlib4@5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Lake execution transcript: `lake-execution/`; cache concurrency records: `lake-concurrency/`.
- Source reports: `lake-package-config-priming-v4-30-0-rc2`, `mathlib-cache-artifact-format-v4-30-0-rc2`, and `lake-clean-cache-seeded-equivalence-v4-30-0-rc2`.
- Pinned Lake source regions: `src/lake/Lake/Build/Module.lean`, `src/lake/Lake/Config/Cache.lean`, and `src/lake/Lake/Load/Lean/Elab.lean` at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Mathlib packing/unpack source: `Cache/IO.lean` and `Cache/Hashing.lean` at `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## Revalidation

Use one frozen package universe and two fresh consumer workspaces. Seed their exact relative manifests before any Lake command; capture producer hashes/mtimes and consumer `.lake` writes; run `build`, `--no-build`, `setup-file`, batch JSON diagnostics, and LSP setup. Separately race artifact-cache writers and package-directory writers under interruption, and compare archive hash/key/header/contents on each target platform. Establish network denial independently of Lake's `--offline` flag.
