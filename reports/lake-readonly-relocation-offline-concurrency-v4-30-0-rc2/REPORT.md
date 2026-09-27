# Lake read-only, relocation, offline, and concurrency behavior at Lean v4.30.0-rc2

## Summary

At `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), Lake does not provide one switch that makes a prepared environment read-only, relocatable, offline, and safe for arbitrary concurrent use. Those properties come from a narrower state contract.

A complete locked manifest is the first boundary. Manifest path entries are relative to the package containing the manifest, and Lake re-roots them under the current workspace. A prepared dependency graph can therefore preserve its dependency identities after relocation when its relative topology is preserved. A locked Git dependency that is already checked out at the recorded revision also avoids a fetch during ordinary materialization. By contrast, a missing manifest sends ordinary workspace loading through dependency update/materialization, and an absent or wrong-revision Git checkout can clone or fetch.

`lake build --offline` is not a network-denial contract at this revision. The CLI parses `--offline`, but ordinary build loading does not propagate that field into `LoadConfig`; `new` and `init` do. Separately, `LAKE_NO_CACHE` / `--no-cache` controls build-cache downloading, not Git or Reservoir dependency access. An offline build therefore depends on the prepared local state: locked dependencies must already be materializable without network access, and every build artifact that Lake intends to obtain remotely must already exist locally or be reproducible without the network.

Read-only consumption is also conditional. Lake can write manifests, dependency checkouts, build products, setup files, `.trace` files, `.hash` files, restored artifacts, and cache metadata. A package tree is safe to expose read-only only when the selected load/build path does not need those writes, or when all mutable state lives elsewhere. Lake's artifact cache helps separate immutable content from package-local build trees, but it does not make every package operation read-only.

Lake has no process-wide build lock at this revision. Its source contains narrower race handling: content-addressed artifact insertion tolerates competing creators, some cache-map files use shared/exclusive file locks, and immutable cache artifacts are made read-only where practical. Those mechanisms do not serialize arbitrary concurrent writes to the same package source tree, build directory, manifest, trace files, or output-mapping paths. Concurrent consumers are strongest when they share only immutable or read-only prepared state and keep their writable workspaces/build state separate.

Anneal V1 provides useful historical execution evidence for that pattern. Current `google/zerocopy` history preserves a regression test that installs a Nix-built Aeneas archive, asserts the archive has no write bits, creates a fresh generated workspace with a complete relative manifest, then runs `lake --old build Generated` and `lake env lean --json` against the archive. Earlier V1 work records why this became necessary: direct writable-looking path dependencies caused races, the old worker/cache-clone approach consumed large amounts of disk, and later work found that `--old` alone was insufficient when mtimes or package-configuration state invalidated the prepared outputs.

That historical test does not prove the stronger current-pin claims by itself. No fresh Lake execution was performed for this report. Source inspection establishes the dependency-resolution, write, cache, and locking mechanisms at the exact v4.30.0-rc2 pin; preserved Anneal tests establish that one prepared-archive design worked in its recorded environment. A fresh exact-pin probe remains necessary before claiming that an arbitrary prepared Lake environment can be relocated, consumed read-only, run without network access, or shared concurrently with no writes or rebuilds.

## Applicability

- repository: `leanprover/lean4`
- revision: `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`
- release: `v4.30.0-rc2`
- component: Lake sources shipped in this Lean tree
- historical Anneal evidence: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, especially `anneal/v1/`
- Anneal context: current Anneal selects this Lean release through its pinned Aeneas toolchain.

This report is about ordinary Lake workspace loading and build behavior. It distinguishes four properties that are often bundled together:

1. **relocation** — whether a prepared dependency/build state remains usable when its filesystem root changes;
2. **read-only consumption** — whether the selected operation needs to mutate prepared dependency state;
3. **offline operation** — whether the selected operation can complete without network access; and
4. **concurrent consumption** — whether several processes/workspaces can safely use shared state at once.

A fact about one property is not evidence for the others. In particular, a relative manifest does not prove build artifacts are relocation-independent, and a content-addressed cache does not prove arbitrary concurrent writers are safe.

## Findings

See [`FINDINGS.md`](FINDINGS.md).

## Boundaries

See [`BOUNDARIES.md`](BOUNDARIES.md).

## Evidence

See [`EVIDENCE.md`](EVIDENCE.md). The primary current-pin evidence is pinned **source** and source documentation. Historical Anneal issues and checked-in tests provide **historical rationale** and **preserved execution-oriented regression evidence**. No fresh execution was performed for this report.

## Revalidation

See [`REVALIDATION.md`](REVALIDATION.md) for the minimal capable-surface probe that separates dependency relocation, package-tree writes, network attempts, cache writes, and concurrent behavior.