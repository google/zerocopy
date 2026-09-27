# Anneal V1 clean-workspace consumption of the prebuilt archive

## Summary

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, retained Anneal V1 is designed to create a new, workspace-owned Lean project while consuming Aeneas and its transitive Lean dependencies directly from the installed prebuilt toolchain archive. The dependency side of that boundary is intended to remain immutable: Anneal generates a complete root `lake-manifest.json` whose Aeneas and inherited package entries are path dependencies relative to the final generated workspace, then runs Lake with `--old` so the archive's already-prepared build products remain reusable. The generated workspace owns the state that can change across verification runs.

The checked-in archive-reuse regression test makes the contract unusually explicit. It creates a fresh temporary Lake workspace, asserts that the installed Aeneas tree has no write bits, writes a tiny generated Lean module plus a complete relative manifest, and runs both `lake --keep-toolchain --old build Generated` and `lake --keep-toolchain env lean --json generated/Generated.lean`. This directly tests the architectural condition that a clean consumer workspace can use the prepared archive without first copying the dependency graph into a mutable facsimile.

The contract arose from V1's earlier Lake integration failures. PR #3450 records that `--old` alone was insufficient: fresh archive-input mtimes could invalidate outputs, and an incomplete root manifest could make Lake reconfigure path dependencies and write lock/configuration state into read-only package trees. PR #3453 then encoded the replacement design as an installed-archive regression. The important invariant is therefore stronger than “a cache exists”: the archive provides the dependency universe and prepared products; a fresh generated workspace provides the mutable consumer state and a complete locked view of that universe.

This report does not claim that every Lake operation is read-only against the archive, that no fallback can ever rebuild or touch the network, or that the current source inspection reproduces a successful exact-pin run. Those broader properties are separate subjects. It records the concrete V1 clean-workspace/prebuilt-archive contract, how current code realizes it, and which regression test is intended to defend it.

## Applicability

The primary subject is retained Anneal V1 at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`. At that revision, `anneal/v1` remains the complete verification implementation; its setup code resolves an Exocrate-installed omnibus toolchain containing Aeneas, Lean, Rust, and prepared Lake state.

Two historical transitions explain the contract preserved by the current code:

- PR #3450, revision `f6aeb9bd14ee0196635f7e1e46bf0641b16950b6`, removed V1's generated-workspace copies/symlinks of dependency Lake state and introduced the complete relative root-manifest approach.
- PR #3453, revision `93cab05584dc15cf9f12236ec0ef24becd21beb0`, added the regression test that installs/uses the prepared archive as a read-only dependency universe from a fresh consumer workspace.

The current implementation has evolved since those commits, so the historical PR descriptions establish design motivation rather than current code identity. Current implementation claims below are bound to `41f5b37...` source.

“Clean workspace” here means a newly created generated Lean workspace with no preexisting workspace-local `.lake` state. It does not mean a toolchain installation built from scratch: the dependency universe is intentionally prebuilt and installed before verification. “Read-only archive” refers specifically to the prepared dependency/toolchain side; the generated workspace remains writable.

Basis: **source** + **documentation** from the historical PR descriptions.

## Findings

### V1 separates immutable dependency state from mutable consumer state

`anneal/v1/src/setup.rs` resolves an installed Exocrate toolchain rather than constructing Aeneas and Lean dependencies during each verification. Its `Toolchain` exposes stable locations for the Aeneas root/backend, Lean sysroot, Rust sysroot, and archive-owned Lake cache.

`anneal/v1/src/aeneas.rs` then creates the verification project's Lean workspace separately. The generated workspace contains generated Aeneas output, Anneal support code, user proofs, a generated `lakefile.lean`, and a generated root `lake-manifest.json`. Its Lake commands point at the installed Lean toolchain rather than requiring a separate per-workspace toolchain installation.

This creates two ownership domains:

```text
installed toolchain archive
  dependency sources + prepared dependency artifacts + tool binaries
  intended to be shared and immutable during verification

generated verification workspace
  generated/user Lean files + root Lake project + workspace-local state
  owned by one verification workspace and allowed to change
```

The separation is the central architectural fact. Prebuilding artifacts without separating mutable state would not be enough: earlier V1 designs still exposed shared dependency configuration trees to workspace-specific Lake writes.

Basis: **source** in `anneal/v1/src/setup.rs` and `anneal/v1/src/aeneas.rs`; **derived** ownership model from those paths plus PR #3450/#3453 history.

### The generated root manifest is part of the reuse contract, not incidental metadata

Current `generated_lake_manifest` reads the installed Aeneas `lake-manifest.json` and constructs the consuming workspace's complete root manifest. The generated manifest includes Aeneas itself and every inherited Aeneas dependency as a path package.

The construction rebases package directories relative to the *final generated workspace location*. It also marks transitive entries inherited and preserves the package metadata needed by Lake while removing archive-internal fields that should not be copied as consumer identity. The root manifest therefore does more than accelerate dependency discovery: it tells the consumer workspace exactly which already-materialized package directories make up its dependency graph.

PR #3450 records why completeness matters. Without a complete root manifest, Lake could reconfigure path dependencies. That configuration step wrote state into package-local trees which Anneal intended to keep read-only. The complete root manifest is therefore part of the write-avoidance boundary as well as the dependency-resolution boundary.

Basis: **source** in current `anneal/v1/src/aeneas.rs`; **documentation** in PR #3450.

### `--old` is one component of reuse, not the whole mechanism

The main current V1 dependency build invokes:

```text
lake --keep-toolchain --old build Generated Anneal
```

The `--old` mode is intentionally paired with archive preparation. Historical PR #3443 normalized vendored source/configuration mtimes so that prepared outputs compare as newer; PR #3450 records that `--old` by itself was not sufficient if archive inputs had fresh mtimes or if Lake still decided it needed package reconfiguration.

Accordingly, the V1 reuse contract is conjunctive:

1. the archive already contains prepared dependency sources and build products;
2. archive preparation gives Lake freshness state compatible with reuse;
3. the consuming workspace has a complete manifest, avoiding dependency re-resolution/reconfiguration;
4. the generated workspace points at the archive rather than copying its dependency tree; and
5. V1 invokes the selected build path with `--old`.

Removing any one of these conditions can change the behavior. In particular, the presence of prebuilt `.olean` files does not by itself guarantee that Lake will reuse them.

Basis: **source** in current `anneal/v1/src/aeneas.rs`; **documentation** in PR #3443 and PR #3450; **derived** conjunction from the combined mechanism.

### The regression test begins from a genuinely fresh consumer workspace

`run_archive_lake_cache_reuse_test` creates a new temporary directory and calls `assert_archive_lake_cache_reuse`. That helper creates `generated-workspace/` from scratch, writes only the files needed for a tiny Lake project, and does not seed a workspace-local `.lake` directory before invoking Lake.

The test writes:

- a copied `lean-toolchain` file;
- `generated/Generated.lean` containing `import Aeneas`;
- a minimal `lakefile.lean` requiring Aeneas; and
- a complete root `lake-manifest.json` derived from the installed archive's Aeneas manifest.

It then runs:

```text
lake --keep-toolchain --old build Generated
lake --keep-toolchain env lean --json generated/Generated.lean
```

This is stronger than testing a warm workspace which may already have consumer-local configuration/build traces. The test specifically exercises whether the installed dependency universe is sufficient for a new consumer to build/check a module importing Aeneas.

Basis: **source** in `anneal/v1/tests/integration.rs` at blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`.

### The test makes Aeneas physically non-writable before consumption

Before it creates the consumer project, `assert_archive_lake_cache_reuse` calls `assert_no_write_bits(&aeneas_root)`. That helper recursively walks the installed Aeneas tree and fails if any ordinary non-symlink entry has a write bit set.

This turns a design assumption into an observable precondition for the test. If the tested Lake path needs to mutate the Aeneas tree, the subsequent command should fail rather than silently hiding the write in a permissive installation.

The check is intentionally narrower than “the entire toolchain is immutable”: this helper verifies the Aeneas tree. Other installed-toolchain paths may have distinct permissions or roles. The report therefore does not generalize this exact assertion to every file below the Exocrate installation root.

Basis: **source** in current `anneal/v1/tests/integration.rs`.

### The test exercises both Lake build reuse and direct Lean checking in the prepared environment

The archive regression has two consumer operations. The first asks Lake to build the generated library with `--old`; the second uses `lake env lean --json` to check the generated module directly.

That distinction matches V1's production verification path. V1 first uses Lake to prepare/build the shared generated libraries and then invokes Lean on individual generated specification files through `lake env lean --json`. A clean-workspace regression that tested only `lake build` would therefore omit a meaningful part of the actual V1 consumption path.

The two commands do not establish every future interactive or language-server use of the archive. They establish the batch build/direct Lean checking path encoded by V1 and defended by this regression.

Basis: **source** in current `anneal/v1/tests/integration.rs` and `anneal/v1/src/aeneas.rs`.

### Relative manifest paths are computed for the final workspace location

Both production manifest generation and the archive regression compute dependency paths relative to the consumer workspace. Current production code takes additional care because the Lean workspace is staged in a temporary directory and then renamed: it computes manifest paths for the final post-rename location instead of accidentally embedding the staging path.

This means the clean-workspace contract does not depend on reproducing the producer's absolute archive root inside the generated project. It does, however, still depend on the relative relationship between the generated workspace and the installed package paths at the time the manifest is constructed.

Full generated-workspace relocation is a separate inventory item. This report only records the path construction needed to create a correct fresh workspace at its intended final location.

Basis: **source** in current `anneal/v1/src/aeneas.rs` and `anneal/v1/tests/integration.rs`.

### The current architecture deliberately no longer reconstructs a per-workspace dependency tree

PR #3438 moved retained V1 onto the same Nix-built omnibus archive used by V2. PR #3450 then removed V1's archive-cache symlink/copied-package model from generated workspaces. The current source no longer contains the earlier worker-cache/smart-clone architecture or the later generated-workspace symlinking of dependency `.lake/build` trees.

The consumer project instead points through its complete manifest to packages in the installed archive. This reduces both disk amplification and the number of duplicated representations of the dependency graph.

That does not make the generated workspace “stateless.” Lake and Lean can still create workspace-local output/configuration state. The point is that dependency *ownership* is no longer transferred into a mutable per-workspace facsimile merely so V1 can consume prebuilt artifacts.

Basis: **documentation** in PR #3438/#3450 + **source** at current `41f5b37...`.

### The archive-reuse test is a regression specification, not proof that fallback is impossible

The test's success criterion is process success while Aeneas is read-only. It does not independently instrument every filesystem write, network access, configuration event, artifact restoration, or rebuild decision. Lake could in principle perform some fallback that stays within writable workspace-local state and still pass.

Likewise, source inspection here does not establish that current CI has run this exact test successfully at `41f5b37...`, nor does it provide a trace proving that every dependency artifact was reused rather than rebuilt somewhere writable.

For Anneal architecture work, the robust interpretation is therefore:

- the code defines a clean-workspace/read-only-dependency contract;
- the regression is designed to fail when that contract requires writes into Aeneas;
- stronger claims such as “zero dependency rebuilds,” “zero network,” or “no unexpected workspace fallback” require dedicated observability/probes.

Basis: **source** + **derived** limitation from what the test observes.

## Boundaries

**No fresh execution.** This investigation inspected exact source and historical PR state but did not run the current archive test or a V1 verification against an installed archive. The report therefore records the implemented/tested contract, not a newly reproduced runtime observation.

**Not a full Lake read-only/offline/concurrency report.** The corpus already has broader Lake reports covering read-only state, offline behavior, concurrency, cache keys, and fallback boundaries. This report preserves V1's concrete consumer architecture rather than replacing those subjects.

**Not a generated-workspace relocation report.** Relative manifest construction is relevant here because a fresh workspace needs valid dependency coordinates. Moving an already-created generated workspace or relocating the installed archive after manifest creation is a separate question.

**Not proof of zero rebuild.** `--old`, prepared mtimes, and a complete manifest are intended to preserve reuse, and the read-only Aeneas assertion constrains where a rebuild may write. The checked-in test does not emit a machine-readable “reused N artifacts, rebuilt 0” account.

**Not proof of zero network.** The tiny archive regression does not instrument network syscalls or run in a network-disabled namespace. Missing/stale source behavior and Lake's broader network fallbacks are separate subjects.

**Aeneas read-only is the explicit permission check.** The current helper checks write bits recursively under the installed Aeneas root, not the entire installed toolchain root. Do not silently widen that exact observed precondition.

**Historical PR descriptions are explanatory evidence.** PR #3450/#3453 explain why the architecture changed and what their authors intended. Current behavior claims use current source; old PR prose is not substituted for the current implementation.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-27.

Primary current subject: `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/v1/tests/integration.rs`, blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`: `run_archive_lake_cache_reuse_test`, `assert_archive_lake_cache_reuse`, `assert_no_write_bits`, `write_relative_archive_manifest`, and `run_lake_archive_command`.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: production generated-workspace construction, `write_lake_manifest` / `generated_lake_manifest`, final-workspace path rebasing, Lake build invocation, and `lake env lean --json` checking path.
- `anneal/v1/src/setup.rs`, blob `32216cedf11c5d6d4b5a4618d8d7bf2578e44b4d`: Exocrate toolchain resolution and installed Aeneas/Lean/Rust layout.

Historical architecture evidence:

- PR #3438, head `47d907d6fa27610a0900f075c0bec879777107a9`: moved retained V1 and V2 onto the same Nix-built omnibus archive.
- PR #3443, head `11bf7f723639c90d6fa88b5dfd9333ec89c5f763`: records the `--old`/mtime requirement for replaying prepared Lake products in the read-only archive.
- PR #3450, head `f6aeb9bd14ee0196635f7e1e46bf0641b16950b6`: records why a complete root manifest was needed and removes generated-workspace package/build symlinking.
- PR #3453, head `93cab05584dc15cf9f12236ec0ef24becd21beb0`: introduces the clean fresh-workspace/read-only-archive regression contract.
- Issue #3668, observed 2026-09-27: retrospective description of the producer/consumer split and the historical sequence of Lake-integration failures and fixes.

Evidence roles are **source**, **documentation**, and **derived** synthesis. No fresh **execution** evidence was produced in this investigation.

## Revalidation

For another Anneal revision, the cheapest source-level revalidation is:

1. inspect `anneal/v1/src/setup.rs` and identify the installed toolchain/archive ownership boundary;
2. inspect V1 generated-workspace construction and confirm whether it copies/symlinks dependency state or instead points at the installed dependency universe;
3. inspect root-manifest generation and verify that Aeneas plus all inherited packages are represented and that their directories are valid for the workspace's final location;
4. inspect the Lake build and direct Lean invocation flags; and
5. inspect the archive-reuse regression and confirm what installed roots it actually makes read-only.

The cheapest behavioral probe should materialize/install the exact archive and then create a brand-new writable workspace. Make the dependency archive physically read-only, deny network access, run the production-equivalent build/check commands, and record filesystem writes plus Lake reuse/rebuild events if available. A useful result should distinguish:

```text
dependency-tree writes: 0
network accesses: 0
package reconfigurations: 0
dependency artifact rebuilds: 0
workspace-local writes: allowed and inventoried
```

Then repeat from a second new workspace against the same installed archive. This separates “a warm workspace can rerun” from the contract this report preserves: independent clean consumers can share one prepared immutable dependency universe.
