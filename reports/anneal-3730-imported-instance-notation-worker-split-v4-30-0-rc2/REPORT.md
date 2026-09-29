# Imported instance and notation changes split resident and new Lean workers

## Summary

Two tiny imported-model changes showed the same direct Lean 4.30.0-rc2 boundary. Rebuilding `Model.olean` after changing a typeclass instance value, or after redirecting a notation token, made a fresh batch proof fail. An already-open proof worker continued to report `no goals` with no diagnostics under its old import, while a newly opened proof URI in the same watchdog reported the remaining goal and an `rfl` failure. This extends the existing transitive-import/macro/plugin/option matrix to typeclass and notation semantics. It does not implement Anneal invalidation or worker attestation.

## Applicability

Each case used one disposable directory with `Model.lean`, `Proof.lean`, and `New.lean`. The proof bytes were unchanged: `import Model; theorem q : selected = 7 := by rfl`. The instance case changed `instance : Carrier := ⟨7⟩` to `⟨9⟩`, with `selected` defined through `Carrier.number`. The notation case kept `left := 7` and `right := 9` but changed `notation "selected" => left` to `=> right`. Direct `lean -o` compiled both model generations to the same `Model.olean` path under `.lake/build/lib/lean`, which the direct server used as `LEAN_PATH`. A separate fresh `lean --json` checked the proof before and after each rebuild. No Lake process, watcher notification, plugin, Anneal, or Rust source was involved.

The experiment was sequential per case on macOS arm64 with the cached pinned Lean binary, `LEAN_NUM_THREADS=1`, and at least 25% reported free memory. Client request IDs started at 1000 to avoid collisions with low-numbered server-to-client requests in the borrowed LSP framing harness. It directly informs #3731 I050 and #3730 E10's broader semantic-import question only as a component control.

## Findings

| Imported change | Old model/batch | Rebuilt model/fresh batch | Resident old worker after rebuild | New URI/worker after rebuild |
| --- | --- | --- | --- | --- |
| Typeclass instance `7 → 9` | Build exit 0; proof exit 0. | Build exit 0; proof exit 1 with `rfl` failure. | `no goals`, empty diagnostics. | `⊢ selected = 7`, `rfl` diagnostic. |
| Notation target `left → right` | Build exit 0; proof exit 0. | Build exit 0; proof exit 1 with `rfl` failure. | `no goals`, empty diagnostics. | `⊢ selected = 7`, `rfl` diagnostic. |

The model OLean SHA-256 changed in both cases. The old URI still reported `no goals` after the new URI had opened and failed. `waitForDiagnostics` completed for both URIs. Basis: **execution**, exact model/proof sources, compiler outputs, hashes, LSP requests/replies, and diagnostics in `support/results.json`; the offline checker verifies all two-case positive and negative controls.

The design consequence is that a proof result's source text and URI are insufficient to identify its elaborated meaning when an imported instance or notation changes. A consumer needs an imported-environment identity and a response fence before calling the old goal current. This is **derived** from the old/fresh split and batch oracle; no particular Anneal key or refresh mechanism was tested.

## Boundaries

- These are two tiny semantic changes to one imported module. The previous `anneal-3730-lean-transitive-import-rpc-matrix-2026-09-29` report covers a different graph with imported value, macro, option, and native plugin changes; this report does not repeat those cells.
- No file-watcher notification or supported worker-refresh operation was sent. The result does not prove an already-open worker could never refresh, only that it did not refresh under this schedule.
- The old proof's `no goals` belongs to its old imported environment. The script does not label it current after rebuild; the fresh batch process is the oracle for the newly compiled model.
- No broader instance search, scoped notation, namespace collision, generated imports, actual Anneal server, or Rust-level verification obligation was tested.
- Physical resource, artifact-cache, and cross-version costs were not measured.

## Evidence

- `support/probe.py`, SHA-256 `2892652c8b123259dc898df667fad29097b49fcccd0d52b01fed3e966d9473d6`, creates both cases, compiles model OLeans, drives direct Lean servers, records fresh batch results, and asserts the resident/new split. It reuses a pinned published LSP framing harness whose hash is in the raw result.
- `support/results.json`, SHA-256 `6ce10f94b3a5f45c6411d58c35202e66f07c40639e716b41297952bada43204e`, retains old/new source bytes and hashes, OLean hashes, command outputs/exits, old/new goal replies and diagnostics, and chronological wire events.
- `support/check.py` validates both cases offline. `support/work/` retains final model source, proof source, and compiled OLean under the exact direct-server import path.

## Revalidation

Run `python3 support/check.py` to verify the retained result. To repeat on the pinned cached binary, run `python3 support/probe.py`, then the checker; the probe replaces only its own `support/work` and `support/results.json`. A production Anneal test should change actual generated imports, compare exact model/obligation identities before accepting a live answer, and run the same proof in a fresh controlled batch environment.
