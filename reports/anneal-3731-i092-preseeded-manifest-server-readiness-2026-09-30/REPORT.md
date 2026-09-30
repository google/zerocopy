# Preseeded Lake server goals with valid and invalid consumer manifests

## Summary

In one pinned Lean/Lake 4.30.0-rc2 two-package fixture, a valid consumer manifest let `lake --no-build --no-cache serve` open `Generated.lean`, reach a processing-empty quiescent state, and return the live goal `⊢ depValue = 7`. Replacing only the consumer manifest with malformed JSON or a valid JSON manifest omitting its declared dependency made the opened document publish Lake setup errors. Both server processes still initialized and exited 0 through the plain `lean --server` fallback, while `$/lean/plainGoal` returned `null` after the bounded eight-second diagnostic wait. Neither invalid-manifest run met the probe's quiescence rule. The null responses are observations under that wait, not proof that a valid goal could never appear in another timing or server state.

## Applicability

This is a retry of the [prior valid-only server observation](../anneal-3731-i092-preseeded-valid-server-goal-2026-09-30/REPORT.md) for [#3731 I092](https://github.com/google/zerocopy/issues/3731), with [#3730 F07](https://github.com/google/zerocopy/issues/3730) as historical context. The experiment used the installed Lake and Lean executables identified in `REPORT.json`, one macOS host, and a private two-package producer/consumer tree. The producer defines `depValue : Nat := 7`; the consumer imports `Dep`, proves `depValue = 7` by `rfl`, and evaluates the value. The initial 36 work files were copied byte-for-byte from the earlier malformed-manifest preflight package and checked against [preseed.json](preseed.json). This retry's `probe.py` ran only the three server cells after that preseed; it did not rebuild or fetch dependencies.

Every server was invoked sequentially from the consumer directory as `lake --keep-toolchain --no-ansi --no-build --no-cache serve`, with `LAKE_NO_NET=1`, a private home/cache, `LAKE_NO_CACHE=1`, and no `LEAN_PATH`. For each cell the client sent initialize, initialized, `textDocument/didOpen` for the same 71-byte `Generated.lean` version 1, `$/lean/plainGoal` at line 1 character 40, shutdown and exit. The three [manifest fixtures](fixtures/) differ only in the consumer manifest: the valid package entry points to the producer; malformed is the two bytes `7b 0a`; semantic no-dependency is parseable JSON with an empty `packages` array despite `require probe_dep` in the unchanged lakefile. The source and preseeded OLean were unchanged. These observations identify this fixture and binary pair, not a general fail-closed contract for Lake, an Anneal V2 prepared archive, or every manifest error.

## Findings

| Manifest state | Fresh RAM admission | Opened-document behavior | Goal response after wait | Server exit |
| --- | ---: | --- | --- | ---: |
| Valid dependency | 31.16% | Information diagnostic `7`; final `processing: []`; quiescence recorded after 6.0899 s | `⊢ depValue = 7` | 0 |
| Malformed JSON | 31.04% | Invalid JSON at offset 2, workspace configuration failure and `lake setup-file` diagnostic; no final empty processing state under the probe rule | `null` after 8.0261 s diagnostic wait | 0 |
| Parseable manifest without dependency | 31.38% | `missing manifest; use lake update`, workspace configuration failure and `lake setup-file` diagnostic; no final empty processing state under the probe rule | `null` after 8.0315 s diagnostic wait | 0 |

The invalid-manifest stderr files also contain `warning: package configuration has errors, falling back to plain \`lean --server\``. A protocol initialize response and exit 0 therefore did not certify a usable Lake document setup in either invalid cell. Their progress streams each emitted an empty `processing` event and then a later `kind: 2` processing state. The probe required the latest file-progress event to be empty plus a 0.7-second quiet interval, and correctly recorded `readiness_quiescent: false`. The goal request was sent anyway as a bounded observation; both replies were JSON `result: null`. Raw server stdout/stderr is preserved under [raw/](raw/), and [results.json](results.json) includes the sent frames, decoded received frames, monotonic event times, process exit codes, diagnostics, inventories, and resource samples.

The valid server emitted 38 decoded frames and returned its goal after the quiescent wait. Each invalid server emitted 25 frames. All three runs recorded `before == after` for the entire private work inventory during that server process, and each phase's producer and cache inventories matched before/after. The consumer manifest was then restored to its original valid SHA-256, `4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230`. No resource guard aborted a run.

## Boundaries

The invalid runs show setup diagnostics and absent goals at the requested position within the eight-second window. They do not show that a goal is impossible under an unbounded wait, a restarted worker, another position, or a different client readiness policy. A goal returning `null` is not equivalent to a verified error result. The fallback is reported by stderr; the experiment does not instrument the child server's import graph or prove exactly which already-built files it loaded. The unchanged file inventories show no observed writes in this private tree during each command, not a system-wide read-only guarantee. This tiny fixture does not exercise native/plugin artifacts, a real Anneal generated consumer, archive identity, or the broader F07 product acceptance criteria.

Fresh admission was above the specified 30% RAM and 10 GiB disk thresholds for each server. The sampled runtime minimum RAM fraction dipped below 30% but stayed above the 20% kill threshold; sampled group RSS stayed below the 1,200 MiB guard. These measurements are sampled process-group values, not a peak unique-memory measurement or independent descendant census.

## Evidence

The executed [probe.py](probe.py) records its exact binary paths and hashes, fixture generation, admission/guard rules, protocol sends, and inventory method. [results.json](results.json) has `status: completed`, three sequential `runs`, each exit 0 and `abort: null`, and manifest/phase hashes. The [raw transcripts](raw/) retain all six stdout/stderr byte streams. The [preseed manifest](preseed.json) identifies the earlier 36-file work tree and source result hash; the final [work tree](work/) retains those files with the valid manifest restored. The report's offline [check.py](check.py) verifies frame decoding and the bounded claims without launching Lean or Lake.

## Revalidation

Run `python3 -B check.py` from this package to verify the retained bytes and claims. Re-running `probe.py` is a new active Lean/Lake experiment: it requires a fresh private directory, a preseeded tree, and resource admission. To strengthen the readiness conclusion, repeat with an explicit final-processing oracle or a longer controlled wait and query after a documented recovery/restart sequence. To address the product residual, run the actual Anneal prepared consumer and verify its identified archive, imports, and goal behavior.
