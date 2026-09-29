# Nested tactic positions across unsaved errors and recovery in Lean 4.30.0-rc2

## Summary

In one direct Lean server, an unsaved nested syntax error made `$/lean/plainGoal` return JSON `null` at the malformed token and the following outer tactic, while a later theorem still exposed its ordinary goal. Replacing the error with an unknown nested tactic instead returned the unresolved outer target at the error token and `null` at the following tactic. Restoring the original unsaved text restored all seven queried positions and cleared diagnostics. These are versioned-wait observations for one tiny file, useful for #3731 I043 and #3730 C02; they do not validate an Anneal proof.

## Applicability

**Execution** used the cached arm64 macOS Lean 4.30.0-rc2 release binary identified in `REPORT.json`, executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. One direct `lean --server` process opened one physical `Nested.lean` URI. The on-disk file stayed valid. Full-text unsaved `didChange` versions moved from valid version 1 to a nested `)` syntax error in version 2, an unknown nested tactic in version 3, and the original valid text in version 4. The client waited for diagnostics for each version before querying. `LEAN_NUM_THREADS=1`; three fresh batch controls ran sequentially before the server. No Lake project, dependency download, plugin, generated Rust proof, or extra worker URI was involved. RSS was not measured or capped.

This report extends the valid-only [nested position grid](../anneal-3730-nested-tactic-position-grid-v4-30-0-rc2/REPORT.md) and the separate [partial elaboration failure probes](../anneal-3730-partial-elaboration-queries-v4-30-0-rc2/REPORT.md). It does not replace either report's fixture or observations.

## Findings

The file has a nested `have hz := by` proof, an outer `exact hz`, and a later independent `tail : True` theorem. Fresh `lean --json` on the preserved variant files exited 0 for valid source and 1 for each error variant; the two failures reported, respectively, `unexpected token ')'` and `unknown tactic` with unsolved goals. The server emitted error diagnostics for versions 2 and 3 and empty final diagnostics for versions 1 and 4. All four versioned `waitForDiagnostics` calls completed. **Basis: execution**, `batch`, `ready`, and `textDocument/publishDiagnostics` events in `support/transcript.json`.

The exact zero-based LSP positions and results are:

| Cursor position | Valid v1 and recovered v4 | Syntax error v2 | Unknown tactic v3 |
| --- | --- | --- | --- |
| Nested token start, line 4 column 4 | `n, h ⊢ n + 0 = 0` | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Two columns into nested tactic, line 4 column 6; syntax token end at column 5 | `n, h ⊢ n = 0` | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Nested tactic end, line 4 column 17/5/24 by version | Empty goals | JSON `null` | `n, h ⊢ n + 0 = 0` |
| Outer `exact hz` start, line 5 column 2 | `n, h, hz ⊢ n + 0 = 0` | JSON `null` | JSON `null` |
| Later `trivial` start, line 8 column 2 | `⊢ True` | `⊢ True` | `⊢ True` |
| Later `trivial` end, line 8 column 9 | Empty goals | Empty goals | Empty goals |
| EOF, line 9 column 0 | Empty goals | Empty goals | Empty goals |

The v2 `null` and v3 unresolved goal are different server selections at the failed nested location. Neither result is a certificate for the erroneous whole file. The later theorem's local goal survived both errors, and the recovered version matched the initial seven results exactly. **Basis: execution**, 28 named `goal` events in `support/transcript.json`; exact strings, positions, diagnostics, source identities, and clean exit are asserted by `support/check.py`.

## Boundaries

- **Not examined:** rich interactive goal objects, macros, tactic combinators, comments or broad whitespace grids, multiple simultaneous files, generated source maps, or an Anneal adapter. I043 remains partial.
- **Not established:** a general parser recovery span, a guarantee that `null` means there was no proof obligation, or that a goal in a later declaration makes an error-bearing module valid.
- **Not examined:** cancellation during elaboration or prefix reuse after an early edit (I036); wrapper proposition fidelity (I037); imported model generation transitions and production invalidation (I056).
- **Not established:** timing or resource scaling. The single server run used one open URI and sequential requests; its wall-clock values are transcript ordering evidence only.

## Evidence

- `support/Nested.lean` is the unchanged on-disk valid source, SHA-256 `0f262ebe59eeef631b313d59110c403d36256634200b0a16c4a621da40a3ab28`. `support/variants/` retains the three exact batch sources; the recovered version equals the valid bytes.
- `support/probe.py` constructs all four unsaved versions, runs batch controls, records full JSON-RPC request and response order, and writes `support/transcript.json` (147 events; SHA-256 `9af1f3c455aa04d7c04e66de39b3dad209ff003533e3c1c222532056f3d2f77a`). Absolute local paths are tokenized in the transcript.
- `support/check.py` performs an offline assertion of binary and source hashes, batch exits and error classes, all four waits and diagnostic states, every goal string and coordinate, version order, and clean server exit. It passed on 2026-09-29.

## Revalidation

Run `python3 support/check.py` to verify retained evidence without Lean. To rerun on the identified cached binary, run `python3 support/probe.py` and then the checker; `LEAN_BIN` can select an explicit binary. The probe writes only this package's `support/variants/` and `support/transcript.json`. Compare the binary hash before interpreting a rerun as the same subject. A different Lean revision should be reported separately.
