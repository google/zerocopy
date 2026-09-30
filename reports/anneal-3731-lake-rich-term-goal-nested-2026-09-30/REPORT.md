# Rich term-goal selection in a nested Lake proof

## Question and result

Issue #3731 I043 asks what goal a cursor selects inside a proof; issue #3730 C02 asks how Lean's rich RPC view compares with its plain goal view. The published corpus already has a Lake-launched reflexive proof with `plainTermGoal`, and separate paired `plainGoal`/`getInteractiveGoals` grids. It did not query `Lean.Widget.getInteractiveTermGoal`. This package exercises that distinct API in a nested `Eq.trans` proof.

In one pinned Lean/Lake 4.30.0-rc2 server, the rich term-goal RPC and `$/lean/plainTermGoal` agreed on target text and source range at eight non-null positions and on null status at the other three positions. The rich non-null replies additionally carried tagged target text and opaque `ctx` and `term` RPC references. At eight inner term positions the two tactic-goal APIs returned empty goal lists, while the term-goal APIs returned a goal. A fresh batch process accepted the exact source bytes, reported no theorem axioms and evaluated the imported value to 7.

This is direct Lean/Lake component evidence. It does not establish an Anneal result or close either product gate.

## Subject and method

- Installed local subject: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2`, macOS arm64. Lake SHA-256: `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; Lean SHA-256: `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`.
- A local dependency defines `depValue : Nat := 7`. The proof imports it and uses `exact Eq.trans (Eq.refl depValue) (Eq.refl depValue)`. Exact source and Lake configuration are in `support/fixture/`.
- The probe performed a clean local Lake build, `setup-file`, and a separate fresh `lake --no-cache env lean --json` batch check. One `lake --no-cache serve` process opened the disk-identical proof at version 1, waited for diagnostics, connected one RPC session, and issued 11 sequential quadruples: `plainGoal`, `getInteractiveGoals`, `plainTermGoal`, `getInteractiveTermGoal`. All requests and replies are retained in `support/results.json`.
- Coordinates are zero-based UTF-16 LSP positions. The measured proof line is ASCII. There were no unsaved edits, restarts or parallel requests.

The hypothesis was that rich term-goal selection exposes the same target and range as the plain term endpoint for this nested expression, with extra structured references. A differing null/non-null result, target, or range at a paired position would have falsified that bounded hypothesis. The design choice sharpened is whether an agent/UI can use the rich endpoint for a local term-hole view while preserving the plain endpoint as a text comparison control. These responses are guidance at a cursor, not proof acceptance.

## Observations

| Cursor on proof line 3 | Character | Plain and rich term target | Returned range on line 3 | Tactic goals |
| --- | ---: | --- | --- | --- |
| `exact` start | 2 | null | — | one input goal |
| `Eq.trans` start | 8 | `depValue = depValue` | 8–54 | empty |
| inside `Eq.trans` | 11 | `depValue = depValue` | 8–54 | empty |
| first `Eq.refl` | 18 | `depValue = depValue` | 18–34 | empty |
| first `depValue` | 26 | `Nat` | 26–34 | empty |
| between arguments | 35 | `depValue = depValue` | 17–35 | empty |
| second `Eq.refl` | 37 | `depValue = depValue` | 37–53 | empty |
| second `depValue` | 45 | `Nat` | 45–53 | empty |
| end of term | 54 | `depValue = depValue` | 36–54 | empty |
| next line 4, character 0 | 0 | null | — | null |
| EOF line 6, character 0 | 0 | null | — | null |

The `between arguments` and `end of term` selections are observed behavior at those exact positions; they do not establish a general endpoint or whitespace rule. The rich target was extracted by concatenating the text leaves of Lean's tagged response, leaving the `info` tags out. At every non-null position the rich response also contained `ctx: {p: ...}` and `term: {p: ...}` references. Those values are session objects, not durable generation identifiers; this probe did not dereference, release or expire them. All 11 tactic-goal pairs also agreed in null status and goal count.

The clean build, setup, batch and server exits were all 0. The batch output said `'nested_term' does not depend on any axioms` and `7`; the final live diagnostics had no errors. The batch file had the same source bytes as the opened proof but a different filename, so this is a same-text control rather than a module-identity comparison. It establishes batch acceptance for this exact proof and local import, separately from goal-query agreement.

## Resource and execution bounds

The probe's retained preflight measured 50.35% reclaimable memory and 20,602,400,768 free disk bytes. It used an empty test home/cache, `LEAN_NUM_THREADS=1`, `LAKE_NO_NET=1`, `sandbox-exec` network denial, a five-minute deadline and a 1,400 MiB process-group RSS kill threshold. Across 26 samples during 5.59 seconds, maximum sampled process-group RSS was 758,560 KiB. Sampling cannot rule out a shorter transient peak. No download or installation occurred.

## Scope and residual

This extends I043/C02 by pairing the *rich term* endpoint with `plainTermGoal` across a nested imported term, including argument and boundary positions. It complements the published reflexive term probe and the tactic-only paired grids. It does not test unsaved term edits, syntax errors, macros in this nested shape, multiple workers, request cancellation, reference dereference/expiry, or a general selection rule.

Both rows remain **partial, product-gated**. Their decisive residual is to run the paired goal APIs over an actual Anneal generated/projected proof with Rust-source coordinates, current document and import-generation fences, and fresh batch comparison. This fixture has no Anneal launcher, generated imports, source map, editor or MCP transport.

## Reproduction

`support/probe.py` is the exact Python standard-library probe. From this package, run:

```sh
python3 -B support/check.py
python3 -B support/probe.py --work /new/absent/private/path --output /new/results.json
```

The first command checks the retained evidence without launching Lean. The second creates an isolated disposable Lake workspace and executes the guarded probe on the same installed pin. It requires an absent work path, at least 20% reclaimable memory and 10 GiB free disk. Compare subject hashes, source hashes, four successful exits, the 11 paired responses and ranges, diagnostics, and sampled resource data. The retained `support/results.json` normalizes temporary paths as `$WORK`, `$WORK_URI`, and `$TOOLCHAIN`; it includes the full request/response transcript. `support/check.py` enforces the expected observations and report metadata offline.
