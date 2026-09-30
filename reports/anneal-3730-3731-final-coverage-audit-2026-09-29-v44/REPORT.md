# #3730/#3731 coverage audit v44: Lake tactic and term positions

## Summary

The [Lake reflexive term-proof report](../anneal-3731-lake-reflexive-term-goal-positions-v4-30-0-rc2/REPORT.md) adds bounded direct evidence to **#3731 I043** and **#3730 C02** in published [v43](../anneal-3730-3731-final-coverage-audit-2026-09-29-v43/REPORT.md). One imported `by exact Eq.refl depValue` proof was queried at nine exact positions through plain tactic goals, rich tactic goals, and `plainTermGoal`. At the start of `exact`, both tactic APIs showed `⊢ depValue = depValue`. Inside `Eq.refl`, both tactic APIs returned empty goal lists while `plainTermGoal` returned the equality goal over `(3,8)`–`(3,24)`; inside its argument, `plainTermGoal` returned `⊢ Nat` over `(3,16)`–`(3,24)`. A separate fresh batch process accepted the same source text. This reflexive fixture establishes these local API responses only.

All **333 row IDs**, **345 suggestion destinations**, inherited request fields and row order are preserved. Only **I043 and C02** have changed residuals. Both remain **partial** at the **product** gate. Every status, gate and next prerequisite is carried forward unchanged; the other 331 rows retain their v43 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@3d88b2c31d6c0774066ff581cf5d2bc27547b948` and its v43 ledger. The source component used installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` Lean/Lake 4.30.0-rc2 on macOS arm64. A local Lake dependency defined `depValue := 7`; the proof imported it and proved the reflexive equality `depValue = depValue` with `by exact Eq.refl depValue`. The server opened the exact on-disk proof bytes. A separate fresh batch file had identical source text and the same prepared import but a different filename. Nine sequential query triples used one server, one document version and one rich RPC session.

The [v44 issue snapshot](support/live-issue-snapshot-v44.json) is byte-identical to v43's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was **not fetched again**. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I043/C02 mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I043 | Nine exact `plainGoal`/`getInteractiveGoals`/`plainTermGoal` triples distinguish the tactic goal at `(3,2)`, the equality term goal at `(3,8)` and `(3,11)` over `(3,8)`–`(3,24)`, and the `Nat` argument goal at `(3,16)`, `(3,20)` and `(3,24)` over `(3,16)`–`(3,24)`. Tactic goals are empty at the term positions. Build/setup and fresh same-text batch succeeded with no error diagnostics. | This is one reflexive term proof. Broader/non-reflexive term selection, combinator and whitespace changes, unsaved nested/error combinations, worker/RPC reconnect, rich reference lifetime, late/stale responses, exact-version/import fencing and Anneal launcher/source-map integration remain open. |
| C02 | Plain and rich **tactic-goal** results agreed in all nine triples: one goal at the start of `exact`, empty lists on six positions inside/on the tactic line, and null at the next line and EOF. `plainTermGoal` separately returned term goals inside the expression and argument. | Rich term-goal comparison was not run. Rich object dereference/expiry, protocol transcript/lifecycle controls, other term proofs, worker/RPC reconnect, generated/projected Anneal proof transport and complete-obligation verification remain open. |

The v43 Lake nested constructor fixture and earlier unsaved macro/error fixture remain separate observations. This v44 source isolates tactic-versus-term position selection in a simple imported proof. The fresh batch exit and no-axiom message establish only this file's successful elaboration; they do not make local goal guidance a proof-correctness verdict for other obligations. **Basis: execution**, source `support/results.json` and exact source bytes; **derived** for the scope distinction.

### Unchanged rows

The other **331 rows**, including I079, I075 and I076, preserve their v43 residuals, prerequisites, statuses, gates and evidence fields. Their v44 assessments state that this reflexive term-position component does not directly exercise their remaining request. All 159 investigation titles, 174 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- The source proof is reflexive and hand-written. It does not test difficult Lean obligations, generated Anneal proofs, Rust source maps, or claim acceptance. Its batch success does not support a general proof-correctness claim.
- `getInteractiveGoals` was used for tactic goals; `plainTermGoal` supplied term goals separately. No rich term-goal endpoint, reference dereference/expiry or context reuse was tested.
- One successful disk-identical version and one RPC session were tested. Combinator/whitespace edits, unsaved nested/error versions, worker or RPC reconnect, late/stale responses, cancellation, simultaneous clients, exact-version/import fencing and broader protocol lifecycle behavior remain open.
- The source preflight measured 27.23% reclaimable memory and 23,440,347,136 free disk bytes; 26 samples over 5.7 seconds observed at most 1,023,920 KiB process-group RSS. Samples cannot exclude a shorter transient peak. The v44 issue text was inherited, not refreshed.

## Evidence

- [source-package-inventory-v44.csv](support/source-package-inventory-v44.csv) hashes every retained file in published v43 and the reviewed Lake term-proof source package. [validation-v44.json](support/validation-v44.json) records their hashes, exact changed IDs and row/link counts.
- The [builder](support/build_audit.py) derives every v44 row from v43 and checks issue titles and suggestion destinations against the retained text. The [checker](support/check.py) verifies inherited fields, unchanged residuals, source inventory hashes, both source checkers and metadata loading.
- The [source results](../anneal-3731-lake-reflexive-term-goal-positions-v4-30-0-rc2/support/results.json), fixture bytes, batch output, 27 goal requests with their replies, diagnostics and cleanup bind the nine triples and exact ranges.
- Published v43's row-challenge SHA-256 is `1bba9b2778f0d436f79c56df00e3be25fb354bd483d9eb247e92ba1a5c3737a9`.

## Revalidation

Run `python3 -B support/check.py` from this package to check retained evidence without starting Lean, Lake or Anneal. Reacquiring the source cell requires the pinned binaries, a new absent private work path and its resource gates. Product I043/C02 coverage still requires the actual version-fenced Anneal launcher and generated source map, with broader term, combinator, whitespace, edit/error and reconnect controls plus fresh batch verification of the complete obligation set.
