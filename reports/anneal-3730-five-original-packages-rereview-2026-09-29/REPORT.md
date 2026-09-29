# Independent re-review of five original #3730/#3731 reports

## Scope and method

A separate GPT-6 Sol High worker re-read the five packages introduced in `41e3f34` and amended or reviewed in `9641a9e`, including their retained evidence and replay/check scripts. The comparison point was `reference` at `335cf976f507b1bc65fea2e4742cd41a710e17d8`. The public issue API returned the same #3730/#3731 body and scope-comment hashes as the retained initial-audit snapshot at 2026-09-29 16:45 UTC. `support/review.json` records those hashes, file hashes, and per-package dispositions. This is a source/evidence review with one corrected finite-model case and one tightened checker; it is not a new Anneal product integration run.

## Dispositions

| Package | Review outcome |
| --- | --- |
| `aeneas-concurrent-generation-determinism-nightly-2026-06-03` | **No change.** Seven pinned Aeneas process results, overlaps, and generated file equality are consistent with the checker. It is limited to the same LLBC input and bounded processes. The later `anneal-3730-aeneas-process-contract-2026-09-29` package separately covers different-input shared destinations and output-shrink/timeout controls, so rerunning those here would duplicate evidence. |
| `anneal-3730-3731-coverage-audit-2026-09-29` | **No change.** This is an explicitly dated initial snapshot, not the current item-status ledger. Its source snapshot has 159 investigations, 64 scope extensions, and 174 #3730 crosswalk rows; the current issue body/comment hashes match its later captured source snapshot. Its `REPORT.json` still identifies the original review point, which the report explains. Subsequent full audits, including v16, supersede its coverage statuses. Rewriting historical classifications would erase that chronology. |
| `anneal-interactive-model-probes-2026-09-29` | **Correction.** Two of ten purported single-field identity mutations changed only the worker epoch, so the prior set had nine distinct deltas. We replaced one duplicate with a symbolic `llbc` identity change, regenerated `support/model-probes.json`, and made both generator and checker assert ten unique deltas. The changed result affects only `identity_ablation`; projection, schedule, and APFS publication results are byte-for-byte unchanged from the retained pre-review output. The new `llbc` value is a model symbol, not an independently translated LLBC artifact. |
| `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2` | **Checker strengthened.** Both recorded 4.29 and 4.30-rc2 transcripts contain `Tactic rfl failed` diagnostics for `NewOpen.lean` version 1 and reopened `OldOpen.lean` version 2. The existing checker asserted goals and fresh batch failure but did not require these diagnostic pairs. It now does. No raw transcript or conclusion changed. |
| `lean-same-server-dependency-generation-v4-30-0-rc2` | **No change.** Original and revalidation transcripts, source/artifact hashes, old/new goals, diagnostics, batch rejection, and one-server chronology agree with the checker. The report correctly bounds this to direct `lean --server` behavior and does not infer an Anneal service contract. |

## Verification and limits

All five package `support/check.py` scripts passed after the two amendments. The reference package loader accepted all five. `support/check.py` in this review package verifies its retained file hashes and the two amended controls. The review did not modify generated Lean, LLBC, publication fixtures, original server transcripts, or the initial audit ledger. The current v16 item-level audit remains the place to track unresolved product, human, platform, and dependency gates.

The review does not claim that ten model mutations cover every identity dimension, that two Lean versions establish general version compatibility, or that seven Aeneas processes establish a scaling limit. Further local runs that would merely repeat these exact scopes are not justified by discrepancies found here. The remaining broader experiments belong to the later report corpus and its item-level residual ledger.
