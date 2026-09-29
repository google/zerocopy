# Independent re-review of five original #3730/#3731 reports

## Scope and method

A separate GPT-6 Sol High worker first re-read the five packages introduced in `41e3f34` and amended or reviewed in `9641a9e`, including their retained evidence and replay/check scripts. The comparison point was `reference` at `335cf976f507b1bc65fea2e4742cd41a710e17d8`. The public issue API returned the same #3730/#3731 body and scope-comment hashes as the retained initial-audit snapshot at 2026-09-29 16:45 UTC. A second pass reviewed the amended local package contents against checkout HEAD `df4f6d6c84f936489c01edfa5ff19b2ee005f4d0` on 2026-09-29; `support/review.json` records both review points, the original issue hashes, current file hashes, and per-package dispositions. These are source/evidence reviews, not Anneal product integration runs.

## First-pass dispositions

| Package | Review outcome |
| --- | --- |
| `aeneas-concurrent-generation-determinism-nightly-2026-06-03` | **No change.** Seven pinned Aeneas process results, overlaps, and generated file equality are consistent with the checker. It is limited to the same LLBC input and bounded processes. The later `anneal-3730-aeneas-process-contract-2026-09-29` package separately covers different-input shared destinations and output-shrink/timeout controls, so rerunning those here would duplicate evidence. |
| `anneal-3730-3731-coverage-audit-2026-09-29` | **No change.** This is an explicitly dated initial snapshot, not the current item-status ledger. Its source snapshot has 159 investigations, 64 scope extensions, and 174 #3730 crosswalk rows; the current issue body/comment hashes match its later captured source snapshot. Its `REPORT.json` still identifies the original review point, which the report explains. Subsequent full audits, including v16, supersede its coverage statuses. Rewriting historical classifications would erase that chronology. |
| `anneal-interactive-model-probes-2026-09-29` | **Correction.** Two of ten purported single-field identity mutations changed only the worker epoch, so the prior set had nine distinct deltas. We replaced one duplicate with a symbolic `llbc` identity change, regenerated `support/model-probes.json`, and made both generator and checker assert ten unique deltas. The changed result affects only `identity_ablation`; projection, schedule, and APFS publication results are byte-for-byte unchanged from the retained pre-review output. The new `llbc` value is a model symbol, not an independently translated LLBC artifact. |
| `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2` | **Checker strengthened.** Both recorded 4.29 and 4.30-rc2 transcripts contain `Tactic rfl failed` diagnostics for `NewOpen.lean` version 1 and reopened `OldOpen.lean` version 2. The existing checker asserted goals and fresh batch failure but did not require these diagnostic pairs. It now does. No raw transcript or conclusion changed. |
| `lean-same-server-dependency-generation-v4-30-0-rc2` | **No change.** Original and revalidation transcripts, source/artifact hashes, old/new goals, diagnostics, batch rejection, and one-server chronology agree with the checker. The report correctly bounds this to direct `lean --server` behavior and does not infer an Anneal service contract. |

## Second-pass dispositions

| Package | Review outcome |
| --- | --- |
| `aeneas-concurrent-generation-determinism-nightly-2026-06-03` | **Wording narrowed.** The recorded end timestamps follow `communicate()`, so they bound post-spawn-to-collection overlap rather than proving that all child processes were alive at one instant. The report now states that distinction; the retained process results are unchanged. |
| `anneal-3730-3731-coverage-audit-2026-09-29` | **Ledger and checker corrected.** The I151 CSV row had malformed quoting. It now parses into the intended columns, and the checker rejects missing or extra CSV fields. The initial audit remains a dated partial-evidence snapshot. |
| `anneal-interactive-model-probes-2026-09-29` | **Controls and replay strengthened.** Stale host digest, projection digest, and document version are separate patch cases; UTF-16 offsets are checked against encoded byte prefixes; accepted schedule publications are checked against their recorded current generation; the retained checker reruns the finite model read-only and checks more APFS transcript details. The filesystem fixture was not regenerated in this pass. |
| `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2` | **Provenance and references corrected.** A non-existent source-revision identity for the generated fixture was removed. The report cites both v4.29 and v4.30 transcripts after successful replay under the pinned binaries. This remains a two-version direct-server fixture, not a general compatibility claim. |
| `lean-same-server-dependency-generation-v4-30-0-rc2` | **Supplementary query retained.** A new transcript records an old-URI query after the new document reported its goal, while both documents remained open in one server process. The old URI still returned `no goals` and the new URI returned `⊢ sharedValue = 3`. The checker now verifies that chronology and the extra result. |

## Verification and limits

At the first pass, all five package `support/check.py` scripts passed after its two amendments, and the reference package loader accepted all five. At the second pass, all five package checkers passed against the local contents. The same-server checker also passed with `revalidation-transcript.json` and `simultaneous-transcript.json`; the Lean cross-version package checker passed against both retained transcripts. The review-package checker verifies current file hashes and selected second-pass controls. No Lean binaries or publication probe were rerun for this review-package update. The later item-level audits remain the place to track unresolved product, human, platform, and dependency gates.

The review does not claim that ten model mutations cover every identity dimension, that two Lean versions establish general version compatibility, or that seven Aeneas processes establish a scaling limit. The remaining broader experiments belong to the later report corpus and its item-level residual ledger.

## Third-pass integrity note

The first- and second-pass hashes in `support/review.json` are historical records. The checker verifies the 18 first-pass files against Git commit `df4f6d6c84f936489c01edfa5ff19b2ee005f4d0` and the 24 second-pass files against `c89f1410d4f1cfbd9b654ea5268b38f5c81e115e` when local Git history is available. Its `third_pass` section pins 28 current files at the third review point, starting from checkout HEAD `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`. The separate `anneal-3730-five-original-packages-third-pass-review-2026-09-29` report records the five latest dispositions and supplementary evidence. The original two pass sections above remain a chronology of their own review points.
