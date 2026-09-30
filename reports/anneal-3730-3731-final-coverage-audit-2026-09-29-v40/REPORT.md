# #3730/#3731 coverage audit v40: target-layout LLBC field matrix

## Summary

The [retained target-layout full-field report](../anneal-3731-i080-target-layout-full-field-2026-09-29/REPORT.md) adds bounded direct evidence to **#3731 I080** in published [v39](../anneal-3730-3731-final-coverage-audit-2026-09-29-v39/REPORT.md). It recursively compares every decoded JSON field in 16 LLBC outputs across 24 matched one-axis pairs: eight warm/cold, eight shared/private, and eight incremental-on/off. Every observed difference is a requested destination path, a positional `short_names` leaf, or, in the last two contrast families, a generated-file local path. The typed-key/name `short_names` maps agree in all pairs. This is a fixed-source, small-fixture artifact observation. It does not prove semantic equivalence, safe target sharing, resource economy or an Anneal publication policy.

All **333 row IDs**, **345 suggestion destinations**, inherited request fields and row order are preserved. Only **I080** has a changed residual. Its status remains **partial**, and every gate and next prerequisite is carried forward unchanged. **D03 is context only**: the source report relates the target-layout comparison to Cargo reuse, but this report does not directly attest D03's complete producing unit, materialized snapshots, representative resources or Anneal ownership. D03 and the other 331 rows retain their v39 residuals.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@bc6753abb676164cf355af600d7abfecd6c3f59f` and its v39 ledger. The source report reanalyzes byte-exact retained outputs of a published private/shared Cargo target × incremental-off/on matrix, with cold and warm A/B requests in each cell. The original run used pinned Charon 0.1.210 and nightly-2026-05-31 Cargo/rustc on macOS arm64. The new full-field comparison used guarded offline Python only. It did not run Charon, Cargo, rustc, Aeneas, Lean, Lake, Anneal, a server or a network request.

The [v40 issue snapshot](support/live-issue-snapshot-v40.json) is byte-identical to v39's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct I080 mapping

Across the **24** matched pairs, the full-field comparator records **154** decoded leaf differences in warm/cold, **167** in shared/private, and **158** in incremental-on/off contrasts. All pairs differ at the requested destination path and positional `short_names` leaves. Each layout and incremental contrast also differs at the generated-file local path under its Cargo target. Those are genuine artifact differences; no normalization was used. All 24 serialized typed-key/name `short_names` maps agree. No function declaration, embedded source contents, crate name, error status or other decoded field differs in these particular pairings. Three synthetic in-memory controls detect a changed crate name, copied function body and short-name order. **Basis: execution** of the retained-data comparator and its checker.

Warm/cold pairs use the same source root within a cell. Layout and incremental contrasts are matched peers, not independent clean-build semantic oracles. The fixed-source matrix's concurrent A/B phases do not supply a changed-source race or cancellation schedule. It complements, without replacing, the earlier **four-output cancellation/retry** full-field comparison and **12-output sequential source edit/revert** full-field comparison. Its synthetic mutations are comparator controls, not changed-source producer outputs. I080 remains partial at its resource gate, with the same next prerequisite for representative Anneal-owned snapshots, dirty shared/private targets, repeated cancellations, descendant/lock traces, full output identity and guarded resource peaks.

### Unchanged rows and suggestion mapping

The other **332 rows** preserve their v39 residual, prerequisite, status, gate and evidence fields. Their v40 assessment states that this target-layout byte comparison does not directly exercise their remaining request. D03's #3730 crosswalk still points to I075;I080, but the precise new evidence does not satisfy its materialized-snapshot reuse and resource questions. No D03 residual or other suggestion residual changes. All 159 investigation titles, 174 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- The 16 outputs come from a tiny fixed-source fixture with deliberately equal-length roots. The source report's known path-sensitive build-script counterexample is outside this matrix.
- Matching decoded fields outside the listed differences do not prove byte-identical LLBC, Rust semantic equivalence, Charon soundness, general path-insensitive cache keys or that every consumer ignores `short_names` order.
- The target-layout comparison adds no source edit, cancellation, restart, descendant trace, complete producing-unit attestation, representative sustained resource observation or Anneal target/publication policy.

## Evidence and revalidation

- [source-package-inventory-v40.csv](support/source-package-inventory-v40.csv) hashes every retained file in published v39 and the new full-field source package. [validation-v40.json](support/validation-v40.json) records the published baseline, input and generated hashes, changed ID, and row/link counts.
- The [builder](support/build_audit.py) derives each v40 row from v39 and checks issue titles and suggestion destinations against the retained snapshot. The [checker](support/check.py) verifies inherited fields, unchanged residuals, inventory hashes, both source checkers and metadata loading.
- The source report's [complete comparison record](../anneal-3731-i080-target-layout-full-field-2026-09-29/support/comparison.json), 16 raw LLBC files, original source results and checker bind every pair, decoded difference and synthetic control. Its guarded Python run sampled minimum 26.2953% reclaimable memory, peak measured self RSS 25,968,640 bytes and elapsed 0.20167 seconds. These are sampled short-run measurements.
- Published v39's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

Run `python3 -B support/check.py` from this package for offline revalidation. Reacquiring the source analysis requires the exact 16 LLBC hashes and a fresh >20% reclaimable-memory preflight under its 64 MiB RSS and five-second caps. Product-path questions require separate guarded producer experiments.
