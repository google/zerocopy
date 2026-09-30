# #3730/#3731 coverage audit v37: retained I080 full-field LLBC comparison

## Summary

The [retained-output comparison](../anneal-3731-i080-full-field-cancel-oracle-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I080** and **#3730 D03/D06** in published [v36](../anneal-3730-3731-final-coverage-audit-2026-09-29-v36/REPORT.md). Four completed warmed shared-target outputs were compared field by field against cold oracles in the same source state. Their decoded JSON leaf differences are confined to requested destination paths, generated-file local paths and positional `translated.short_names` order; typed-key/name maps agree. A separate edited-versus-baseline cold-oracle control detects the expected source/body change, including literal 2 versus 1. The result strengthens completed-output checks in the existing cancellation/retry fixture; it does not change the recorded cancellation schedule or establish product ownership.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. Only I080, D03 and D06 have changed residuals. Their statuses remain **partial**, all gates and prerequisites are carried forward unchanged, and other suggestions retain their v36 assessments.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@52b16195ee71b52b936476b2efd6da2e49622cd0` and its v36 ledger. The source report is offline Python reanalysis of six retained LLBC files from the pinned Charon 0.1.210, nightly Cargo/rustc, `CARGO_INCREMENTAL=1` warmed shared-target cancellation/retry probe. The source package retains all six LLBC bytes and its comparison procedure, exact differences, source execution record, checker and resource observations. This v37 audit did not run Charon, Cargo, rustc, Anneal, Lean or Lake.

The [v37 issue snapshot](support/live-issue-snapshot-v37.json) is byte-identical to v36's retained issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Direct observation | Remaining scope |
| --- | --- | --- |
| I080 | Prewarm A, prewarm B and companion B each differ from cold baseline B in the same source state only in two path leaves and positional short-name order; recovered A differs from cold edited A in those same families. The keyed name maps agree. Edited versus baseline control detects the source/body change. | The canceled A request produced no LLBC. Lock timing, stage-wide descendants and cleanup, path-sensitive provenance, representative resource economics and Anneal ownership/publication remain open. |
| D03 | The full-field comparison extends prior selected-body-hash evidence for the warmed shared Cargo target's completed outputs. Paths and array positions remain genuine differences; no field was normalized away in the comparison. | Complete producing-Cargo-unit attestation, representative dirty shared/private snapshots, path-sensitive cache identity and Anneal target policy remain open. |
| D06 | Companion B and retried A completed in the earlier canceled-A schedule; their retained LLBCs now have full decoded comparison with cold oracles. The edited control confirms this comparison can detect a substantive source/model change. | No new schedule or cleanup observation was made. Cancellation across other stages, escaped descendants, repeated failures, last-good publication, representative resources and Anneal owner remain open. |

**Basis: execution** of the retained-data Python comparison and the earlier pinned Charon schedule; **derived** for the limited row mapping. Decoded JSON equality outside the observed difference families does not establish byte identity, semantic equivalence or a safe path-insensitive artifact key.

### Unchanged rows

The other **330 rows** preserve their v36 residual, prerequisite, status, gate and evidence fields. Their new v37 assessment says this retained-output comparison does not directly exercise their remaining request. All 159 investigation titles, 174 #3730 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- Only four same source-state completed-output pairs and one edited-versus-baseline negative control were compared. The canceled A request had no output to compare.
- Requested destination and generated-file paths differ, and short-name array positions differ even though typed-key/name maps agree. A byte-keyed cache or consumer sensitive to those values needs its own policy and tests.
- The reanalysis does not establish cancellation lock acquisition or release timing, all-stage cleanup, escaped-descendant absence, repeated-failure behavior, model soundness or Rust semantic equivalence.
- No actual Anneal owner, materialized-snapshot target policy, publication transaction or representative workload was exercised. I080 and D03/D06 remain partial at their inherited gates.

## Evidence

- [source-package-inventory-v37.csv](support/source-package-inventory-v37.csv) hashes every retained file in published v36 and the full-field source package. [validation-v37.json](support/validation-v37.json) records input and generated hashes, the three direct IDs and row/link counts.
- The [builder](support/build_audit.py) derives every v37 row from v36 and checks 159 investigation titles, 174 suggestion destinations and 345 links against the retained public issue text. The [checker](support/check.py) validates inherited fields, unchanged rows, inventory hashes, both source checkers and metadata loading.
- The source report's [complete differences](../anneal-3731-i080-full-field-cancel-oracle-2026-09-29/support/comparison.json), six raw LLBCs, copied source execution record and checker bind each comparison. Its guarded Python analysis ran for 0.05482 seconds, measured at most 22,216,704 bytes self RSS and sampled at least 22.6244% reclaimable memory. These samples do not measure a sustained host peak.
- Published v36's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies the retained evidence without starting compilers or servers. Reacquisition of the full-field source analysis requires its six exact LLBC hashes and fresh resource preflight. Product closure requires guarded Anneal-owned snapshots, target and output ownership, representative resource measurement and repeated cancellation across build, extraction and publication stages.
