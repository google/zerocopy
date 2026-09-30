# #3730/#3731 coverage audit v38: sequential I080 full-field edit/revert outputs

## Summary

The [sequential edit/revert LLBC comparison](../anneal-3731-i080-full-field-edit-revert-oracles-2026-09-29/REPORT.md) adds direct, bounded evidence to **#3731 I080** and its **#3730 D03** Cargo-reuse suggestion in published [v37](../anneal-3730-3731-final-coverage-audit-2026-09-29-v37/REPORT.md). Across incremental-off and incremental-on sequential shared-target runs, all 12 completed shared outputs were compared field by field with same source-state cold oracles. Their only decoded differences are requested destination paths, generated-file local paths and positional `short_names` order; typed-key/name maps agree. Two edited-versus-baseline cold controls detect the expected embedded source and serialized `step` literal change. This is a separate corpus from v37's **incremental-on concurrent cancellation/retry** comparison. It adds no cancellation schedule, cleanup observation or Anneal product behavior.

All 333 row IDs, 345 suggestion destinations, inherited request fields and row order are preserved. Only I080 and D03 have changed residuals. Their statuses remain **partial**, all gates and prerequisites are carried forward unchanged, and D06 and every other suggestion retain their v37 residual.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The baseline is published `reference@44772095872665264473eddf7131eb897b1821f0` and its v37 ledger. The new source report is offline Python reanalysis of 16 retained LLBC files from the pinned Charon 0.1.210, nightly-2026-05-31 Cargo/rustc two-root source edit → rebuild → revert run. The original run used one sequential writable shared target per incremental mode, independent cold A oracles, equal-length A/B source roots, and no concurrent cancellation. The new report retains all 16 raw LLBCs, copied source results, complete differences, guards and checker. No Charon, Cargo, rustc, Aeneas, Lean, Lake or Anneal process was run for v38.

The [v38 issue snapshot](support/live-issue-snapshot-v38.json) is byte-identical to v37's retained public issue text, originally fetched at `2026-09-30T01:30:04.750897+00:00`; it was not fetched again. #3730 body/comment SHA-256 values remain `81bdc705843328085400eb3816ccd473266a95723cfcdba94c753bc22617e6f0` / `7544fde70a98d0fdc6ffa14a7bb08827e1b40ad7b8f8eb4263a0f67d0491531e`; #3731 values remain `0375e6dc74b7f89e170c6c1a699212c1cf82b4260dfda4f14a02bcb54b2c4a88` / `4cc532789c728ce2cfaca08d7636c6f0fd91f0710fd9e90de74a25993b43f488`.

## Findings

### Direct row mapping

| Row | Distinct direct observation | Remaining scope |
| --- | --- | --- |
| I080 | A separate sequential A/B source edit/revert corpus under both `CARGO_INCREMENTAL=0` and `1` has 12 full decoded shared-output/cold-oracle comparisons. All 248 differing leaves belong to two path fields or positional `short_names` order; keyed names agree. Both cold edited/baseline controls detect embedded source and literal `"2"` versus `"1"`. This extends the source report's five selected local body hashes. | V37's concurrent cancellation result is unchanged. Dirty concurrent and repeated cancellation across stages, lock and descendant tracing, path-sensitive provenance, representative cost, and Anneal-owned target/output publication remain open. |
| D03 | The same sequential full-field evidence strengthens the exact Cargo reuse component for both incremental settings. Its output paths and array positions are genuine differences and were not normalized out of the comparison. | Complete producing-Cargo-unit attestation, representative materialized snapshots, dirty concurrent targets, path-sensitive keys, Anneal target ownership and transactional publication remain open. |

The new report compares **12 completed shared outputs against four reused cold oracle files**, not 16 independent shared-output/oracle pairs. V37's distinct four-pair cancellation comparison remains preserved in the inherited I080/D03 residual and evidence. The #3730 D03 crosswalk has destinations **I075;I080**, and this component directly advances its I080 reuse slice. D06 is unchanged because this sequential report adds no cancellation mechanics. **Basis: execution** of the retained-data comparison and prior pinned source run; **derived** for the narrow row mapping. No decoded equality outside the observed difference families establishes byte identity, Rust semantic equivalence or a safe path-insensitive artifact key.

### Unchanged rows

The other **331 rows** preserve their v37 residual, prerequisite, status, gate and evidence fields. Their new v38 assessment says the sequential edit/revert comparison does not directly exercise their remaining request. All 159 investigation titles, 174 #3730 suggestion rows and 345 destinations still match the retained issue text.

## Boundaries

- This was offline reanalysis of completed LLBC files. It did not observe another Cargo or Charon execution, producer lock, cancellation, descendant, cleanup or Anneal transaction.
- The source roots were deliberately equal in pathname length and the workload was tiny and sequential. A prior path-sensitive build-script counterexample remains relevant; this corpus does not establish general path-independent reuse.
- Requested destination and generated-file local paths differ in every pair; `short_names` positions differ even where keyed maps agree. Cache identity and consumer interpretation require explicit policy and controls.
- The edited/baseline controls detect one source/model change, not every possible dependency or source edit. I080 and D03 remain partial with their inherited resource and product gates.

## Evidence

- [source-package-inventory-v38.csv](support/source-package-inventory-v38.csv) hashes every retained file in published v37 and the new full-field source package. [validation-v38.json](support/validation-v38.json) records baseline/input and generated hashes, two direct IDs, and row/link counts.
- The [builder](support/build_audit.py) derives every v38 row from v37 and checks all issue titles and suggestion destinations against the retained snapshot. The [checker](support/check.py) checks inherited fields, unchanged residuals, inventory hashes, both source checkers and metadata loading.
- The source report's [complete comparison record](../anneal-3731-i080-full-field-edit-revert-oracles-2026-09-29/support/comparison.json), 16 raw LLBCs, copied source execution record and checker bind all 12 oracle pairs and two negative controls. Its guarded Python analysis measured minimum 22.5082% reclaimable memory, maximum self RSS 24,739,840 bytes and elapsed 0.13825 seconds. Samples do not establish a sustained host peak.
- Published v37's row-challenge SHA-256 is recorded in this report's metadata and verified by the checker.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies retained evidence without starting a compiler or server. Reacquiring the source comparison separately requires the 16 exact LLBC hashes and its guarded memory/RSS/time preflight. Product closure needs representative Anneal-owned snapshots, complete Cargo producer and output ownership, path-sensitive and dirty concurrent cases, resource measurement and repeated cancellation across build, extraction and publication stages.
