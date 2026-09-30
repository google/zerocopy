# #3730/#3731 coverage audit v46: native-plugin mappings in Lean workers

## Summary

One reviewed [native-plugin mapped-worker report](../anneal-3731-i125-i154-native-plugin-mapped-workers-2026-09-30/REPORT.md) adds bounded direct evidence to the published [v45 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v45/REPORT.md). Residuals change only for **I125 and I154**. The report is bounded context for **J08 and J12**, the two #3730 suggestions whose retained destinations include I154; their residuals stay unchanged. No other agenda row receives new evidence.

All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, original issue fields and row order are preserved. Every status, gate and next prerequisite is carried forward unchanged. I125 and I154 remain **partial** at the **product** gate.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability and current issue state

The parent is published upstream/reference at 22c27b3d8ba12ab9708cb7cd8f13eb29217ec71a. A fresh public REST fetch on 2026-09-30 found #3730 closed and #3731 open, with one comment each. Their bodies and comments are byte-identical to the [retained v45 snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-30-v45/support/live-issue-snapshot-v45.json). The [refreshed v46 snapshot](support/live-issue-snapshot-v46.json) records the exact texts, hashes and fetch time. Thus the issue agenda, 159 titles, 174 suggestion rows and 345 destination relationships did not change during this update.

## Direct row mapping

| Row | New bounded observation | Remaining decision |
| --- | --- | --- |
| I125 | Both lsof and vmmap recorded v1 mapped in the first watchdog and file worker, then v2 mapped in a new file worker while the same watchdog retained v1. The first worker was absent after didClose. A separate forced restart mapped v1 in a fresh watchdog and worker and returned a clean goal result. | The 1.5 GiB summed-RSS guard stopped the live tree before an in-one-watchdog reverse v1 worker could open. A same-run v2 initializer marker was not retained. Resident bytes, ABI compatibility, multiple dependencies, canonical plugin identity, GC and Anneal worker routing remain open. |
| I154 | Actual mapped paths add a native-plugin contamination sentinel to the earlier initializer-marker sequence, including close and a forced restart. | The in-one-watchdog v1→v2→v1 mapped transition was not completed. Representative fixture scoping, imported-model contamination, cleanup and Anneal test-runner integration remain open. |

J08 and J12 receive the mapped-worker report only because their established #3730 destinations include I154. Their v45 residuals and all prerequisites are preserved. This component does not measure per-test, per-fixture or per-suite reuse in an Anneal runner.

## Evidence and boundaries

The same-basename v1/v2 dylib targets are retained as byte files, and full lsof/vmmap output is compressed in the copied package. The mapping observations distinguish target paths, while the earlier published reversal report supplies initializer-marker evidence from a separate run. This audit does not merge those observations into one successful live reversal.

The retained server exceeded a 1,572,864 KiB summed-RSS cap by 3,744 KiB, so the probe killed the watchdog and active worker. The separate forced-restart run peaked at 1,572,736 KiB, only 128 KiB below that cap. Summed RSS includes shared pages, and sampling may miss shorter peaks. These figures limit further worker experiments on the recorded host; they are not Lean semantic failures or capacity estimates for an Anneal service.

[source-package-inventory-v46.csv](support/source-package-inventory-v46.csv) hashes every retained file in the v45 parent audit and the exact copied mapped-worker package. [validation-v46.json](support/validation-v46.json) records input and generated hashes, counts, changed IDs and source packages. The [builder](support/build_audit.py) derives every v46 row from v45, checks issue headings and destination mappings, and writes the ledgers. The [checker](support/check.py) verifies inheritance, changed-row limits, source hashes, copied package checks, inventory and metadata. It does not rerun Lean or the OS mapping tools.

Run python3 -B support/check.py from this package. The next product work remains the inherited Anneal worker-generation ownership, plugin identity, fixture isolation and end-to-end verification gates. This report records evidence for agenda rows; it does not select an architecture.
