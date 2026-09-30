# #3730/#3731 coverage audit v71: Kotlin/Swift current-source context

## Summary

This audit inherits the published [v70 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v70/REPORT.md) and reconciles the sole report package added through frozen `reference@a7dba95cacd7659fb84ad5e619821568fbb25b61`: the [R410 Kotlin/Swift source review](../kotlin-swift-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I002, I020, I096 and I157, and through inherited destinations to five #3730 suggestions. No row status, gate, residual or next prerequisite changes. The source review executed no compiler, language server or Anneal product.

## Exact context mapping

The [source map](support/source-map-v71.json) names `kotlin-swift-compiler-backed-ide-boundaries-2021-2026` as R410's exact predecessor. The published v67 ID map links that report to **I002, I020, I096 and I157**. The newer review keeps its six source-map claims and three separate repository identities: Kotlin FIR/Analysis API, Swift compiler SourceKit and SourceKit-LSP. It finds unchanged selected claim-mapped source blobs on forward Kotlin and Swift compiler ranges; SourceKit-LSP has no forward default-branch revision. These are bounded source-file observations, not whole-project semantic continuity or runtime behavior. The review states every newer runtime result is unexecuted and Anneal product implications unassessed.

The five suggestion IDs with context through exact inherited destinations are **D07, F05, F17, L07 and L08**. Per-row source links are recorded in the [row challenge](support/row-challenge-v71.json) and [validation](support/validation-v71.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v70 at `0acbffd307e1d4288d784055f9883dd9fa5fd3b9`, and this uncommitted candidate's exact frozen parent is `a7dba95cacd7659fb84ad5e619821568fbb25b61`. [Validation](support/validation-v71.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v71.csv) hashes all **19 files** in the complete v70 audit and one new report package.

The [investigation ledger](support/investigation-final-v71.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v71.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v71.json) retains all **333** v70 rows and every inherited field value; it appends only v71 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v71.json) is byte-identical to v70's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The grouped report compares selected source files, not complete editor or Anneal behavior. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v71 from the frozen parent, published v70 package and sole new package. The checker verifies v49→v70→v71 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
