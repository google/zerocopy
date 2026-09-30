# #3730/#3731 coverage audit v74: SerAPI/Rocq-LSP current-source context

## Summary

This audit inherits the published [v73 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v73/REPORT.md) and reconciles the sole report package added through frozen `reference@e0da59ac5dea7e4e75ddd021fc0c26d69bd74cda`: the [R386 SerAPI/Rocq-LSP source review](../rocq-serapi-fleche-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I002, I007 and I157, and through inherited destinations to four #3730 suggestions. No row status, gate, residual or next prerequisite changes. No SerAPI, Rocq LSP, Flèche, Rocq or Anneal runtime was executed.

## Exact context mapping

The [source map](support/source-map-v74.json) names `coq-rocq-stm-serapi-fleche-architecture-2013-2026` as R386's exact predecessor. The published v67 ID map links that report to **I002, I007 and I157**. The new review freezes its eleven evidence-map claims and finds both official default-branch tips equal to their original report pins. Their forward source ranges are therefore zero commits, with unchanged claim-mapped blobs. This is a source-identity disposition, not a newer-version validation or a runtime behavior finding. The review labels current runtime unexecuted and Anneal product unassessed.

The four suggestion IDs with context through exact inherited destinations are **H09, L04, L07 and L08**. Per-row source links are recorded in the [row challenge](support/row-challenge-v74.json) and [validation](support/validation-v74.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v73 at `f64e634e06aaf8b7eae2fefb3a9d7f2ebf82d3b2`, and this uncommitted candidate's exact frozen parent is `e0da59ac5dea7e4e75ddd021fc0c26d69bd74cda`. [Validation](support/validation-v74.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v74.csv) hashes all **27 files** in the complete v73 audit and one new report package.

The [investigation ledger](support/investigation-final-v74.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v74.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v74.json) retains all **333** v73 rows and every inherited field value; it appends only v74 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v74.json) is byte-identical to v73's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares exact source identities and claim-mapped files. It does not establish newer implementation behavior or an Anneal integration result. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v74 from the frozen parent, published v73 package and sole new package. The checker verifies v49→v73→v74 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
