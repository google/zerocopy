# #3730/#3731 coverage audit v73: Buck2 current-source context

## Summary

This audit inherits the published [v72 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v72/REPORT.md) and reconciles the sole report package added through frozen `reference@bac23b79ad9acef60309d1f9917a1024d441ed0d`: the [R346 Buck2 source review](../buck2-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I144 and I159, and through inherited destinations to 23 #3730 suggestions. No row status, gate, residual or next prerequisite changes. No Buck2, DICE or Anneal runtime was executed by the source review.

## Exact context mapping

The [source map](support/source-map-v73.json) names `buck-to-buck2-one-graph-rewrite-2013-2026` as R346's exact predecessor. The published v67 ID map links that report to **I144 and I159**. The newer review finds the four cited architecture-document blobs unchanged across a 29-commit forward Buck2 `main` range. It separately identifies an adjacent DICE `compute_with_key` API and source test. This source delta does not establish changed scheduling, invalidation, early cutoff, performance, or Anneal architecture behavior. The source test was not run; newer runtime and Anneal product results remain unassessed.

The 23 suggestion IDs with context through exact inherited destinations are **I05, N01–N12 and O01–O10**. Per-row source links are recorded in the [row challenge](support/row-challenge-v73.json) and [validation](support/validation-v73.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v72 at `ef8e39197bf8d1f6bb8753e7155c3a494fa8e2f4`, and this uncommitted candidate's exact frozen parent is `bac23b79ad9acef60309d1f9917a1024d441ed0d`. [Validation](support/validation-v73.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v73.csv) hashes all **21 files** in the complete v72 audit and one new report package.

The [investigation ledger](support/investigation-final-v73.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v73.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v73.json) retains all **333** v72 rows and every inherited field value; it appends only v73 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v73.json) is byte-identical to v72's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares source identity, cited documents and adjacent DICE source. It does not run a build graph or test, or establish newer-version Buck2 or Anneal behavior. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v73 from the frozen parent, published v72 package and sole new package. The checker verifies v49→v72→v73 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
