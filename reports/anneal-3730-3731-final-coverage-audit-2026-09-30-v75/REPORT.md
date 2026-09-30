# #3730/#3731 coverage audit v75: Salsa/rustc current-source context

## Summary

This audit inherits the published [v74 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v74/REPORT.md) and reconciles the sole report package added through frozen `reference@b78cc3c330fb54d8bce1b769e33fe785c2df3b10`: the [R566 Salsa/rustc source review](../salsa-rustc-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I005, I015, I056 and I159, and through inherited destinations to 14 #3730 suggestions. No row status, gate, residual or next prerequisite changes. No Salsa, rustc or Anneal runtime was executed.

## Exact context mapping

The [source map](support/source-map-v75.json) names `salsa-rustc-query-granularity-2016-2026` as R566's exact predecessor. The published v67 ID map links it to **I005, I015, I056 and I159**. The newer review finds a changed Salsa cycle-documentation clause and adjacent implementation for tracked-struct restrictions; other cited Salsa blobs and two rustc developer-guide blobs are unchanged. It compares a framework implementation with compiler documentation, **not** current rustc compiler source. The source tests were not run. These observations do not establish runtime correctness, compatibility, query-granularity behavior in Anneal, or product coverage.

The 14 suggestion IDs with context through exact inherited destinations are **C10, K08 and N01–N12**. Per-row source links are recorded in the [row challenge](support/row-challenge-v75.json) and [validation](support/validation-v75.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v74 at `ca4e34659fadfb1ad24084db833adae9ffd8eb05`, and this uncommitted candidate's exact frozen parent is `b78cc3c330fb54d8bce1b769e33fe785c2df3b10`. [Validation](support/validation-v75.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v75.csv) hashes all **39 files** in the complete v74 audit and one new report package.

The [investigation ledger](support/investigation-final-v75.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v75.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v75.json) retains all **333** v74 rows and every inherited field value; it appends only v75 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v75.json) is byte-identical to v74's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares selected source files and documentation. It does not inspect current rustc compiler implementation or run a representative workload. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v75 from the frozen parent, published v74 package and sole new package. The checker verifies v49→v74→v75 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
