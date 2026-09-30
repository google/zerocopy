# #3730/#3731 coverage audit v72: reconciliation current-source context

## Summary

This audit inherits the published [v71 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v71/REPORT.md) and reconciles the sole report package added through frozen `reference@5ec5624ac2177633ce09ea3852f5488c05082a2e`: the [R510 reconciliation source review](../reconciliation-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I010, I063 and I064, and through inherited destinations to four #3730 suggestions. No row status, gate, residual or next prerequisite changes. The review executed no controller, watcher, Kubernetes cluster or Anneal product.

## Exact context mapping

The [source map](support/source-map-v72.json) names `reconciliation-event-hints-repair-loops-2005-2026` as R510's exact predecessor. The published v67 ID map links that report to **I010, I063 and I064**. The new source review keeps controller-runtime and client-go identities separate. Controller-runtime `main` is still at the original pin; the cited Reflector file in the Kubernetes monorepo has an unchanged blob on a 20-commit forward `master` range. These findings are bounded to selected source files. They do not establish runtime convergence, watch continuity, publication safety or Anneal behavior. The review labels runtime unexecuted and Anneal product unassessed.

The four suggestion IDs with context through exact inherited destinations are **H04, H06, H07 and K07**. Per-row source links are recorded in the [row challenge](support/row-challenge-v72.json) and [validation](support/validation-v72.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v71 at `7aba064d95afec974b2478feca6f8c1a1c0b3088`, and this uncommitted candidate's exact frozen parent is `5ec5624ac2177633ce09ea3852f5488c05082a2e`. [Validation](support/validation-v72.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v72.csv) hashes all **19 files** in the complete v71 audit and one new report package.

The [investigation ledger](support/investigation-final-v72.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v72.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v72.json) retains all **333** v71 rows and every inherited field value; it appends only v72 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v72.json) is byte-identical to v71's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares source identity and selected claim-mapped files, not complete controller, cache or Anneal behavior. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v72 from the frozen parent, published v71 package and sole new package. The checker verifies v49→v71→v72 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
