# #3730/#3731 coverage audit v78: RedLeaf/Linux current-source context

## Summary

This audit inherits the published [v77 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v77/REPORT.md) and reconciles the sole report package added through frozen `reference@bdc6c4706d89a710b2ff8925de2eb26b7f97c55d`: the [R511 RedLeaf/Linux source review](../redleaf-linux-current-source-review/REPORT.md). R511 revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I007 and I159, and through inherited destinations to 14 #3730 suggestions. **I092 has no R511 source-map link** and remains unchanged. No row status, gate, residual or next prerequisite changes. No Linux, RedLeaf or Anneal runtime was executed.

## Exact context mapping

The [R511 frozen matrix](../redleaf-linux-current-source-review/support/matrix.json) identifies `reports/redleaf-mixed-language-isolation-boundaries-2020-2026/REPORT.md` as its original report. The [v78 source map](support/source-map-v78.json) names that exact predecessor. The published [v67 ID map](../anneal-3731-source-spec-synthesis-2026-09-30/support/id-map.json) links it to **I007 and I159 only**. It contains no I092 entry; I092 concerns a distinct server/manifest investigation. The checker independently validates the R511 matrix path and these exact ID relationships.

The R511 version-inventory pin is a Linux commit, unchanged at the inspected official default branch. The RedLeaf paper-associated branch also remains at its pin, while current default `master` is divergent rather than a proven forward successor. The report records path-level differences across that divergent line without inferring architectural evolution. This supports only bounded source identity and comparison context, not isolation behavior, runtime compatibility or Anneal product coverage.

The 14 suggestion IDs with context through exact inherited destinations are **H09, L04 and N01–N12**. Per-row source links are recorded in the [row challenge](support/row-challenge-v78.json) and [validation](support/validation-v78.json). Suggestion context is not a run of the suggestion. All other rows, including I092, receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v77 at `d8ebe60bc920363d4e43d95713e7e6a2de5363d7`, and this uncommitted candidate's exact frozen parent is `bdc6c4706d89a710b2ff8925de2eb26b7f97c55d`. [Validation](support/validation-v78.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v78.csv) hashes all **38 files** in the complete v77 audit and the new R511 package.

The [investigation ledger](support/investigation-final-v78.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v78.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v78.json) retains all **333** v77 rows and every inherited field value; it appends only v78 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v78.json) is byte-identical to v77's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares source identities and cited files across independent and partly divergent lines. It does not run an isolation workload or verify an Anneal integration. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v78 from the frozen parent, published v77 package and sole new package. The checker verifies v49→v77→v78 row continuity, every inherited field, exact destination links, R511 matrix-to-ID mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
