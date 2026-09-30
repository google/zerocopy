# #3730/#3731 coverage audit v77: seL4/CompCert/Everest source context

## Summary

This audit inherits the published [v76 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v76/REPORT.md) and reconciles the sole report package added through frozen `reference@1a73769318280689985be655c67693ac59b56cae`: the [grouped R507/R578 source review](../sel4-compcert-everest-current-source-review/REPORT.md). The two report rows are treated separately. **R507** revisits an exact v67 source/spec analog and adds **source-review context only** to I001 and linked suggestion I01. **R578** has no v67 ID map and is inventoried without a #3731 row link. No row status, gate, residual or next prerequisite changes. No proof, compiler, extraction or Anneal runtime was executed.

## Exact context mapping

The [source map](support/source-map-v77.json) names `proof-maintenance-architectures-sel4-compcert-everest-2009-2026` as R507's exact predecessor. The published v67 ID map links that report only to **I001**. R578's narrower `verified-compiler-pass-composition-compcert-3-18-popl-2008` report is absent from that map. Its newer CompCert source review is retained in the grouped package and corpus inventory but does not add row context.

The grouped review observes five default-branch repositories still at their original pins. CompCert development `master` is four commits forward, while its three cited blobs are unchanged. This is bounded selected-file continuity. The latest CompCert release remains v3.18; the development commits are not a newer official release. No theorem replay, proof maintenance workload or Anneal product was run, so neither R507 nor R578 establishes a current runtime outcome or product coverage.

The sole suggestion ID with context through an exact inherited destination is **I01**. Its link and source package assignment are recorded in the [row challenge](support/row-challenge-v77.json) and [validation](support/validation-v77.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v76 at `47d8250bff3ea17f1fbb4340370032e03692617b`, and this uncommitted candidate's exact frozen parent is `1a73769318280689985be655c67693ac59b56cae`. [Validation](support/validation-v77.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v77.csv) hashes all **39 files** in the complete v76 audit and one grouped report package.

The [investigation ledger](support/investigation-final-v77.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v77.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v77.json) retains all **333** v76 rows and every inherited field value; it appends only v77 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v77.json) is byte-identical to v76's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares exact source identities and selected claim-mapped files. It does not replay proofs or verify current release behavior. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v77 from the frozen parent, published v76 package and sole new package. The checker verifies v49→v76→v77 row continuity, every inherited field, exact destination links, per-report source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
