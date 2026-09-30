# #3730/#3731 coverage audit v76: Dafny/Boogie/Viper current-source context

## Summary

This audit inherits the published [v75 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v75/REPORT.md) and reconciles the sole report package added through frozen `reference@a26086ac804f194593749dbd74bcd1900bebeba6`: the [R389 Dafny/Boogie/Viper source review](../dafny-boogie-viper-current-source-review/REPORT.md). It revisits one exact analog in v67's source/spec synthesis. It adds **source-review context only** to I001 and, through an inherited destination, suggestion I01. No row status, gate, residual or next prerequisite changes. No verifier, backend, solver, service or Anneal runtime was executed.

## Exact context mapping

The [source map](support/source-map-v76.json) names `dafny-boogie-viper-obligation-boundaries-2005-2026` as R389's exact predecessor. The published v67 ID map links that report only to **I001**. The new review keeps six independent repository identities and finds every observed default-branch tip equal to its original report pin. Their forward source ranges are zero, with unchanged cited blobs. Separate release tags are older or divergent and are not forward claim rechecks. This is a source-identity disposition, not newer-version validation of semantic obligations, runtime behavior or Anneal product coverage.

The sole suggestion ID with context through an exact inherited destination is **I01**. Its link and package assignment are recorded in the [row challenge](support/row-challenge-v76.json) and [validation](support/validation-v76.json). Suggestion context is not a run of the suggestion. All other rows receive no new mapped evidence.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v75 at `2720194c6f74fe5489428adecc1ded39df98b096`, and this uncommitted candidate's exact frozen parent is `a26086ac804f194593749dbd74bcd1900bebeba6`. [Validation](support/validation-v76.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v76.csv) hashes all **35 files** in the complete v75 audit and one new report package.

The [investigation ledger](support/investigation-final-v76.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v76.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v76.json) retains all **333** v75 rows and every inherited field value; it appends only v76 assessment, source package and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v76.json) is byte-identical to v75's v65-origin snapshot. No GitHub issue was fetched or changed.

## Limits and revalidation

The new package compares exact source identities and claim-mapped files. It does not run semantic-obligation or product acceptance paths. The inherited product, platform and representative-workload prerequisites remain in force.

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v76 from the frozen parent, published v75 package and sole new package. The checker verifies v49→v75→v76 row continuity, every inherited field, exact destination links, source mapping, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
