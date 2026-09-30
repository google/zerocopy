# #3730/#3731 coverage audit v68: newer-source context through frozen reference 9148ef08

## Summary

This audit inherits the published [v67 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v67/REPORT.md) and reconciles all **12 report packages** added after v67 through exact frozen `reference@9148ef08a73a546d6b214a48bc92ffbdb2f3e3d0`. Six source reviews have exact analogs in v67's 41-package source/spec synthesis. They add **source-review context only** to 15 investigations and, through 345 inherited destination links, 43 suggestions. No new Anneal product path was executed by those reviews; no row status, gate, residual, or prerequisite changes. The other six additions are inventoried but provide no exact mapped row evidence in this audit.

## Lineage and corpus

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`; v67 was published at `36676e26578f0662fed4fac97f291058e61b2574`; the frozen v68 parent is `9148ef08a73a546d6b214a48bc92ffbdb2f3e3d0`. The [validation](support/validation-v68.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v68.csv) hashes all **152 files** in the complete v67 audit and 12 added packages. The [source map](support/source-map-v68.json) classifies each addition with an exact mapping basis or exclusion reason.

The six mapped source reviews are F*, HLS/hie-bios, Netstack3, Nix/Guix, Roslyn, and TypeScript. Their mapping follows the already published v67 source-package ID map, not a new interpretation of issue wording. The affected investigation IDs are **I001, I002, I005, I007, I009, I010, I011, I020, I063, I064, I096, I144, I145, I157, I159**. The exact 43 affected suggestion IDs and per-row package links are in [validation](support/validation-v68.json) and the [row challenge](support/row-challenge-v68.json). Some source reviews found no newer source commit or a source range with no mapped-path drift; others found source changes or an unresolved implementation mapping. None validates the full frozen claim or an Anneal product outcome.

The remaining five version/source packages cover Aeneas's compatible bundle, standalone Charon, Lean/Lake 4.34.1 (two packages), and Rust/Cargo 1.98.1. They preserve version and source comparisons but do not supply an exact v67 ID map. Their results remain subject-specific source context and are **not** promoted into an arbitrary #3731 row. The twelfth package, the I102 same-key interruption attempt, completed only an initial cache-disabled prebuild and was refused at the next memory admission before any cache writer, interruption, or recovery cell. Its own report expressly retains the v67 I102 residual. All six are recorded in the corpus inventory.

## Preservation and boundaries

The [investigation ledger](support/investigation-final-v68.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v68.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v68.json) retains all **333** v67 rows and every previous field byte-for-byte as values; it appends only v68 assessment, source package, and link fields. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v68.json) is byte-identical to v67's v65-origin snapshot; no current GitHub issue read, update, or state change occurred.

Source identity, source diff, release metadata, or a stopped attempt does not establish product coverage. The source reviews do not resolve their newer runtime claims, and no matched Anneal V2 execution was performed here. Existing product, platform, and representative-workload prerequisites remain. The six inventory-only packages remain available for a future exact row mapping if new direct evidence justifies one; this audit makes no such inference.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates the v68 ledger and source inventory from the frozen parent, published v67 package, and 12 report packages. The checker verifies v49→v67→v68 ID/order continuity, all inherited fields, link counts, exact source mapping, every source file hash, and metadata. This is an uncommitted candidate; no issue text was edited.
