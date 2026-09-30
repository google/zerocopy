# #3730/#3731 coverage audit v80: R443 static Lean artifact recheck inventory

## Summary

This audit inherits the published [v79 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v79/REPORT.md) and inventories the sole report package added through frozen `reference@33094f85390762325b8ce8b27cde93be11639689`: the [R443 Lean Linux AArch64 leantar static recheck](../lean-430rc2-to-4341-linux-aarch64-leantar-static-recheck/REPORT.md). The exact frozen inventory predecessor is `lean-430-rc2-linux-aarch64-leantar-anomaly`, which does not appear in v67's published #3731 source/spec ID map. This review therefore adds **no investigation or suggestion evidence links**. All statuses, gates, residuals, prerequisites and issue snapshot remain inherited unchanged.

## Static finding and mapping disposition

The [frozen R443 inventory row](../lean-430rc2-to-4341-linux-aarch64-leantar-static-recheck/support/frozen-inventory-row.json) records the exact predecessor report path and title. This audit's [source map](support/source-map-v80.json) records R443, that path, the absence of a v67 ID-map predecessor, and the static-only evidence scope. The [checker](support/check.py) verifies these against the frozen inventory and published [v67 ID map](../anneal-3731-source-spec-synthesis-2026-09-30/support/id-map.json). No I or #3730 suggestion row receives v80 evidence.

The new report confirms that the old official Lean v4.30.0-rc2 `linux_aarch64` archive bundled an x86-64 `leantar` (`ELF e_machine=62`) in its frozen evidence, while the inspected official v4.34.1 `linux_aarch64` archive bundles an AArch64 `leantar` (`e_machine=183`). The old archive was not downloaded again; the newer archive was hashed and one member extracted for static inspection. **Neither helper was executed**, and no Lean, Lake, cache, compiler or Anneal path was run. The finding does not establish functional leantar behavior, cache compatibility, installer selection, or production completion. The pinned old-version workaround remains historical context.

The setup prompt for the R443 review correctly verified the exact frozen inventory ID and predecessor path before source work. Keep that order for future version rechecks, then separately label static package inspection and executed behavior. A newer archive member's architecture alone cannot retire a workaround in a pinned product setup.

## Preservation, lineage and evidence

The v49 audit was published at `4db5d007205b9b1a3967f0f05b4b08d49c6563e1`, v79 at `71f4f352ccaf10afde6fea5a1f1c459c6a36c19e`, and this uncommitted candidate's exact frozen parent is `33094f85390762325b8ce8b27cde93be11639689`. [Validation](support/validation-v80.json) records these commits, the parent catalog SHA-256, inherited input hashes and generated output hashes. The [source inventory](support/source-package-inventory-v80.csv) hashes all **29 files** in the complete v79 audit and new R443 report package.

The [investigation ledger](support/investigation-final-v80.csv) retains all **159** I001–I159 rows. The [suggestion crosswalk](support/3730-crosswalk-final-v80.csv) retains all **174** suggestions and **345** exact destination links. The [row challenge](support/row-challenge-v80.json) retains all **333** v79 rows and every inherited field value; its v80 fields explicitly record no mapped new evidence. Status counts remain investigations: 151 partial, 4 complete, 3 conditional, 1 not-run; suggestions: 162 partial, 3 complete, 4 conditional, 5 not-run. The inherited [issue snapshot](support/live-issue-snapshot-v80.json) is byte-identical to v79's v65-origin snapshot. No GitHub issue was fetched or changed.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the reference root. The offline [builder](support/build_audit.py) regenerates v80 from the frozen parent, published v79 package and sole new package. The checker verifies v49→v79→v80 row continuity, every inherited field, exact destination links, R443 inventory ID and predecessor, absence of an exact v67 source map, source file hashes, metadata and frozen parent identity. No issue text was edited, and this candidate is not committed or pushed.
