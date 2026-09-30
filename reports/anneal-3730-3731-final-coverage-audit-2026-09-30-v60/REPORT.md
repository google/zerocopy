# #3730/#3731 coverage audit v60: stepwise Lean document versions

## Summary

The [stepwise direct Lean LSP experiment](../anneal-3731-i112-stepwise-lsp-versions-2026-09-30/REPORT.md) adds intermediate diagnostic and goal observations to the published [v59 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v59/REPORT.md). Only **I112** receives an appended residual. The #3730 crosswalk has no suggestion mapped to I112, so no suggestion row receives context or a changed residual. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, and row order are preserved. Every status, gate, and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `2cec790eeec883e83ac66dcfa021c51ad65ad4f1`. This audit derives from its v59 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v60.json) of both issue bodies and comments was fetched on 2026-09-30. #3730 remained closed as not planned and #3731 remained open. Issue fields match v59 byte-for-byte apart from fetch time. No issue checkbox or status was modified.

The source package used installed Lean 4.30.0-rc2 in two separate direct server processes, one at a time. The malformed version sequence v1/v2/v4/duplicate-v4/lower-v3/v5 yielded source-specific goals 1/2/4/40/3/5 after unique diagnostic markers; the fresh monotonic v1–v5 control yielded 1/2/3/4/5. Each retained the final v5 goal after a 1.5-second quiet interval. Six separate fresh batch checks confirmed that every source variant produced its unique marker and goal text, while intentionally failing verification because each file contained a placeholder and unknown identifier.

## Row disposition

I112's residual now records the stepwise direct Lean observations and preserves the need for actual lost watcher/transport/MCP delivery, reconnect and Anneal authoritative-state reconciliation. Its status remains **partial**, its gate remains **product**, and its next prerequisite remains the implemented Anneal V2 integration contract. The other 332 rows inherit v59 without a new residual.

Duplicate/lower versions deliberately violate the client's monotonic-update assumption. The observed direct-server behavior is not an LSP compliance claim and does not exercise message loss, an editor, or product publication fences.

## Evidence and revalidation

[source-package-inventory-v60.csv](support/source-package-inventory-v60.csv) hashes all retained files in the v59 audit and new I112 report. [validation-v60.json](support/validation-v60.json) records the parent tip, fresh issue snapshot, input/generated hashes, counts, direct ID and source packages. [build_audit.py](support/build_audit.py) derives v60 rows from v59 and checks the 159 issue headings, 174 crosswalk rows and 345 links against current issue content. [check.py](support/check.py) verifies inheritance, only I112's residual update, unchanged statuses/gates/prerequisites, inventory, source metadata and the source package's offline checker. It does not rerun Lean.

Run `python3 -B support/check.py` from this audit directory and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim needs another public fetch. Product-level delivered-event provenance, authoritative resync and stale-query rejection remain open until implemented Anneal behavior can be measured.
