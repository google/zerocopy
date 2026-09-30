# #3730/#3731 coverage audit v58: direct Lean RPC keep-alive control

## Summary

The [Lean RPC keep-alive experiment](../anneal-3731-i044-rpc-keepalive-positive-2026-09-30/REPORT.md) adds a bounded positive control to the published [v57 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v57/REPORT.md). Only **I044** receives an appended residual. **C08** gains handle-lifetime context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, and row order are preserved. Every status, gate, and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `30b9d5749aed6049d949f4f582dd64c70088d07a`. This audit derives from its v57 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v58.json) of both issue bodies and comments was fetched on 2026-09-30. #3730 remained closed as not planned and #3731 remained open. Issue fields match v57 byte-for-byte apart from fetch time. No issue checkbox or status was modified.

The new source package uses one direct Lean 4.30.0-rc2 server, one actual rich RPC reference, five keep-alive notifications over 43.1137 seconds, and a final successful dereference of the same reference/session. The published 42.01-second no-message control on the same source/tool pin returned `-32900 Outdated RPC session`. This is a bounded component comparison, with separate host runs.

## Row disposition

I044's residual now records the positive control and preserves the need for many-reference retention and product generation-specific policy. Its status remains **partial**, its gate remains **product**, and its next prerequisite remains an implemented Anneal V2 integration contract. C08 receives context only; its residual, status, gate, and prerequisite remain unchanged. The remaining 331 rows inherit v57 unchanged.

The positive control establishes that this reference stayed usable under the retained keep-alive schedule; it does not give a universal TTL, validate old references after edits/import changes, or choose Anneal's owner/reclaim policy.

## Evidence and revalidation

[source-package-inventory-v58.csv](support/source-package-inventory-v58.csv) hashes all retained files in the v57 audit and new I044 report. [validation-v58.json](support/validation-v58.json) records the parent tip, fresh issue snapshot, input/generated hashes, counts, direct/context IDs, and source packages. [build_audit.py](support/build_audit.py) derives v58 rows from v57 and checks the 159 issue headings, 174 crosswalk rows, and 345 destination links against current issue content. [check.py](support/check.py) verifies ledger inheritance, only I044's residual update, unchanged C08 residual, statuses/gates/prerequisites, inventory, source metadata, and the source package's offline checker. It does not rerun Lean.

Run `python3 -B support/check.py` from this audit directory and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim needs another public fetch. Product-level RPC lifetime, expiry recovery and durable owner/reclaim behavior remain open until Anneal can be exercised.
