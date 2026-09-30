# #3730/#3731 coverage audit v59: thirty-two Lean RPC references

## Summary

The [32-reference release and keep-alive experiment](../anneal-3731-i044-many-ref-retention-release-2026-09-30/REPORT.md) adds a bounded many-reference functional cell to the published [v58 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v58/REPORT.md). Only **I044** receives an appended residual. **C08** gains handle-lifetime context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, and row order are preserved. Every status, gate, and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `e24b726c9f84d54957c034ac856e8dad83ea6a96`. This audit derives from its v58 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v59.json) of both issue bodies and comments was fetched on 2026-09-30. #3730 remained closed as not planned and #3731 remained open. Issue fields match v58 byte-for-byte apart from fetch time. No issue checkbox or status was modified.

The new source package used one direct Lean 4.30.0-rc2 server and 32 distinct rich RPC references on one document version. All 32 resolved before release. After releasing 16 and sending five keep-alives over 43.2004 seconds, all released references failed with `-32602` and all retained references succeeded. Server/file-worker PIDs remained the same. This measures a controlled 32-reference functional split, not attributable memory or an Anneal retention policy.

## Row disposition

I044's residual now includes the 32-reference control and preserves the remaining need for larger-scale lifetime/cost measurements and Anneal generation-specific ownership/reclaim policy. Its status remains **partial**, its gate remains **product**, and its next prerequisite remains the implemented Anneal V2 integration contract. C08 receives context only; its residual, status, gate, and prerequisite stay unchanged. The other 331 rows inherit v58 without a new residual.

The previous single-reference no-message and keep-alive reports remain separate controls. The new fixture differs from both, so this audit makes no same-fixture causal memory or exact-TTL claim.

## Evidence and revalidation

[source-package-inventory-v59.csv](support/source-package-inventory-v59.csv) hashes all retained files in the v58 audit and new I044 report. [validation-v59.json](support/validation-v59.json) records the parent tip, fresh issue snapshot, input/generated hashes, counts, direct/context IDs, and source packages. [build_audit.py](support/build_audit.py) derives v59 rows from v58 and checks the 159 issue headings, 174 crosswalk rows, and 345 links against current issue content. [check.py](support/check.py) verifies inheritance, only I044's residual update, unchanged C08 residual, statuses/gates/prerequisites, inventory, source metadata, and the source package's offline checker. It does not rerun Lean.

Run `python3 -B support/check.py` from this audit directory and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim needs another public fetch. Product-level reference ownership, expiry recovery, memory accounting and durable historical-query semantics remain open until implemented Anneal behavior can be measured.
