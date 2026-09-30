# #3730/#3731 coverage audit v52: Lean LSP encoding version boundary

## Summary

The [Lean 4.29 versus 4.30-rc2 Unicode LSP report](../anneal-3731-i062-lean429-version-diff-2026-09-30/REPORT.md) adds a bounded version comparison to the published [v51 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v51/REPORT.md). Only **I062** receives a revised residual. **B03** and **I025** receive bounded context while their residuals remain unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, issue fields and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `badec4d90493d883e5e6886f6695239fbfb7ac74`. This audit derives from its v51 row ledger and copies its retained [issue snapshot](support/live-issue-snapshot-v52.json) exactly. That inherited snapshot records #3730 closed and #3731 open. **No new public issue fetch was performed for v52.**

The source package reused v51's byte-identical Unicode fixture and coordinate oracle with the locally installed Lean 4.29.0 binary, compared against retained published v51 results from Lean 4.30.0-rc2. Both pins ran on one host; no later Lean release, Anneal projection, real editor or MCP adapter was involved. The 4.29 executable hash is retained; its preflight `lean --version` output was not retained as a raw transcript.

## Findings

For both versions, UTF-8-only and UTF-16-only initialize responses omitted `positionEncoding`. Initial Unicode `unknownName` diagnostics used UTF-16 characters 16–27; a UTF-16-range incremental edit cleared the error, while a UTF-8-byte-range edit under a UTF-8-only offer produced an unexpected-end diagnostic. Fresh original/patched batch exits were 1/0, and batch JSON messages matched after excluding absolute `fileName` values. Decoded initialize capabilities differed at one field: `experimental.rpcProvider.rpcWireFormat` was absent in 4.29 and `"v1"` in 4.30-rc2. No RPC request exercised that field. **Basis: direct execution at 4.29 and exact retained v51 baseline evidence, mapped to the inherited ledger here.**

I062's residual now records the one-fixture older-pin comparison and the capability delta. It remains **partial** at the **product** gate. The v51 statement that cross-version behavior had not been tested is narrowed to later releases; real editor, Anneal projection, fallback and source mapping remain open. B03 and I025 gain context only, with their residuals unchanged.

## Boundaries

One older local pin and one release candidate on the same host do not establish behavior of later compatible versions or a general Lean protocol contract. One extra transient file-progress notification occurred in the 4.29 UTF-8 session; this is not treated as a stable version difference. The source report does not claim an accepted UTF-8 encoding, a protocol violation, complete post-edit server text or RPC behavior. No issue checkbox, status, gate or prerequisite changes. The inherited issue snapshot does not establish public issue state after its earlier fetch.

## Evidence

[source-package-inventory-v52.csv](support/source-package-inventory-v52.csv) hashes all retained files in the v51 audit and new I062 version report. [validation-v52.json](support/validation-v52.json) records the parent tip, inherited issue snapshot, input/generated hashes, counts, changed and context IDs and source packages. The [builder](support/build_audit.py) derives v52 rows from v51 and checks issue headings and destination mappings. The [checker](support/check.py) verifies ledger inheritance, the sole I062 residual update, unchanged B03/I025 residuals, statuses/gates/prerequisites, metadata, inventory and the source-package checker. It does not restart Lean.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 tools/reference.py check` from the corpus root. A new live issue comparison requires a fresh public fetch. Product closure still needs actual client/server capability handling through an Anneal projection and representative editor round trips.
