# #3730/#3731 coverage audit v51: Unicode Lean LSP encoding offers

## Summary

The [Unicode Lean LSP encoding report](../anneal-3731-i062-utf8-only-unicode-lsp-2026-09-30/REPORT.md) adds one bounded direct server result to the published [v50 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v50/REPORT.md). Only **I062** receives a revised residual. **B03** and **I025** receive bounded context while their residuals remain unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, issue fields and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `ebfeac694e945da0b52e09c6a185d857f982f4f3`. This audit derives from its v50 row ledger and copies its retained [issue snapshot](support/live-issue-snapshot-v51.json) exactly. That inherited snapshot records #3730 closed and #3731 open. **No new public issue fetch was performed for v51.**

The source package ran locally installed pinned Lean 4.30.0-rc2 in two strictly sequential direct `lean --server` sessions, then two batch checks. It used one Python stdio client and a tiny Unicode Lean file. There was no Anneal projection, real editor, MCP adapter or generated model.

## Findings

Both the UTF-8-only and UTF-16-only initialize responses omitted an explicit `positionEncoding`; both initial `unknownName` diagnostics used UTF-16 characters 16–27, whereas independent UTF-8 byte positions were 19–30. A UTF-16-positioned incremental replacement cleared the error. The UTF-8-byte-positioned replacement after a UTF-8-only offer produced an `unexpected end of input` diagnostic. Fresh original/patched batch checks exited 1/0. The exact wire frames, fixture, coordinate oracle, resource samples and cleanup are retained in the source report. **Basis: execution in the source package, with inherited and derived row mapping here.**

I062's residual now records this direct Lean component result. Its **partial/product** status and next prerequisite remain unchanged because the observation does not establish a negotiated UTF-8 selection, protocol violation, real editor behavior or Anneal source mapping. B03's UTF-16 stress-test row and I025's coordinate-conversion row gain context only; their product residuals and prerequisites remain unchanged.

## Boundaries

The UTF-8-only offer did not produce an explicit UTF-8 selection. The resulting post-edit complete document text was not returned by the server; only its diagnostic was observed. No representative editor/client, Rust-hosted projection, unsaved source owner, cross-tool diagnostic router or future Lean version was tested. No issue checkbox, status, gate or prerequisite changes. The inherited issue snapshot does not establish public issue state after its earlier fetch.

## Evidence

[source-package-inventory-v51.csv](support/source-package-inventory-v51.csv) hashes every retained file in the v50 audit and new I062 report. [validation-v51.json](support/validation-v51.json) records the parent tip, inherited issue snapshot, input/generated hashes, counts, changed and context IDs and source packages. The [builder](support/build_audit.py) derives v51 rows from v50 and checks issue headings and destination mappings. The [checker](support/check.py) verifies ledger inheritance, the sole I062 residual update, unchanged B03/I025 residuals, statuses/gates/prerequisites, metadata, inventory and the source-package checker. It does not restart Lean.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 tools/reference.py check` from the corpus root. A new live issue comparison requires a fresh public fetch. Product closure still needs actual client/server capability handling through an Anneal projection and representative editor round trips.
