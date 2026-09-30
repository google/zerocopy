# #3730/#3731 coverage audit v57: Lean UTF-32-only LSP offer

## Summary

The [UTF-32-only Lean LSP experiment](../anneal-3731-i062-utf32-only-unicode-lsp-2026-09-30/REPORT.md) adds a bounded capability-offer and Unicode edit specimen to the published [v56 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v56/REPORT.md). Only **I062** receives an appended residual. **I025** gains coordinate context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links** and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `a5ecd5bde3d2b33457b5a13b4b435d79515f4012`. This audit derives from its v56 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v57.json) of both issue bodies and comments was fetched on 2026-09-30. #3730 remained closed as not planned and #3731 remained open. Issue fields match v56 byte-for-byte apart from fetch time. No issue checkbox or status was modified.

The source package used one direct Lean 4.30.0-rc2 server with a UTF-32-only client offer and fresh original/patched batch controls on one Unicode file. It did not exercise Anneal, a real editor or a generated proof. The normative LSP 3.17 initialization contract makes UTF-16 mandatory for clients even when absent from their advertised list and defaults an omitted server choice to UTF-16.

## Findings

The initialize response omitted `positionEncoding`. The initial `unknownName` diagnostic used UTF-16 characters 16–27 rather than scalar/UTF-32 15–26 or UTF-8 byte 19–30. A version-2 scalar-range edit yielded an `Unknown constant Nat.zeroe` diagnostic; the complete post-edit buffer was not returned. Fresh batch Lean failed on the exact original bytes and passed on the intended patched bytes. The UTF-32-only offer did not establish a selected UTF-32 wire encoding or a protocol violation. **Basis: direct wire-frame and batch execution, with independent coordinate oracle and the normative LSP definition.**

I062's residual now includes this third offer cell. It remains **partial** at its **product** gate: a real editor, Anneal projected source, source-map conversion and client fallback are still open. I025 receives coordinate context only; its residual, gate and prerequisite stay unchanged.

## Boundaries

One fixture and one server session do not establish behavior for other capability sets, Lean versions, clients or Anneal projections. The post-edit `Nat.zeroe` message is an observed diagnostic, not independent evidence of exact server buffer bytes. No issue checkbox or state change follows from this experiment.

## Evidence

[source-package-inventory-v57.csv](support/source-package-inventory-v57.csv) hashes all retained files in the v56 audit and new I062 report. [validation-v57.json](support/validation-v57.json) records the parent tip, fresh issue snapshot, input/generated hashes, counts, direct/context IDs and source packages. [build_audit.py](support/build_audit.py) derives v57 rows from v56 and checks the 159 issue headings, 174 crosswalk rows and 345 links against current issue content. [check.py](support/check.py) verifies ledger inheritance, only I062's residual update, unchanged I025 residual, statuses/gates/prerequisites, inventory and source metadata. The source checker reparses raw framed messages and batch output; the audit checker does not rerun Lean.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim needs another public fetch. Product-level editor encoding and source mapping remain open until implemented Anneal behavior can be measured.
