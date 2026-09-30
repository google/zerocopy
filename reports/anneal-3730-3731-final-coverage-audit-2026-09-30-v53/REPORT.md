# #3730/#3731 coverage audit v53: owned empty-line coordinate bridge

## Summary

The [copied empty-line/v2 bridge report](../anneal-3731-i025-empty-owned-v2-bridge-2026-09-30/REPORT.md) adds a bounded component specimen to the published [v52 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v52/REPORT.md). Only **I025** receives a revised residual. **I026** receives border-policy context; its residual is unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links**, issue fields and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `e1c4cf18da52136936eec8d6361607a9036adcb9`. This audit derives from its v52 row ledger and copies its retained [issue snapshot](support/live-issue-snapshot-v53.json) exactly. That inherited snapshot records #3730 closed and #3731 open. **No new public issue fetch was performed for v53.**

The source package ran a local pinned nightly Rust compiler and Lean 4.30.0-rc2 against a small Rust doc-comment fixture and hand-authored Lean projection. It retained an explicit zero-length owned segment, a version-2 unsaved server insertion, a fresh batch comparison, five negative controls, and an excluded first run with a harness response-ID fault. The evidence does not run an Anneal projection or an editor client.

## Findings

The source package associated one empty `///| ` payload at Rust byte 58 with a projected Lean insertion at byte 33 under exact source/projection hashes and version 1. A direct Lean server accepted a version-2 insertion, with the disk still at v1. Its unknown-identifier diagnostic occupied zero-based UTF-16 line 3 columns 16–28; fresh batch on the exact v2 bytes reported one-based scalar line 4 columns 15–27. The package checker rejected synthetic header and blank-line positions, CRLF interior, wrong document version and an emoji surrogate interior. Rust, server and batch process exits were 0, 0, and 0/1 for v1/v2. The first harness attempt's empty LSP result is excluded because a server-initiated request was mistaken for a wait response; raw evidence is retained to make that exclusion reviewable. **Basis: direct bounded execution and offline source-map policy checks.**

I025's residual now records this local empty-owner and unsaved-edit specimen. It remains **partial** at the **product** gate. Its prerequisite still requires an implemented Anneal Rust-hosted projection/source map and real batch/live/editor round trips. I026 gains context for one explicitly owned zero-length segment; its direct residual, gate and prerequisite remain unchanged.

## Boundaries

The hand-authored map is illustrative. The run does not decide Anneal's annotation grammar, empty-line ownership, cross-segment edit policy, source identity after an actual Rust edit, negotiated editor encoding, generated obligations, or display-width loss. The inherited issue snapshot does not establish public issue state after its earlier fetch. No checkbox or issue status is changed by this audit.

## Evidence

[source-package-inventory-v53.csv](support/source-package-inventory-v53.csv) hashes all retained files in the v52 audit and new I025 report, including the excluded first attempt and final raw frames. [validation-v53.json](support/validation-v53.json) records the parent tip, inherited issue snapshot, input/generated hashes, counts, changed and context IDs, and source packages. The [builder](support/build_audit.py) derives v53 rows from v52 and checks issue headings/destination mappings. The [checker](support/check.py) verifies ledger inheritance, the sole I025 residual update, unchanged I026 residual, statuses/gates/prerequisites, metadata, inventory and the source-package checker. It does not restart Rust or Lean.

## Revalidation

Run `python3 -B support/check.py` from this package, then `python3 tools/reference.py check` from the corpus root. A new live issue comparison requires a fresh public fetch. Product closure still requires an actual Anneal projection, source map, and representative editor round trips.
