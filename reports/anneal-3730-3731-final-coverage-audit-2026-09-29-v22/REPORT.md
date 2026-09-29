# #3730/#3731 coverage audit v22: current Anneal V2 source surface

## Summary

The current Anneal V2 redesign has a reachable `setup` command and source helpers for Cargo target selection, LLBC filenames, toolchain paths, and directory locking. None of those helpers currently provides a verification command, a Charon/Aeneas/Lean production chain, proof acceptance, LSP, or MCP. This source map narrows wording in the [333-row ledger](support/row-challenge-v22.json) without promoting any investigation or suggestion. The 159 [#3731 investigations](support/investigation-final-v22.csv), 174 [#3730 suggestions](support/3730-crosswalk-final-v22.csv), and [13 gated rows](support/unrun-conditional-inputs-v22.csv) retain v21 status counts.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 4 | 161 | 5 | 4 |

## Applicability

This audit starts from the `reference` tree at `a5b4d034aa65aa44d85afc943c3caec26a5229ba`, the v21 ledger, and the separate [current V2 source report](../anneal-v2-current-source-surface-main-bd0956b-2026-09-29/REPORT.md) for `google/zerocopy` `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`. The source report concerns the tracked `anneal/` redesign, not historical `anneal/v1/`. Its Cargo build and default test attempts stopped during offline dependency resolution before compilation; they are not runtime results.

The public #3730 and #3731 issue bodies and their one comment each were reread at **2026-09-29 18:49:42 UTC**. Their state, update metadata, and body/comment SHA-256 hashes exactly match v21; #3730 is closed and #3731 open. The [frozen issue text](support/issue-scope-snapshot.json) and [live hash record](support/live-issue-hashes.json) bind this audit to the same 333 requested IDs. Issue proposals are investigation scope, not adopted product requirements.

## Findings

The [row challenge](support/row-challenge-v22.json) attaches the source report to 62 explicitly mapped rows. Nine residuals received narrower current-source wording: I020, I075, I076, I078, I089, I096, I157, L07, and L08. The other mapped residuals and all unmapped residuals retain v21 text and prerequisites. Every row has a v22 status, evidence assessment, and next prerequisite; no new complete ID or newly available distinct cached-only experiment was identified. Basis: **source** for current V2 reachability, **execution** only for the source report's failed offline dependency resolution, and **derived** mapping against the preserved issue ledger.

- **Selection and output names:** `resolve.rs` enumerates package, target, and crate kind; `scanner.rs` derives an LLBC filename. The CLI does not call either helper. The complete producing compilation-unit identity, Charon invocation attestation, and collision rejection remain open for I020/I075/I076 and D07.
- **Locks and concurrent work:** `LockedRoots` and `DirLock` supply a run-directory exclusion primitive. The CLI does not call it, and the shared Cargo target path lies outside that lock. This does not close transactional Charon publication, single-flight ownership, cancellation, lock ordering, or the mapped #3730 concurrency suggestions.
- **Setup and prepared consumers:** `setup` is reachable, and a feature-gated test assembles a read-only Lake archive fixture. The report did not execute that fixture or obtain a real archive, fresh first goal, InfoView/RPC operation, or prepared-environment attestation. F04 and the other archive-gated rows retain their exact inputs.
- **Locators versus generations:** Workspace/run and LLBC paths are useful locators, but do not authenticate source, LLBC, generated Lean, imports, workers, RPC sessions, or trust state. The cross-layer identity and provenance investigations remain partial.
- **Verification and annotations:** The CLI has no verify path, generated obligation/claim manifest, checked result, live proof query, or Rust-hosted annotation projection. I137 and I138 remain complete only for their disposable vertical-slice scopes. I072 remains not run for an existing MCP adapter under Anneal conditions.

The [source-package inventory](support/new-file-inventory-v22.csv) pins the source report's two files. The [validation record](support/validation-v22.json) pins prior-ledger bytes, issue hashes, counts, source revision, and all generated files. The [audit snapshot](support/audit-snapshot.json) names the exact reference and upstream revisions.

## Boundaries

Source presence is not executed acceptance evidence. Current V2 Rust code was not compiled in the source report because its pinned Charon checkout was missing from the offline cache. The feature-gated archive test, actual archive, product concurrency lifecycle, and full verification workflow were not run. V21's cached-resource recheck and 13 not-run/conditional gates remain the basis for those prerequisites; this audit did not fetch or install dependencies.

The 333 statuses classify investigation coverage at the stated scope. They do not measure implementation completeness. The four `complete` investigation rows and four `complete` suggestions preserve their own narrow scopes, including I137/I138's disposable prototypes. This source report does not extend them to the current binary.

## Evidence

- **Issue scope and live state:** Public GitHub REST issue and comments endpoints for [#3730](https://github.com/google/zerocopy/issues/3730) and [#3731](https://github.com/google/zerocopy/issues/3731), reread 2026-09-29; [hash record](support/live-issue-hashes.json) and [frozen bodies/comments](support/issue-scope-snapshot.json).
- **Current source:** [Anneal V2 source-surface report](../anneal-v2-current-source-surface-main-bd0956b-2026-09-29/REPORT.md), upstream `google/zerocopy` `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, especially its reachability table, item-level mapping, and offline Cargo result.
- **Prior coverage:** [v21 audit](../anneal-3730-3731-final-coverage-audit-2026-09-29-v21/REPORT.md), reference `a5b4d034aa65aa44d85afc943c3caec26a5229ba`; v21 ledgers and row challenge are the preserved decision baseline.
- **Derived material:** [v22 builder](support/build_audit.py), [checker](support/check.py), [package review](support/new-package-review-v22.csv), [file inventory](support/new-file-inventory-v22.csv), and [validation record](support/validation-v22.json). The builder is offline and derives every v22 decision from the frozen v21 baseline plus an explicit source-map ID set and nine residual corrections.

## Revalidation

Run `python3 support/check.py` from this package. It rebuilds derived files twice, compares all 333 rows against v21, verifies unchanged statuses and 13 gated inputs, checks issue and source-report hashes, and confirms the nine narrowed residuals. Run `python3 tools/reference.py check` at the corpus root for structural validation. At a newer upstream revision, trace actual CLI reachability and rerun eligible offline build/tests before changing product-gated statuses; reread issue bodies/comments if their hashes or state change.
