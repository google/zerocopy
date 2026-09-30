# #3730/#3731 coverage audit v54: Charon lexical source-file aliases

## Summary

The [matched Charon symlink/copy report](../anneal-3731-i079-symlink-module-identity-2026-09-30/REPORT.md) adds a bounded file-identity specimen to the published [v53 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v53/REPORT.md). Only **I079** receives a revised residual. **I031** gains source-provenance context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links** and row order are preserved. Every status, gate and next prerequisite remains unchanged.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `6b0acaee13124bc17bef31c764693836a93ff25a`. This audit derives from its v53 row ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v54.json) was fetched on 2026-09-30 from both issues and their comments. #3730 remained closed as not planned and #3731 remained open. Their bodies, comment bodies, update timestamps and states were byte-identical to the v53 snapshot; only the fetch timestamp changed. No checkbox or status was modified.

The source package ran two sequential pinned Charon/Cargo controls on one macOS APFS host. The same crate's two lexical module paths were either symlinks to one inode or distinct physical copies of identical source bytes. The source report directly measures LLBC file IDs and item associations. It does not run Anneal's source map, cache key or editor pipeline.

## Findings

In the symlink layout, both `common.rs` paths dereferenced to one device/inode. In the physical-copy control, they had distinct inodes. Both Charon LLBCs nonetheless recorded separate local file IDs 1 and 2 for `src/left/common.rs` and `src/right/common.rs`; the corresponding `left::step` and `right::step` items retained those separate file IDs, while embedded source text and hashes matched. A full decoded comparison found seven differing leaves: the requested destination path and six positional `short_names` key/value leaves across three entries. Typed-key/name maps agreed. The ordering difference is not causally attributed to symlinks, and selected-field agreement does not establish semantic equivalence. **Basis: direct bounded execution and retained filesystem/LLBC artifacts.**

I079's residual now records this same-inode lexical-alias case. It remains **partial** at its **product** gate: general LLBC normalization, multi-file source association under actual Anneal, and cache-key policy are still open. I031 receives context for raw Charon provenance but no direct diagnostic-routing or ownership-map evidence; its residual, gate and prerequisite remain unchanged.

## Boundaries

One APFS host and one extraction per layout cannot define cross-filesystem, cross-version or long-term numeric file-ID stability. The source report does not test symlink spelling variations, `cfg_attr(path)`, path remapping, Aeneas/Lean mapping or editor diagnostics. The issue snapshot establishes current public issue fields only at its fetch time. No issue checkbox or issue state changes follow from this package.

## Evidence

[source-package-inventory-v54.csv](support/source-package-inventory-v54.csv) hashes all retained files in the v53 audit and new I079 report. [validation-v54.json](support/validation-v54.json) records the parent tip, fresh issue snapshot, input/generated hashes, counts, changed/context IDs and source packages. The [builder](support/build_audit.py) derives v54 rows from v53 and verifies the 159 issue headings, 174 crosswalk rows and 345 destination links against the fresh issue content. The [checker](support/check.py) verifies ledger inheritance, only I079's residual update, unchanged I031 residual, statuses/gates/prerequisites, metadata, inventory and the source-package checker. It does not rerun Charon.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim requires another public fetch. Anneal product-level source association still needs the implemented Rust-hosted pipeline and representative multi-file diagnostics.
