# #3730/#3731 coverage audit v56: conditional Charon module source

## Summary

The [corrected Charon `cfg_attr(path)` experiment](../anneal-3731-i079-cfg-attr-module-2026-09-30/REPORT.md) adds a bounded conditional source-selection specimen to the published [v55 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v55/REPORT.md). Only **I079** receives an appended residual. **I031** gains source-provenance context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links** and row order are preserved. No status, gate or next prerequisite changes.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `1018438e175202747f052dc1c0734d331b656f01`. This audit derives from its v55 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v56.json) of both issues and comments was fetched on 2026-09-30. #3730 remained closed as not planned and #3731 remained open. Their issue fields matched the v55 snapshot byte-for-byte, apart from fetch time. No issue checkbox or issue status was modified.

The source package used one macOS arm64 host and pinned local Charon/Cargo/rustc binaries. Two corrected, offline Cargo feature cells used the same root and logical module declaration, private target directories and separate LLBC destinations. The alternate cell added only `feature="alternate"`; both disabled default features. A preliminary run with an extra empty default feature is retained solely for provenance and excluded from conclusions.

## Findings

The default LLBC selected `src/default.rs` as local file ID 1, with marker literal 17. The alternate LLBC selected `src/alternate.rs` as local file ID 1, with marker literal 29. Each unselected file was absent. The logical `cfg_attr_module_probe::selected::marker` item name, numeric file ID and span stayed the same. Full decoded LLBC trees differed at selected file name/content, marker MIR literal/source text, and requested destination only. **Basis: bounded corrected Charon pair and retained raw LLBC/driver command evidence.**

I079's residual records this two-feature conditional selection. It remains **partial** at its **product** gate: general normalization, implemented Anneal source association and cache policy are still open. I031 receives context for source provenance, without direct Anneal diagnostic-routing evidence. Its residual, gate and prerequisite remain unchanged.

## Boundaries

One crate, two feature states and one extraction per state do not establish general `cfg_attr` behavior, stable numeric file IDs across arbitrary builds, Aeneas/Lean mapping, diagnostics, or Anneal cache-key rules. The pair only proves logical name and numeric file ID are insufficient to distinguish these two outputs; selected path, source content or feature state each distinguish this pair. The issue snapshot establishes current public fields only at fetch time.

## Evidence

[source-package-inventory-v56.csv](support/source-package-inventory-v56.csv) hashes all retained files in the v55 audit and new I079 report, including the explicitly excluded preliminary acquisition. [validation-v56.json](support/validation-v56.json) records the parent tip, snapshot/input/generated hashes, counts, direct/context IDs and source packages. [build_audit.py](support/build_audit.py) derives v56 rows from v55, and [check.py](support/check.py) verifies exact inheritance, only I079's residual update, unchanged I031 residual, statuses/gates/prerequisites, inventory and source metadata. The source checker reconstructs projections from raw LLBC; the audit checker does not rerun Charon.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim requires a new public fetch. Product-level source association remains open until implemented Anneal behavior can be measured.
