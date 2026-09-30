# #3730/#3731 coverage audit v55: Rust and Charon path remapping

## Summary

The [pinned path-remap experiment](../anneal-3731-i079-path-remap-2026-09-30/REPORT.md) adds a bounded cross-tool filename specimen to the published [v54 ledger](../anneal-3730-3731-final-coverage-audit-2026-09-30-v54/REPORT.md). Only **I079** receives an appended residual. **I031** gains source-provenance context with its residual unchanged. All **333 row IDs**, **159 investigations**, **174 #3730 suggestions**, **345 destination links** and row order are preserved. No status, gate or next prerequisite changes.

| Scope | Complete | Partial | Not run | Conditional |
| --- | ---: | ---: | ---: | ---: |
| #3731 investigations | 4 | 151 | 1 | 3 |
| #3730 suggestions | 3 | 162 | 5 | 4 |

## Applicability

The parent published `reference` tip is `87bbe2425ed749ba4eff9e729ad6799313124cb2`. This audit derives from its v54 ledger. A [fresh public GitHub REST snapshot](support/live-issue-snapshot-v55.json) of both issue bodies and comments was fetched on 2026-09-30. #3730 remained closed as not planned; #3731 remained open. Their issue fields matched the v54 snapshot byte-for-byte, apart from the new fetch timestamp. This package makes no issue edit.

The new source report uses one macOS arm64 host and pinned local Rust/Cargo and Charon binaries. Its deliberately invalid rustc control and valid three-file Charon crate use the same remap flag, but are different source files. It does not exercise Anneal's provenance map, cache identity or editor pipeline.

## Findings

For the invalid Rust file, `--remap-path-prefix=src=/virtual/anneal-src` changed rustc JSON `file_name` from `src/error.rs` to `/virtual/anneal-src/error.rs`. Cargo verbose stderr proves the flag reached Charon's driver in the successful extraction. Both LLBC local file tables nevertheless retained `src/lib.rs`, `src/left/common.rs` and `src/right/common.rs`; embedded contents and local item file IDs, spans and source texts matched. The raw decoded LLBC trees differed at the requested destination path and four positional `short_names` leaves, while typed short-name maps agreed. The ordering variation is not attributed to remapping. **Basis: bounded four-cell execution with retained raw JSON, command line and LLBC evidence.**

I079's residual now records this path-remap contrast. It remains **partial** at its **product** gate: a general normalizer, implemented Anneal source association and editor conversion remain unobserved. I031 gains context for cross-tool source locators, without any direct Anneal diagnostic-routing evidence. Its residual, gate and prerequisite stay unchanged.

## Boundaries

One remap prefix, one crate, one invalid diagnostic file and one extraction per control do not determine internal Charon/rustc source-map mechanics, behavior for absolute paths or generated files, other versions/platforms, or Anneal cache policy. The issue snapshot establishes public fields only at fetch time. No issue checkbox or state is changed.

## Evidence

[source-package-inventory-v55.csv](support/source-package-inventory-v55.csv) hashes all retained files in the v54 audit and new I079 report. [validation-v55.json](support/validation-v55.json) records the parent tip, snapshot and generated/input hashes, counts, direct/context IDs and source packages. [build_audit.py](support/build_audit.py) derives v55 rows from v54, and [check.py](support/check.py) verifies inheritance, the exact I079 update, unchanged I031 residual, stable statuses/gates/prerequisites, source hashes and metadata. The source package's own checker independently reads the raw LLBC and rustc JSON evidence. The audit checker does not rerun Rust or Charon.

## Revalidation

Run `python3 -B support/check.py` from this package and `python3 -B tools/reference.py check` from the corpus root. A later issue-state claim requires another public fetch. Product-level source association remains open until implemented Anneal behavior can be measured.
