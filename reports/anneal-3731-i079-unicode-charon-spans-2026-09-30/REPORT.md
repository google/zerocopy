# Charon Unicode source-span columns in a small Rust crate

## Summary

One offline pinned Charon extraction produced an error-free LLBC for an independently retained three-line Rust source. Five unique local items, serialized as seven local item records because two constants appear in both function and global arrays, have spans and `source_text` matching their exact source slices. Their line numbers are one-based and their end columns follow the end of the item text. The seven local records match a **fixture-specific display-cell calculation**: the emoji `😀` contributes two columns and the combining acute mark in `é` contributes zero. A single consistent UTF-8 byte, Unicode-scalar, or UTF-16-code-unit interpretation is contradicted by at least one of these records.

This supplements #3731 I079 and #3730 D05/A02/A08. The earlier published [ASCII-local span report](https://github.com/google/zerocopy/blob/reference/reports/anneal-3731-i079-local-span-source-text-2026-09-29/REPORT.md) found 64 matching file-ID-0 item spans but could not distinguish Unicode column units. Its 32 generated-file-ID-1 local item records were excluded because the corresponding original generated Rust file was not independently retained. This new fixture resolves the **three proposed column-unit interpretations for these local item spans only**; it does not validate those 32 generated-file records or a Rust-to-Lean mapping.

## Subject and method

- Installed local Charon binary SHA-256: `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; pinned Rust nightly `2026-05-31` was used through the installed local toolchain. The Charon binary is the same hash recorded by the earlier I079 source package.
- The executable hash identifies the observed binary. This package does not independently establish which source commit built it; any source pin in earlier reports is separate source-analysis provenance.
- `fixture/src/lib.rs` contains an emoji before `after_emoji` on the same line, a decomposed `e` plus combining acute before `after_combining` on the next line, and both sequences within `unicode_body`'s string. The fixture source SHA-256 is `b26ba311378fd7aeffcb4e82f2d38768e3577fa0df6b629cbdb602043655822c`.
- `probe.py` ran `charon cargo --preset aeneas --dest-file ... -- --manifest-path ... --package unicode_span_probe --lib --offline --locked` with one Cargo job, incremental compilation disabled, one Rayon thread, and offline Cargo. The exact command, environment subset, tool hashes, preflight, samples, output hash, and compiler output are in `results.json`. It cleaned its private `work/` tree afterward.
- `check.py` independently decodes the retained fixture and `unicode.llbc`, requires the embedded file-ID-0 contents to equal fixture bytes, locates each serialized `source_text` exactly once on the stated source line, calculates four coordinate hypotheses from the prefix through each span endpoint, and compares them to serialized columns. The fixture display-cell calculation assigns zero to combining marks, two to East Asian Wide/Fullwidth characters, and one to other fixture characters. It is an **oracle for these exact characters**, not a specification of Charon's handling of every Unicode sequence.

## Observations

| Unique local item | Observed start→end column | UTF-8 bytes | Scalars | UTF-16 units | Fixture display cells |
| --- | ---: | ---: | ---: | ---: | ---: |
| `after_emoji`, line 1 | 30→73 | 32→75 | 29→72 | 30→73 | **30→73** |
| `after_combining`, line 2 | 33→80 | 35→82 | 34→81 | 34→81 | **33→80** |
| `unicode_body`, line 3 | 0→46 | 0→50 | 0→46 | 0→47 | **0→46** |
| `EMOJI`, line 1 | 0→29 | 0→31 | 0→28 | 0→29 | **0→29** |
| `COMBINING`, line 2 | 0→32 | 0→34 | 0→33 | 0→33 | **0→32** |

Both constant spans occur twice in the LLBC, yielding seven local records. Across those seven, mismatch counts are **7 for UTF-8 bytes, 6 for Unicode scalars, 4 for UTF-16 units, and 0 for the fixture display-cell calculation**. The emoji item distinguishes byte and scalar counts from UTF-16/display; the combining-mark item distinguishes display from all three. Shifted-start and inclusive-end controls fail the independently located source-text endpoints; a changed-source-text mutation control was **not run**. LLBC file ID 0 contains the exact independently retained Rust source bytes, and `has_errors` is false. One nonlocal `core::str::len` record points to file ID 1 and is excluded because that external source is not retained here.

## Limits

This is one tiny crate, one compiler/Charon version, three source lines, and item metadata only. It does not establish the general algorithm for display width, tabs, zero-width joiners, other emoji sequences, multiline spans, macro-expanded or generated files, or editor coordinate conversion. Rust compiler/Charon source metadata and LLBC are not an authenticated Anneal declaration map. Item-span matching does not prove that a source annotation attaches to a particular generated Lean declaration, that cache keys preserve provenance, or that a proof query uses the right generation. I079's Anneal product gate and I149 remain open.

The retained run's preflight measured 75% system memory free and 20,586,795,008 free disk bytes. Over 0.255 seconds, three samples observed a peak process-tree RSS of 133,856 KiB, below the 800 MiB cap. Peak sampled and final private scratch were 6,271 bytes, below the 1 GiB cap. The short run could hide a sub-sample RSS peak. The process exited 0, retained a 20,024-byte LLBC, and removed `work/`. No download or installation occurred. Exact samples are in `results.json`.

## Revalidation

Run `python3 -B check.py` in this package. It verifies all retained source/output hashes, exact local names and spans, the seven coordinate comparisons, nonlocal exclusion, mismatch controls, and run guard results without invoking Charon or network access. To reacquire the producer observation, copy the package without `unicode.llbc`, `results.json`, `comparison.json`, or `work/` to an absent private directory on a host with the pinned local tools, run `python3 -B probe.py`, then run `python3 -B check.py --write` to write a new comparison for review. Absolute tool paths in `probe.py` are specific to this host.
