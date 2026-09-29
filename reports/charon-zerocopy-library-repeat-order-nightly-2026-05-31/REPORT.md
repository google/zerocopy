# Charon repeat extraction of the zerocopy library

## Summary

Three serial, offline Charon 0.1.210 runs on the real `zerocopy --lib` target
produced equal-length LLBC with different raw SHA-256 hashes. The only differences
found were the requested output filename in `options.dest_file` and the order of
17,903 `short_names` entries. The entries had unique keys and an identical
key/value multiset. After removing that one array and normalizing the one
run-specific output path, every remaining LLBC byte matched across all three
runs.

All three Charon commands exited zero but serialized `has_errors: true` and
reported 13 extraction warnings. The pinned Aeneas importer clears
`short_names` before translation, making this particular order difference
irrelevant to that importer. Aeneas and Lean were not run on the 173.5 MB,
error-bearing LLBC. This is a real library-source instance of harmless Charon
textual instability, not evidence of a successful end-to-end translation or
global determinism.

## Applicability

The source was the `zerocopy/` subtree at
`google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, Git tree
`574add5aabfa15dd2d16a4646f01f6f944d124d8`. The subtree was clean when
copied to private scratch. Charon 0.1.210 used its `aeneas` preset with Cargo's
`--package zerocopy --lib --offline --locked`; no features or alternate target
were requested. Each run had its own Cargo target directory, one build job,
disabled incremental compilation, and a new Charon process. The host was macOS
arm64 with 8 GiB physical RAM. This exact package/tool/input combination is the
measured subject.

The Aeneas subject in `REPORT.json` was inspected as source only. The release
binary was present and hashed, but it was not executed for this experiment.

## Findings

### Raw LLBC differs while its non-cache content stays byte-identical

| Run | LLBC bytes | Raw SHA-256 | Peak process-group RSS | Minimum system free memory |
| --- | ---: | --- | ---: | ---: |
| 1 | 173,520,683 | `426fa64ab7ee1be150c9d1d063f7a34decfdcf892ecde9b29f5f022d43c83f50` | 985,408 KiB | 40% |
| 2 | 173,520,683 | `60d183425f61fdc64ad082168684ea1c04d58416413255a11b3d988786a1502e` | 964,688 KiB | 42% |
| 3 | 173,520,683 | `aec93122b46a466c4ff560e369d597dd261cd76b442283d4b3e1426c9a5c35a1` | 976,816 KiB | 45% |

The first raw mismatch is the run digit in the serialized absolute
`options.dest_file` path. The sole `translated.short_names` array begins at byte
offset 4,417,993 and is 1,540,054 bytes in each output. It has 17,903 entries
and 17,903 unique keys. Its order differs; the first changed position is index
17,471 (zero-based). `support/first-order-differences.json` retains the first
three differing positions and their exact records.

Sorting canonical encodings of the array's complete key/value entries gives the
same SHA-256 in every run:
`959066b8e35940df5b72296f77c44a8d3ba4b8fe297b7f2d433e3369f1c947a8`.
The order-sensitive hashes differ. After omitting precisely that array and
replacing `/run1/`, `/run2/`, or `/run3/` in the one destination path with
`/runX/`, the complete remaining bytes have the same SHA-256:
`18be28d9c96069266916733aa4336e9473c9c2f727c9670cc4acbfceb8b76d18`.
This exact byte comparison includes the serialized declaration sequence, bodies,
source spans, and `has_errors` field; it does not infer equality by ignoring an
unreviewed part of the LLBC. Basis: **execution** and the field-aware checker.

The guarded replay completed three further serial runs in a new scratch root.
Their absolute destination path was nine bytes longer, so their raw output
lengths were 173,520,692 bytes. The same 17,903-entry multiset and
within-replay byte-equality checks passed. The replay comparison is retained in
`support/replay-comparison.json`; this is a repeat of the same target and settings,
not a second workload.

### This Charon output is error-bearing despite process success

Each LLBC ends in `"has_errors":true`. Each stderr has 13 `Could not compute the
value of ... Target ... needed to update item reference ... Deref` warnings, and
the aggregate `The extraction generated 13 warnings` line. The Charon process
then reports a completed Cargo build and exits zero. Thus a zero process status
cannot be treated as a valid Aeneas input for this full library. The 13 warnings
are preserved, with local path prefixes redacted, in `support/run*-stderr.txt`;
their original byte hashes and the empty stdout hashes are in
`support/observations.json`. Basis: **execution**.

### The pinned Aeneas importer discards this field

`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
`src/Main.ml`, lines 556–564, calls `crate_of_json_file` and then replaces the
imported crate with `{ m with short_names = [] }` before logging, pre-passes, and
`Translate.translate_crate` (lines 735–739). Its adjacent comment says this is
to make printing more deterministic. This source path supports the narrow
interpretation that the observed `short_names` permutation cannot affect that
pin's subsequent translation through the CLI importer, provided the LLBC loads.
No generated-source equality was measured for the full zerocopy library. Basis:
**source** plus **derived** application to the measured field difference.

### #3731 I148 alignment

This adds one real, substantially larger library-source workload to the earlier
small Charon/Aeneas repeat probes. It demonstrates why comparing raw LLBC hashes
can report a difference even when all non-cache serialized bytes agree. For the
exact I148 residual, it improves representativeness of the Charon serialization
observation but leaves successful Aeneas/Lean output and product workload
determinism open. The v25 prerequisite for a larger matched *successful* corpus
or an actual Anneal product workload remains.

## Boundaries

Only one crate, library target, preset, feature selection, host target, and
compiler pin were tested. The array comparison treats `short_names` as a
keyed name cache only for this source-backed Aeneas CLI consumer; other LLBC
consumers may use it. The `has_errors: true` input cannot establish successful
translation, semantic correctness, Lean elaboration, or proof validity. Aeneas
and Lean were not run because a low-memory acceptance preflight for a 173.5 MB
error-bearing LLBC was unavailable on this 8 GiB host. No arbitrary flags,
layouts, revisions, concurrency, same-process calls, or Anneal V2 integration
were tested.

The local Charon and Aeneas source revisions identify inspected checkouts; the
executed Charon binary hash identifies the run. This probe did not rebuild that
binary from the source checkout or independently attest release provenance.

The three full LLBC files remain in the conversation's Meta Data scratch area.
The public reference package retains their exact hashes, field-aware comparison,
selected differing records, command and environment, complete redacted stderr,
checker, and guarded replay. It does not mirror 520 MB of generated LLBC.

## Evidence

- Source: `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`,
  `zerocopy/Cargo.toml`, `Cargo.lock`, `build.rs`, and `src/lib.rs`; hashes and
  complete subtree Git object are in `support/observations.json`.
- Tool: `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`,
  Charon binary SHA-256
  `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`.
  The Charon driver, pinned Cargo/rustc, and unexecuted Aeneas binary hashes are
  also retained in `support/observations.json`.
- Aeneas source: `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`,
  `src/Main.ml`, blob `b3f373f8c449eeae0f9a50bb0ce2d2963903eddc`,
  `main` LLBC import and short-name reset at lines 556–564. The related
  [generated-source determinism report](../aeneas-generated-source-determinism-nightly-2026-06-03/REPORT.md)
  independently records the same source behavior.
- Execution: `support/observations.json` records the exact command template,
  environment inputs, result hashes, durations, resource ceilings, and log
  hashes. `support/comparison.json` is the three-run comparison. `support/compare.py`
  implements the narrow field-aware comparison; `support/check.py` checks the
  retained evidence; `support/replay.py` recreates the offline run in fresh
  caller-owned scratch with 180-second, 3.5 GiB process RSS, 15% system memory,
  and 15 GiB disk guards. The replay script itself completed under these guards
  on the observation date.

## Revalidation

From this report directory, run `python3 support/check.py` to validate the
retained observations and redacted logs. If the original Meta Data scratch is
available, add `--work /absolute/path/to/i148-zerocopy-library
--exact-original` to verify all three original LLBC and raw log hashes and rerun
the field comparison. To repeat the experiment, run `python3 support/replay.py
--repo /absolute/path/to/zerocopy --tools /absolute/path/to/.anneal-local-tools
--work /absent/scratch/path`; the script checks the source Git tree and tool
hashes before copying source and starts only offline, locked, serial Cargo/Charon
runs. The work directory must not already exist.
