# Same-path warm Charon LLBC bytes vary only in short-name array order

Observed 2026-09-29 with pinned Charon 0.1.210 and Rust/Cargo nightly 2026-05-31 on macOS arm64. This R42 follow-up to [R37](../anneal-3730-nested-parallelism-budget-2026-09-29/REPORT.md) addresses a narrow part of #3731 I079: why a warm, source-unchanged Charon request rewrote LLBC with a new SHA-256. It uses a copy of R37's tiny root crate, two path dependencies, build script, command flags, and environment controls. It is a component observation, not an Anneal cache-key implementation.

## Reproduction and byte isolation

Five consecutive `charon cargo --preset aeneas --dest-file <same probe.llbc> -- --manifest-path <same Cargo.toml> --lib --offline --locked -j 1` requests used the same copied workspace, target directory, destination pathname, and source-file manifest. `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, `RAYON_NUM_THREADS=1`, pinned `RUSTUP_HOME`/`CARGO_HOME`, and `CHARON_TOOLCHAIN_IS_IN_PATH=1` matched R37. Each request exited 0. Cargo's log compiled the root crate on every call; path dependencies were compiled on the cold first call and skipped on the four warm calls. The first call took 0.752 seconds; warm calls took 0.076–0.078 seconds in this run.

All five outputs were **10,936 bytes**, and each destination mtime and SHA-256 changed. The first 2,645 bytes and all bytes from offset 2,870 to end were identical across all five files. The only varying region was the 225-byte JSON field `translated.short_names`, at zero-based byte offsets **2645–2869**. The four entries were the same keyed pairs in every run; only their array order differed:

| Run | `Fun` ID order in `short_names` | LLBC SHA-256 prefix |
|---|---|---|
| 1 | 0, 1, 2, 3 | `ec4dc523318d` |
| 2 | 3, 2, 1, 0 | `e211fbe97e71` |
| 3 | 0, 2, 1, 3 | `bb30246bfd6f` |
| 4 | 0, 3, 2, 1 | `5fcf6f267387` |
| 5 | 2, 0, 1, 3 | `d9559b90f96e` |

Each adjacent parsed-JSON diff contains only leaves under `$.translated.short_names[*]`. The serialized item names, definitions, bodies, spans, file table, options, and every other field were byte-identical in this fixture. Sorting just this array by its unique `Fun` key yields one common canonical byte stream and SHA-256 `ec4dc523318d6e1ed34b0d82f3650fe68c69998d17bbd65a3552c19d0cbed1ba`. That is a **field-specific comparison experiment**: an array consumer can observe order, and sorting arbitrary LLBC arrays or discarding source provenance would not be justified by this result.

## Plausible emitter mechanism

The available Charon source snapshot at commit `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` is consistent with the measured variation. In `compute_short_names.rs`, the transform collects names in `std::collections::HashMap<String, FoundName>`, iterates that map, and inserts results into `ctx.translated.short_names`. The translated-crate field is a `SeqHashMap` (`IndexMap`) serialized by `SeqHashMapToArray`, whose implementation walks its insertion order to make an array. `support/source-inspection.json` retains exact file hashes, line-numbered excerpts, and the source commit. Randomized `HashMap` iteration feeding an insertion-ordered serialized array explains the observed permutations. We did not rebuild the binary from this source snapshot in this experiment, so the source reading is mechanism evidence consistent with the pinned binary behavior, not a separate binary-provenance attestation.

## Replay and validation

From the checkout, using only existing local pins:

```sh
python3 reports/anneal-3730-charon-warm-noop-byte-diff-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new-scratch-directory
python3 reports/anneal-3730-charon-warm-noop-byte-diff-2026-09-29/support/verify.py
```

The scratch path must not exist, and the script requires at least 15 GiB free. `support/fixture/` is self-contained. `support/results.json` retains exact commands, environment settings, tool/source hashes, Cargo logs, timings, output lengths/mtimes/hashes, byte offsets, parsed leaf changes, and canonical hash. `support/artifacts/` retains the five raw LLBC files and sorted-field canonical copy. `support/diffs/` contains exact textual diffs of the isolated 225-byte field rather than an unreadable whole one-line JSON diff. The verifier checks the retained raw files, unchanged prefix/suffix, field-only parsed changes, source manifest, and canonical agreement. Replay may yield different permutations or occasionally the same permutation twice; the specific five SHA values and order sequence are observations from this run, not required future outcomes.

## I079 coverage and residual

This pin and fixture disprove a byte-identical-output assumption for source-unchanged warm Charon extraction and identify a concrete order-only source of raw LLBC hash churn. A cache or golden-diff harness should distinguish raw artifact identity from a schema-aware structural comparator while keeping the exact original artifact and provenance. This does not establish general semantic equivalence for arbitrary LLBC, complete normalization rules, effects of paths/comments/flags/revisions, annotation association safety, or same-process library behavior. Those broader I079 questions remain open.
