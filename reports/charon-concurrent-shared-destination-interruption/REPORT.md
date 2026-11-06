# Charon Concurrent and Sequential Shared-Destination Races, Live-Reader Tear Observations, and Multi-Format Interruption Controls

## Summary

Four execution experiments under pinned Charon `0.1.210` and Rust/Cargo `nightly` demonstrate that Charon does not serialize, lock, or atomically replace output files when multiple sequential or concurrent invocations target the same `--dest-file` path, nor when `--format all` emits companion `.llbc` and `.llbc.postcard` files:

1. **Sequential silent overwrite across compilation profiles (`support/sequential-shared-destination/`):** Directing two distinct compilation subjects of the same Rust library (`src/lib.rs` SHA-256 `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d`)—a `--release` build (selected U32 literals `11 / 23`) and a debug `--cfg probe_alt` build (selected U32 literals `7 / 29`)—sequentially to the same `--dest-file` succeeded with exit `0` in both orders (`release → cfg` and `cfg → release`), silently replacing the first subject's LLBC with the second subject's model.
2. **Concurrent shared-destination corruption and silent last-writer wins (`support/charon-concurrency-interruption/`, `support/concurrent-shared-destination/`, `support/live-reader-shared-destination/`):**
   - When `alpha` and `beta` crates wrote to **private** destinations, both direct `charon rustc` and `charon cargo` pairs exited `0` with valid, distinct LLBCs. When directed concurrently to **one shared destination**, both producers exited `0` in every round, yet `1/6` direct `charon rustc` rounds, `1/3` `charon cargo` rounds, and `1/5` `--format all` rounds left malformed, unparsable JSON at the shared `.llbc` path (e.g., a complete JSON object followed by trailing residual bytes `ors":false}` from the longer writer).
   - In a simultaneous release-versus-`cfg` pair (`support/concurrent-shared-destination/`), both processes exited `0` after overlapping in 5 of 6 RSS samples and left a parseable release model (`11 / 23`, 5,592 bytes, SHA-256 `14940da1…`).
   - In a staggered (~35–41 ms) release-first pair monitored by a live double-open reader (`support/live-reader-shared-destination/`), both processes exited `0`, yet the settled 5,520-byte shared LLBC (`a3142ee6…`) failed `json.loads` at byte 5,518: a complete 5,518-byte `cfg` JSON document (`7 / 29`) was followed by the 2-byte trailing suffix `e}` from the 2-byte-longer release output. Four in-flight double reads matched that exact 5,520-byte corrupted state (`st_ino` and SHA-256 equal across both opens), proving that neither zero exit codes nor two consecutive identical file reads guarantee a valid LLBC when writers share a destination path.
3. **Stale destination retention on compile failure and non-atomic `--format all` families (`support/charon-concurrency-interruption/`):** Passing malformed Rust (`beta`) with `--dest-file` pointing to an existing valid `alpha.llbc` exited `2` while leaving `alpha.llbc` (`6de2fd7b…`) byte-identical. Using named-pipe (FIFO) barriers, killing a process group (`SIGKILL`, `-9`) during `--format all` after `alpha.llbc` (`6425124e…`) completed but while `.llbc.postcard` was blocked left a complete JSON file with no regular Postcard companion, demonstrating that multi-format emission is not published as an atomic transaction.

## Applicability

All findings apply to the pinned macOS `aarch64-apple-darwin` execution environment:

- **Charon `0.1.210`** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, executable SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`);
- **Rust compiler `1.98.0-nightly` (`nightly`)** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, executable SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`);
- **Cargo `1.98.0-nightly` (`nightly`)** (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, executable SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`).

Only a single version of each tool is examined. All runs executed offline (`--offline --locked`, `CARGO_NET_OFFLINE=true`) on macOS `arm64` (APFS filesystem, 8 GiB RAM) with `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, `RAYON_NUM_THREADS=1`, and private `CARGO_TARGET_DIR` directories per writer so that contention was isolated strictly to the `--dest-file` output path.

## Findings

### Concurrent Shared-Destination Corruption and Multi-Format Interruption (`support/charon-concurrency-interruption/`)

Two two-function crates—`alpha` (`marker_alpha`, source SHA-256 `8159027a71991d6bb4d95a90d461badfcdf4618c7eae11b5d79015ade3bcee6f`) and `beta` (`marker_beta`, source SHA-256 `ce3f4d3f2789922c1f8fe59c9d49688ce32fdb348fc512880610f7bd0ab9866f`)—were extracted in parallel (at most 2 concurrent processes, scratch tree 1.5 MiB):

| Output destination mode | Rounds | Producer exit codes | Parseable JSON LLBCs | Malformed JSON LLBCs | Companion / control observation |
| --- | ---: | --- | ---: | ---: | --- |
| Direct `charon rustc`, private `alpha.llbc` & `beta.llbc` | 1 | `0, 0` | 2 | 0 | Both `has_errors: false` with expected crate and marker names. |
| `charon cargo`, private targets & private `.llbc` paths | 1 | `0, 0` | 2 | 0 | Both `has_errors: false` with expected crate and marker names. |
| Direct `charon rustc`, single shared `.llbc` | 6 | `0, 0` in all 6 rounds | 5 | 1 | Parser rejected mixed shared file in round with overlapping write. |
| `charon cargo`, private targets, single shared `.llbc` | 3 | `0, 0` in all 3 rounds | 2 | 1 | Malformed file ended with trailing `ors":false}` after a complete JSON object. |
| Direct `charon rustc --format all`, single shared output base | 5 | `0, 0` in all 5 rounds | 4 | 1 | Malformed JSON round had a valid `.llbc.postcard` companion decoding to `beta` via `charon pretty-print --format postcard`. |

Additional determinism, stale-retention, and FIFO interruption controls in `support/charon-concurrency-interruption/` established:

- **Path/order/flag and warm controls:** Two fresh `charon rustc` processes translating `alpha.rs` to different destination paths produced distinct raw LLBC SHA-256 digests (`1ee92d10…` vs `7805baf5…`) with identical local function names and body hashes. Reordering declarations changed serialized local order; passing `--cfg selected` added `alpha::flagged`. Three sequential warm-target `charon cargo` runs (cold build, unchanged source after deleting output, and comment-only touch) all logged `Compiling alpha`, exited `0`, and wrote fresh LLBCs.
- **Stale destination after compile error:** Running `charon rustc` on malformed `beta` source with `--dest-file` pointing to an existing valid `alpha` LLBC exited `2` and left the prior `alpha` LLBC byte-identical (`6de2fd7b4e4db63bf445282d197353d1bfcc259993b6349f74ee9bf1c848e4c0`).
- **Named-pipe (FIFO) phase barriers and `SIGKILL` (`-9`):**
  1. Pointing `--dest-file` at a FIFO with no reader held the `charon` process alive after compilation until its process group was killed (`-9`), leaving no regular file.
  2. Reading from a FIFO destination for a 320-function crate captured an 8,185-byte non-JSON prefix (`f57a1140086a74c5f2c3bcf539424a37c103846fdcecaaa03a89763b31eab063`) while the writer was live; killing the process group (`-9`) and retrying to a regular file exited `0` with a valid `large` LLBC.
  3. Under `--format all` with a regular `.llbc` path and a FIFO at `.llbc.postcard`, Charon finished writing a complete, parseable `alpha.llbc` (`6425124eb0020595b8630d5363e7da915c7214dc9f37e24ef83327cb0889cbca`) and blocked opening the Postcard FIFO; killing the process group (`-9`) left the split artifact family incomplete until the FIFO was removed and a retry exited `0` with both JSON and Postcard files valid.

Basis: **execution** in `support/charon-concurrency-interruption/results.json` (SHA-256 `14b79f1b2456174600ac83707527030634f47953acf6719651dd7b3325dfd9b9`) and `support/charon-concurrency-interruption/summary.json`.

### Sequential Profile/Cfg Overwrite at a Shared Destination (`support/sequential-shared-destination/`)

Using a dependency-free library (`unit_key_probe`, `src/lib.rs` SHA-256 `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d`) whose `profile_value` and `config_value` functions branch on `#[cfg(debug_assertions)]` and `#[cfg(probe_alt)]`, six sequential `charon cargo --preset aeneas --lib --offline --locked -v -j 1` commands compared separate control destinations against shared destinations in both serial orders (reclaimable memory `36.0027%–38.2198%`, free disk `18,989,367,296–18,989,817,856` bytes, peak process-group RSS `123,216 KiB`, peak scratch `184 KiB`, total time `1.8684 s`):

| Cell | First snapshot (`profile_value / config_value` U32) | Second snapshot (`profile_value / config_value` U32) | Snapshot SHA-256 prefixes (first → second) |
| --- | --- | --- | --- |
| Separate release (`-C opt-level=3`) and cfg (`--cfg probe_alt`) controls | release `11 / 23` | cfg `7 / 29` | `89a6ce7259ea` / `3460774c7dba` |
| Shared destination: `release → cfg` | release `11 / 23` | cfg `7 / 29` | `f64506320b0c` → `06fc00c73422` |
| Shared destination: `cfg → release` | cfg `7 / 29` | release `11 / 23` | `b42b4d6982a4` → `cf4fd779cde4` |

All six commands exited `0` with `has_errors: false`; in both shared-path cells, the second invocation silently overwrote the first invocation's LLBC model without warning or conflict detection.

Basis: **execution** in `support/sequential-shared-destination/results.json`.

### Concurrent and Staggered Live-Reader Shared-Destination Races (`support/concurrent-shared-destination/`, `support/live-reader-shared-destination/`)

Using the same `unit_key_probe` fixture (`990beab5…`) and pinned separate controls (`89a6ce7259ea…` for release `11 / 23` and `3460774c7dba…` for cfg `7 / 29`), two probes launched concurrent release and cfg writers with private `CARGO_TARGET_DIR` paths but a single shared, initially absent `--dest-file`:

| Subprobe and launch schedule | Writer exit codes | Process-group overlap evidence | In-flight reader observations | Final settled shared LLBC outcome |
| --- | --- | --- | --- | --- |
| `support/concurrent-shared-destination/`: simultaneous launch (release PID `97577`, cfg PID `97578`, elapsed `0.2843 s`) | `0, 0` | 5/6 RSS samples had both groups live (e.g., `33,264 KiB` & `33,312 KiB` at `0.2262 s`; peak sum `66,576 KiB`, min reclaimable `34.2907%`) | Not polled in-flight (post-settlement snapshot only) | 5,592 bytes, SHA-256 `14940da1e9aa6b79b8c03abd3981bb85a6cee4b99a6fac97093a51c3d163fe49`; valid JSON matching **release** (`11 / 23`). |
| `support/live-reader-shared-destination/`: staggered ~35–41 ms, `release` then `cfg` | `0, 0` | 16/16 RSS samples had both groups live | 370 absent/disappeared; 4 double reads of identical 5,520-byte state (`a3142ee6…`) | 5,520 bytes, SHA-256 `a3142ee67648b21c8b1703c3ee135bdff03d97116ff1413806332c239473b099`; **malformed JSON** (complete 5,518-byte `cfg` JSON `7 / 29` + 2-byte trailing suffix `e}` at byte 5,518). |
| `support/live-reader-shared-destination/`: staggered ~35–41 ms, `cfg` then `release` | `0, 0` | 5/7 RSS samples had both groups live (peak RSS across both pairs `254,656 KiB`, min reclaimable `30.3524%`) | 123 absent/disappeared; 42 double reads across two valid states: 5,514-byte `cfg` (`4183b22754037b1ccc355d7f498ed09e3aed036740ada3140928f5ef91f48932`, `7 / 29`) then 5,516-byte `release` (`11 / 23`) | 5,516 bytes, SHA-256 `15757df7f92055ccb8b41b7c7bcc806dd83de8b566f4719ec15f13c4b01d062a`; valid JSON matching **release** (`11 / 23`). |

The `release, then cfg` cell in `support/live-reader-shared-destination/` is a concrete mechanism witness for non-truncated concurrent overwrite corruption: when the first writer (`release`, ~5,520 bytes) writes a slightly longer file than the second writer (`cfg`, 5,518 bytes) without coordination or atomic temp-file-and-rename publication, the shorter overwrite leaves the tail bytes (`e}`) of the longer file intact after byte 5,518, causing strict JSON deserialization to fail with extra trailing data even though both Charon processes exited `0` and consecutive reader opens observed stable length and SHA-256 values.

Basis: **execution** in `support/concurrent-shared-destination/results.json` and `support/live-reader-shared-destination/results.json`.

## Boundaries

- **Not examined:** Same-process `charon_lib` worker reuse, OS crash durability (`fsync`/power loss on regular files), cross-platform filesystems outside macOS APFS, or downstream Aeneas/Lean behavior on corrupted LLBCs.
- **Unknown:** Exact kernel `write()` syscall interleaving timestamps inside `charon-driver` (observations record user-space polling snapshots and final settled bytes, not kernel tracepoints).
- **Known not to apply:** Process exit status `0`, file existence, or two consecutive identical file reads at a shared `--dest-file` path do not guarantee that the file is parseable JSON or that it corresponds to the caller's compilation subject. Every concurrent or sequential Charon invocation must write to an invocation-private staging path and verify exit status, schema version, and compilation-unit identity before atomic publication.

## Evidence

- **Concurrent `alpha`/`beta` collision and FIFO interruption subprobe:**
  - `support/charon-concurrency-interruption/probe.py` (SHA-256 `bf8867ed0d0da1719c39fb963c3f15896901cae7af73c544145cc568b8d0565f`), `support/charon-concurrency-interruption/analyze.py`, `support/charon-concurrency-interruption/results.json` (SHA-256 `14b79f1b2456174600ac83707527030634f47953acf6719651dd7b3325dfd9b9`), `support/charon-concurrency-interruption/summary.json`, and 34 raw artifacts in `support/charon-concurrency-interruption/artifacts/`.
- **Sequential shared-destination subprobe:**
  - `support/sequential-shared-destination/acquisition-probe.py.txt`, `support/sequential-shared-destination/probe.py`, `support/sequential-shared-destination/check.py`, `support/sequential-shared-destination/results.json`, `support/sequential-shared-destination/fixture/`, `support/sequential-shared-destination/raw/`, and `support/sequential-shared-destination/artifacts/`.
- **Concurrent shared-destination subprobe:**
  - `support/concurrent-shared-destination/probe.py`, `support/concurrent-shared-destination/check.py`, `support/concurrent-shared-destination/results.json`, `support/concurrent-shared-destination/fixture/`, `support/concurrent-shared-destination/controls/`, `support/concurrent-shared-destination/raw/`, and `support/concurrent-shared-destination/artifacts/shared-final.llbc` (SHA-256 `14940da1e9aa6b79b8c03abd3981bb85a6cee4b99a6fac97093a51c3d163fe49`).
- **Live-reader staggered shared-destination subprobe:**
  - `support/live-reader-shared-destination/probe.py`, `support/live-reader-shared-destination/check.py`, `support/live-reader-shared-destination/results.json`, `support/live-reader-shared-destination/fixture/`, `support/live-reader-shared-destination/controls/`, `support/live-reader-shared-destination/raw/`, `support/live-reader-shared-destination/artifacts/`, and `support/live-reader-shared-destination/work/`.

## Revalidation

To validate all retained artifacts, hashes, overlap samples, and malformed/valid JSON classifications offline without invoking Charon or Cargo, run:

```sh
python3 support/charon-concurrency-interruption/analyze.py
python3 -B support/sequential-shared-destination/check.py
python3 -B support/concurrent-shared-destination/check.py
python3 -B support/live-reader-shared-destination/check.py
```

To re-execute the probes on a host with the pinned Charon and Rust nightly binaries and at least 10 GiB free disk, run `support/charon-concurrency-interruption/probe.py --work <new-absent-path>` or run `probe.py` in a clean copy of any of the other three subprobes. Because concurrent writer scheduling is nondeterministic, new runs may produce different winner or corruption frequencies; evaluate whether shared destinations remain vulnerable to silent subject overwrite or trailing-byte corruption.
