# Charon and Cargo Warm-Target Reuse, Shared-Target Concurrency, Incremental Cache Transitions, and Full-Field LLBC Comparisons

## Summary

Ten component experiments and full-field decoded JSON reanalyses under pinned Charon `0.1.210` and Rust/Cargo `nightly` characterize how warm Cargo target directories, shared writable `CARGO_TARGET_DIR` caches, `CARGO_INCREMENTAL=0` versus `1`, source `A → B → A` edit-revert transitions, and mid-build `SIGTERM` cancellation affect Charon producer execution and emitted LLBC artifacts:

1. **Warm multi-unit test collision versus warm forced-dirty binary rebuild:** Repeating `charon cargo --dest-file <new.llbc> -- --test check` against a warmed `CARGO_TARGET_DIR` re-invoked all three `charon-driver rustc` units (`subject_matrix`, `check`, and `subject_matrix_cli`) and exited `0`, but the driver execution order flipped from `subject_matrix, subject_matrix_cli, check` (cold, leaving `check` at the destination) to `subject_matrix, check, subject_matrix_cli` (warm, overwriting the single destination with `subject_matrix_cli`). Repeating `--bin subject_matrix_cli` on a retained target logged `Dirty subject_matrix ... couldn't read metadata for file ...libsubject_matrix-21be0fdd0836da51.rlib`, recompiled both library and binary, and wrote a valid `subject_matrix_cli` LLBC (`5d1ae9cb…` cold vs `6021a295…` warm).
2. **Concurrent shared-target serialization and cancellation survival:** When two `charon cargo` processes with equal-length source roots (`A` and `B`) and distinct `.llbc` destinations shared one writable `CARGO_TARGET_DIR`, Cargo serialized build-directory access (`Blocking waiting for file lock on build directory`) and both exited `0` with parseable LLBCs across all four `{private, shared} × {CARGO_INCREMENTAL=0, 1}` cells (16 total runs). Sending `SIGTERM` (`-15`) to process group `A` after its `build.rs` entry marker while `B` waited on the build-directory lock left no LLBC at `A`'s destination, allowed `B` to complete with baseline LLBC (`0`), and allowed a subsequent retry of edited `A` on the same shared `CARGO_INCREMENTAL=1` target to recover the edited LLBC (`0`).
3. **Sequential `A → B → A` source edit and revert in a shared target:** Across 12 shared-target extractions (`baseline A, baseline B, edited A, unchanged B, reverted A, unchanged B` under both `CARGO_INCREMENTAL=0` and `1`), every output matched its corresponding independent cold oracle's local function-body projection (`warm_probe::step` hash `0194e911c5ac…` for baseline/reverted vs `5ffbb331be1e…` for edited `wrapping_add(2)`), while incremental file counts grew from `55` to `70` (`2,588` to `2,988 KiB`).
4. **Exhaustive full-field JSON equivalence outside paths and `short_names` order:** Across all four full-field decoded JSON audits—1 cold/warm binary pair (30 differing leaves), 4 shared-target cancellation/retry pairs against cold oracles (14, 12, 17, and 19 differing leaves), 12 edit/revert shared-target pairs against cold oracles (248 total differing leaves), and 24 one-axis pairs across the 16-run target-layout matrix (479 total differing leaves)—100% of decoded JSON leaf differences were confined to `/translated/options/dest_file`, the generated-file local path `/translated/files/1/name/Local`, and array-slot permutations of `/translated/short_names` whose serialized typed-key-to-name maps were identical in every pair.

## Applicability

All execution and offline-comparison claims apply to:

- **Charon `0.1.210`** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, macOS `aarch64-apple-darwin` executable SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`);
- **Rust compiler `1.98.0-nightly` (`nightly`)** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, executable SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`);
- **Cargo `1.98.0-nightly` (`nightly`)** (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, executable SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`).

Only a single version of each subject is examined. All producer runs executed offline (`--offline --locked`, `CARGO_NET_OFFLINE=true`) on macOS `arm64` (8 GiB RAM) with `CARGO_BUILD_JOBS=1` and `RAYON_NUM_THREADS=1` under `--preset aeneas`. In the shared-target experiments over `warm_probe`, source roots `A` and `B` were constructed with equal absolute path lengths so that `warm_probe`'s `build.rs` computation (`SNAPSHOT_VALUE = BUILD_VALUE + len(CARGO_MANIFEST_DIR)`) stayed constant across roots; unequal path lengths remain governed by the stale path-sensitive build-script hazard documented for relocated workspaces.

## Findings

### Warm Selected Binary and Multi-Unit Test Target Controls

Two bounded warm-target producer probes (`support/warm-bin-target/` and `support/warm-multiunit-test-target/`) reused a single private `CARGO_TARGET_DIR` across two sequential invocations over the dependency-free `subject_matrix` fixture (`subject_matrix` library, `subject_matrix_cli` binary, and `check` integration test), supplying a fresh, initially absent `--dest-file` path on each call:

| Subprobe and cell | `charon-driver` crate order in verbose stderr | Exit | Decoded `translated.crate_name` at destination | Raw LLBC bytes / SHA-256 |
| --- | --- | ---: | --- | --- |
| `support/warm-bin-target/` cold baseline (`--bin subject_matrix_cli`) | `subject_matrix`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | 54,276 B / `5d1ae9cb6d26d618985cd092fd0218faf1a3c6e2c188f77eebd8615fccf20580` |
| `support/warm-bin-target/` warm repeat (`--bin subject_matrix_cli`) | `subject_matrix`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | 54,279 B / `6021a295099927891f14c18bfbb0ec2b1e6b851f72b800f1c203443e9d5cbe0d` |
| `support/warm-multiunit-test-target/` cold baseline (`--test check`) | `subject_matrix`, `subject_matrix_cli`, `check` | 0 | `check` | `218a41353a6755bcfc6b1ebb2b8c4f21e2f5a7430e1f18b7c4e2b56bf297a623` |
| `support/warm-multiunit-test-target/` warm repeat (`--test check`) | `subject_matrix`, `check`, `subject_matrix_cli` | 0 | `subject_matrix_cli` | `007fe60b44f660294b1253c76758f77841b0f85fbfb904c3aa28556adb5ae370` |

- **Forced-dirty warm binary rebuild and full-field diff (`support/warm-bin-target/`, `support/warm-bin-full-field/`):** In the second `--bin subject_matrix_cli` call, Cargo logged `Dirty subject_matrix ... couldn't read metadata for file ...libsubject_matrix-21be0fdd0836da51.rlib` and recompiled both units (sampled reclaimable memory minimum `23.012%`, free disk minimum `40,099,659,776` bytes, peak process-group RSS `124,704 KiB`, peak scratch `115,917` bytes). In `support/warm-bin-full-field/comparison.json` (SHA-256 `463abe75a867c3a14dc1d827bd08430b606ee07aaaadf0270fdc89eddeab4360`), an exhaustive recursive JSON comparison of the two LLBCs (running in `0.02585 s`, peak self RSS `22,429,696` bytes, minimum reclaimable memory `24.4379%`) found **30 differing leaves**: `/translated/options/dest_file` (accounting for the 3-byte size difference between `baseline.llbc` and `warm_repeat.llbc`) and 29 positional leaves across 11 reordered slots (indices 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14) of the 15-entry `/translated/short_names/` array. Indexed by serialized typed key, the 15 key/value entries are identical, and both files round-trip byte-for-byte through compact JSON reserialization.
- **Warm multi-unit test destination overwrite (`support/warm-multiunit-test-target/`):** In the warm `--test check` repeat (reclaimable memory minimum `23.333%`, free disk minimum `43,310,911,488` bytes, peak process-group RSS `137,392 KiB`, peak scratch `419,083` bytes), Cargo re-invoked all three `charon-driver` units rather than skipping extraction, but because `subject_matrix_cli` ran after `check` on the warm pass, the single `--dest-file` was overwritten by the binary's LLBC (`translated.crate_name = "subject_matrix_cli"`).

Basis: **execution** in `support/warm-bin-target/results.json`, `support/warm-bin-full-field/comparison.json`, and `support/warm-multiunit-test-target/results.json`.

### Private versus Shared Cargo Target Layout Matrix (`CARGO_INCREMENTAL=0` and `1`)

In `support/incremental-target-layout-matrix/`, four cells crossed `{private (2 targets), shared (1 target)} × {CARGO_INCREMENTAL=0, CARGO_INCREMENTAL=1}` over equal-length `A` and `B` copies of `warm_probe` (with a 1-second sleep in `app/build.rs` to force overlap). Within each cold or warm phase, `A` and `B` ran concurrently into separate `.llbc` files:

| Target layout | `CARGO_INCREMENTAL` | Cold phase elapsed | Warm phase elapsed | Final target allocation after warm | Incremental files after warm | Build-directory lock wait in stderr |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| Private, two targets | 0 | 1.722 s | 0.148 s | 1,260 KiB each (2,520 KiB total) | 0 each | None recorded |
| Private, two targets | 1 | 1.836 s | 0.141 s | 2,692 KiB each (5,384 KiB total) | 59 each (~1.468 MB each; 56 / ~1.389 MB after cold) | None recorded |
| Shared, one target | 0 | 1.595 s | 0.147 s | 1,260 KiB | 0 | Recorded in both phases |
| Shared, one target | 1 | 1.717 s | 0.147 s | 2,852 KiB | 65 (~1.627 MB; 59 / ~1.468 MB after cold) | Recorded in both phases |

All 16 requests exited `0` with `has_errors: false` and identical five-function local declaration-body hash maps (minimum free memory `48%`, minimum free disk `43.40 GiB`). In `support/target-layout-full-field/comparison.json` (SHA-256 `4d4396890b7a05eaad9684ccaf76067cf6f0ba1e74bd8d48caf109dd75dd4c02`), an offline full-field comparison across all **24 matched one-axis pairs** (elapsed `0.20167 s`, peak self RSS `25,968,640` bytes, minimum reclaimable memory `26.2953%`) found 479 aggregate leaf differences:

| Matched comparison axis | Pairs | Total decoded leaf diffs | Per-pair range | Non-`short_names` differing JSON paths |
| --- | ---: | ---: | ---: | --- |
| Warm versus cold (same root, layout, incremental mode) | 8 | 154 | 16–21 | `/translated/options/dest_file` |
| Shared versus private (same incremental mode, phase, root) | 8 | 167 | 14–22 | `/translated/options/dest_file`, `/translated/files/1/name/Local` |
| Incremental-on versus incremental-off (same layout, phase, root) | 8 | 158 | 16–22 | `/translated/options/dest_file`, `/translated/files/1/name/Local` |

Every pair had identical `short_names` typed-key-to-name maps and zero differences in function declarations, embedded source contents, crate name, or error status. Three in-memory synthetic negative controls (mutating crate name, one function body, and `short_names` order) triggered the expected comparator failures.

Basis: **execution** in `support/incremental-target-layout-matrix/results.json` (SHA-256 `040f6e477a358b602af87298fbc8517cd5269e8803d4ede7e70762ae31d58828`) and `support/target-layout-full-field/comparison.json`.

### Shared-Target Cancellation, Companion Completion, and Same-Target Retry (`CARGO_INCREMENTAL=0` and `1`)

Two probes tested process-group `SIGTERM` (`-15`) during active shared-target builds:

1. **Fresh shared target with `CARGO_INCREMENTAL=0` (`support/shared-cargo-target-two-process/`):**
   - In the `complete` phase, two concurrent `charon cargo` processes (`A` and `B`, with a 2-second sleep in `app/build.rs`) overlapped across 43 sampled 50 ms intervals (~3.52 s); `B` logged `Blocking waiting for file lock on build directory`, both exited `0` (24,068-byte LLBCs, SHA-256 `9e8a04820ae19333e5bcb6e26e9007a2f1a6edf8b5ddb43d8914eb6dc37b9986` and `e284623c7768e23486bcfac0d0aa0b8bfebd38c5d7118c5350d28292b47c15c8`), peak sampled tree RSS sums were `155,184 KiB` and `33,664 KiB`, peak scratch was `1,376 KiB`, and final shared target size was `1,260 KiB` (35 regular files).
   - In the `cancel` phase on a second fresh shared target, `A` received `SIGTERM` after writing its build-script entry marker while `B` was live; `A` exited `-15` with no LLBC, while `B` waited on the build-directory lock, exited `0`, and wrote a valid 24,064-byte LLBC (`dd05cfe299cf3f86201001c15e3f55def2c707ebda8c252a8c78f5cd2c`, peak tree RSS sums `181,696 KiB` and `105,648 KiB`, peak scratch `2,652 KiB`). Post-run `ps` checks (`support/shared-cargo-target-two-process/cleanup.json`, SHA-256 `ce73e0fd77286c8b43f7bbffe4d9486645e8cae7b653d719e6a55ba82fca60e9`) confirmed zero remaining members in all four process groups.
2. **Warmed shared target with `CARGO_INCREMENTAL=1`, source edit, cancellation, and retry (`support/incremental-on-shared-target-cancel-recovery/` and `support/full-field-cancel-oracle/`):**
   - After prewarming one shared target with baseline `A` and `B`, `A` edited `step` from `wrapping_add(1)` to `wrapping_add(2)` and added a 3-second `build.rs` sleep plus entry marker (`0.468 s`). `B` launched at `0.470 s`; `A` received `SIGTERM` at `0.662 s` and exited `-15` at `0.663 s` leaving no `cancel-A.llbc`. Companion `B` logged `Blocking waiting for file lock on build directory` and exited `0` at `3.966 s` with baseline bodies. Retrying edited `A` on the same shared target exited `0` (Cargo completion in `0.04 s`) with the edited `step` body (`5ffbb331be1e…` vs baseline `0194e911c5ac…`). Sampled minimum free memory was `43%`, minimum free disk `46.27 GB`, peak process-group RSS sum `204,096 KiB`, and peak private work allocation `9,116 KiB`.

| Step or full-field cold-oracle comparison | Incremental files in target | Target allocation | Full-field decoded leaf diffs vs cold oracle (`support/full-field-cancel-oracle/comparison.json`) |
| --- | ---: | ---: | --- |
| Prewarm A, then B on shared target | 55, then 58 | 2,588, then 2,668 KiB | `prewarm A → baseline B`: 14 leaves (12 `short_names`, `dest_file`, `files/1/name/Local`); `prewarm B → baseline B`: 12 leaves (10 `short_names`, same 2 paths) |
| Cancel edited A (`-15`); companion B completes (`0`) | 109 after B | 3,752 KiB after B | `companion B → baseline B`: 17 leaves (15 `short_names`, same 2 paths) |
| Retry edited A on same shared target (`0`) | 112 | 3,832 KiB | `recovered A → edited A`: 19 leaves (17 `short_names`, same 2 paths) |
| Cold edited-A and baseline-B oracles (separate targets) | 57 and 55 | 2,628 and 2,588 KiB | Negative control (`edited A vs baseline B`): 23 leaves including source text `wrapping_add(2)` vs `wrapping_add(1)` and call literal `2` vs `1` at `/translated/fun_decls/0/body/Structured/body/statements/2/kind/Call/args/1/Const/kind/Literal/Scalar/Unsigned/1` |

Basis: **execution** in `support/shared-cargo-target-two-process/results.json` (`ad8da253…`), `support/incremental-on-shared-target-cancel-recovery/results.json` (`42822b05…`), and `support/full-field-cancel-oracle/comparison.json` (`be26b95d…`, elapsed `0.05482 s`, peak self RSS `22,216,704` bytes, minimum reclaimable memory `22.6244%`).

### Sequential Source Edit and Revert in a Shared Target (`CARGO_INCREMENTAL=0` and `1`)

In `support/source-edit-revert-incremental-cache/`, equal-length roots `A` and `B` sequentially reused one writable `CARGO_TARGET_DIR` through `baseline A → baseline B → edited A (wrapping_add(2), SHA-256 d264e3214d6b…) → unchanged B → reverted A (wrapping_add(1), SHA-256 bbe231375dfe…) → unchanged B` under both `CARGO_INCREMENTAL=0` and `1` (minimum free memory `49%`, minimum free disk `48.87 GB`):

| Incremental mode | Shared-target state | `A` `step` body vs cold oracle | `B` `step` body vs cold oracle | Incremental files after `A`, then `B` | Shared target allocation after `B` | Full-field leaf diffs vs same-state cold oracle (`A / B` in `support/full-field-edit-revert-oracles/`) |
| --- | --- | --- | --- | --- | ---: | --- |
| Off (`0`) | Baseline | Baseline (`0194e911c5ac…`) | Baseline | 0, 0 | 1,256 KiB | 22 / 22 |
| Off (`0`) | Edited `A` | Edited (`5ffbb331be1e…`) | Baseline | 0, 0 | 1,256 KiB | 22 / 17 |
| Off (`0`) | Reverted `A` | Baseline (`0194e911c5ac…`) | Baseline | 0, 0 | 1,256 KiB | 22 / 22 |
| On (`1`) | Baseline | Baseline (`0194e911c5ac…`) | Baseline | 55, 58 | 2,668 KiB | 20 / 18 |
| On (`1`) | Edited `A` | Edited (`5ffbb331be1e…`) | Baseline | 61, 64 | 2,828 KiB | 20 / 22 |
| On (`1`) | Reverted `A` | Baseline (`0194e911c5ac…`) | Baseline | 67, 70 | 2,988 KiB | 22 / 19 |

Across all 12 shared-target outputs in `support/full-field-edit-revert-oracles/comparison.json` (SHA-256 `7fb668a000adbf5bd8d2a8534e40b1c0164aac1e7e9c9d71d797bd17a3977be7`, 248 total leaf differences, elapsed `0.13825 s`, peak self RSS `24,739,840` bytes, minimum reclaimable memory `22.5082%`), every pair differed in `/translated/options/dest_file`, `/translated/files/1/name/Local`, and positional `/translated/short_names/` slots while maintaining identical typed-key maps and declaration bodies. The two cold edited-versus-baseline negative controls differed at 24 (`CARGO_INCREMENTAL=0`) and 20 (`CARGO_INCREMENTAL=1`) leaves, including `/translated/files/0/contents` and the unsigned scalar literal `"2"` versus `"1"`.

Basis: **execution** in `support/source-edit-revert-incremental-cache/results.json` (`e1f8ac94…`) and `support/full-field-edit-revert-oracles/comparison.json`.

## Boundaries

- **Not examined:** Truly cache-fresh warm `--bin` or `--test` invocations where Cargo skips running `charon-driver` for the selected unit (the warm `--bin` repeat was forced dirty by an unreadable `.rlib` metadata file, and the warm `--test` repeat recompiled all three units).
- **Not examined:** Equal-path-length controls in `warm_probe` deliberately avoided changing `len(CARGO_MANIFEST_DIR)`; sharing a `CARGO_TARGET_DIR` across workspaces with different path lengths or different path-sensitive `build.rs` inputs remains unsafe without full build-script input closure.
- **Not examined:** Cancellation at arbitrary `rustc` parsing, MIR borrow-checking, LLBC serialization, or `SIGKILL` (`-9`) points on a shared incremental target, or multi-worker scaling beyond two concurrent processes on a tiny two-crate fixture.
- **Known not to apply:** Raw whole-file LLBC SHA-256 equality does not hold across cold/warm, shared/private, or incremental-on/off runs because `/translated/options/dest_file`, `/translated/files/1/name/Local`, and `/translated/short_names` entry order vary.

## Evidence

- **Warm binary and multi-unit test subprobes:**
  - `support/warm-bin-target/probe.py`, `support/warm-bin-target/check.py`, `support/warm-bin-target/results.json`, `support/warm-bin-target/fixture/`, `support/warm-bin-target/raw/`, and `support/warm-bin-target/artifacts/`.
  - `support/warm-bin-full-field/compare.py` (SHA-256 `8e511e81aa48dde2695348314bf1145eb6496919e2055a8fdfd67682a24f9332`), `support/warm-bin-full-field/check.py`, `support/warm-bin-full-field/comparison.json` (SHA-256 `463abe75a867c3a14dc1d827bd08430b606ee07aaaadf0270fdc89eddeab4360`), `support/warm-bin-full-field/source-results.json` (SHA-256 `ecc7934451a6da4bc94ee7e0e7006f5fdfa162736afa344e32f31d4491b7dac5`), and `support/warm-bin-full-field/artifacts/`.
  - `support/warm-multiunit-test-target/probe.py`, `support/warm-multiunit-test-target/check.py`, `support/warm-multiunit-test-target/results.json`, `support/warm-multiunit-test-target/fixture/`, `support/warm-multiunit-test-target/raw/`, and `support/warm-multiunit-test-target/artifacts/`.
- **Target-layout and shared-target concurrency/cancellation subprobes:**
  - `support/incremental-target-layout-matrix/probe.py` (SHA-256 `d7f5d76da27a817d550d380314feb18974c495c3bc1aac2261e3cdc588de26a0`), `support/incremental-target-layout-matrix/check.py`, `support/incremental-target-layout-matrix/results.json` (SHA-256 `040f6e477a358b602af87298fbc8517cd5269e8803d4ede7e70762ae31d58828`), `support/incremental-target-layout-matrix/fixture-origin/`, and `support/incremental-target-layout-matrix/artifacts/`.
  - `support/target-layout-full-field/compare.py` (SHA-256 `867d5f0f2d568d6f7b1a69057df48c90757ea482ceb34852eba668508cd5eae7`), `support/target-layout-full-field/check.py`, `support/target-layout-full-field/comparison.json` (SHA-256 `4d4396890b7a05eaad9684ccaf76067cf6f0ba1e74bd8d48caf109dd75dd4c02`), `support/target-layout-full-field/source-results.json`, and `support/target-layout-full-field/artifacts/`.
  - `support/shared-cargo-target-two-process/probe-observed.py` (SHA-256 `8ea5be460e0ce3d1ec99f7f6dfa1cf4ffac9c402eddbbcd6e6f69cb82aab0de1`), `support/shared-cargo-target-two-process/probe.py`, `support/shared-cargo-target-two-process/check.py`, `support/shared-cargo-target-two-process/results.json` (SHA-256 `ad8da2539f790ffb728374bb006925f90ee527863a692ab82a85b06868d8e31b`), `support/shared-cargo-target-two-process/cleanup.json` (SHA-256 `ce73e0fd77286c8b43f7bbffe4d9486645e8cae7b653d719e6a55ba82fca60e9`), `support/shared-cargo-target-two-process/fixture-origin/`, and `support/shared-cargo-target-two-process/artifacts/`.
  - `support/incremental-on-shared-target-cancel-recovery/probe.py` (SHA-256 `9e9249c178d5e42dc6d800bde65d4769d2883b127b15a4d3a48adfdf0a41ff6e`), `support/incremental-on-shared-target-cancel-recovery/check.py`, `support/incremental-on-shared-target-cancel-recovery/results.json` (SHA-256 `42822b050fc86ffa0506927e7ba19a9055c2b57c04d6914253b0682070667107`), `support/incremental-on-shared-target-cancel-recovery/fixture-origin/`, and `support/incremental-on-shared-target-cancel-recovery/artifacts/`.
  - `support/full-field-cancel-oracle/compare.py` (SHA-256 `cbe0ac43e1a4d81458c9256a066b8cea224de504a889b5d47f2363895d8f22fc`), `support/full-field-cancel-oracle/check.py`, `support/full-field-cancel-oracle/comparison.json` (SHA-256 `be26b95d7a7e290624598f1916382ab79db89832271a1ad0ae742785db942029`), `support/full-field-cancel-oracle/source-results.json`, and `support/full-field-cancel-oracle/artifacts/`.
- **Sequential edit-revert subprobes:**
  - `support/source-edit-revert-incremental-cache/probe.py` (SHA-256 `014de68845008f2238863e17077ae7f429b17a44634f2620c8f34086404e72ca`), `support/source-edit-revert-incremental-cache/check.py`, `support/source-edit-revert-incremental-cache/results.json` (SHA-256 `e1f8ac94a2bda6f93ca21d11c8fae4c6030bd2f9a9ac5491d2e4b36f981e1d4a`), `support/source-edit-revert-incremental-cache/fixture-origin/`, and `support/source-edit-revert-incremental-cache/artifacts/`.
  - `support/full-field-edit-revert-oracles/compare.py` (SHA-256 `e70c139e1c4b9769b789ca67023bf1a523f89f118f5a68a199ff6565648bd804`), `support/full-field-edit-revert-oracles/check.py`, `support/full-field-edit-revert-oracles/comparison.json` (SHA-256 `7fb668a000adbf5bd8d2a8534e40b1c0164aac1e7e9c9d71d797bd17a3977be7`), `support/full-field-edit-revert-oracles/source-results.json`, and `support/full-field-edit-revert-oracles/artifacts/`.

## Revalidation

All ten subprobes include read-only offline verifiers that check every retained artifact hash, decoded JSON diff, `short_names` typed-key map, negative control, and resource-guard sample without invoking Charon or Cargo:

```sh
python3 -B support/warm-bin-target/check.py
python3 -B support/warm-bin-full-field/check.py
python3 -B support/warm-multiunit-test-target/check.py
python3 -B support/incremental-target-layout-matrix/check.py
python3 -B support/target-layout-full-field/check.py
python3 -B support/shared-cargo-target-two-process/check.py
python3 -B support/incremental-on-shared-target-cancel-recovery/check.py
python3 -B support/full-field-cancel-oracle/check.py
python3 -B support/source-edit-revert-incremental-cache/check.py
python3 -B support/full-field-edit-revert-oracles/check.py
```

To replay the producer experiments on a machine with the pinned toolchain and at least 10 GiB free disk, copy the desired subprobe directory to a disposable path with no pre-existing transient `work/` subdirectory and run its `probe.py` followed by `compare.py` and `check.py`.
