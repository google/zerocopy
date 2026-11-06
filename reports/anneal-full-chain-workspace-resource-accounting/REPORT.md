# End-to-End Rust-to-Lean Pipeline Concurrency, Per-Worker Disk Accounting, and Scratch-Pool Scaling

## Summary

Running concurrent Rust-to-Lean verification pipelines (`cargo` / Charon $\rightarrow$ Aeneas $\rightarrow$ Lake $\rightarrow$ `lean --server` / batch `lean`) on an 8 GiB Apple Silicon (APFS) host requires bounding both memory oversubscription across nested tool invocations and per-worker disk amplification across generated artifacts. Across nine empirical measurement packages using pinned Charon `0.1.210` (`0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`), Aeneas `nightly-2026.06.03` (`ac9f1bc5262a5e4ff1e24ca78617121382202727`), Rust/Cargo `nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` / `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`), and Lean/Lake `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`):

1. **Combined Rust-to-Lean pipeline concurrency (`support/combined-pipeline-concurrency/`, `support/full-lake-server-chain/`):** Two complete private-root `Rust -> Charon -> Aeneas -> batch Lean` workflows executed concurrently in `25.946 s` (vs. `44.276 s` serially in low-overhead mode) with a sampled process-group RSS peak of `3,599,968 KiB` (`663.5 MiB` summed macOS `phys_footprint` in instrumented mode); serializing only the Lean compilation slot across the two overlapping workflows reduced sampled peak RSS to `1,999,216 KiB` (`331.9 MiB` `phys_footprint`) with an identical `25.868 s` wall time. Extending a single worker chain through `lake build -v` (`1,686` graph jobs with cached Aeneas/Mathlib packages), `lake serve` live goal query (`⊢ pipeline_workload.inc 0#u32 = Aeneas.Std.Result.ok 1#u32`), and fresh `lake env lean --json` batch checking completed in `54.754 s` with `2,590,336 KiB` sampled peak RSS across `5` processes; a conservative `4,500,000 KiB` admission gate rejected the two-worker full-Lake-server cell before execution because projected doubled RSS (`5,180,672 KiB`) exceeded the `3,000,000 KiB` two-worker admission ceiling.
2. **Full-chain retained and transient disk bills (`support/retained-full-chain-byte-timing-inventory/`, `support/full-chain-transient-workspace-accounting/`):** A retained single-worker full-chain directory (`work/one/u0`, excluding the shared `.lake/packages` symlink target) contains `54` regular files and `1` symlink totaling `4,524,103` logical bytes and `4,698,112` allocated `st_blocks * 512` bytes, dominated by `.lake` local build artifacts (`34` files, `4,471,665` logical bytes, `4,583,424` block bytes). Copying the `3` Aeneas-generated `.lean` modules across the generator output, direct Lean consumer, and Lake project duplicated `3,364` logical bytes (`1,682 B * 2`). Boundary-and-interval sampling (`24` stage boundaries + `331` `200 ms` polls) during a fresh full-chain replay observed a peak regular-file allocation of `4,825,088` bytes before Cargo target cleanup removed `12` transient target files (`5,838` logical bytes, `28,672` block bytes), settling at `55` inodes (`4,520,749` regular-file logical bytes, `4,681,728` block bytes).
3. **Per-worker copied-byte vs. symlink/clone sharing (`support/per-worker-copied-byte-inventory/`, `support/resource-economics/`):** In a 5-file (`6,189` payload bytes, `24,576` block bytes) compiled Lean dependency fixture, byte-copying dependencies into each worker charged `6,189` extra dependency payload bytes per worker (`30,187` total bytes across producer + 2 cold workers), whereas symlinking each worker's `deps` directory to the shared immutable producer charged `0` dependency payload bytes (`17,809` total bytes across producer + 2 warm workers, consisting strictly of `5,810` private proof/config/output bytes per worker). Hardlinking shared inodes caused naive per-path `st_blocks` summation to double-count `24,576` block bytes (`77,824 B` path sum vs. `53,248 B` distinct-inode charge) while coupling permissions and in-place mutations.
4. **Nested outer $\times$ inner parallelism budgets (`support/nested-parallelism-budget/`):** Sweeping outer unit concurrency (`1, 2, 4`) against inner thread/job settings (`1, 2`) showed that configuring `CARGO_BUILD_JOBS=1`, `RAYON_NUM_THREADS=1`, and `cargo -j 1` still spawned up to `12` concurrent processes (`charon`, `cargo`, `charon-driver`, `rustc`, linkers, and build scripts) and `6-8` OS threads per Cargo process at `4` outer units (`202 MiB` sampled RSS). Similarly, setting `LEAN_NUM_THREADS=1` on `4` concurrent `lean --server` units spawned `8` processes (`4` watchdogs + `4` file workers) with `5` OS threads per watchdog and `6-12` OS threads per worker (`1,735 MiB` summed RSS vs. `480 MiB` summed `phys_footprint`). Warm no-op `charon cargo` reruns completed in `109-189 ms` but rewrote `.llbc` output files with new mtimes and SHA-256 digests on every invocation.
5. **Prewarmed `1/2/4/8` scratch-pool scaling and `16`-generation retention economics (`support/scratch-pool-scaling/`, `support/retention-economics-v4-30-0-rc2/`):** Scaling concurrent `lean --server` scratch workers across `1, 2, 4, 8` open proofs fit within `1,288 MiB` (cold local-build) and `1,337 MiB` (warm symlinked-dependency) group `footprint` at `8` workers, whereas summed RSS reached `3,644 MiB` and `3,887 MiB` due to shared-page double-counting. Live disk payload scaled as `6,189 + 6,470 * W` bytes in cold mode vs. `6,189 + 281 * W` bytes in warm symlink mode (where `148 B` of the `281 B` per-worker private state is a `lake-manifest.json` created by `lean --server`). Across `16` sequential Lake generations (`support/retention-economics-v4-30-0-rc2/`), retaining `16` compiled `.lake` trees consumed `3,589,946` logical bytes (`5,056 KiB` blocks across `448` files) and halved historical generation preparation latency (`0.407 s` `--no-build` vs. `0.830 s` source-only rebuild), compared to `12,101 B` (`512 KiB`) for generated source/control files or `215 B` (`64 KiB`) for source-only records.

## Applicability

All nine experiments executed on macOS `26.6.2` (`Darwin 25.6.0` arm64, `8 GiB` physical RAM, APFS `/System/Volumes/Data` volume) using the pinned local toolchain bundle:
- **Lean 4 and Lake (`leanprover/lean4`):** revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`), `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.
- **Charon (`AeneasVerif/charon`):** revision `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1` (`0.1.210`), binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`.
- **Aeneas (`AeneasVerif/aeneas`):** revision `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`), binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`.
- **Rust and Cargo (`rust-lang/rust`, `rust-lang/cargo`):** `nightly` (`rustc` revision `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`; `cargo` revision `fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`).

All Cargo and Lake runs operated strictly offline (`--offline --locked`, `LAKE_NO_NET=1`, `LAKE_ARTIFACT_CACHE=false`) against pre-populated local caches.

## Findings

### 1. End-to-End Rust $\rightarrow$ Charon $\rightarrow$ Aeneas $\rightarrow$ Lake $\rightarrow$ Lean Concurrency and Admission (`support/combined-pipeline-concurrency/`, `support/full-lake-server-chain/`)

In [`support/combined-pipeline-concurrency/probe.py`](support/combined-pipeline-concurrency/probe.py), each worker processed a 3-function Rust crate (`inc`, `twice`, `choose` using `u32::wrapping_add`) through `charon cargo`, `aeneas -backend lean -sequential`, three direct `lean` module compilations (`Types.lean`, `Funs.lean`, `Current.lean` against prebuilt `Aeneas.olean`), and a batch `Proof.lean` check discharging `obl_inc`, `obl_twice`, and `obl_choose` (`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`).

| Pipeline Schedule (`support/combined-pipeline-concurrency/`) | Low-Overhead Group Wall Time | Low-Overhead Sampled Peak RSS | Instrumented Group Wall Time | Instrumented Peak RSS | Instrumented Summed `phys_footprint` | Max Sampled Processes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 workflows serial | `44.276 s` | `1,999,008 KiB` | `19.770 s` | `2,061,632 KiB` | `330.7 MiB` | `3` |
| 2 workflows unconstrained parallel | `25.946 s` | `3,599,968 KiB` | `33.672 s` | `3,729,616 KiB` | `663.5 MiB` | `6` |
| 2 workflows parallel, 1-slot Lean semaphore | `25.868 s` | `1,999,216 KiB` | `54.797 s` | `1,900,032 KiB` | `331.9 MiB` | `6` |
| 4 workflows parallel | Skipped (admission guard) | — | Skipped (admission guard) | — | — | — |

Gating only the Lean compilation stage with a 1-slot semaphore while allowing Charon and Aeneas to overlap cut sampled peak RSS from `3,599,968 KiB` (`663.5 MiB` `phys_footprint`) to `1,999,216 KiB` (`331.9 MiB` `phys_footprint`), preventing a `>4,000,000 KiB` two-worker simultaneous-Lean RSS spike observed in an unguarded preliminary trial. Across all six worker units, generated `.lean` sources and compiled `Current/Funs.olean` artifacts were byte-identical, whereas raw `.llbc` SHA-256 digests differed across private worker paths.

In [`support/full-lake-server-chain/probe.py`](support/full-lake-server-chain/probe.py), one worker extended the direct chain (`17.068 s`) with a private Lake project build (`lake build -v` over `1,686` graph jobs in `12.045 s`), a `lake --keep-toolchain --no-cache serve` LSP session returning `⊢ pipeline_workload.inc 0#u32 = Aeneas.Std.Result.ok 1#u32`, and a fresh `lake env lean --json Proof.lean` batch verification (`7.256 s`). The complete one-worker cell took `54.754 s` (`18.385 s` outside the three stage timers for setup, copying, server handshake, and process polling) and peaked at `2,590,336 KiB` sampled group RSS across `5` processes (`32%` minimum system free memory). The two-worker full-Lake-server cell was rejected prior to launch because post-run free memory (`40%`) was below the `45%` two-worker floor and projected two-worker RSS (`5,180,672 KiB`) exceeded the `3,000,000 KiB` admission cap.

### 2. Full-Chain Retained and Transient Workspace Disk Accounting (`support/retained-full-chain-byte-timing-inventory/`, `support/full-chain-transient-workspace-accounting/`)

Traversing the retained one-worker directory from the full-chain run ([`support/retained-full-chain-byte-timing-inventory/inventory.py`](support/retained-full-chain-byte-timing-inventory/inventory.py)) and re-running the full chain with `24` stage-boundary snapshots plus `331` `200 ms` periodic polls ([`support/full-chain-transient-workspace-accounting/probe.py`](support/full-chain-transient-workspace-accounting/probe.py)) decompose per-worker disk usage across pipeline stages:

| Pipeline Stage / Artifact Family | Retained Final Files (Reg / Symlink) | Retained Logical Bytes | Retained `st_blocks * 512` | Transient Replay Cumulative Inodes | Transient Replay Logical Bytes | Transient Replay Allocated Bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Rust crate + Cargo target (`after Cargo/Charon`) | `3 / 0` (post-cleanup) | `418 B` | `12,288 B` | `16` (includes `12` target files + `.llbc`) | `22,250 B` | `57,344 B` |
| Charon `.llbc` output | `1 / 0` | `16,087 B` | `16,384 B` | (included above) | (included above) | (included above) |
| Aeneas generated `.lean` (`after Aeneas`) | `3 / 0` | `1,682 B` | `12,288 B` | `19` | `23,932 B` | `69,632 B` |
| Direct Lean consumer (`after direct Lean proof`) | `7 / 0` | `28,422 B` | `49,152 B` | `26` | `52,354 B` | `118,784 B` |
| Lake project config + symlink (`after Lake setup`) | `6 / 0` (config/source) | `5,829 B` | `24,576 B` | `33` | `58,183 B` | `143,360 B` |
| Lake `.lake/build` + symlink (`after Lake build`) | `34 / 1` | `4,471,665 B` | `4,583,424 B` | `67` | `4,526,587 B` | `4,710,400 B` |
| Post-Cargo-target cleanup (`final worker state`) | **`54 / 1`** | **`4,524,103 B`** (incl. `99 B` link) | **`4,698,112 B`** | **`55`** | **`4,520,749 B`** (reg. files) | **`4,681,728 B`** |

Key accounting observations:
- **Peak transient allocation:** Including probe-side Python bytecode (`20,480 B`) and 6 compressed stage logs (`94,208 B`), the disposable run directory peaked at `4,825,088` allocated bytes before Cargo target removal deleted `12` files (`5,838` logical bytes, `28,672` allocated bytes).
- **Duplicate generated source files:** The three Aeneas outputs (`20 B`, `542 B`, and `1,120 B`, totaling `1,682 B`) were copied into three locations (generator output, direct Lean consumer, and Lake project), adding `3,364` redundant logical bytes per worker.
- **Path-length sensitivity of Lake metadata:** Between the two runs, identical semantic builds differed by `3,255` logical bytes (`16,384` block bytes) solely because path-bearing strings inside `current.llbc` (`93 B`), three Lake setup JSON files (`558 B`), and four `.trace` files (`2,604 B`, crossing a `4 KiB` block boundary on four files) embedded different scratch-root directory path lengths.
- **External cache invariance:** Before/after `du -sk` totals and root mtimes/ctimes on Cargo home, Rustup home, the Aeneas backend, and the Lean toolchain showed zero net change at `1 KiB` resolution when `TMPDIR`, `TMP`, `TEMP`, and `XDG_CACHE_HOME` were redirected into the worker scratch tree.

### 3. Per-Worker Copied Bytes vs. Symlinks, Hardlinks, and APFS Clones (`support/per-worker-copied-byte-inventory/`, `support/resource-economics/`)

[`support/per-worker-copied-byte-inventory/probe.py`](support/per-worker-copied-byte-inventory/probe.py) compared six sharing topologies for a 5-file compiled dependency set (`Dep.lean` `24 B`, `lean-toolchain` `29 B`, `Dep.c` `1,295 B`, `Dep.ilean` `289 B`, `Dep.olean` `4,552 B`; total `6,189` payload bytes and `24,576` `st_blocks` bytes) consumed by 1 or 2 workers (each producing `7` private files: `Proof.lean` `59 B`, `3` config/manifest files `122 B`, and `Proof.olean`/`.ilean`/`.c` `5,629 B`; total `5,810` payload bytes and `28,672` `st_blocks` bytes, with identical `Proof.olean` SHA-256 `0167443fca001f19617fd0734b02d3f965448348e5a70c02fadc1cf2829d8305`):

| Sharing Case | Workers | Regular Files | All Distinct Inodes | Regular Payload Bytes | Path-Summed `st_blocks` | Distinct-Inode `st_blocks` | Per-Worker Copied Dependency Payload |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `cold-1` (byte copy) | `1` | `17` | `22` | `18,188 B` | `77,824 B` | `77,824 B` | `6,189 B` |
| `cold-2` (byte copy) | `2` | `29` | `37` | `30,187 B` | `131,072 B` | `131,072 B` | `12,378 B` (`6,189 B * 2`) |
| `warm-1` (directory symlink) | `1` | `12` | `17` | `11,999 B` | `53,248 B` | `53,248 B` | `0 B` |
| `warm-2` (directory symlink) | `2` | `19` | `27` | `17,809 B` | `81,920 B` | `81,920 B` | `0 B` |
| `hardlink-1` (file hardlinks) | `1` | `17` | `17` | `18,188 B` | `77,824 B` | `53,248 B` | `6,189 B` (apparent path sum; `0 B` new inodes) |
| `clone-1` (`/bin/cp -c`) | `1` | `17` | `22` | `18,188 B` | `77,824 B` | `77,824 B` | `6,189 B` (apparent `st_blocks`; distinct inodes) |

In [`support/resource-economics/probe.py`](support/resource-economics/probe.py), two independent Lake consumers (`selected := 7` and `selected := 9`) each occupied `15` regular files (`7` directories, `109,440 B` / `109,312 B` logical payload, `159,744 B` `st_blocks`). Building both cold in parallel took `808.1 ms` (`4` processes, `2,102,542,336 B` sampled summed RSS) vs. `1,571.6 ms` combined serial (`956.2 ms` + `615.4 ms`); warm no-change parallel builds took `537.3 ms` (`2` processes, `1,303,625,728 B` summed RSS). Across four alternating edit rounds in two `lean --server` watchdogs (`4` processes total), summed `ps` RSS grew from `1,044,250,624 B` (`369,165,376 B` summed `phys_footprint`) to `1,385,152,512 B` (`695,633,472 B` `phys_footprint` after close/reopen) before dropping to `0 B` on shutdown.

### 4. Nested Parallelism Budgets and Process/Thread Oversubscription (`support/nested-parallelism-budget/`)

[`support/nested-parallelism-budget/probe.py`](support/nested-parallelism-budget/probe.py) swept `outer in {1, 2, 4}` $\times$ `inner in {1, 2}` for both `charon cargo --preset aeneas` (on a root crate with two path dependencies and a `150 ms` build script) and direct `lean --server` units:

| Outer $\times$ Inner | Cargo Cold (`ms`) | Cargo Warm No-Op (`ms`) | Cargo Warm Edit (`ms`) | Cargo Cold Max Procs / RSS (`MiB`) | Lean Cold / Warm Wait Max (`ms`) | Lean Stable Procs | Lean Summed RSS / `phys_footprint` (`MiB`) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `1 x 1` | `1,593` | `109` | `457` | `5 / 174` | `245 / 211` | `2` | `429 / 111` |
| `1 x 2` | `670` | `110` | `447` | `3 / 37` | `238 / 212` | `2` | `438 / 116` |
| `2 x 1` | `839` | `111` | `567` | `6 / 73` | `240 / 213` | `4` | `868 / 233` |
| `2 x 2` | `803` | `113` | `574` | `6 / 74` | `240 / 209` | `4` | `869 / 234` |
| `4 x 1` | `1,241` | `189` | `832` | `12 / 202` | `370 / 214` | `8` | `1,735 / 480` |
| `4 x 2` | `1,218` | `114` | `801` | `12 / 143` | `355 / 214` | `8` | `1,735 / 490` |

- **Inner thread/job flags do not cap total OS processes or threads:** Even at `inner = 1` (`CARGO_BUILD_JOBS=1`, `RAYON_NUM_THREADS=1`, `-j 1`, `LEAN_NUM_THREADS=1`), `4` outer Cargo units spawned `12` concurrent processes (`6-8` OS threads per Cargo process), and `4` outer Lean units spawned `8` processes (`5` OS threads per server watchdog and `6-12` OS threads per file worker).
- **Warm no-op Charon rewrites `.llbc` artifacts:** Every warm no-op `charon cargo` invocation exited `0` in `109-189 ms` but rewrote its `.llbc` file with a new mtime and a changed SHA-256 digest, demonstrating that `charon cargo` without an external content-hash gate triggers downstream timestamp/digest invalidation even when Rust sources are unchanged.

### 5. Prewarmed `1/2/4/8` Scratch-Pool Scaling and `16`-Generation Retention Tiers (`support/scratch-pool-scaling/`, `support/retention-economics-v4-30-0-rc2/`)

[`support/scratch-pool-scaling/probe.py`](support/scratch-pool-scaling/probe.py) scaled concurrent `lean --server` scratch workers (`1, 2, 4, 8`) opening `Proof.lean` (`exact ?_` $\rightarrow$ `⊢ depValue = 7`, then `didChange` to `rfl` $\rightarrow$ `no goals`):

| Pool Cell | Worker Prepare Sum (`s`) | Launch / Open-Query / Edit-Query (`s`) | Group `footprint` Open $\rightarrow$ Edited (`MiB`) | Edited Summed RSS (`MiB`) | Live Payload / Block Charge (`B`) | Live Files / Inodes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `cold-1` / `warm-1` | `0.162` / `0.000` | `0.030/0.313/0.212` / `0.028/0.301/0.212` | `123 -> 154` / `122 -> 153` | `477` / `476` | `12,659 / 65,536` vs. `6,470 / 40,960` | `14/17` vs. `9/12` |
| `cold-2` / `warm-2` | `0.328` / `0.001` | `0.056/0.332/0.207` / `0.055/0.349/0.212` | `253 -> 315` / `259 -> 321` | `958` / `964` | `19,129 / 106,496` vs. `6,751 / 57,344` | `23/28` vs. `13/18` |
| `cold-4` / `warm-4` | `0.659` / `0.000` | `0.112/0.512/0.216` / `0.112/0.479/0.220` | `532 -> 655` / `519 -> 646` | `1,938` / `1,929` | `32,069 / 188,416` vs. `7,313 / 90,112` | `41/50` vs. `21/30` |
| `cold-8` / `warm-8` | `1.319` / `0.000` | `0.276/0.895/0.262` / `0.284/0.968/0.225` | `1,081 -> 1,288` / `1,135 -> 1,337` | `3,644` / `3,887` | `57,949 / 352,256` vs. `8,437 / 155,648` | `77/94` vs. `37/54` |

Separately, [`support/retention-economics-v4-30-0-rc2/probe.py`](support/retention-economics-v4-30-0-rc2/probe.py) built `16` distinct Lake generations (`Dep.lean` + `Generated.lean`) and compared three retention tiers across `1, 2, 4, 8, 16` retained generations:

| Retained Generations | Source-Only (`source.json` only) | Generated (`.lean` + `lakefile` + manifest, no `.lake`) | Compiled (Full `.lake` build tree) |
| ---: | ---: | ---: | ---: |
| `1` | `14 B` / `4 KiB` / `1` file | `758 B` / `32 KiB` / `8` files | `224,337 B` / `316 KiB` / `28` files |
| `2` | `28 B` / `8 KiB` / `2` files | `1,516 B` / `64 KiB` / `16` files | `448,674 B` / `632 KiB` / `56` files |
| `4` | `56 B` / `16 KiB` / `4` files | `3,032 B` / `128 KiB` / `32` files | `897,348 B` / `1,264 KiB` / `112` files |
| `8` | `111 B` / `32 KiB` / `8` files | `6,061 B` / `256 KiB` / `64` files | `1,794,674 B` / `2,528 KiB` / `224` files |
| `16` | `215 B` / `64 KiB` / `16` files | `12,101 B` / `512 KiB` / `128` files | `3,589,946 B` / `5,056 KiB` / `448` files |

Reconstructing historical generation `1` (`depValue = 1`, OLean SHA-256 `ecdb4514...`) or current generation `16` (`depValue = 16`, OLean SHA-256 `be00ba30...`) took `0.791-0.830 s` prepare + `0.473-0.487 s` query from the Source-Only and Generated tiers, versus `0.404-0.407 s` `--no-build` prepare + `0.470-0.482 s` query from the Compiled tier. An already-running Lean reader that had imported generation `1` before its directory was deleted still evaluated `depValue = 1` (`exit 0`, `1,181,152 KiB` RSS), whereas a fresh process launched after deletion failed with `unknown module prefix 'Dep'` (`exit 1`).

## Boundaries

- **Sampled memory vs. instantaneous physical peaks:** Process-group RSS (`ps`) and sequential per-PID macOS `footprint` (`phys_footprint`) snapshots are sampled at `40-200 ms` intervals or stage boundaries. Summed RSS double-counts shared read-only mappings (nearly `3x` higher than `phys_footprint` in 8-worker server pools), while sequential `footprint` calls add monitoring overhead and can miss sub-interval compiler spikes.
- **Tiny synthetic crates vs. production Mathlib/Anneal scale:** Although the full-chain Lake runs linked the cached `1,686`-job Aeneas/Mathlib package graph, the newly compiled per-worker Rust crates (`3` functions) and Lean proof files (`1-3` theorems) are small fixtures. Their absolute timings and `8`-worker footprints do not extrapolate linearly to multi-module workspace rebuilds or heavy tactic proofs.
- **Sub-interval temporary files:** The `200 ms` periodic filesystem walks in `support/full-chain-transient-workspace-accounting/` establish a lower bound (`4,825,088 B`) on peak workspace allocation and cannot observe ephemeral files created and unlinked between samples.

## Evidence

- **Combined pipeline and full Lake/server chain (`support/combined-pipeline-concurrency/`, `support/full-lake-server-chain/`):**
  - [`support/combined-pipeline-concurrency/probe.py`](support/combined-pipeline-concurrency/probe.py), [`support/combined-pipeline-concurrency/check.py`](support/combined-pipeline-concurrency/check.py), [`support/combined-pipeline-concurrency/results-uninstrumented.json`](support/combined-pipeline-concurrency/results-uninstrumented.json), and [`support/combined-pipeline-concurrency/results-instrumented.json`](support/combined-pipeline-concurrency/results-instrumented.json).
  - [`support/full-lake-server-chain/probe.py`](support/full-lake-server-chain/probe.py), [`support/full-lake-server-chain/check.py`](support/full-lake-server-chain/check.py), and [`support/full-lake-server-chain/results.json`](support/full-lake-server-chain/results.json).
- **Retained and transient full-chain byte/timing inventories (`support/retained-full-chain-byte-timing-inventory/`, `support/full-chain-transient-workspace-accounting/`):**
  - [`support/retained-full-chain-byte-timing-inventory/inventory.py`](support/retained-full-chain-byte-timing-inventory/inventory.py), [`support/retained-full-chain-byte-timing-inventory/check.py`](support/retained-full-chain-byte-timing-inventory/check.py), and [`support/retained-full-chain-byte-timing-inventory/results.json`](support/retained-full-chain-byte-timing-inventory/results.json).
  - [`support/full-chain-transient-workspace-accounting/probe.py`](support/full-chain-transient-workspace-accounting/probe.py), [`support/full-chain-transient-workspace-accounting/check.py`](support/full-chain-transient-workspace-accounting/check.py), [`support/full-chain-transient-workspace-accounting/observations.json.gz`](support/full-chain-transient-workspace-accounting/observations.json.gz), and [`support/full-chain-transient-workspace-accounting/baseline-retained.json`](support/full-chain-transient-workspace-accounting/baseline-retained.json).
- **Per-worker copied bytes and Lake/server resource economics (`support/per-worker-copied-byte-inventory/`, `support/resource-economics/`):**
  - [`support/per-worker-copied-byte-inventory/probe.py`](support/per-worker-copied-byte-inventory/probe.py), [`support/per-worker-copied-byte-inventory/check.py`](support/per-worker-copied-byte-inventory/check.py), [`support/per-worker-copied-byte-inventory/results.json`](support/per-worker-copied-byte-inventory/results.json), and [`support/per-worker-copied-byte-inventory/inventory.csv`](support/per-worker-copied-byte-inventory/inventory.csv).
  - [`support/resource-economics/probe.py`](support/resource-economics/probe.py), [`support/resource-economics/summarize.py`](support/resource-economics/summarize.py), [`support/resource-economics/transcript.json`](support/resource-economics/transcript.json), and [`support/resource-economics/summary.json`](support/resource-economics/summary.json).
- **Nested parallelism, scratch-pool scaling, and retention economics (`support/nested-parallelism-budget/`, `support/scratch-pool-scaling/`, `support/retention-economics-v4-30-0-rc2/`):**
  - [`support/nested-parallelism-budget/probe.py`](support/nested-parallelism-budget/probe.py), [`support/nested-parallelism-budget/check.py`](support/nested-parallelism-budget/check.py), and [`support/nested-parallelism-budget/results.json`](support/nested-parallelism-budget/results.json).
  - [`support/scratch-pool-scaling/probe.py`](support/scratch-pool-scaling/probe.py), [`support/scratch-pool-scaling/check.py`](support/scratch-pool-scaling/check.py), and [`support/scratch-pool-scaling/results.json`](support/scratch-pool-scaling/results.json).
  - [`support/retention-economics-v4-30-0-rc2/probe.py`](support/retention-economics-v4-30-0-rc2/probe.py), [`support/retention-economics-v4-30-0-rc2/results.json`](support/retention-economics-v4-30-0-rc2/results.json), and [`support/retention-economics-v4-30-0-rc2/replay-results.json`](support/retention-economics-v4-30-0-rc2/replay-results.json).

## Revalidation

Run the offline verification scripts across all retained transcripts and inventories:

```sh
python3 support/combined-pipeline-concurrency/check.py
python3 support/full-lake-server-chain/check.py
python3 support/retained-full-chain-byte-timing-inventory/check.py
python3 support/full-chain-transient-workspace-accounting/check.py
python3 support/nested-parallelism-budget/check.py
python3 support/per-worker-copied-byte-inventory/check.py
python3 support/resource-economics/summarize.py
python3 support/scratch-pool-scaling/check.py
```

To re-execute any live probe on a host with the pinned toolchains (`lean`, `lake`, `charon`, `aeneas`, `cargo`) and at least `35%` free memory and `15 GiB` free disk, run the corresponding `probe.py` against a fresh disposable work directory and re-verify with `check.py` / `summarize.py`.
