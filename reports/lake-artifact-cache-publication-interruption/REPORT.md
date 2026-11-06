# Lake Artifact-Cache Publication Atomicity, Writer Interruption, and Recovery

## Summary

At Lean and Lake `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), Lake's local artifact cache separates content-addressed artifact insertion (`Lake/Build/Common.lean`, `Cache.saveArtifact`) from package output-map publication (`Lake/Config/Cache.lean`, `IO.FS.writeFile`). Across six component execution suites, interrupting or corrupting these two surfaces produced distinct failure and recovery behaviors:

1. **Output-map write interruption vs. artifact-directory denial**: Imposing a 64-byte file-size limit (`RLIMIT_FSIZE=64`) tore the direct `IO.FS.writeFile` output-map write on signal 25 (`SIGXFSZ`) after all three module artifacts (`.olean`, `.ilean`, `.c`) had entered the cache. A fresh consumer's `--no-build setup-file` rejected the 64-byte partial JSON mapping with exit 3 (`invalid JSON`), and an ordinary `lake build` rewrote the mapping to restore valid `--no-build` setup and direct Lean import. Denying write permission on the cache artifact directory aborted object insertion (`exit 1`) before any map was written; restoring permissions and retrying completed the four-file cache.
2. **Interrupted cross-volume binary artifact writes and false-hit retries**: When the cache resided on a separate APFS volume so hard-linking fell back to `writeBinFileIfNew`, interrupting the fallback write with `RLIMIT_FSIZE` at half the target size left truncated `.olean` (2,448 of 4,896 bytes), `.ilean` (404 of 809 bytes), or `.c` (764 of 1,529 bytes) objects in the cache without an output map. Because `Cache.saveArtifact` skips writing when the target cache pathname already exists, an ordinary `lake build` retry **without deleting the partial object** exited 0 and published a valid output map pointing to the truncated object. Subsequent `--no-build` builds and `setup-file` calls exited 0 (a local cache false hit). Direct Lean import crashed on signal 11 (`SIGSEGV`) or rejected the header (`invalid header`) for corrupted `.olean` bytes, while accepting truncated `.ilean` and `.c` sidecars during pure module import. Unlinking the damaged object and map before rebuilding restored golden cache hashes.
3. **Cache-only reconstruction vs. batch search-path placement**: Restoring a source/control-only workspace from an eight-file artifact cache under `--no-build` succeeded for `lake --no-build build` and `lake --no-build setup-file` (which returned the cache-resident `.olean` path), but `lake env lean --json` exited 1 (`unknown module prefix 'Dep'`) when the cache remained writable because the conventional `Dep.olean` filename was not materialized in local `.lake/build/lib/lean` search paths.
4. **Frozen producer vs. shared writable producer concurrency**: Freezing a prebuilt producer directory (`0444` files, `0555` directories) allowed 1, 2, and 4 simultaneous consumers with private writable directories to build without mutating the producer or cache inventory. Conversely, sharing a writable source-only producer across concurrent consumers caused a schedule-dependent compiled-configuration collision at 2 writers (`compiled configuration is invalid; run with '-R' to reconfigure`) and duplicate module builds at 4 writers. Under same-mtime source mutation (`depValue` changed from `7` to `9` with nanosecond `mtime` restored), hash-mode `--no-build` rejected the stale artifact (`exit 3`), whereas `--old --no-build` accepted the stale `7` artifact (`exit 0`) and caused downstream theorem checking to fail.

## Applicability

All observations apply to Lean and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), executed on macOS arm64 (`Darwin 25.6.0` / macOS `26.6.2`, APFS, 8 GiB physical RAM) with pinned binary digests:

- `lean` SHA-256: `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`
- `lake` SHA-256: `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`
- `src/lake/Lake/Config/Cache.lean` SHA-256: `f5d1430622af25dd672c256ac50941735f9a3cc129abc3f5efe066a26fd4e3f7`
- `src/lake/Lake/Build/Common.lean` SHA-256: `4ce4b9ce5ad8b55335719928c56ec5a057e2d1b749e54022bca0c95c553d8ea3`

Each subprobe uses a local two-package fixture: a producer package `probe_dep` defining `depValue : Nat := 7` (or `9` in mutation controls) in `Dep.lean`, and a consumer package `probe_consumer` importing `Dep`, proving `depValue + 1 = 8` by `decide`, and evaluating the expression. Every consumer workspace contains a pinned `lean-toolchain` file and a complete relative-path `lake-manifest.json` before its first Lake invocation. Commands ran with `LEAN_NUM_THREADS=1`, isolated `HOME` directories, explicit `LAKE_CACHE_DIR` and `LAKE_ARTIFACT_CACHE` settings, bounded per-command timeouts (10–30 seconds), and sampled process-tree RSS guards.

These experiments characterize single-revision (`v4.30.0-rc2`) local filesystem cache and build-tree behavior on small synthetic fixtures without network dependencies, Mathlib graphs, native plugins, or live `lake serve` sessions. Continuity to other Lean/Lake revisions or non-APFS filesystems is not inferred.

## Findings

### Output-Map Tearing, Permission Refusal, and Post-Publication Object Truncation

In `Lake/Config/Cache.lean`, Lake writes package output mappings via direct `IO.FS.writeFile` after creating parent directories. In `Lake/Build/Common.lean`, `Cache.saveArtifact` checks whether the destination cache path exists, attempts a hard link (`IO.FS.hardLink`), and falls back to `writeBinFileIfNew` when hard-linking fails for a reason other than `alreadyExists`. On a single APFS volume, binary artifacts enter the cache via hard links while the small JSON output map is written as a regular file.

| Control | Publication State and Consumer Result | Repair Result |
| --- | --- | --- |
| Output-map write under `RLIMIT_FSIZE=64` | Lake exited `-25` (signal 25); three intact cache artifacts plus one 64-byte partial JSON output map (SHA-256 `02c91130c41608834ae358a017864d13285f30b71440dc877047a9d2ff4459bb` vs. valid map `4374ce75e3040a0287f0da02104f90620d0b53e417a218b68ab5e7c4cd21f4e7`). Fresh `--no-build setup-file` exited 3 with `invalid JSON`. | Ordinary `lake build` exited 0 and rewrote the mapping; `--no-build setup-file` and direct Lean theorem check exited 0. |
| Artifact directory permission denied | Lake exited 1 with `failed to cache artifact: permission denied` at the `.olean` path. Cache had no artifact or output-map files. | Restored directory permissions; ordinary `lake build` exited 0 with three artifacts and one map. |
| Existing `.olean` truncated from 4,896 to 100 bytes | Unchanged mapping still named `7b7a31f2adb2306a.olean` (truncated SHA-256 `44a98c92e903ee59f4cdea10d0a485ad7d91d141f6ad14ab69d64159a8aa820d` vs. valid `4d2519d8006d6b63510989fa471021ac046867c69ec94aa8e11212bc8468da85`). Fresh `--no-build setup-file` exited 0; ordinary build reported `Fetched Dep` and exited 0; direct Lean import exited `-11` (signal 11). | Unlinking the bad object made fresh `--no-build setup-file` exit 3 (`artifact missing`). Ordinary build regenerated the 4,896-byte object; `--no-build setup-file` and direct Lean exited 0. |

Two private writable package trees consuming a read-only (`0444` files, `0555` directories) copy of the repaired four-file cache concurrently via `lake build Dep` both exited 0 without mutating the cache inventory, and subsequent `--no-build setup-file` calls exited 0 (peak sampled summed RSS: 1,326,192 KiB). A separate pair of processes running `lake build Dep` in a single shared writable consumer/producer tree with the artifact cache disabled reached overlapping 1.5-second `run_cmd` markers and exited 0 (peak sampled summed RSS: 3,563,664 KiB under a 5,500,000 KiB guard). Basis: **source + execution** (`support/lake-cache-publication-atomicity/probe.py`, `support/lake-cache-publication-atomicity/results.json`).

### Cross-Volume Same-Key Writers and Interrupted Artifact Write Fallbacks

Placing `LAKE_CACHE_DIR` on a separate 128 MiB APFS disk image forced `IO.FS.hardLink` to fail across device IDs and execute `writeBinFileIfNew`. For each artifact class (`.olean` `7b7a31f2adb2306a.olean`, `.ilean` `256fdbc46043cf30.ilean`, `.c` `19804e4afa920628.c`), the cache was pre-seeded with the other two golden objects and `RLIMIT_FSIZE` was set to half the target artifact's byte size.

| Trial | Observed Result | Verification Oracle |
| --- | --- | --- |
| Three two-process same-key misses | Both process markers appeared; all six Lake processes exited 0. Pair sampled summed-RSS peaks were 3,557,536, 3,516,256, and 3,484,976 KiB (under a 3,800,000 KiB cap). Each cache map and all three object hashes matched the single-writer golden cache (`outputs/probe_dep/566c416840dafb01.json`). | Fresh private `--no-build setup-file` and fresh direct Lean import exited 0 after every pair. |
| `.olean` write limit (`2,448` / `4,896` bytes) | Lake exited `-25`; partial object was 2,448 bytes. Initial fresh `--no-build` exited 3 (map absent). Ordinary retry with partial object still present exited 0 and published the map while retaining the truncated `.olean`; subsequent fresh `--no-build` exited 0. | Direct Lean import of the partial `.olean` exited `-11`. Deleting the partial object and map and rebuilding restored golden cache hashes and fresh import exit 0. |
| `.ilean` write limit (`404` / `809` bytes) | Lake exited `-25`; partial object was 404 bytes. Ordinary retry with partial object present exited 0 and published the map; subsequent fresh `--no-build` exited 0. | Fresh direct Lean import exited 0 despite the truncated `.ilean`. Exact SHA-256 verification rejected it; deleting and rebuilding restored golden bytes. |
| `.c` write limit (`764` / `1,529` bytes) | Lake exited `-25`; partial object was 764 bytes. Ordinary retry with partial object present exited 0 and published the map; subsequent fresh `--no-build` exited 0. | Fresh direct Lean import exited 0 despite the truncated `.c`. Exact SHA-256 verification rejected it; deleting and rebuilding restored golden bytes. |

A separate guarded retry (`support/same-key-interruption-admission-refusal/probe.py`) completed `prebuild-a` (`lake --keep-toolchain --no-ansi build Dep`, caching disabled) in 7.1935 seconds with exit 0 (admitted at 30.8668% reclaimable RAM, runtime low 24.0709%, peak summed RSS 1,813,424 KiB), but stopped before `prebuild-b` when fresh reclaimable RAM measured 25.6100% (`18,499,035,136` bytes free disk), below that runner's strict `>30%` admission gate (`RuntimeError('prebuild-b:fresh_admission_denied')`). Basis: **execution** (`support/lake-same-key-artifact-writers/results.json`, `support/same-key-interruption-admission-refusal/results.json`).

### Pre-Publication Writer Kill and Survivor Cache Population

When `SIGKILL` (`-9`) terminated a solo writer during `Dep.lean` elaboration (`run_cmd` 1.5-second pause) before module artifacts were emitted (sampled summed RSS 1,799,328 KiB across two processes), the shared cache remained empty and the producer directory held only six files (source/control, compiled configuration and trace, and `Dep.setup.json`, with no `.olean`, `.ilean`, `.c`, or module trace). `--no-build setup-file Generated.lean` exited 3 (`target is out-of-date and needs to be rebuilt`). An ordinary `lake build Dep` retry exited 0, grew the producer directory to 13 files, and populated the four-file cache.

When two independent package trees shared only `LAKE_CACHE_DIR` (sampled summed RSS 3,512,256 KiB across four processes), killing writer A (`-9`) while letting writer B finish (`exit 0`) populated the four-file cache (`.olean` SHA-256 `4d2519d8006d6b63510989fa471021ac046867c69ec94aa8e11212bc8468da85`, map SHA-256 `4374ce75e3040a0287f0da02104f90620d0b53e417a218b68ab5e7c4cd21f4e7`). Killed consumer A then ran `--no-build build Dep` (`exit 0`, `Fetched Dep`) and `--no-build setup-file Generated.lean` (`exit 0`), growing A's producer directory from 6 to 9 files (resolving `importArts.Dep` directly to the cache path without creating a local `Dep.olean`). Truncating the shared cache's output map to `{"data":` caused a fresh consumer's `--no-build setup-file` to exit 3; ordinary `lake build Dep` rewrote the map to `4374ce75e3040a0287f0da02104f90620d0b53e417a218b68ab5e7c4cd21f4e7` without altering the three artifact files. Basis: **execution** (`support/lake-writer-recovery/results.json`).

### Relocation, Cache-Only Reconstruction, and Search-Path Placement Divergence

After building `Generated` (`exit 0`, output `8`), copying the producer/consumer pair from `original/` to `other/depth/relocated/`, removing `original/`, and making the relocated producer read-only yielded:

| Operation from Relocated Consumer | Exit | Observation |
| --- | ---: | --- |
| `--no-cache --no-build build Dep` | 0 | All targets up to date under ordinary hash freshness. |
| `--no-cache --old --no-build build Dep` | 0 | All targets up to date in `--old` mtime mode. |
| `--no-cache --no-build setup-file Generated.lean` | 0 | `importArts.Dep` identified the relocated producer `.olean`. |
| `--no-cache env lean --json Generated.lean` | 0 | Information diagnostic evaluated to `8`; producer inventory unchanged. |

In contrast, when a fresh source/control-only producer and consumer reconstructed state from an eight-file writable artifact cache (six artifacts, two output maps), `--no-build build Dep` (`Fetched Dep`), `build Generated` (`Fetched Dep`, `Fetched Generated`), and `--no-build setup-file Generated.lean` all exited 0, but `lake env lean --json Generated.lean` exited 1 (`unknown module prefix 'Dep'`) because the cache-fetched object was not placed at the conventional `.lake/build/lib/lean/Dep.olean` search path. Replacing the cached `.olean` with invalid bytes (`not an olean\n`) versus deleting it produced:

| Cache Object State | `--no-build build Dep` | `--no-build setup-file Generated.lean` | Direct Lean Loader via `Dep.olean` Symlink |
| --- | --- | --- | --- |
| Intact | exit 0 (`Fetched Dep`) | exit 0 (returned cache artifact path) | exit 0 (evaluated `8`) |
| Missing | exit 3 (artifact-not-found / out-of-date) | exit 3 | exit 1 (`unknown module prefix`) |
| Present with invalid bytes (`not an olean\n`) | exit 0 (`Fetched Dep`) | exit 0 (returned cache artifact path) | exit 1 (`invalid header`) |

In a separate frozen-producer sweep (`--no-cache build Generated`), 1, 2, and 4 simultaneous consumers completed in 0.584 s, 0.654 s, and 0.832 s respectively (all exit 0, producer payload ~105.3 KiB unchanged, per-consumer logical payload ~119.9 KiB). Basis: **execution** (`support/lake-concurrency-preparation-v4-30-0-rc2/results.json`).

### Shared Writable Producer Collisions and Same-Mtime Changed-Definition Sentinel

Comparing simultaneous consumers sharing one writable source-only producer against simultaneous consumers over a frozen prebuilt producer (`--keep-toolchain --no-cache`, `LAKE_ARTIFACT_CACHE=false`) showed:

| Consumers | Shared Writable Exits; Group Wall Time | Frozen Producer Exits; Group Wall Time | Sampled Peak Summed RSS (Shared / Frozen) |
| ---: | --- | --- | ---: |
| 1 | `0`; 2.033 s | `0`; 1.058 s | 1,833,792 / 1,823,008 KiB |
| 2 | `0, 1`; 1.779 s | `0, 0`; 1.238 s | 1,834,160 / 3,666,992 KiB |
| 4 | `0, 0, 0, 0`; 4.131 s | `0, 0, 0, 0`; 1.605 s | 7,144,400 / 6,930,688 KiB |

In the first 2-consumer shared-writable run, one consumer failed during configuration loading with `compiled configuration is invalid; run with '-R' to reconfigure`; in the 4-consumer shared-writable run, all four logged `Built Dep` against the same output paths. A clean replay (`support/lake-writer-scale-v4-30-0-rc2/writer-scale-replay-results.json`) exited `0`, `0,0`, and `0,0,0,0` (4-writer summed RSS peak 6,986,096 KiB), confirming that the 2-writer configuration collision is schedule-dependent. Each finished producer had 13 files (~105.5 KiB logical payload, 148 KiB allocated blocks) and each consumer had 14 files (~119 KiB logical payload, 164 KiB allocated blocks).

When configuration was primed first and only module build directories were removed before two writers entered `Dep.lean` compilation (`support/lake-writer-scale-v4-30-0-rc2/interruption.py`, peak summed RSS 3,630,016 KiB), killing writer A (`-9`) during the 1.5-second `run_cmd` pause allowed writer B to exit 0 (`Built Dep`, `Built Generated`, producer `.olean` SHA-256 `750e919bd9db10c05dda7f98916f39a98e85b81d914fb09ec847d146640035bb`), and subsequent `--no-build build Dep` exited 0 (reproduced identically in `support/lake-writer-scale-v4-30-0-rc2/interruption-replay-results.json`).

In the same-mtime changed-definition sentinel, `Dep.lean` was built with `depValue := 7` (source SHA-256 `195f6a0685fc4b969a2b7670245b5fcfe9b5061c7ec8bb16c7802996267d68bc`, `.olean` SHA-256 `1655c61e49be501e366f40626eb3b524aa5795e87f78294c03dc1454aacc6350`), then edited to `depValue := 9` (source SHA-256 `44acb75972b0addd77d692627d8d9318ced81820d30aef9622f8469d91bea16f`) with its original nanosecond `mtime` restored. Hash-mode `--no-build build Dep` exited 3 (out of date), whereas `--old --no-build build Dep` exited 0 (falsely up to date), causing `lake env lean --json Generated.lean` to fail (`exit 1`) on a theorem expecting `9` while `#eval` printed `7`. An ordinary rebuild exited 0, printed `9`, and replaced `Dep.olean` with SHA-256 `bb5da5cf57ec84fd22a4f6e66a9964ee04647bd492e58af870e5618b6256dc25`. Basis: **execution** (`support/lake-writer-scale-v4-30-0-rc2/writer-scale-results.json`, `support/lake-writer-scale-v4-30-0-rc2/interruption-results.json`).

## Boundaries

- **Same-volume hard-link tearing and power-loss durability (`not examined`)**: Output-map tearing was induced via `RLIMIT_FSIZE=64` on `IO.FS.writeFile`, and binary artifact truncation was induced on a cross-volume `writeBinFileIfNew` fallback. Kernel crash or power-loss durability, filesystem journal replay, and concurrent same-key output-map write syscall collisions were **not examined**.
- **Shared writable package-tree safety (`known not to apply`)**: Although bounded two-writer and four-writer schedules in a shared writable package directory completed in specific runs, the schedule-dependent configuration collision (`compiled configuration is invalid`) establishes that shared writable package directories are not safe for uncoordinated concurrent Lake writers.
- **Lake cache lookup as a byte-integrity oracle (`known not to apply`)**: Lake's local artifact-cache restoration and `Cache.saveArtifact` existence check validate pathname presence and JSON map syntax, not the cryptographic hash of existing cached artifact bytes. Any consumer requiring byte-level integrity after interrupted writes must validate artifact digests independently.
- **High-concurrency scaling, remote cache transport, and full dependency archives (`not examined`)**: Runs were bounded to 1–4 concurrent processes on an 8 GiB RAM host using synthetic two-package fixtures. Remote HTTP cache downloads, archive extraction interruptions, native plugins/dynlibs, Mathlib-scale dependency closures, and live `lake serve` sessions under cache interruption were **not examined**.

## Evidence

### Cache Publication Atomicity (`support/lake-cache-publication-atomicity/`)
- Driver and results: [`support/lake-cache-publication-atomicity/probe.py`](support/lake-cache-publication-atomicity/probe.py) (SHA-256 `b0402a686de8e3c8e880a8a888823ab04378b1475b5dd832deffe62cd7c94313`), [`support/lake-cache-publication-atomicity/results.json`](support/lake-cache-publication-atomicity/results.json) (SHA-256 `73a4cd35877b30d9dbf4256d6ff1b98fcd9578c8458a55764e169b51209b562a`).
- Preserved failure and repaired specimens: [`support/lake-cache-publication-atomicity/artifacts/partial-output-map.json`](support/lake-cache-publication-atomicity/artifacts/partial-output-map.json), [`support/lake-cache-publication-atomicity/artifacts/truncated-olean.bin`](support/lake-cache-publication-atomicity/artifacts/truncated-olean.bin), [`support/lake-cache-publication-atomicity/artifacts/map-repaired-cache/`](support/lake-cache-publication-atomicity/artifacts/map-repaired-cache/), [`support/lake-cache-publication-atomicity/artifacts/artifact-repaired-cache/`](support/lake-cache-publication-atomicity/artifacts/artifact-repaired-cache/), [`support/lake-cache-publication-atomicity/artifacts/object-repaired-cache/`](support/lake-cache-publication-atomicity/artifacts/object-repaired-cache/), and [`support/lake-cache-publication-atomicity/fixture/`](support/lake-cache-publication-atomicity/fixture/).

### Concurrency Preparation and Cache Integrity (`support/lake-concurrency-preparation-v4-30-0-rc2/`)
- Driver and results: [`support/lake-concurrency-preparation-v4-30-0-rc2/probe.py`](support/lake-concurrency-preparation-v4-30-0-rc2/probe.py) (SHA-256 `29e8cff5aca8aabd5ebcc9769c264e082353b9ecb4546a04c73984a041049db6`), [`support/lake-concurrency-preparation-v4-30-0-rc2/results.json`](support/lake-concurrency-preparation-v4-30-0-rc2/results.json).

### Same-Key Artifact Writers and Cross-Volume Interruption (`support/lake-same-key-artifact-writers/` and `support/same-key-interruption-admission-refusal/`)
- Cross-volume driver, offline checker, and results: [`support/lake-same-key-artifact-writers/probe.py`](support/lake-same-key-artifact-writers/probe.py), [`support/lake-same-key-artifact-writers/check.py`](support/lake-same-key-artifact-writers/check.py), [`support/lake-same-key-artifact-writers/results.json`](support/lake-same-key-artifact-writers/results.json), [`support/lake-same-key-artifact-writers/fixture/`](support/lake-same-key-artifact-writers/fixture/), and [`support/lake-same-key-artifact-writers/artifacts/`](support/lake-same-key-artifact-writers/artifacts/).
- Guarded admission refusal record: [`support/same-key-interruption-admission-refusal/probe.py`](support/same-key-interruption-admission-refusal/probe.py), [`support/same-key-interruption-admission-refusal/check.py`](support/same-key-interruption-admission-refusal/check.py), [`support/same-key-interruption-admission-refusal/results.json`](support/same-key-interruption-admission-refusal/results.json), [`support/same-key-interruption-admission-refusal/raw/`](support/same-key-interruption-admission-refusal/raw/), [`support/same-key-interruption-admission-refusal/fixture/`](support/same-key-interruption-admission-refusal/fixture/), and [`support/same-key-interruption-admission-refusal/work/`](support/same-key-interruption-admission-refusal/work/).

### Pre-Publication Writer Kill and Recovery (`support/lake-writer-recovery/`)
- Driver, results, and snapshots: [`support/lake-writer-recovery/probe.py`](support/lake-writer-recovery/probe.py) (SHA-256 `6304d7953ed43bc75dd621f85f882d51824d26341f7a63c2091cb8daf90badf2`), [`support/lake-writer-recovery/results.json`](support/lake-writer-recovery/results.json) (SHA-256 `5accf91a0611bff361ceb03bd4e2de2f43ebb17ce34ef17768ebb5239b3dc215`), and [`support/lake-writer-recovery/artifacts/`](support/lake-writer-recovery/artifacts/).

### Shared-Writer Scale and Changed-Definition Sentinel (`support/lake-writer-scale-v4-30-0-rc2/`)
- Drivers and transcripts: [`support/lake-writer-scale-v4-30-0-rc2/probe.py`](support/lake-writer-scale-v4-30-0-rc2/probe.py) (SHA-256 `3f6b2ab83e0675f92185873e311c045dd8d22752e8346806d4a50616f389e56b`), [`support/lake-writer-scale-v4-30-0-rc2/interruption.py`](support/lake-writer-scale-v4-30-0-rc2/interruption.py) (SHA-256 `70e1f36d203e9c886c9ebbb446fe69fe77cf16cae11efd29e276a3c2db6924b8`), [`support/lake-writer-scale-v4-30-0-rc2/writer-scale-results.json`](support/lake-writer-scale-v4-30-0-rc2/writer-scale-results.json), [`support/lake-writer-scale-v4-30-0-rc2/writer-scale-replay-results.json`](support/lake-writer-scale-v4-30-0-rc2/writer-scale-replay-results.json), [`support/lake-writer-scale-v4-30-0-rc2/interruption-results.json`](support/lake-writer-scale-v4-30-0-rc2/interruption-results.json), and [`support/lake-writer-scale-v4-30-0-rc2/interruption-replay-results.json`](support/lake-writer-scale-v4-30-0-rc2/interruption-replay-results.json).

## Revalidation

To verify the preserved cross-volume partial-write and admission-gate artifacts offline without invoking Lake or Lean:

```console
python3 support/lake-same-key-artifact-writers/check.py
python3 -B support/same-key-interruption-admission-refusal/check.py
```

To re-execute the active probes against a pinned or candidate `lake` and `lean` binary pair, supply fresh absent work directories on an owned filesystem:

```console
python3 support/lake-cache-publication-atomicity/probe.py --work /new/empty/work-atomicity
python3 support/lake-same-key-artifact-writers/probe.py --work /new/empty/work-same-key
python3 support/lake-writer-recovery/probe.py --work /new/empty/work-recovery
python3 support/lake-concurrency-preparation-v4-30-0-rc2/probe.py --lake /path/to/lake --lean /path/to/lean --work /new/empty/work-prep --out /new/empty/out-prep
python3 support/lake-writer-scale-v4-30-0-rc2/probe.py --lake /path/to/lake --lean /path/to/lean --work /new/empty/work-scale --out /new/empty/out-scale
python3 support/lake-writer-scale-v4-30-0-rc2/interruption.py --lake /path/to/lake --lean /path/to/lean --work /new/empty/work-int --out /new/empty/out-int
```

Compare exit codes, `SIGXFSZ` (`-25`) truncation behavior, `--no-build` rejection of malformed JSON maps versus false-hit acceptance of present corrupted objects, and direct Lean loader verdicts.
