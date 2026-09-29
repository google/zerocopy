# Bounded 1/2/4/8 scratch-pool scaling with tiny imported Lean goals

## Summary

Eight direct Lean language-server cells exercised one, two, four, and eight simultaneous scratch workers in both cold local-build and warm shared-dependency modes. Every worker opened an unsolved imported proof, returned `⊢ depValue = 7`, received an edit to `rfl`, then returned no goal. All 30 server shutdowns were clean. The eight-worker edited-state macOS group `footprint` charges were **1,288 MiB cold** and **1,337 MiB warm**; both were below the preflight 4.5 GiB cap. Summed RSS at the same samples was 3,644 and 3,887 MiB, respectively, illustrating why RSS cannot be interpreted as unique physical memory. After the workers were shut down and their owned directories removed, only the 5-file, 6,189-byte dependency producer directory remained in each cell.

This is a tiny, serially prepared, concurrently resident Lean LSP pool. It supplies a bounded experimental slice for #3731 J05 and I116/I153, not a Mathlib-scale or Anneal-generated workspace capacity claim. Each cell is one observed run, with only two memory snapshots; transient peak, sustained soak, CPU saturation, and long-term leak behavior remain unresolved.

## Fixture and admission

The pinned binary was `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `v4.30.0-rc2`, Lean SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Execution used an 8 GiB macOS arm64 machine, one private scratch tree on the internal APFS Data volume, and roughly 51 GiB free disk. `memory_pressure -Q` reported 48% free before the matrix. Cases ran in increasing pool size; each cell's servers were stopped before the next cell. No backup volume, global installation, or remote service was involved.

One producer `Dep.lean` defines `depValue : Nat := 7` and is compiled to `Dep.olean`, `Dep.ilean`, and `Dep.c`; its five source/config/artifact files total 6,189 payload bytes and 24,576 bytes of file `st_blocks` charge. In **cold** mode, each worker copies only `Dep.lean` and `lean-toolchain`, then compiles its own three dependency artifacts in its own `deps` directory. In **warm** mode, each worker's `deps` is a directory symlink to the producer's prebuilt immutable files. This is a local source build versus prebuilt import comparison; it does not invoke Lake's artifact cache, and the producer's build cost exists in both modes. Worker creation and dependency compiles were serial, so the measured open/edit fanout begins only after all worker files are prepared.

Each `Proof.lean` initially has `exact ?_` and is edited in memory to `rfl`; its on-disk text remains the initial version. Servers were launched with `LEAN_PATH` pointing at the worker's dependency path and `LEAN_NUM_THREADS=1`. For each phase, the harness sent the open or edit to every client before collecting `textDocument/waitForDiagnostics` and `$/lean/plainGoal` results. The reported phase wall times include serial collection of those responses, not an independent per-request latency distribution. Direct Lean server startup created a 148-byte `lake-manifest.json` in each worker directory; the ledger captures that live product. The `lakefile.toml` is a tiny local config, not an Anneal generator output.

Before entering each pool size, the harness computed a projected group footprint from the largest prior observed per-worker footprint, multiplied by worker count and a 1.12 allowance. For the first cell it used a conservative 1.35 GiB per-worker seed. It required the projection to fit below 4.5 GiB and to leave 0.5 GiB of the currently reported free host memory untouched. Projected values were 1,548, 346, 719, and 1,467 MiB for 1, 2, 4, and 8 workers; reported free-memory estimates were 3,932, 3,932, 4,178, and 4,014 MiB. Each cell was admitted. The harness then checked the sampled open/edit group footprints against the 4.5 GiB cap. This admission and two-snapshot check is bounded: it cannot prove that an unobserved transient peak stayed below the cap.

## Results

`footprint` figures below are macOS `Summary Footprint` for the server and child Lean processes in the owned process trees. RSS is the sum of each process's `ps` RSS at the edited-state sample. Disk bytes are regular-file payload and `st_blocks × 512` charges from a non-following `lstat` walk of the cell root, including the producer once. Inodes include files, directories, and symlinks.

| Cell | Worker prepare (sum s) | Launch / open-query / edit-query (s) | Group footprint open → edited (MiB) | Edited RSS sum (MiB) | Live payload / block charge (B) | Live files / inodes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| cold-1 | 0.162 | 0.030 / 0.313 / 0.212 | 123 → 154 | 477 | 12,659 / 65,536 | 14 / 17 |
| warm-1 | 0.000 | 0.028 / 0.301 / 0.212 | 122 → 153 | 476 | 6,470 / 40,960 | 9 / 12 |
| cold-2 | 0.328 | 0.056 / 0.332 / 0.207 | 253 → 315 | 958 | 19,129 / 106,496 | 23 / 28 |
| warm-2 | 0.001 | 0.055 / 0.349 / 0.212 | 259 → 321 | 964 | 6,751 / 57,344 | 13 / 18 |
| cold-4 | 0.659 | 0.112 / 0.512 / 0.216 | 532 → 655 | 1,938 | 32,069 / 188,416 | 41 / 50 |
| warm-4 | 0.000 | 0.112 / 0.479 / 0.220 | 519 → 646 | 1,929 | 7,313 / 90,112 | 21 / 30 |
| cold-8 | 1.319 | 0.276 / 0.895 / 0.262 | 1,081 → 1,288 | 3,644 | 57,949 / 352,256 | 77 / 94 |
| warm-8 | 0.000 | 0.284 / 0.968 / 0.225 | 1,135 → 1,337 | 3,887 | 8,437 / 155,648 | 37 / 54 |

Each cell separately spent about 0.177–0.181 seconds compiling its producer dependency before worker preparation; this common cost is excluded from the `Worker prepare` column. The cold preparation sums show eight sequential small local dependency compiles, not eight-way compile throughput. The warm preparation costs rounded to 0.000–0.001 seconds for symlink/config creation in this fixture; they exclude producing the shared artifact in the first place. Timing differences between warm and cold open/edit cells are too small and variable for a speedup conclusion from one run each.

The disk ledger reconciles exactly: live cold payload = `6,189 + 6,470 × workers`, and live warm payload = `6,189 + 281 × workers`. The 6,470 cold worker bytes are a 6,189-byte locally built dependency copy plus 281 bytes of private proof/config/manifest data. Warm workers retain just the 281 private bytes and a symlink inode. In both modes, the server generated `lake-manifest.json` accounts for 148 of those 281 private bytes. The linked mode's inode count grows by six per worker; the locally compiled mode grows by eleven. The file and inode rows are all preserved in the JSON transcript, including source, config, artifact, directory, and symlink entries. After shutdown and recursive deletion of only each cell's owned worker directories, every cell inventoried exactly six remaining entries/inodes: producer directory plus its five files. All server shutdown responses exited 0, and no owned server processes remained.

All 30 first-phase goal results contained `⊢ depValue = 7`; all 30 post-edit goal results were `null` after successful diagnostic waits. Thus the measured pools did perform imported goal queries and edits rather than merely keeping idle processes resident. The exact goal and wait replies are retained in [`support/results.json`](support/results.json).

## Interpretation and limits

The macOS `footprint` group summary is a task memory charge sampled through the OS tool, and the transcript also retains per-process `phys_footprint` plus summed RSS. Shared mappings, compressed memory, file cache, and sampled timing mean none of these is an exact count of unique host DRAM pages attributable to an Anneal pool. The 8-worker cell is evidence that **this** tiny import/query workload fit the observed cap, not that eight large Lean/Mathlib workers will fit on this 8 GiB host. No CPU utilization, steady-state pressure, cold cache flush, setup plugin, native artifact, or multi-hour reuse is measured.

The remaining J05/I116/I153 work is a representative generated Anneal project with real dependency/archive sharing, actual scratch-worker lifecycle, sustained edit/query fanout, measured peak footprint and temporary disk writes, and cleanup across failed/cancelled workers. The existing fixture supports exact accounting mechanics and a small upper worker-count control. It cannot extrapolate linearly to Mathlib imports or establish a production concurrency limit. A separate process monitor or memory-pressure trace would be needed to substantiate a hard peak-memory bound rather than the present admission plus open/edit samples.

## Evidence and reproduction

[`support/probe.py`](support/probe.py) is the complete bounded harness; [`support/results.json`](support/results.json) retains admission inputs, commands, wall times, per-process memory transcripts, LSP replies, complete before/live/after/reclaimed disk walks, and cleanup results. [`support/check.py`](support/check.py) reconciles all eight cells, role arithmetic, hashes, admission, goals, physical-memory samples, and post-cleanup state. It passed on the retained result, and the package passed `tools/reference.py` validation.

Run with the pinned binary and an absent owned work directory on a machine with sufficient headroom:

```console
python3 support/probe.py --lean /absolute/path/to/pinned/lean --work /owned/absent/work --out /owned/output
python3 support/check.py
```

The harness records a skipped cell with its projected-memory reason if admission fails. Do not treat a skip as a measured eight-worker result. This recorded run admitted all sizes and did not install anything.
