# R506 narrow Lean persistent-collection recheck, 4.30.0-rc2 to 4.34.1

## Scope and result

The [published R506 report](../persistent-data-structures-snapshot-space-costs-1989-2026/REPORT.md) (REPORT.md SHA-256 `67f844e0fc159342365932e91075ee60bf1a233c1da539eb59cc2f648a5e39a0`) is a broad source-grounded analysis of persistent snapshots, arenas, hash-consing, filesystems, and Anneal implications. This supplement checks only its Lean `PersistentArray`/`PersistentHashMap` path-copying example against installed Lean 4.34.1. It is **not** a benchmark of Anneal's workload or a replacement for the R506 survey.

Both exact toolchains passed a [batch-only fixture](fixture/Probe.lean): an old root was retained, every key/index was updated in a latest root, and old/new endpoint values were queried. Separate functions ran the same updates while discarding the old root. At `n=8,192` and `n=65,536`, each of four modes ran three times per toolchain. All **48 serial `lean --run` processes** exited 0 with identical expected semantic outputs across versions; no Lean server ran. This establishes that the tested old-root values survive updates in both versions. It does not prove a particular object-sharing layout or allocation bound from output alone.

## Exact source comparison

| Collection | Lean 4.30.0-rc2 Git blob | Lean 4.34.1 Git blob | Claim-relevant observation |
| --- | --- | --- | --- |
| `src/Lean/Data/PersistentArray.lean` | `516fb0ce50651c1ef39cccdca48663335dac7790` | `e252526851a5eb4bb988d67dd8854b90a2cf970c` | `setAux` through `set` is byte-identical; `forInAux`/`forIn` gain `@&` borrow annotations, and namespace placement changes. |
| `src/Lean/Data/PersistentHashMap.lean` | `f963f3a3f3cfc8c262e14bfcf56d21fc3a55442d` | `e4d81c5cc33ac8d6e67ad217402ec8688b11486e` | `insertAux` through `insert` is byte-identical; lookup/traversal functions gain `@&` annotations, and a separate `alter` API is added. |

The exact roots are `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and `@5045d0056413266e57c625dcd7c365b10e377c52`; [source-diff.patch](source-diff.patch) and [source-observation.json](source-observation.json) retain the comparison. Repository source uses `src/Lean/Data/`; installed Lean archives bundle the same source under `src/lean/Lean/Data/`. The structural-update mechanism described by R506 therefore remains visible in the inspected functions. Changes to read borrowing may affect constants, but this probe cannot attribute any measured RSS difference to that source edit.

The installed 4.30.0-rc2 `lean` executable SHA-256 is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; 4.34.1 is `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` (both arm64 release builds). `lean --version` and executable paths are retained in [results.json](results.json).

## Bounded RSS observations

The runner sampled each direct Lean process's RSS every 25 ms and stopped any child sampled above 1 GiB or running longer than 30 seconds. Figures below are **median sampled peak RSS in MB** across three independent processes; `retained / discarded` identifies whether the old root remains live until endpoint lookup.

| Entries and updates | Toolchain | Array retained / discarded | Map retained / discarded |
| --- | --- | ---: | ---: |
| 8,192 | 4.30.0-rc2 | 393.15 / 393.02 | 397.61 / 397.21 |
| 8,192 | 4.34.1 | 422.25 / 421.48 | 427.39 / 427.21 |
| 65,536 | 4.30.0-rc2 | 397.59 / 397.72 | 408.76 / 402.82 |
| 65,536 | 4.34.1 | 428.18 / 427.20 | 438.80 / 432.91 |

At 65,536 updates, retaining the old map root coincided with about **5.9 MB** higher median peak RSS in each version. The array retained/discarded gaps are small and inconsistent, near this process-level measurement's noise. RSS includes Lean startup, elaboration, runtime, heap and allocator behavior; the polling can miss a short peak. No allocation counter, heap profile, unique-node count, or post-GC retained-byte measurement was available. The old/new absolute RSS difference (~30 MB here) is a whole-toolchain/process observation, **not** a measured collection-regression or proof that new `@&` annotations caused it. These small two-point probes cannot establish asymptotic space behavior.

## Evidence, safety, and replay

[results.json](results.json) stores each command, admission sample, elapsed time, exit, sampled RSS, and stream hashes; [raw outputs](raw/) preserve every stdout/stderr byte. [support/probe.py](support/probe.py) uses exact locally supplied binaries, one process at a time, no build or server, and a fresh per-child requirement of >20% estimated reclaimable RAM, >1 GiB free disk, and <100 MB owned raw-output scratch. The minimum observed admissions were **22.51%** RAM and **4,722,233,344** free disk bytes; maximum sampled RSS was **439,009,280** bytes, below the 1 GiB cap. No install, download, or shared-checkout edit occurred.

Run `python3 -B support/check.py` for an offline check of all outputs, hashes, and bounds. To also verify exact installed source blobs and regenerate the diff, pass `--old-source-root /path/to/lean-4.30.0-rc2 --new-source-root /path/to/lean-4.34.1`. An active repeat uses `python3 -B support/probe.py --old-lean /path/to/4.30/lean --new-lean /path/to/4.34/lean --n 8192` and again with `--n 65536`; the runner appends missing cells and does not invoke network services. Repeating may yield different RSS because of process scheduling and allocator state.
