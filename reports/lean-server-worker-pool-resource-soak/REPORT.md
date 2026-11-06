# Lean LSP Server Topology, Multi-Project Routing, Module Layout Tradeoffs, and Multi-Worker Resource Soaks

## Summary

Across eight empirical topology, layout, fault-isolation, and multi-minute soak experiments on Lean and Lake `v4.30.0-rc2` (arm64 macOS, 8 GiB RAM, `LEAN_NUM_THREADS=1`), direct `lean --server` watchdogs and Lake module layouts demonstrate the following operational characteristics:
1. **Single-watchdog `LEAN_PATH` sharing vs. multi-project server routing**: A single `lean --server` watchdog binds one process-wide import path (`LEAN_PATH`) at launch. Opening files from two workspaces `A` (`selected := 11`) and `B` (`selected := 22`) that both `import Dep` under `A`'s watchdog causes `B`'s file to resolve `A`'s `Dep.olean` (`11`) and fail `B`'s `rfl` proof (`867,074,048` B summed RSS across 1 watchdog + 2 workers). Routing `A` and `B` to separate watchdogs (`967,688,192` B summed RSS across 2 watchdogs + 2 workers, a ~100.6 MB overhead for the second watchdog) isolates their imports and preserves `A`'s unsaved failing buffer across an `A -> B -> A` project switch until `A`'s server is restarted from disk.
2. **Per-annotation vs. per-file vs. per-artifact module layouts**: Splitting two claims into separate modules (`Model -> Shared -> AnnOne, AnnTwo -> Aggregate`) requires two live file workers (`917–931` MB summed RSS vs. `496–516` MB for 1-worker per-file and per-artifact layouts) and increases sequential Lake build times (`2,672–3,255` ms cold vs. `1,073–1,614` ms), but isolates incremental rebuilds and failures (`AnnTwo.olean` stays byte-identical and passes batch verification when `AnnOne` is edited or fails with `exact ?_`) and prevents cross-annotation references unless an explicit `import AnnOne` is added.
3. **Multi-worker scaling (`1 / 2 / 4` file workers) and contamination sentinels**: Under a single watchdog, scaling from 1 to 2 to 4 open file workers scales stable summed RSS from `460–466` MB (`~122–123` MB summed `phys_footprint`) to `872–946` MB (`~223–304` MB `phys_footprint`) to `1,695–1,842` MB (`~432–591` MB `phys_footprint`, peak `1,864,056,832` B). Across 25 sentinel queries (`probe0 = 7`, `probe1 = 9`, `probe2 = 11`, `probe3 = 13`) and 69 multi-minute edit/goal checks, zero cross-file goal or diagnostic contamination occurred.
4. **Long-running edit/restart resource drift**: Across a 336.55-second (`5.6`-minute) soak spanning three consecutive server lifetimes (21 edits and 21 goal queries per lifetime, 63 total, with two full server restarts), macOS process-group `footprint` rose from `116.3–116.5` MiB at launch to `331.8–331.9` MiB after the first elaboration and plateaued at `332.4–332.6` MiB at the end of all three lifetimes, with zero orphan processes or scratch-inode growth (`4` inodes / `16,384` block bytes throughout).
5. **Pool fault isolation and bidirectional JSON-RPC ID collision**: In a 4-server pool (peak summed RSS `620,003,328` B), injecting a type error (`exact 0` for `True`) in worker 0 and sending `SIGKILL` (`exit -9`) to worker 1's process group left workers 2 and 3 unaffected and allowed worker 1 to reconstruct cleanly from disk. In bidirectional JSON-RPC framing, `lean --server` emits low-numbered server-to-client requests such as `workspace/inlayHint/refresh` (observed with `id: 23`), which collides with client-to-server request IDs unless the client filters incoming messages by absence of a `method` field and/or offsets client request IDs.

## Applicability

- **Evaluated Toolchain Subject**: Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` executable SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) on an 8 GiB (`8,589,934,592` B) arm64 macOS host with `LEAN_NUM_THREADS=1`.
- **Subprobe Coverage**:
  1. **Direct server topology and conflicting imports** (`support/server-topology-v4-30-0-rc2/`): 1-watchdog (2 workers) vs. 2-watchdog (1 worker each) comparison on conflicting `A/Dep.olean` (`11`) and `B/Dep.olean` (`22`), plus scratch worker PID replacement (`47653 -> 47657`) and RPC session invalidation (`-32900`).
  2. **Two-project `A -> B -> A` router** (`support/project-switch-router-v4-30-0-rc2/`): Client-side project router switching between live server `A` (PID 93693, unsaved failing version-2 buffer `selected = 99` vs. disk `11`) and server `B` (PID 93696, `selected = 22`), followed by cold `A` restart (PID 93703).
  3. **Per-annotation, per-file, and per-artifact module layouts** (`support/lean-artifact-layouts-v4-30-0-rc2/`): Two repetitions across 3 layouts × 2 model sizes (1 and 128 `pad` definitions), measuring cold, warm, and single-proof-edit Lake build times, batch check times, worker RSS, failure isolation, and cross-annotation visibility (`semantic.py`).
  4. **1/2/4 file-worker ramp and contamination sentinels** (`support/resource-soak-contamination/`): 25 sentinel goal queries across 1, 2, and 4 open files under one watchdog (`7.87` s total elapsed).
  5. **15-second 24-edit soak, wrong-import control, RPC release, and client timeout** (`support/lean-server-soak-context-rpc/`): 12 edits and 2 close/reopens each in workspaces `A` and `B`, `InfoWithCtx` dereference and `$/lean/rpc/release` (`-32602`), and a 120 ms client timeout on nonexistent `waitForDiagnostics(version=999)`.
  6. **188.97-second guarded 1/2/4-worker ramp and RPC soak** (`support/lean-multiminute-restart-resource-soak/`): 69 versioned edit/goal checks and 8 initial checks across cells `A-1`, `A-2`, `A-4`, and `B-1`, plus the retained `pilot-id-collision.json` trace (`id: 23` collision on `workspace/inlayHint/refresh`).
  7. **336.55-second 3-lifetime edit/restart resource-drift soak** (`support/lean-server-resource-drift-soak/`): 3 lifetimes × 21 edits/goals (`111.5–111.6` s per lifetime) with 36 periodic macOS `footprint`, RSS, free-RAM, and inode-ledger samples.
  8. **4-server pool failure isolation and `SIGKILL` restart** (`support/lean-pool-failure-isolation/`): 4 concurrent `lean --server` process groups with buffer fault injection on worker 0, `SIGKILL` + disk restart on worker 1, and an explicit `(epoch, version, source_hash)` stale-result fence model (an 8-worker follow-up was declined by the 45% free-memory admission guard when post-cell free RAM measured 42%).

## Findings

### 1. Multi-Workspace Topology and `A -> B -> A` Project-Switch Routing

- **1-watchdog vs. 2-watchdog conflicting `Dep.olean` topology** (`support/server-topology-v4-30-0-rc2/transcript.json` SHA-256 `8689cb07deca24a640f729d457383b057e32a6d2bcbb0ec8ecdeb18b05129b0c`, `support/server-topology-v4-30-0-rc2/summary.json` SHA-256 `2d4646b7feb93e33f4f4322623dc7be165e6bbffd91b67f60add9bc4d4618075`):

| Topology | `B` file `#eval selected` | `B` `rfl` claim | Loaded processes | Summed RSS | Per-Process RSS Breakdown |
| --- | --- | --- | ---: | ---: | --- |
| One `A`-configured watchdog, `A` and `B` open | `11` | Failed: `selected` did not reduce to `22` | 3 | 867,074,048 B | 1 watchdog (`91,553,792` B) + 2 workers (`388,022,272` B, `387,497,984` B) |
| Separate `A` and `B` watchdogs | `22` | No `rfl` error | 4 | 967,688,192 B | 2 watchdogs (`97,517,568` B, `95,289,344` B) + 2 workers (`387,563,520` B, `387,317,760` B) |

  Initialization took `30.0` ms for the shared watchdog and `26.4` ms for each separate watchdog; version-1 `waitForDiagnostics` took `235.5–239.2` ms, and `plainGoal` took `0.4–1.4` ms. In the scratch worker phase, editing `exact ?_` to `rfl` at version 2 completed `waitForDiagnostics` in `211.3` ms; closing and reopening the URI at version 1 (`240.0` ms) replaced the worker PID (`47653 -> 47657`) and invalidated the prior RPC session (`-32900 Outdated RPC session`) (**Basis: execution**).

- **Two-project `A -> B -> A` routing and cold disk reopen** (`support/project-switch-router-v4-30-0-rc2/results.json`):
  - Routing `A` (PID 93693, init `28.82` ms, initial wait `247.54` ms, summed RSS `399,261,696` B) → `B` (PID 93696, init `28.43` ms, initial wait `309.73` ms, summed RSS `441,679,872` B; combined two-server RSS `840,941,568` B) → `A` (PID 93693, warm wait `0.64` ms) preserved `A`'s unsaved version-2 failing buffer (`⊢ selected = 99`) while on-disk `A/Proof.lean` remained valid (`selected = 11`).
  - Shutting down `A` PID 93693 and starting cold `A` PID 93703 (init `27.02` ms, wait `269.51` ms) read the saved disk file (`selected = 11`, no goals), demonstrating that a project router must replay unsaved editor buffers if it recycles a server process (**Basis: execution**).

### 2. Module Layout Tradeoffs: Per-Annotation vs. Per-File vs. Per-Artifact

In `support/lean-artifact-layouts-v4-30-0-rc2/comparison.json` (SHA-256 `02a67438b3738568a7e0553cc9497a92800465f4b75492e27868bde45d1c9e6b`), `support/lean-artifact-layouts-v4-30-0-rc2/raw-run1.json` (SHA-256 `ff1b0b47ee854bba72ee1328b7a44b275fb40a6c6bbe755c6bc4a2655498e90a`), and `support/lean-artifact-layouts-v4-30-0-rc2/raw.json` (SHA-256 `5094cd4c96e81d38d8bd6742a58264e296c77e3c517b3b6f7bc2b00cffcaec82`):

| Model pads | Layout (`Module Graph`) | Modules / live file workers | Cold build sequence | Warm build sequence | One-proof edit build sequence | Fresh proof batch check sum | Summed server RSS |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | Per annotation (`Model → Shared → AnnOne, AnnTwo → Aggregate`) | 5 / 2 | 2708–3255 ms | 2090–2091 ms | 2291–2300 ms | 342–344 ms | 917–920 MB |
| 1 | Per file (`Model → File → Aggregate`) | 3 / 1 | 1612–1614 ms | 1248–1249 ms | 1448–1449 ms | 180–181 ms | 496 MB |
| 1 | Per artifact (`Artifact → Aggregate`) | 2 / 1 | 1079–1091 ms | 831–832 ms | 1023–1031 ms | 181–182 ms | 499 MB |
| 128 | Per annotation (`Model → Shared → AnnOne, AnnTwo → Aggregate`) | 5 / 2 | 2672–2680 ms | 2094–2096 ms | 2282–2289 ms | 342–344 ms | 926–931 MB |
| 128 | Per file (`Model → File → Aggregate`) | 3 / 1 | 1607–1612 ms | 1246–1251 ms | 1441–1447 ms | 180–181 ms | 496 MB |
| 128 | Per artifact (`Artifact → Aggregate`) | 2 / 1 | 1073–1078 ms | 828–831 ms | 1024–1027 ms | 214 ms | 516 MB |

- **Artifact growth and incremental reuse**: Increasing `Model` from 1 to 128 inert `pad` definitions grew `Model.olean` from `5,704` to `132,400` bytes while keeping `AnnOne.olean` and `AnnTwo.olean` byte-identical; the aggregate consumer's fresh import check took `164–166` ms across all six cells. Editing `AnnOne` rebuilt `AnnOne.olean` and `Aggregate.olean` while leaving `AnnTwo.olean`, `Shared.olean`, and `Model.olean` untouched; injecting `exact ?_` in `AnnOne` left `AnnTwo.lean` passing fresh batch checks.
- **Cross-annotation visibility restriction** (`support/lean-artifact-layouts-v4-30-0-rc2/semantic-results.json`, SHA-256 `46238feae509edee827e1eafd51d7f840ebf9d09b050376d75ea91c63d06988e`): Referencing `claimOne` inside `AnnTwoWithoutImport.lean` failed (`exit 1`, `Unknown identifier claimOne`) unless `import AnnOne` was added or both claims resided in `Combined.lean` (**Basis: execution**).

### 3. Multi-Worker Scaling (`1 / 2 / 4` File Workers), RPC Soaks, and Request-ID Collision

- **Short 1/2/4-worker contamination sweep** (`support/resource-soak-contamination/transcript.json`, SHA-256 `80b63975d220f3610136eac6a71dd7933033cb24c43ee0fbb1818e924f51a522`, 25 `waitForDiagnostics` calls median `213.1` ms [range `205.3–243.2` ms], 25 `plainGoal` calls median `1.0` ms [range `0.7–1.8` ms]):

| Open files | Tree processes at stable sample | Summed RSS, stable | Sum of separately queried `phys_footprint`, stable | Largest sampled summed RSS in cell | Cell elapsed |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 460,505,088 B | 121,676,032 B | 535,871,488 B | 1,164.6 ms |
| 2 | 3 | 946,143,232 B | 304,298,816 B | 1,073,709,056 B | 1,958.8 ms |
| 4 | 5 | 1,842,298,880 B | 591,293,888 B | 1,846,132,736 B | 4,043.1 ms |

- **15.22-second 24-edit soak and client timeout** (`support/lean-server-soak-context-rpc/transcript.json`, SHA-256 `e0e91b44b61f7f6ef5b1ed684fc2748bb31359660e1a7d48528767b0c0ed65aa`):
  - Completed 12 edit cycles in `A` (`n = 11`) and 12 in `B` (`n = 22`), closing and reopening after edit cycles 4 and 8, dereferencing `InfoWithCtx` (`{"p":"0"}`) across 3 edits, confirming `-32602` after `$/lean/rpc/release` and `-32900` after reopen/restart, and verifying that `waitForDiagnostics(version=999)` timed out locally at `120` ms and did not reply within a 5 s post-`$/cancelRequest` wait while the watchdog still answered version-1 `plainGoal` and shut down cleanly.
  - Stable 1-worker summed RSS was `464,584,704` B (`A`) and `465,846,272` B (`B`), with `phys_footprint` `121,954,752` B (`A`) and `123,838,976` B (`B`), peaking at `695,058,432` B across 3 processes (median `waitForDiagnostics` `211.6` ms across 34 calls; median `plainGoal` and rich RPC `0.4` ms across 35 and 33 calls).

- **188.97-second multi-minute 1/2/4-worker ramp and RPC soak** (`support/lean-multiminute-restart-resource-soak/transcript.json`, SHA-256 `fef3401ba4ebf5a5a684d36e8c0d8a595a9945bd28471bc2cd4638ec96d8caaa`, 1,679 events; 86 `waitForDiagnostics` median `212.35` ms, 77 `plainGoal` median `0.8` ms, 29 rich RPC calls median `0.6` ms):

| Cell | File workers + watchdog at stable sample | Edit cycles / checks | Stable summed RSS | End summed RSS | Stable / end summed `phys_footprint` | Cell elapsed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `A-1` | 2 | 9 / 9 | 465,879,040 B | 694,370,304 B | 123,118,208 / 350,135,680 B | 48.01 s |
| `A-2` | 3 | 9 / 18 | 871,940,096 B | 824,852,480 B | 222,706,880 / 433,209,152 B | 50.15 s |
| `A-4` | 5 | 9 / 36 | 1,694,547,968 B | 1,864,056,832 B | 431,992,704 / 598,831,296 B | 54.59 s |
| `B-1` | 2 | 6 / 6 | 465,682,432 B | 437,420,032 B | 122,872,128 / 349,594,752 B | 32.34 s |

  After edit cycle 5 in each cell, closing and reopening all files invalidated old RPC sessions (`-32900`). In `support/lean-multiminute-restart-resource-soak/pilot-id-collision.json` (SHA-256 `e1c9f08bdd6b4d63e07017b074ecf90168b97271b0faea5407c3ee7c0da32a3e`), an exploratory run aborted at `54.35` s when the server sent a `workspace/inlayHint/refresh` request with numeric `id: 23` while client request `id: 23` was pending; filtering replies by `method is None` resolved the collision (**Basis: execution**).

### 4. 336.55-Second Resource-Drift Soak and 4-Server Pool Fault Isolation

- **Three-lifetime 5.6-minute edit/query/restart drift soak** (`support/lean-server-resource-drift-soak/results.json`, `support/lean-server-resource-drift-soak/sample-ledger.csv`):

| Server lifetime | Edits and goals | Lifetime (s) | Group `footprint` start → after first edit → end (MiB) | Sampled `footprint` max (MiB) | Summed RSS start → end / sampled max (MiB) | Processes after shutdown |
| --- | ---: | ---: | --- | ---: | --- | ---: |
| 1 | 21 / 21 | 111.548 | 116.4 → 331.8 → 332.6 | 332.6 | 438.7 → 367.5 / 657.1 | 0 |
| 2 | 21 / 21 | 111.636 | 116.3 → 331.9 → 332.6 | 332.6 | 438.6 → 494.9 / 657.4 | 0 |
| 3 | 21 / 21 | 111.623 | 116.5 → 331.8 → 332.4 | 332.4 | 438.6 → 657.2 / 657.2 | 0 |

  Across all 36 full samples (12 per lifetime), the process tree held exactly 2 processes (1 watchdog + 1 worker), disk allocation stayed fixed at 3 files / 4 inodes (`4,634` B before first save, `4,659` B thereafter, `16,384` `st_blocks` bytes), and `footprint` remained flat at `332.4–332.6` MiB (**Basis: execution**).

- **Four-server pool failure isolation and `SIGKILL` recovery** (`support/lean-pool-failure-isolation/transcript.json`):
  - Across 4 independent `lean --server` process groups (peak summed pool RSS `620,003,328` B below the 2.4 GiB cap; minimum host free RAM 41%; post-cleanup scratch `16,384` B), injecting `exact 0` into worker 0's buffer produced `numerals are data in Lean, but the expected type is a proposition` on worker 0 without affecting workers 1–3 (`⊢ True`, empty diagnostics).
  - Sending `didChange(version=2)`, `waitForDiagnostics`, and `$/cancelRequest` to worker 1 followed immediately by process-group `SIGKILL` (`exit -9`) left zero processes in worker 1's group, left workers 2 and 3 healthy, and allowed a fresh server on worker 1's directory to reopen the saved valid proof (`⊢ True`, empty diagnostics) (**Basis: execution**).

## Boundaries

- **Not examined**: Hours-long daemon operation on Mathlib-scale or large Aeneas-generated dependency graphs, or Linux proportional set size (PSS) / cgroup memory accounting (macOS `ps` RSS double-counts shared pages across processes, and sequential `phys_footprint` / `footprint` queries are periodic snapshots rather than continuous high-water marks).
- **Not examined**: Eight concurrent server workers (explicitly skipped by `support/lean-pool-failure-isolation/probe.py`'s admission guard because post-4-worker free RAM was 42%, below its 45% threshold for 8 workers).
- **Unknown**: Whether the per-process RSS fluctuations between `367.5` MiB and `657.4` MiB during the 5.6-minute soak (while `footprint` remained constant at `332.4–332.6` MiB) reflect macOS shared-library page fault accounting or transient allocator caches.
- **Known not to apply**: Pooling files from workspaces with conflicting `LEAN_PATH` or package configurations under a single `lean --server` watchdog is unsound because the watchdog's initial environment overrides per-URI directory location; additionally, matching JSON-RPC responses by `id` alone without checking that `method` is absent fails when `lean --server` initiates server-to-client requests such as `workspace/inlayHint/refresh`.

## Evidence

- **Server topology and conflicting imports**: [`support/server-topology-v4-30-0-rc2/probe.py`](support/server-topology-v4-30-0-rc2/probe.py) (SHA-256 `e25dffeefadbd86f7d3eec4f862a8cf882e709fb99365a6730d8359be42288c0`), [`support/server-topology-v4-30-0-rc2/transcript.json`](support/server-topology-v4-30-0-rc2/transcript.json) (SHA-256 `8689cb07deca24a640f729d457383b057e32a6d2bcbb0ec8ecdeb18b05129b0c`), [`support/server-topology-v4-30-0-rc2/summarize.py`](support/server-topology-v4-30-0-rc2/summarize.py) (SHA-256 `6d3276187c2bae0421b4fb998290efc6bd81928c4b6f4d4c4c26ddd7d125d71a`), [`support/server-topology-v4-30-0-rc2/summary.json`](support/server-topology-v4-30-0-rc2/summary.json) (SHA-256 `2d4646b7feb93e33f4f4322623dc7be165e6bbffd91b67f60add9bc4d4618075`), and [`support/server-topology-v4-30-0-rc2/work`](support/server-topology-v4-30-0-rc2/work).
- **Project-switch router (`A -> B -> A`)**: [`support/project-switch-router-v4-30-0-rc2/probe.py`](support/project-switch-router-v4-30-0-rc2/probe.py), [`support/project-switch-router-v4-30-0-rc2/results.json`](support/project-switch-router-v4-30-0-rc2/results.json), [`support/project-switch-router-v4-30-0-rc2/check.py`](support/project-switch-router-v4-30-0-rc2/check.py), and [`support/project-switch-router-v4-30-0-rc2/fixture`](support/project-switch-router-v4-30-0-rc2/fixture).
- **Module artifact layouts**: [`support/lean-artifact-layouts-v4-30-0-rc2/probe.py`](support/lean-artifact-layouts-v4-30-0-rc2/probe.py) (SHA-256 `4a603f56ae82d91d95060b05df5d09aff1225264774ffe0b183ed796871eeea0`), [`support/lean-artifact-layouts-v4-30-0-rc2/raw-run1.json`](support/lean-artifact-layouts-v4-30-0-rc2/raw-run1.json), [`support/lean-artifact-layouts-v4-30-0-rc2/raw.json`](support/lean-artifact-layouts-v4-30-0-rc2/raw.json), [`support/lean-artifact-layouts-v4-30-0-rc2/summarize.py`](support/lean-artifact-layouts-v4-30-0-rc2/summarize.py), [`support/lean-artifact-layouts-v4-30-0-rc2/summary-run1.json`](support/lean-artifact-layouts-v4-30-0-rc2/summary-run1.json), [`support/lean-artifact-layouts-v4-30-0-rc2/summary.json`](support/lean-artifact-layouts-v4-30-0-rc2/summary.json), [`support/lean-artifact-layouts-v4-30-0-rc2/compare.py`](support/lean-artifact-layouts-v4-30-0-rc2/compare.py), [`support/lean-artifact-layouts-v4-30-0-rc2/comparison.json`](support/lean-artifact-layouts-v4-30-0-rc2/comparison.json), [`support/lean-artifact-layouts-v4-30-0-rc2/semantic.py`](support/lean-artifact-layouts-v4-30-0-rc2/semantic.py) (SHA-256 `f9b979dcd167e8621cf58d3bad0a4f457caf2ab56bc1b4d26c78e4baa0997981`), [`support/lean-artifact-layouts-v4-30-0-rc2/semantic-results.json`](support/lean-artifact-layouts-v4-30-0-rc2/semantic-results.json), [`support/lean-artifact-layouts-v4-30-0-rc2/setup-attempt.json`](support/lean-artifact-layouts-v4-30-0-rc2/setup-attempt.json), [`support/lean-artifact-layouts-v4-30-0-rc2/work`](support/lean-artifact-layouts-v4-30-0-rc2/work), and [`support/lean-artifact-layouts-v4-30-0-rc2/semantic-work`](support/lean-artifact-layouts-v4-30-0-rc2/semantic-work).
- **1/2/4-worker contamination sweep**: [`support/resource-soak-contamination/probe.py`](support/resource-soak-contamination/probe.py) (SHA-256 `4b721610dc0ab4a9058ecefa4f836616c3b78eb14d1dd44037382ab337db89ba`), [`support/resource-soak-contamination/check.py`](support/resource-soak-contamination/check.py) (SHA-256 `8b2a42de9ef71ccb32ca3526740f30c8c25d7011d409ba4f5a10dd006c2f3f6b`), [`support/resource-soak-contamination/transcript.json`](support/resource-soak-contamination/transcript.json) (SHA-256 `80b63975d220f3610136eac6a71dd7933033cb24c43ee0fbb1818e924f51a522`), and [`support/resource-soak-contamination/work`](support/resource-soak-contamination/work).
- **24-edit soak and RPC context**: [`support/lean-server-soak-context-rpc/probe.py`](support/lean-server-soak-context-rpc/probe.py) (SHA-256 `ca1cfede5f46103417671350fc0dcc19fdd6f1746c766e358f60a27d7bfe8ced`), [`support/lean-server-soak-context-rpc/check.py`](support/lean-server-soak-context-rpc/check.py) (SHA-256 `be554c194b64020791c1817b6a8d947a3abbea3b6de18bffccb65227d99cc844`), [`support/lean-server-soak-context-rpc/transcript.json`](support/lean-server-soak-context-rpc/transcript.json) (646 events, SHA-256 `e0e91b44b61f7f6ef5b1ed684fc2748bb31359660e1a7d48528767b0c0ed65aa`), and [`support/lean-server-soak-context-rpc/work`](support/lean-server-soak-context-rpc/work).
- **Multi-minute 1/2/4-worker ramp and RPC soak**: [`support/lean-multiminute-restart-resource-soak/probe.py`](support/lean-multiminute-restart-resource-soak/probe.py) (SHA-256 `64ea6982653f41e0be7050d41f7135e28f76f2e2712f5f2f580086bff351029d`), [`support/lean-multiminute-restart-resource-soak/check.py`](support/lean-multiminute-restart-resource-soak/check.py) (SHA-256 `d790f7d2b868c35d07698915c4971ff6cdf4e1c390979ba0b05dc6b3631192e5`), [`support/lean-multiminute-restart-resource-soak/transcript.json`](support/lean-multiminute-restart-resource-soak/transcript.json) (1,679 events, SHA-256 `fef3401ba4ebf5a5a684d36e8c0d8a595a9945bd28471bc2cd4638ec96d8caaa`), [`support/lean-multiminute-restart-resource-soak/pilot-id-collision.json`](support/lean-multiminute-restart-resource-soak/pilot-id-collision.json) (SHA-256 `e1c9f08bdd6b4d63e07017b074ecf90168b97271b0faea5407c3ee7c0da32a3e`), and [`support/lean-multiminute-restart-resource-soak/work`](support/lean-multiminute-restart-resource-soak/work).
- **5.6-minute 3-lifetime resource-drift soak**: [`support/lean-server-resource-drift-soak/probe.py`](support/lean-server-resource-drift-soak/probe.py), [`support/lean-server-resource-drift-soak/build_ledger.py`](support/lean-server-resource-drift-soak/build_ledger.py), [`support/lean-server-resource-drift-soak/check.py`](support/lean-server-resource-drift-soak/check.py), [`support/lean-server-resource-drift-soak/results.json`](support/lean-server-resource-drift-soak/results.json), and [`support/lean-server-resource-drift-soak/sample-ledger.csv`](support/lean-server-resource-drift-soak/sample-ledger.csv).
- **4-server pool fault isolation**: [`support/lean-pool-failure-isolation/probe.py`](support/lean-pool-failure-isolation/probe.py), [`support/lean-pool-failure-isolation/verify.py`](support/lean-pool-failure-isolation/verify.py), and [`support/lean-pool-failure-isolation/transcript.json`](support/lean-pool-failure-isolation/transcript.json).

## Revalidation

Run all offline verification and comparison scripts across the eight retained subprobes without starting Lean or Lake:

```sh
python3 support/server-topology-v4-30-0-rc2/summarize.py
python3 support/project-switch-router-v4-30-0-rc2/check.py
python3 support/lean-artifact-layouts-v4-30-0-rc2/compare.py
python3 support/resource-soak-contamination/check.py
python3 support/lean-server-soak-context-rpc/check.py
python3 support/lean-multiminute-restart-resource-soak/check.py
python3 support/lean-server-resource-drift-soak/check.py
python3 support/lean-pool-failure-isolation/verify.py
```

To re-run live acquisition on a pinned `v4.30.0-rc2` installation, invoke each subprobe's `probe.py` in an isolated copy of the subprobe directory with `LEAN_NUM_THREADS=1` and the respective preflight memory/RSS guards enabled.
