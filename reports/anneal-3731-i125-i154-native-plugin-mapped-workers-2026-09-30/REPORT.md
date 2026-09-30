# Loaded native-plugin paths across Lean file workers and a forced restart

## Question and result

Published [native-plugin evidence](https://github.com/google/zerocopy/blob/reference/reports/anneal-3730-plugin-reversal-worker-order-2026-09-29/REPORT.md) used initializer markers to show a v1→v2→v1 transition but did not inspect actual process mappings. This local extension inspected the mapped dylib in the Lean watchdog and file workers with both macOS `lsof` and `vmmap`. A stable plugin basename was a symlink to separate **same-basename** v1 and v2 dylibs, so the mapped target paths distinguish the versions without changing the initializer symbol.

The retained worker sequence directly shows v1 in the watchdog and first file worker, then v1 still mapped in the watchdog while a newly opened second worker mapped v2. Closing the first document removed its worker from the observed process tree while the watchdog retained v1. A 1.5 GiB summed-RSS guard stopped the retained server before a third file could reopen v1. A separate forced restart after that stop mapped v1 in a fresh watchdog and worker, returned a clean goal result, and exited normally. This is **partial I125/I154 component evidence**: the in-one-watchdog v1→v2→v1 mapped sequence and Anneal routing policy remain open.

## Subject and procedure

- Installed Lean 4.30.0-rc2 executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; source analysis pin `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. This report identifies the observed executable by hash; the source revision does not independently attest its build provenance.
- Prepared local plugin files are byte-identical to the published v1/v2 artifacts: v1 SHA-256 `3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4`, v2 `f7b4c875cb1c91a35259462b5034f48ad96f819e519d9414edc68975045f92a9`. The copied `Dep.olean` and proof bytes were held fixed. No new plugin build occurred.
- The stable `plugin__probe_Plugin.dylib` symlink pointed first to `v1/plugin__probe_Plugin.dylib`, then atomically to `v2/plugin__probe_Plugin.dylib`. `--plugin` received the stable path. Each mapping snapshot enumerated the watchdog's PID descendants, ran same-user `lsof -nP -p` and `vmmap` on each Lean process, and retained their full raw output compressed under `support/mapping-logs/`.
- The probe required at least 30% reported free memory and 10 GiB free disk, sampled unique process-tree RSS including the Python observer and its direct tool children, and killed the Lean tree once a sample exceeded 1,536 MiB. The first mapping and v2 mapping were retained before the cap stop. The forced-restart run had a separate fresh preflight and the same cap. No network access, install, shared toolchain mutation, or publication-worktree edit occurred.

## Direct observations

| Snapshot | Watchdog mapping | File-worker mapping | Lifecycle observation |
| --- | --- | --- | --- |
| `v1-first` | PID 93511 → v1 | PID 93518 → v1 | First document open; both `lsof` and `vmmap` include the v1 real path. |
| `v1-after-close` | PID 93511 → v1 | No file worker in the watchdog's process tree | `didClose` for the first document was sent and a 0.5-second delay elapsed. This is an observed worker exit, not a proof of plugin unloading or garbage collection. |
| `v2-open` | PID 93511 → v1 | PID 93706 → v2 | Stable symlink pointed to v2; both tools include the distinct v2 real path for the new worker. |
| `forced-restart-v1` | PID 93910 → v1 | PID 93911 → v1 | Following the resource-triggered tree stop, the symlink returned to v1. A fresh server opened the proof, wrote `plugin-v1`, returned an empty goal list, and exited 0. |

The v1/v2 paths are the exact `.../v1/plugin__probe_Plugin.dylib` and `.../v2/plugin__probe_Plugin.dylib` targets retained in the raw maps. The retained v1 and v2 files hash to the artifact values above. The v2 worker's launch command in `guard-abort.json` names `P1.lean`, tying that PID to the second document. At `v2-open`, the watchdog still mapped v1: changing the symlink did not change that existing mapping. The first worker was absent after `didClose`; the fresh server's transcript records no remaining server/worker PIDs after shutdown.

The retained server reached a unique-PID summed RSS sample of **1,576,608 KiB** against a **1,572,864 KiB** cap, exceeding it by 3,744 KiB. The guard killed watchdog PID 93511 and worker PID 93706, and the subsequent LSP write failed. This is an infrastructure/resource stop, not a Lean semantic failure or a clean normal shutdown. The separate forced restart's 63 samples peaked at **1,572,736 KiB**, just 128 KiB below the same cap, and it completed with server exit 0. These narrow margins make further workers unsafe under this cap. RSS sums include shared pages and are not unique physical memory; polling can miss a shorter peak.

`support/restart-transcript.json` preserves the v1 forced-restart marker, goal reply, process IDs, tool exit codes, mapping-line hashes and clean shutdown. For the earlier retained sequence, full `lsof`/`vmmap` outputs and `guard-abort.json` survive, but its in-memory LSP transcript was not written after the guard stop. A same-run v2 initializer marker is therefore **not retained** in this package. The published reversal report supplies marker evidence in a different run; it must not be conflated with these mapping snapshots.

## Limits and revalidation

`lsof` and `vmmap` show mapped file paths and OS file records. They do not hash resident pages or attest every native dependency and ABI. The fixture does not define an Anneal worker-generation key, perform plugin reference release, test an explicit GC operation, or prove cross-platform deletion behavior. I125 and I154 remain partial at the product gate. The mapped reverse transition in one live watchdog was not reached because of the resource stop.

Run `python3 -B support/check.py` to verify the retained v1/v2 artifact hashes, exact mapped paths in both tools' compressed outputs, the close/worker absence, guard stop, forced restart response and cleanup, and metadata. Reacquisition requires the already installed pinned Lean binary, `vmmap`, `lsof`, a new private work tree, and resource admission. The retained `support/probe.py` and `support/restart.py` show the exact commands and guard; the first intentionally aborts if the same 1.5 GiB limit is crossed. This report does not recommend repeating the multiworker cell on this 8 GiB host under the current cap.
