# Bounded Lake consumer and Lean server resource economics on an 8 GiB APFS host

## Summary

Two independent tiny Lake consumers built distinct same-name `Generated` modules successfully with a sampled peak of 2.10 GB **summed RSS** across four Lake/Lean processes. One no-change warm pair sampled two processes and 1.30 GB summed RSS. Four short edit rounds under two separate direct Lean servers kept value-7 and value-9 goal/diagnostic sentinels distinct; the two watchdogs plus two workers grew in sampled summed RSS from 1.04 to 1.39 GB and dropped to zero after clean shutdown. macOS `phys_footprint` samples were far below summed RSS for the server trees, illustrating why RSS sums are not unique physical memory. These small fixtures do not justify a production Anneal worker cap or high-worker extrapolation.

## Applicability

Execution used the pinned arm64 macOS Lean/Lake `v4.30.0-rc2` release at `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. Binary SHA-256: `lean` `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`. The host reported 8,589,934,592 bytes RAM; the fixture resided on APFS under `/System/Volumes/Data`. `memory_pressure -Q` reported 51% system-wide free at start and 46% at end; `vm.swapusage` reported the same 746.38 MiB used at both endpoints. Host readings include unrelated system activity and are not a process-specific bill.

Each of four independent workspaces has one tiny module `Generated` defining `selected := 7` or `9`, a matching theorem, and one scratch proof. Lake used `--keep-toolchain --no-cache`, `LEAN_NUM_THREADS=1`, `LAKE_CACHE_DIR=''`, `LAKE_ARTIFACT_CACHE=false`, and `MATHLIB_NO_CACHE_ON_UPDATE=1`. No external dependency or Mathlib was installed. The run used at most two Lake consumers concurrently. Its guard killed process groups if sampled summed RSS exceeded 4.6 GB or sampled system free memory fell below 20%; neither guard fired. The guard samples were about 70 ms apart with `memory_pressure` checked every fifth sample, so very brief peaks could be missed. The server phase used at most two watchdogs and two file workers. These choices avoid repeating the prior four-consumer Lake run that approached 7 GiB summed RSS on this host.

## Findings

### Cold, warm, and proof-edit build costs

| Lake phase | Wall time | Sampled peak processes | Sampled peak summed RSS |
| --- | ---: | ---: | ---: |
| Cold serial A, value 7 | 956.2 ms | 2 | 1,027,457,024 B |
| Cold serial B, value 9 | 615.4 ms | 2 | 777,338,880 B |
| Cold parallel A+B | 808.1 ms | 4 | 2,102,542,336 B |
| Warm parallel A+B | 537.3 ms | 2 | 1,303,625,728 B |
| Proof-only edit, parallel A+B | 672.8 ms | 2 sampled | 1,304,084,480 B sampled |
| Warm after edit, parallel A+B | 538.8 ms | 2 | 1,303,248,896 B |

All Lake calls exited 0. The two cold serial runs together took 1,571.6 ms versus 808.1 ms for the one parallel pair in this run. This is an observed single-run wall comparison with cold-start and monitoring effects, not a throughput curve or stable speedup estimate. The cold parallel group sampled two Lake parents and two Lean children. The proof-edit group changed `by decide` to `by rfl` and produced different OLean hashes, although the ~70 ms sampler recorded only the two Lake parents; it missed any short-lived compiler child. Warm reruns kept each OLean hash unchanged. The value-7 and value-9 OLean hashes matched between serial and parallel cold builds and remained distinct from each other. **Basis: execution**, `group` and `proof_edit` events, with hash assertions in `support/summarize.py`.

This graph has one module per workspace, so `LEAN_NUM_THREADS=1` plus at most two outer Lake invocations bounded the observed process count, but the experiment did not establish a general global parallelism budget inside a larger Lake graph or across Cargo, rustc, Charon, Aeneas, plugins, and MCP. The sampled one-shot `footprint` calls during some Lake groups caught Lake parents rather than all compiler descendants; they are retained in the transcript but are not used as whole-build physical-footprint estimates. **Basis: execution and boundary of the measurement method**.

### Disk and temporary artifact accounting

Each completed workspace contained 15 regular files, 7 directories, 15 unique file inodes, and 159,744 bytes summed from `st_blocks * 512`. The two parallel consumers together occupied 319,488 such block bytes and 30 files. Before the proof edit, logical file payload was 109,440 bytes for A and 109,312 for B; after the edit it was 108,325 and 108,197 bytes. Each workspace inventory included two `.olean` files (one is Lake's compiled configuration), one `.ilean`, two `.trace`, and one generated `.c`, plus hashes and control files. The probe retained source and output inventories under `support/work` and their exact hashes in the transcript. No filename matching `.tmp`, `.temp`, or `~` was seen in the periodic scans or final inventory. **Basis: execution**.

The recorded maximum sampled or final allocated-block total was 159,744 bytes per workspace. This is not the total bytes written or a proof that no short-lived temporary files existed between samples. `df` available-space readings differed by 716 KiB between start and end, which can include unrelated host activity and metadata. The inventory excludes the shared toolchain, caches outside the work root, filesystem compression/clones, and directories' physical allocation. For sharing-mode mutation tests on this same APFS host, see the separate [APFS sharing report](../anneal-3730-filesystem-sharing-apfs-v4-30-0-rc2/REPORT.md); this probe deliberately used independent writable build trees rather than trying symlink/hardlink/clone aliases again.

### Two-server short soak and memory metric distinction

Two direct `lean --server` watchdogs each opened a `Scratch.lean` importing its own `Generated.olean`. In A, the diagnostic `#eval selected` yielded `7` and the goal was `⊢ selected = 7`; in B the corresponding values were `9`. Four edit rounds alternated A/B request order, changed scratch proof text, waited for diagnostics, and checked both goals. Closing both files and reopening in reverse order yielded the same separate sentinels. Every server request succeeded, and both clean shutdowns returned exit code 0. This is an isolation sentinel in two independent processes, not a shared-workspace reset or plugin contamination test. **Basis: execution**, `sentinel`, `soak`, and `server_stop` events.

| Server phase | Sampled process count | Summed RSS | Sum of separately sampled `phys_footprint` |
| --- | ---: | ---: | ---: |
| Initial two files | 4 | 1,044,250,624 B | 369,165,376 B |
| After edit round 1 | 4 | 1,163,034,624 B | unmeasured |
| After edit round 2 | 4 | 1,258,242,048 B | unmeasured |
| After edit round 3 | 4 | 1,359,773,696 B | unmeasured |
| After edit round 4 | 4 | 1,385,152,512 B | unmeasured |
| After close/reopen | 4 | 1,382,039,552 B | 695,633,472 B |
| After shutdown | 0 | 0 B | unmeasured |

macOS `ps` RSS includes resident shared mappings in each process; summing it can count those pages repeatedly. `/usr/bin/footprint --noCategories --format bytes` reported each process's `phys_footprint`, sampled sequentially at initial and reopened states. Its sum is a different metric and is **not** Linux proportional set size (PSS) or an atomic whole-tree unique-memory measurement. The upward short-session values can reflect retained caches, mapped pages, or other runtime state; four rounds cannot distinguish bounded warming from a leak. The after-stop process-tree sample found no surviving watchdog or direct file worker. **Basis: execution**, retained per-PID `ps` rows and full `footprint` outputs in the transcript.

Initial/reopened open-and-wait times were 610.9, 626.0, 600.2, and 590.0 ms. Across 12 waits, `waitForDiagnostics` latency ranged 211.3–626.0 ms (median 211.55); across 12 post-wait `plainGoal` calls, latency ranged 0.4–1.4 ms (median 0.5). These are local direct-server timings for tiny files, not end-to-end Anneal capture, projection, import preparation, or MCP latency. **Basis: execution**, `server_open` and `latency` events.

### Relation to remaining #3731 resource questions

| Item | Added here | Still required |
| --- | --- | --- |
| I113 | Per-workspace logical/block bytes, entries, inode count, sampled temporary filenames | Full Rust/LLBC/Lean/cache/log bill, bytes written, peak temporary space, writes outside root |
| I114/I115 | 1/2 cold/warm Lake consumers, process-count/RSS guard | Representative high-worker sweep and all inner-tool parallel controls |
| I116/I117 | Four server edit rounds, close/reopen, RSS plus macOS footprint | Long soak, retained-generation accounting, PSS or platform-equivalent whole-tree unique memory |
| I118 | Lake group, server open/wait, and goal timing segments | Capture, extraction, translation, import, plugin, and MCP stages at realistic sizes |
| I119 | Independent writable trees; references APFS sharing control | Complete prepared-tree sharing and physical extent accounting |
| I139 | Explicit guard and paired isolated sentinel | Actual Anneal generated projects and integrated acceptance thresholds |
| I146 | One short live-worker retention cycle; references prior [16-generation tier report](../anneal-3730-retention-economics-v4-30-0-rc2/REPORT.md) | Retained workers and historical imports at 1/2/4/8/16 realistic generations |
| I153/I154 | Two per-workspace servers with alternating sentinel order | Same-watchdog N-file comparison, MCP/scratch pool, shared fixture reset, plugin conflict and forced restart |

## Boundaries

- **Not examined:** production Anneal or MCP code; generated Rust/Charon/Aeneas outputs; Mathlib-scale imports; native plugins; high-worker load; long-running cache/leak behavior; real parallel test fixtures or shared mutable workspace contamination.
- **Unknown:** peak compiler RSS and transient disk space between ~70 ms polls. Warm/proof-edit process counts may miss brief compiler children. The guard is conservative for this test but cannot certify that every instantaneous host-pressure spike was observed.
- **Not measured:** PSS, unique physical footprint of the entire process tree at one instant, CPU utilization, thread count, energy, bytes written, APFS clone extent sharing, and writes outside the work root. Summed per-process `phys_footprint` is provided only for stable server phases, with sequential samples.
- **Not established:** a safe production concurrency cap, a stable parallel speedup, a monotonic memory leak, full fixture isolation under shared workspaces, or a choice of retention tier. The prior four-consumer Lake run approached the 8 GiB host's practical limit; this experiment intentionally stopped at two consumers.

## Evidence

- Complete standard-library harness: [`support/probe.py`](support/probe.py), SHA-256 `787f967a151e85c93761ae505f98c011af75e95362d4499be5841c354d8514c6`.
- Raw sanitized run: [`support/transcript.json`](support/transcript.json), SHA-256 `bfe3ca05a09f821422322543fec3ee47f040dd4b8927250e6f0147ecd539a7da`; 262 events include all commands, exits, stdout/stderr, process trees, `footprint` output, host guard checks, source/OLean hashes, filesystem inventories, server messages, and latency events. Local paths are tokenized as `$WORK_URI`, `$WORK`, `$LEAN_BIN`, and `$LAKE_BIN`.
- [`support/summarize.py`](support/summarize.py) asserts build success and semantic sentinels, serial/parallel/warm/edited OLean hash relations, resource guards, file/inode/block counts, server cycle responses, footprint availability, and cleanup. Its passing compact result is [`support/summary.json`](support/summary.json). The generated fixtures and final Lake build trees are under [`support/work`](support/work).
- Comparison evidence: [prior direct Lean server memory run](../lean-server-memory-and-protocol-concurrency-v4-30-0-rc2/REPORT.md), [prior Lake writer scale/interruption run](../anneal-3730-lake-writer-scale-v4-30-0-rc2/REPORT.md), [APFS sharing mutation controls](../anneal-3730-filesystem-sharing-apfs-v4-30-0-rc2/REPORT.md), and [16-generation retention economics](../anneal-3730-retention-economics-v4-30-0-rc2/REPORT.md). Their fixtures and limits remain distinct from this run.

## Revalidation

On an 8 GiB or larger macOS/APFS host with the pinned toolchain, run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py`, then `python3 support/summarize.py`. The probe replaces only its own `support/work` directory, checks a 30% free-memory floor before starting, runs at most two Lake consumers, and kills its process groups if the sampled resource guard fires. Verify the binary hashes and guard outcome before comparing times. On Linux or another filesystem, adapt the memory and allocation probes explicitly; do not label RSS or macOS footprint as PSS.
