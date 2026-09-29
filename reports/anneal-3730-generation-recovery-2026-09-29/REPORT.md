# Causally gated generation publication and recovery on APFS

## Summary

In a disposable multi-file generation fixture on macOS/APFS, a selected pointer exposed either the complete old generation or the complete new one across nine separately gated `SIGKILL` points. Kills before pointer replacement left A selected; a kill after replacement left B selected. A complete B directory moved into place just before the pointer update remained an orphan after interruption and was removed on reconstruction. A late old child completed successfully after logical cancellation and a newer B publication, but the publication gate classified it obsolete. These are **observations of this synthetic process/filesystem protocol**, not Anneal or Lake behavior and not power-loss durability evidence.

A cooperating reader that pinned A and held a shared `flock` lease could read A after B published; garbage collection skipped A until the reader released its lease. An unleased reader pinned the same A path, then missed its second file open after GC removed A. Killing a leased reader released its OS lock, allowing collection. Three repeated kill/restart/cleanup cycles preserved A and removed complete unselected B directories; a later B5 publication replaced A. The script and one normalized raw result are retained; two executions produced byte-identical JSON.

## Applicability

`support/probe.py` executed with CPython 3.14.7 on macOS 26.6.2 arm64 on the local APFS data volume. Every run used temporary directories beneath the conversation-owned `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731` scratch root and removed them afterward. The process boundary is real: the parent starts child Python writers/readers, waits for marker files, and uses `SIGKILL` at exact named phases. The generation content is invented: `Model.lean`, `Proof.lean`, optional A-only `Legacy.lean`, and files named `.olean` whose bytes are explicit `FAKE-OLEAN-*` strings. Neither Lean nor any compiler reads them.

The fixture writes a manifest of exact file names and SHA-256 hashes, validates that inventory, moves a complete staged directory into `generations/`, and replaces one `current` symlink with `os.replace`. Selection and garbage collection use one advisory `fcntl.flock` publication lock and generation-local lease locks. The experiment therefore applies to these OS/file operations under cooperative readers and this locking protocol. It does not establish the behavior of a real prepared Lean environment, an actual Anneal adapter, crash durability, or cross-platform rename semantics.

The requested scope is issue #3731 I051–I055, I105–I112, and I121–I122. Adjacent corpus reports provide real Charon/Aeneas failure output, direct Lean stale-import behavior, and Lake writable-tree conflicts. This report contributes a new OS-process and filesystem slice of the publication/retention questions. It does not treat those other reports as execution of this fixture or as proof of an integrated Anneal pipeline.

## Findings

### Complete selection is a separate operation from producing files

The worker writes `Model.lean`, `Proof.lean`, fake `Model.olean`, fake `Proof.olean`, then an exact file manifest. A's manifest includes `Legacy.lean`; B's does not. The validator requires the actual file set to equal the manifest file set, rehashes every file, and rejects B if a stale `Legacy.lean` is present. This gives the selected B tree a two-module output set without carrying A-only `Legacy.lean` through a reused destination. It is a syntactic completeness and ownership check in the fixture, not Lean elaboration or semantic dependency closure.

The nine kill points and observations were:

| Child stopped after | Selected immediately after kill | Restart cleanup |
| --- | --- | --- |
| Model source | Complete A | Removed incomplete `staging/B`. |
| Proof source | Complete A | Removed incomplete `staging/B`. |
| Model artifact | Complete A | Removed incomplete `staging/B`. |
| Proof artifact | Complete A | Removed incomplete `staging/B`. |
| Manifest write | Complete A | Removed `staging/B`, even though the manifest exists. |
| Manifest validation | Complete A | Removed complete but unpublished `staging/B`. |
| Publication lock acquired | Complete A | Removed complete but unpublished `staging/B`. |
| Stage moved to `generations/B` | Complete A | Removed complete unselected `generations/B`. |
| `current` symlink replaced | Complete B | Removed retired A. |

For all nine, a fresh reconstruction read `current` and its manifest and found a valid selected tree with the expected exact file set. The result does **not** imply every filesystem crash is safe: a `SIGKILL` stops one userspace process without power loss, buffer-cache loss, or an `fsync` durability protocol. It also does not prove readers never see mixed files if they resolve `current` independently for multiple reads; the earlier `anneal-3730-snapshot-capture-jobs-2026-09-29` fixture shows that weak read pattern can accept a mixed A/B snapshot. A reader must pin one immutable generation before opening its components. Basis: **execution** for this table; **derived** for the reader rule using the paired snapshot counterexample.

### Cancellation and completion order cannot choose the current generation

The parent held an old epoch-1 child at its post-validation gate. It then advanced authoritative epoch to 2, marked that child logically cancelled, let a B child publish complete epoch-2 output, and released the old child. The old process exited normally and recorded `obsolete`; B remained selected, with its four-file manifest valid. Reconstruction removed the old child’s `staging/Old` and retired A. This is a causally ordered **execution** result. The schedule deliberately changed both epoch and cancellation status, so this run alone cannot isolate which guard rejected the old child. The separate finite model in `anneal-3730-fault-model-2026-09-29` removes those guards individually and finds bounded counterexamples; neither package proves a production engine implements them.

The publication test happens under one advisory lock after all stage files are complete. An old process can finish and its complete output can still be unselected; cancellation is not equivalent to output deletion or safe publication. The fixture does not insert obsolete output into a reusable cache, deliver late diagnostics, or cancel descendant compiler processes.

### Live-reader leases and garbage collection have a concrete failure boundary

The leased reader resolved `current -> generations/A`, acquired a shared `flock` on A's `lease.lock`, and paused. After B published, GC attempted a nonblocking exclusive lock on A, saw it held, and retained A. The reader then opened `Proof.lean` under pinned A and got SHA-256 `46597fe091b38e8772380253f6daf528cfde2c5a17d4933d0c2111f133dec388`. After reader exit, a second GC removed A. The unleased control pinned A but held no lock; GC removed A after B, and the reader's delayed open returned `FileNotFoundError`. A third run killed a leased reader while it paused; the OS released its lock and GC removed A. Basis: **execution** with marker-gated child processes and advisory locks.

This proves only the fixture's cooperative lease rule. If a Lean worker, scratch fork, replay process, or external tool can later open generation files without acquiring the lease, the GC condition is insufficient. Holding an already-open descriptor or memory map is also not equivalent to guaranteeing *later path opens*. The negative control demonstrates the latter. Native/Lean artifact mapping, worker-internal references, lease persistence across service restart, and network filesystem lock behavior remain untested.

### Restart can reconcile selected files without trusting notifications

Three successive runs in one temporary workspace killed complete B2/B3/B4 workers just after directory move and before pointer replacement. Each startup-like GC read the selected A manifest, removed the unselected complete directory, and on an immediate second pass removed nothing. A later B5 child published, and GC removed A while preserving B5. A separate control kept an observed notification state at A, dropped the B notification, and supplied a late duplicate A event. Re-reading the actual selected pointer and manifest recovered epoch 2/B. The file operations and process deaths are **execution**; the event stream is a modeled delivery choice, not an OS filesystem watcher or MCP/LSP transport.

A child killed while holding the advisory publication lock also released that lock at process death; a new B writer then acquired it and published. This is one-lock recovery evidence only. It says nothing about ordering across preparation, cache, server-restart, and GC locks, or about a thread/process that stays alive while holding a lock indefinitely.

### Item-level results and exact remaining conditions

| ID | Evidence here | Remaining requested investigation |
| --- | --- | --- |
| I051 | Two-module synthetic tree, staged manifest, nine kill points and selected-pointer checks. | Real generated Lean source and compiled artifact families with readers paused after each write; compare immutable staging with coordinated in-place replacement. |
| I052 | Adjacent to this suite only: move-before-pointer observed. | Prepare at permanent versus relocated paths with Lake manifests, traces, setup, native search paths, and retained workers. |
| I053 | Old epoch-1 process completed after B and was rejected. | Independently test generated source, compiled artifacts, diagnostics, and cache insertion for real obsolete backend output. |
| I054 | Old A remained selected through failed/interrupted B attempts. | Real extraction, translation, compilation, and server-preparation failures with explicit visible last-good model status. |
| I055 | B's complete file set omitted A-only `Legacy.lean`. | Actual Rust item/module/obligation deletion, reused Lean module names, and resolver checks in selected generation. |
| I105 | Writers killed with `SIGKILL` at nine controlled phases. | Stage-specific Cargo/rustc/Charon/Aeneas/Lake/Lean cancellation, descendants, pipes, locks, temp outputs, and escalation bounds. |
| I106 | Late logically cancelled child could not replace B. | Late diagnostics, progress, worker exit, request correlation, and reusable obsolete cache output in real transports. |
| I107 | No real shared single-flight build here; prior finite model has two consumers. | Multiple proof consumers of one actual build, individual cancel/failure, ownership counts, retry and failure fan-out. |
| I108 | One publication lock released after holder `SIGKILL`. | Multi-lock ordering/deadlock matrix across preparation, publication, cache, worker restart, and GC with pause/crash controls. |
| I109 | This suite injects process death but no resource exhaustion. | Bounded time, memory, disk, descriptor, and process-slot exhaustion with recovery and last-good preservation. |
| I110 | Fresh file-based reconstruction after worker kills and repeated cleanup. | Kill watchdog, Anneal process, and real build subprocess separately; reconstruct unsaved buffers/imports/outstanding requests and compare fresh oracle. |
| I111 | No edit-storm fairness measurement. | Batch/live load, rapid edits, slow document, several agents, and tail latency/starvation/queue policy. |
| I112 | Dropped/duplicate event control reconciled from selected files. | Real watcher and transport drop/reorder/disconnect, reconciliation timing and stale-query rejection. |
| I121 | Leased/unleased/killed readers distinguish safe delayed opens in fixture. | Actual Lean workers, pending queries, scratch forks, imported memory maps, later opens, and durable lease ownership. |
| I122 | Three crash/restart/GC cycles, idempotent second passes. | Longer service restarts, owner identity beyond process locks, expired RPC objects, abandoned scratch, and measured retained/reclaimed space. |

I052 is shown because path movement is an obvious but **unanswered** extension of the publication sequence; it is not part of the assigned ID set and this report does not mark it covered. All listed IDs remain partial or unexecuted at their full #3731 scope.

## Boundaries

- The fixture's `.olean` names are deliberately fake bytes. It cannot establish Lake trace coherence, Lean import success, declaration identity, compiler error behavior, or proof acceptance.
- `os.replace` of a symlink and advisory `flock` were observed on one APFS host. No `fsync` or directory-sync durability sequence was tested. Machine crash, power loss, Windows, and network filesystem behavior remain unknown.
- The manifest validator checks exact bytes and files, not semantic dependencies, assumptions, or whether the complete file set is sufficient for a Lean query.
- The worker and authority update are causally controlled by the parent. The fixture does not test two concurrently competing publishers changing authority, a malicious writer, or noncooperating readers. The authority file update is atomic but is not acquired under the same publication lock in this run; this schedule fixes its order with marker gates.
- The reconstruction policy deletes complete but unselected B directories. A different product might retain them for historical queries or cache reuse if it can prove identity and safe leases; this fixture measures neither benefit nor cost.
- The failed/cancelled old worker's result checks epoch and cancellation together, so their independent necessity comes from the separate finite-model mutants, not this OS-process trial.
- No real watcher, LSP, MCP, Charon, Aeneas, Cargo, Lake, or Lean server was driven by this report.

## Evidence

- `support/probe.py`, SHA-256 `9d4672d507216c233df5c58f41661843cdddd213f654bfeb6f08a10f676af098`, is the complete deterministic driver and child process implementation. It embeds all fixture source/fake artifact bytes, manifest rules, gates, locks, GC, and assertions.
- `support/results.json`, SHA-256 `c3ce28244872667263e01637784d7ab7563add6b0b7e763e1479f608c2eb9de0`, preserves every phase's selected manifest/file list, killed child exit, cleanup disposition, the late result, reader/lock outcomes, repeated restart cycles, and event-reconciliation state. Two executions on 2026-09-29 yielded the same JSON hash. Basis: **execution** on the stated host; the event-loss choice is **model input**.
- `anneal-3730-snapshot-capture-jobs-2026-09-29/REPORT.md` is the earlier APFS mixed-snapshot and fake-stage late-result control. `anneal-3730-fault-model-2026-09-29/REPORT.md` is the bounded guard-mutant model. `anneal-3730-charon-aeneas-boundary-2026-09-29/REPORT.md` records actual stale LLBC and partial Lean after failures. `anneal-3730-lake-writer-scale-v4-30-0-rc2/REPORT.md` records actual shared writable Lake writer outcomes. These have separate exact subjects and limits.
- [Issue #3731](https://github.com/google/zerocopy/issues/3731), body at the SHA-256 in `REPORT.json`, supplies the investigation scopes; it is an agenda, not a normative implementation contract.

## Revalidation

Set `ANNEAL_PROBE_SCRATCH` to an existing owned scratch directory and run `python3 support/probe.py` from this package. It writes only `support/results.json` outside its temporary directories. Check that all nine kill cases expose a valid selected A or B as listed, that the late old child is obsolete, that leased and unleased readers differ, that `SIGKILL` releases the lease and publication lock, and that repeated cleanup is idempotent. The JSON should match the retained result on the same host/tool conditions; if timestamps or platform strings change, compare semantic fields rather than assuming byte identity. To test a real Anneal design, substitute real Charon/Aeneas/Lake/Lean artifact families and reader processes while keeping the causal gates and verify exact captured imports/claims against a fresh oracle.
