# Concurrent Lean servers with independent V1 workspaces and shared dependencies

## Summary

Two Lean 4.30.0-rc2 server processes served two separate copies of a small generated V1 workspace while sharing the same local immutable Aeneas/Mathlib dependency tree. Both maintained independent goal state across edits, and one could be stopped and reconstructed while the other remained live. Summed process-tree RSS peaked at 377,454,592 bytes in the sampled two-server run; system-reported free memory bottomed at 30% on an 8 GiB host. This extends the earlier bare-core four-server measurement to a generated-project dependency closure, but does not provide a production concurrency limit.

## Applicability

Each workspace had its own generated modules, project build directory, proof document, and Lean process. Both used the same read-only-in-practice Aeneas and Mathlib artifact tree under the local V1 toolchain. Each generated target was built with `lake --offline build Generated`; Lakefile Aeneas paths were relative and the dependency manifests resolved through the same local toolchain layout. The host was macOS arm64 with 8 GiB physical memory. Process memory was sampled with `proc_pidinfo` over each Lean process tree; system free memory came from `memory_pressure -Q`.

## Findings

### Independent workspaces shared imported products while retaining separate session state

Both servers returned `⊢ True` before their proof tactic and “no goals” after it. Each was edited from `trivial` to `exact True.intro`; after the edit, both again reported the pre-tactic goal and no post-tactic goals. The query transcripts are keyed by server and document URI, and no cross-workspace state appeared in the observed results.

Basis: execution.

### Graceful restart reconstructed one worker without stopping its peer

Worker A was shut down and launched as a fresh process against its current source while worker B remained live. Worker A again returned the expected open goal and solved state; worker B remained available until its later clean shutdown. The restart reconstructed document state from bytes and the same Lake environment. This is a graceful restart, not crash recovery or cancellation evidence.

Basis: execution.

### Measured process RSS and system memory pressure

At baseline the host reported 55% free memory. A sample with one generated-project server recorded 218,316,800 bytes of process-tree RSS and 47% free memory. With two loaded servers the RSS sum was 361,938,944 bytes and the system reported 30% free memory; after independent edits the sampled RSS sum peaked at 377,454,592 bytes, with 30% free memory. Restarting worker A while B stayed live recorded 164,610,048 bytes and 30% free memory. After both servers stopped, process-tree RSS was zero and free memory returned to 50%. Disk free at the two-server sample was approximately 56.1 GB decimal (52.3 GiB).

Summed RSS can double-count shared pages and is not unique physical footprint. The non-monotonic samples are snapshots, not evidence that adding a server reduces memory. The transcripts, C process-tree monitor, workspaces, and harness are retained under `support/`.

Basis: execution.

## Boundaries

Only two simultaneous sessions, one tiny theorem per workspace, and one shared local dependency closure were measured. No real zerocopy crate proof, Mathlib-scale active-file load, native plugin, sustained session, cancellation storm, forced crash, cross-host filesystem, or worker-count sweep was run. Aeneas warnings about pre-existing `sorry` declarations mean a successful Lake build is not a theorem-trust result. The 1.5 GiB guard from the earlier core-only server probe was not adopted as a production threshold; this run used a 3.5 GB test guard only to stop an unsafe local probe.

## Evidence

- Exact Lean source/release and V1 source identities are in `REPORT.json`.
- Raw JSON-RPC and resource transcript: `support/concurrency-transcript.json` (local checkout prefixes are replaced by `$ANNEAL_LOCAL_TOOLS`).
- Per-workspace Lake manifest, Lakefile, toolchain file, and generated Lean source: `support/worker-a/` and `support/worker-b/`.
- Harness and process monitor: `support/run.py`, `support/proc-tree.c`. The monitor was compiled with the host `clang`; no package install was required.

## Revalidation

Copy `support/worker-a/` and `support/worker-b/` into a scratch `workspace-root` and create the tested sibling `toolchain` link so each workspace's relative manifest paths resolve. With the matching local toolchain on `PATH`, run `lake --offline build Generated` in both workspaces. Compile `support/proc-tree.c` with host Clang, then run `python3 support/run.py --workspace-root WORKSPACE_ROOT --evidence-dir OUT --monitor PATH_TO_PROC_TREE`. The harness has RSS, memory, and disk guardrails and stops its server processes on exit. Repeat under other toolchains, larger projects, or higher worker counts before generalizing.
