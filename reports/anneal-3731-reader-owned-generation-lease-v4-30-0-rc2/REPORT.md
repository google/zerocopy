# Reader-owned generation leases across a worker crash

## Summary

Two independently spawned readers held their own shared leases on a retained real generated-model family. After selection changed from A to B, garbage collection deferred through one reader's forced death and the other reader's later Lean import. It reclaimed A only after the last reader exited. The published [v20 audit](../anneal-3730-3731-final-coverage-audit-2026-09-29-v20/REPORT.md) had used a parent-held proxy lease; this is a distinct ownership and crash-lifetime cell for [#3731 I121](https://github.com/google/zerocopy/issues/3731) and [#3730 J11](https://github.com/google/zerocopy/issues/3730).

## Applicability

The fixture reuses the seven exact Charon LLBC, Aeneas Lean source, and compiled Lean files per A/B generation from [the prior GC package](../anneal-3731-real-generation-gc-lease-v4-30-0-rc2/REPORT.md). It also reuses that package's old and new proof text and Lean environment helper. The A generation ID is `bc62fce58f5d7edca726224f9174b1bc41ed706a4ced9bca8bafaededd6da2a9`; B is `620055318c21f7616fb671ce0c33f3f289b9a6f237d21aeddb48c0fa5c5d4e4b`. Each is SHA-256 of canonical JSON mapping the seven relative file paths to their SHA-256 values. The zero-byte advisory lock is excluded. The checker recomputes every hash from the retained inputs.

At `reference@c89f1410d4f1cfbd9b654ea5268b38f5c81e115e`, the [probe](support/probe.py) created disposable A/B copies under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/reader-owned-lease-run/two-readers`. It selected A through a `current` symlink. Two separately spawned wrappers each opened A's `lease.lock`, acquired its own `flock(LOCK_SH)`, recorded its PID and exact A family, then paused before starting Lean. The parent never opened or held a lease descriptor. It atomically selected B by replacing the symlink and invoked a separate GC process. GC checks the selected family and tries nonblocking `LOCK_EX` on A's lock before deleting A.

The parent then sent `SIGKILL` to reader one, waited for its exit, and retried GC while reader two remained paused with its own lock. It released reader two to start fresh `lean --json` processes through the pinned A path, checked old and new proof claims, and had reader two pause again while still holding the lease. GC was retried at that point. Finally reader two exited and released its lock, GC was retried, and a fresh B proof was checked. Lean was the already installed `v4.30.0-rc2` binary, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; no source or dependency was installed or downloaded. The source inputs were retained; Charon and Aeneas were not rerun.

## Findings

Reader processes 15964 and 15965 acquired separate shared leases before B selection. GC process 15966 deferred while both were present. After reader 15964 was killed and reaped with status `-SIGKILL`, GC process 15967 still deferred because reader 15965 held its own lease. Reader 15965 then started fresh Lean imports through A: the A old proof passed without `sorryAx`, and the B new proof failed with `Tactic rfl failed` and a `sorryAx` diagnostic. That A result is **stale relative to selected B**, although valid against retained A. GC process 15973 again deferred while reader 15965 waited after the import. After it exited, GC process 15974 acquired the exclusive lock and removed A; its seven files accounted for 44,471 logical bytes. A fresh B proof still passed without `sorryAx`.

The decisive GC sequence is `deferred-reader-lease`, `deferred-reader-lease`, `deferred-reader-lease`, `removed`. Basis: **execution** of the retained fixture and **derived** inference from the process-specific lock ownership and event order.

## Boundaries

This is a component experiment, not an Anneal V2 implementation or closure of I121/J11. It narrows the independent-worker and crash-lifetime component. It does not show Anneal-owned lease acquisition, a product GC, pending-query or scratch-fork retention, replay identity, post-crash reconciliation by a supervisor, power-loss durability, or other filesystem platforms. `flock` is advisory; a reader or collector that ignores the protocol can still race.

## Evidence

The raw [result record](support/results.json) contains PIDs, nanosecond event times, commands, return codes, standard streams, per-file hashes, selected-family snapshots, lock outcomes, and all Lean JSON output. The timestamps order acquisition, B selection, the first GC, reader-one exit, second GC, reader-two Lean completion, third GC, and final GC. The [offline checker](support/check.py) verifies those relationships, exact inputs and generation IDs, proof source hashes and diagnostics, distinct PIDs, and logical byte accounting. It passed on the retained package. The source package and Lean binary are pinned in `REPORT.json`; the live observation was made on 2026-09-29.

## Revalidation

From this `reference` checkout, run `python3 reports/anneal-3731-reader-owned-generation-lease-v4-30-0-rc2/support/check.py` for the retained offline evidence. To repeat the live schedule with the installed Lean and retained inputs, set `I121_READER_SCRATCH` to an owned disposable directory and run `python3 reports/anneal-3731-reader-owned-generation-lease-v4-30-0-rc2/support/probe.py`. The probe replaces only its `two-readers` child directory and rewrites `support/results.json`; compare hashes and outcomes rather than PIDs or absolute paths.
