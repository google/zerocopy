# Cooperative garbage collection with a live real-generation Lean reader

## Summary

In a disposable fixture containing the retained seven-file Charon/Aeneas/Lean A and B model families, a shared advisory lease kept unselected A available for a **fresh Lean process started after B selection and a GC attempt**. The later A import accepted the A proof and rejected the B proof, while a fresh B import did the reverse. After the A server and gated reader exited and the lease was released, GC removed A; a new A import failed because `Current` was absent, and B still accepted its proof. In the unleased control, GC removed A before the gated Lean process started, and both attempted A imports failed. The A document already open in a Lean server continued to report `no goals` in both cases, so its cached answer alone was not a retention oracle.

This observes a fixture-level cooperative `flock` protocol with real generated files. It does not establish Anneal's production lease ownership, GC implementation, or cross-platform behavior.

## Applicability

The A and B inputs are the actual retained `current.llbc`, `Current/Types.lean`, `Current/Types.olean`, `Current/Funs.lean`, `Current/Funs.olean`, `Current.lean`, and `Current.olean` families from `anneal-3731-real-generation-publication-v4-30-0-rc2`. A represents `golden_vertical` with `wrapping_add(1)`; B represents the regenerated `wrapping_add(2)` model. This report copies the exact input bytes and proof texts under `support/inputs/`; it does not rerun Charon or Aeneas. The A generation ID is `bc62fce58f5d7edca726224f9174b1bc41ed706a4ced9bca8bafaededd6da2a9`, and B is `620055318c21f7616fb671ce0c33f3f289b9a6f237d21aeddb48c0fa5c5d4e4b`. Each ID is SHA-256 of canonical JSON mapping the seven relative paths to their SHA-256 values. The lease lock is excluded from this model-family identity.

The experiment ran on the local macOS arm64 host with installed Lean `v4.30.0-rc2` (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, Python 3.14.7, the existing Aeneas Lean dependency paths, and `LEAN_NUM_THREADS=1`. No install or download was performed. The GC and reader paths were owned disposable directories under `/Users/josh/Codex/Meta/Data/20260929-142500-live-generation-gc-lease/run`.

## Findings

### Causal schedule and exact family identity

Each case copied complete A and B directories, selected A through a `current` symlink, checked the A old-proof-pass/new-proof-fail oracle, and opened an A proof document in a Lean `--server` process with `LEAN_PATH` pinned to the resolved A directory. The server returned `no goals`. A separate reader wrapper then paused **before starting Lean**. The parent replaced the selected symlink with B, ran fresh B old-proof-fail/new-proof-pass checks, invoked GC in another process, and only then released the wrapper. Thus the wrapper had not made an in-flight import or file-open syscall at the gate. Its two `lean --json` calls began after the GC decision and imported through the pinned A path. All exact selected-family and proof-source hashes, process IDs, commands, return codes, streams, and raw LSP messages are in `support/results.json`. Basis: **execution**.

The old proof is `golden_vertical.inc 0#u32 = .ok 1#u32`; the new proof changes the result to `.ok 2#u32`. Passing checks print axioms `[propext, Classical.choice, Quot.sound]` and contain no `sorryAx`. These are discriminator checks for this retained model pair, not a proof of the Rust-to-Lean translation. Basis: **execution** plus retained source bytes.

### Shared lease retains A for a later import

In the leased case, the parent acquired `LOCK_SH` on `generations/A/lease.lock` and kept it for the lifetime of the A server and gated reader. After B became selected, GC process 12657 attempted nonblocking `LOCK_EX`, failed to acquire it, recorded `deferred-lease-held`, and left all seven A files intact. The released reader wrapper (PID 12654) then started fresh Lean processes under pinned A: the old proof passed, the new proof failed, and its exact family hash remained A. That old result is explicitly labeled **stale relative to selected B**. The open A server also returned `no goals` after B selection and GC, with its A generation ID and stale status recorded. Basis: **execution**.

After the reader had exited, the server exited cleanly and the parent released `LOCK_SH`. A second GC process (PID 12670) acquired `LOCK_EX`, removed A, and reported 44,471 logical file bytes reclaimed. A new A import then failed with `unknown module prefix 'Current'`; a fresh B import still passed its B proof. Logical bytes are the sum of file sizes, including the zero-byte lock file, and are not a physical disk-space or APFS allocation measurement. Basis: **execution**.

### Unleased control and cached-document limit

In the unleased case the same A server document was open and a new reader wrapper was gated before Lean start, but no shared lock was held. GC process 12688 acquired `LOCK_EX` after B selection and removed A, reclaiming 44,471 logical file bytes. When released, wrapper PID 12684 started fresh Lean processes; both A-path proofs failed with `unknown module prefix 'Current'`. Fresh B import still passed. The previously opened A server nevertheless returned `no goals` after A removal. This separates its cached document response from the later-open path property that the lease protects. The open A answer is labeled stale relative to B, and the missing A import is not assigned a generation ID. Basis: **execution**.

The parent-held lease is a cooperative proxy for the A reader cohort. The fresh wrapper itself did not acquire a lock. The result therefore establishes that a held shared lock and a GC process honoring it can retain this complete real family until a later import, and that omission permits a later import to fail. It does not establish a production ownership or handoff protocol for independently spawned Lean workers.

## Boundaries

- **Not examined:** Anneal V2 publisher or GC code, Lake archive ownership, editor/MCP calls, scratch forks, worker restart, independent leases per spawned process, contention among several GC processes, or crash recovery during deletion.
- **Not established:** that an already open Lean document will continue to answer every query after unlink, or that any such answer is current. This run observed one `plainGoal` response per case after publication/GC.
- **Not established:** memory-map lifetime, page residency, physical disk reclamation, power-loss durability, Windows or network filesystem locks, and behavior when any participant ignores advisory locking.
- The model pair was fully prepared before the pointer change. This report tests GC after selection, not generation staging or publication atomicity; that separate schedule is retained in `anneal-3731-real-generation-publication-v4-30-0-rc2`.

## Evidence

- `support/inputs/A/` and `support/inputs/B/` contain the seven source/compiled artifacts; adjacent manifests and paired proof texts carry the producer hashes and source oracles. Their exact inventories and generation IDs are recomputed by `support/check.py`.
- `support/probe.py` (SHA-256 `5851d5d0902ea92faa110ffee0442e81af02f5f8fcc78687cedf5d0403eb4c47`) contains the lease, gate, selection, fresh Lean, server, and GC schedule. `support/publication_probe.py` (SHA-256 `d2a3d1c90aaf2aacb4d3f06ae4f4d645d2bc7c181151a87cfb284a0c56c635e8`) is a copied helper from the preceding real-publication report for Lean environment and LSP transport. `support/results.json` (SHA-256 `f13e4f85c77944f184e87f0606adbaa66b39f8dd13a4d23f7eb292c2bf0dd6fd`) preserves raw execution records including the gate wrapper PIDs, GC PIDs and lock outcomes, all selected and pinned family hashes, proof streams, `no goals` JSON-RPC messages, lease acquire/release flags, and logical bytes.
- The executable fixtures ran on 2026-09-29. `python3 support/check.py` (SHA-256 `2d48b6a69a71c8937b7230e213b4d3a42d9704a60385468d9e7a6b34dea0c99e`) performs an offline consistency check of the retained inputs and result record. It checks exact A/B files and IDs, proof text hashes, decisive old/new oracles, raw error/axiom strings, LSP goal messages, gate and PID relationships, lock decisions, and byte accounting. A passing check validates this evidence package; it does not verify Anneal product behavior.

Issue alignment: this narrows #3731 I121 and #3730 J11 with a real generated-family, gated later-open GC experiment. Production lease/GC integration remains open.

## Revalidation

Run `python3 support/check.py` from this package for the retained offline evidence. To repeat the live experiment with installed tools, set `I121_SCRATCH` to an owned disposable directory and run `python3 support/probe.py`. The probe replaces only its two named case directories within that scratch path and writes `support/results.json`; compare outcomes and hashes rather than PIDs or absolute paths. For another toolchain or model family, regenerate both complete seven-file families and rerun the same gate schedule and old/new proof matrix. Keep the wrapper paused before Lean starts when testing later path opens.
