# Live Lean import after an OLean artifact is removed

## Summary

An already-open Lean server document continued to return its prior goal after its imported `Dep.olean` was unlinked. A second document opened in that same server after the unlink, and a document opened in a fresh server, both reported `unknown module prefix 'Dep'` and returned no goal. A fresh `lean --json` process also failed while the OLean was missing, then passed after exact artifact reconstruction. The experiment identifies a live-reader retention boundary for #3731 I121; it is a direct Lean component probe, not an Anneal lease or garbage collector.

## Procedure and evidence

The pinned Lean 4.30.0-rc2 binary SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. In an isolated temporary root, `lean -o Dep.olean Dep.lean` compiled `def depValue : Nat := 7`. `Proof.lean` imported `Dep` and proved `depValue = 7` with `decide`. `LEAN_PATH` contained only that temporary root. The script first ran a fresh batch check, then opened `Proof.lean` in a direct `lean --server` LSP process, awaited diagnostics, and queried `$/lean/plainGoal` at the tactic position. It unlinked `Dep.olean` while that server stayed live, queried the same open document, and opened a second importing document. It subsequently used a fresh batch process and fresh server while the OLean was absent, rebuilt the OLean, and checked batch again. All commands and requests were bounded to 18 seconds, and both servers shut down with exit 0.

| Observation | Exact result |
| --- | --- |
| Batch before unlink | Exit 0; no JSON diagnostics. |
| First open server document | No diagnostics; goal `⊢ depValue = 7`. |
| Same document after unlink | Same goal `⊢ depValue = 7`. |
| Second document in same server after unlink | Import diagnostic `unknown module prefix 'Dep'`; goal result `null`. |
| Fresh server and fresh batch after unlink | Same missing-import diagnostic; server goal `null`, batch exit 1. |
| Batch after rebuilding OLean | Exit 0; restored OLean SHA-256 equals the original. |

`support/results.json` retains the full client/server LSP messages, diagnostics, batch output, artifact hashes, and server exits. `support/check.py` validates the retained observations offline. The probe script SHA-256 is `d703178dad96db715f3ea59cac50c536ffa830a15fa1f065162c89a4df9edd26`; result SHA-256 is `921c2f7911f7b7f947da9cb0918c954c51be8b5cd662796ebe56c6cf25be3a74`.

## Interpretation and limits

The unchanged goal on the already-open document is **cached elaboration state**, not evidence that a new import can still consume the unlinked artifact. The second document and fresh process are the negative controls. The result demonstrates why preserving already-running queries alone cannot establish safe artifact reclamation: later opens need an importable artifact or an explicit reconstruction path. It does not prove an OS mapped-file lifetime or a Lean-internal reference count; neither was measured.

I121 remains partial. The fixture has no Anneal generation leases, pending queries across a pointer swap, scratch forks, replay log, or GC policy. It does not test concurrent unlink during an actual import syscall, crash recovery, Lake cache objects, or another platform. The prior `anneal-3730-generation-recovery-2026-09-29` and R26 controlled source-generation path/pointer retention; this package supplies a direct compiled-artifact/live-Lean counterpart.

## Revalidation

Run `python3 support/check.py` for the retained evidence. Running `python3 support/probe.py` repeats the tiny experiment with the already-cached Lean binary and rewrites only this package's `support/results.json`; copy the report package first if retaining this acquisition. Set `ANNEAL_PROBE_SCRATCH` to an owned existing scratch directory if needed. No dependency is downloaded or installed.
