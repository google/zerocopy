# Direct Lean cancellation and private Cargo descendant control for H09

## Summary

A direct Lean 4.30.0-rc2 `lean --server` run returned JSON-RPC error `-32800` for a cancelled `textDocument/waitForDiagnostics` request. A later request on the same open document succeeded, and fresh batch Lean accepted the proof. The cancellation response arrived about 3.91 seconds after `$/cancelRequest`, near the delayed elaboration's completion; this is evidence of processed cancellation and result suppression, not an observed saving in compute time.

A separate Cargo 1.98.1 control cancelled one private build process group while another private build was active. The cancelled group contained Cargo, its build script, and `/bin/sleep`; after SIGTERM no members remained. The peer was still running immediately after that cancellation, completed, and produced its library. The cancelled build had no final library at the check point and succeeded on retry. No Anneal scheduler, editor adapter, projection, shared job, or upstream task ownership protocol was involved.

## Applicability

- Host: macOS 26.6.2, arm64. Preflight reported 46% system-wide free memory and 53,787,795,456 free disk bytes. This run had one Lean server and at most two tiny Cargo builds; it did not measure peak RSS.
- Lean: release binary `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; direct `lean --server` with one private `LEAN_PATH` and `LEAN_NUM_THREADS=1`.
- Cargo: Homebrew `cargo 1.98.1 (797e8a9bc 2026-08-05)`, executable SHA-256 `778478868dbfe74960e49329bb5813d2f5ba95c8bfb1f37cd626c62cb26a214a`; local `rustc 1.98.1 (48a229cea 2026-09-01)`. Two separate package roots and target directories, `--offline`, one Cargo job per build. No dependencies, downloads, or installs.
- The Lean fixture has a custom tactic that calls `IO.sleep 3000` then `trivial`; batch verification exits 0. The Cargo build script spawns `/bin/sleep 5`, records its and the child's PIDs, then waits.

## Findings

### Lean processed a cancelled request but continued elaboration

The client sent `didOpen` for `Slow.lean`, request ID 2 for `textDocument/waitForDiagnostics`, then `$/cancelRequest` for ID 2 at transcript time 0.4176 seconds. The server returned `{"error":{"code":-32800,"message":""},"id":2}` at 4.3291 seconds. It then returned success for a new wait request ID 3 on the same URI/version; diagnostics remained empty, fresh `lean --json Slow.lean` exited 0, and the server exited cleanly with no process-group members left.

Pinned Lean source inspection explains the narrow mechanism: `Lean/Server/Watchdog.lean` forwards cancellation for a routed request to its file worker, and `Lean/Server/FileWorker.lean` marks the pending request cancelled and can emit `requestCancelled` rather than a partial result. The transcript provides the actual `-32800` response. Because that response arrived after the delayed command continued, it does not establish early interruption of a running tactic, resource reclamation, or that every Lean RPC behaves this way.

Basis: **execution** in `support/results.json`; **source inspection** of the pinned Lean 4.30.0-rc2 `Watchdog.lean` cancellation handler and `FileWorker.lean` pending-request/response handlers.

### Cargo process-group cancellation did not terminate a separate peer

At the signal point, the victim process group contained Cargo PID 87527, build-script PID 87549, and sleep PID 87550. The peer group contained Cargo PID 87553, build-script PID 87568, and sleep PID 87569. Sending SIGTERM to the victim group yielded Cargo exit `-15`; after process collection, neither group had residual members. Immediately after victim exit, the peer was still running with its build script and sleep child. It later exited 0, and its final library existed. The victim's final library was absent before retry; a fresh offline build exited 0 and produced it.

This is an independently owned process-group control. It does not test the harder case where two editor requests consume one shared regeneration job: process-group isolation alone cannot decide whether that shared job should continue after one request is cancelled.

Basis: **execution** in `support/results.json`; exact fixtures in `support/fixture/`.

## Issue alignment and residuals

- **#3730 H09 / #3731 I105:** Direct LSP cancellation produced an observable cancellation error, and a private upstream Cargo stage plus descendants could be terminated and retried. The editor-to-projection-to-Anneal-scheduler mapping remains unimplemented here; there is no real cross-stage request identity, ownership reference count, or cancellation of a generated-workspace job.
- **#3731 I007:** The peer result shows only independent process-group isolation. The policy for a shared job with two consumers, one abandoning and one continuing, remains untested without a scheduler or equivalent ownership layer.
- **#3731 I107:** This was two independent, private target directories with no shared cache-miss storm. It does not test high-parallel shared artifact-cache writers or producer cancellation. That item remains open.

The experimental `$/cancelRequest` is a direct protocol notification. There was no editor cancellation gesture, Rust-to-Lean projection, MCP request, Charon/Aeneas stage, Lake build, or Anneal publication. The Cargo process group was created and signalled by the Python harness, not by Anneal. A different tactic or server workload may react at a different cancellation point.

## Evidence and revalidation

- `support/probe.py` — bounded replay harness using the existing binaries only; it refuses to overwrite an existing `support/work/` directory and enforces free-memory and free-disk preflight floors.
- `support/results.json` — time-ordered raw JSON-RPC messages, process-group snapshots, exit states, marker PIDs, output state, retry, tool hashes, and command output. Local work and binary paths are scrubbed.
- `support/fixture/` — retained Lean and Cargo source bytes; compiled outputs were removed after the run.
- `support/check.py` — offline assertions over the fixture hashes, JSON-RPC ordering and cancellation code, continued Lean service, Cargo descendant/peer state, and retry.

Run `python3 support/check.py` from the package directory. For a fresh run, set `LEAN_BIN` to the pinned executable and optionally `CARGO_BIN`, then run `python3 support/probe.py` in a copy of this package. The replay creates only `support/work/` and rewrites `support/results.json` in that copy. Compare the cancellation code, request ordering, process-group cleanup, and retry; timing and PIDs are observations, not stable replay invariants.
