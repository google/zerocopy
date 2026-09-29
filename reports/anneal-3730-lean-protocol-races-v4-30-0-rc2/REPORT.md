# Lean goal-query version race with a tactic gate

## Summary

At Lean 4.30.0-rc2, a client can receive a successful version-1 diagnostics wait and a version-1 goal **after it has sent** a version-2 edit. Once version 2 completes, a `waitForDiagnostics` request specifying version 1 still succeeds, and `$/lean/plainGoal` returns version-2 goals even when its `textDocument` object includes `version: 1`. The `plainGoal` request schema has no version field. A separate controlled cancellation returned JSON-RPC error `-32800` **before any edit** in three runs. Thus neither a successful old wait nor an unversioned goal response can be used alone as an exact-snapshot result.

This is a direct Lean protocol result, not a test of Anneal, Lake, Aeneas, or an MCP adapter. The causally gated overlap shows what a client must fence; it does not prove Lean processed the edit before issuing the old reply.

## Applicability

The fixture used the local release binary for `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` on arm64 macOS, invoked as direct `lean --server` with `LEAN_NUM_THREADS=1`, no Lake project, no imported user module, no plugin, and one open file. The binary SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The source checkout had the same Git revision. Batch controls used that same binary, cwd, and file path. The gated overlap and independent cancellation control each ran three times on 2026-09-29.

The V1 source proves `True` after a `run_tac` tactic that writes `gate.entered` and blocks until the harness writes `gate.release`. V2 replaces the proof with a `False` goal and `exact ?_`. SHA-256: V1 `a84abfa4112f89dbfe60e1ed52d8e418d91323e79fcb7c0da52eb84091900331`; V2 `d87b07267df747133d8f19ecd92fe84aa367c47966d090a9b4ff1a5afd3b5d7a`.

## Findings

### Causally ordered protocol observations

The script starts server A, opens V1 at document version 1, and sends wait request 10. Only after the executing tactic creates `gate.entered` does it send goal requests 20 and 23, then `didChange` to V2, then cancellation of request 23, then release the tactic gate, then wait request 11 for version 2. It records each outbound/inbound JSON-RPC message and monotonic elapsed time. The gate establishes real elaboration overlap with the edit. It does **not** establish whether request 10 or 20 was internally completed before Lean handled the edit.

In each of three runs:

| Response | Request and observed result |
| --- | --- |
| 10 | V1 `waitForDiagnostics` returned `{}` after the client sent V2. |
| 20 | V1 `plainGoal` returned `⊢ True` after the client sent V2. |
| 23 | In-flight V1 `plainGoal` at a later position returned `-32800` after both an edit and explicit `$/cancelRequest`; this run alone cannot attribute the cancellation. |
| 11 | V2 `waitForDiagnostics` returned `{}` after version-2 error diagnostics were published. |
| 12 | A *new* wait specifying version 1, sent only after V2 completed, returned `{}`. |
| 21 and 22 | `plainGoal` after V2 completion returned `⊢ False` for both supplied `textDocument.version: 1` and `version: 2`. |

Basis: **execution**. Exact chronology and payloads are in `support/transcript-run{1,2,3}.json`. For example, in run 1 the gate appeared at 3680 ms; the edit was sent at 3680 ms; responses 10, 20, and 23 arrived at 3694–3695 ms; V2 wait response 11 arrived at 3890 ms. All three runs gave the same qualitative result, with different timings.

A response 20 carrying `⊢ True` was a valid old-snapshot observation when requested. It became stale for a *latest snapshot* query once the client sent V2. An adapter that attaches its current V2 label to that unversioned response would misattribute it. The successful request 12 gives a deterministic negative control against treating `waitForDiagnostics(version=1)` as proof that the current snapshot is version 1. The matching responses 21 and 22 give a deterministic negative control against treating an extra `version` key in `plainGoal.textDocument` as a version constraint. The schema in [`Extra.lean`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L100) extends `TextDocumentPositionParams` without a version, while the wait documentation explicitly says it accepts diagnostics from a version **greater or equal** to the requested one; the [handler](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L466) checks `p.version ≤ doc.meta.version` and waits on reporter plus command snapshots.

### Cancellation separated from edit invalidation

The separate `support/cancel-control.py` uses the same tactic gate, sends request 23 at a later proof position, sends `$/cancelRequest` for 23, and then releases the gate. It waits for response 23 **before sending any edit**. In three runs, response 23 was error `-32800`; event order, rather than rounded millisecond timestamps, establishes that it preceded the edit. This is **execution** evidence for explicit cancellation in this request state. It does not establish cancellation behavior for requests that have already completed or for every other method.

### Batch, diagnostics, and fresh-process controls

Batch `lean --json` over saved V1 exited 0 with no diagnostics. Batch over saved V2 exited 1 with two errors: a placeholder could not be synthesized and `⊢ False` remained unsolved. The server's version-2 error notification reported the same substantive two errors, with LSP zero-based ranges instead of batch one-based positions. A fresh server B opened the same V2 text at version 1, reused request IDs 10 and 20 on its own transport, and returned V2 errors and `⊢ False`. This is a reconstruction control for the **current V2 source only**; it is not reconstruction of a complete Anneal generation or import environment.

Empty diagnostics notifications appeared before V2's error notification. An empty version-2 notification also appeared after the client sent `shutdown`, before the shutdown reply. Therefore neither the first empty notification nor simply the last observed notification across a whole server session is a reliable whole-file success signal in this trace. The V2 goal is locally present even though elaboration produced errors; a goal payload alone does not establish theorem acceptance. These claims are **execution** results from the three transcripts.

### Result envelope suggested by this evidence

A minimal Anneal adapter should bind each request at submission to `(server incarnation, document URI, local document generation, exact source hash, requested position, intended import/preparation generation)`. After the wait and after the goal response, it should compare that binding against its current state and return either the bound historical result under an explicit historical contract or a stale/cancelled status. It must separately carry completed diagnostics and batch/whole-file verification status. This is a **derived design requirement** from the observed race and Lean's version semantics, not an implemented or proven Anneal contract. The experiment supplies no worker-incarnation token directly from Lean; a client must manage it through its own process/session lifecycle.

### Backlog coverage and remaining deltas

| Issue #3731 item | Evidence here | Residual question |
| --- | --- | --- |
| I041 exact-version goals | Controlled old/new race and ignored extra version field | Implement and prove client fence; test more edit orderings and snapshot-specific documents. |
| I042 readiness | Wait semantics, provisional empty diagnostics, completed V2 errors | Separately delay imports/asynchronous tasks and classify permanent setup failure. |
| I045 worker/request incarnation | Fresh process reuses URI/version/request IDs without confusion on separate transport | Delay a response across actual worker replacement and test RPC object lifetime. |
| I046 failed elaboration | V2 has errors plus a readable unsolved goal | Test valid proof before/after syntax errors, timeouts, and partial files. |
| I047 historical query | Old goal delivered after latest edit and old wait succeeds against newer document | Retain/reconstruct old snapshot and measure cost. |
| I129 goal versus verification | V2 goal and diagnostics differ in meaning; V1 batch acceptance control | Test admitted declarations, obligation coverage, and stale model claims. |
| I134 real concurrency | Tactic-file handshake puts edit inside in-flight elaboration and records wire order | Add server-side instrumentation to order edit handling against response production. |

Existing corpus reports cover the source-level RPC lifecycle, direct-server imported artifact staleness, and small concurrent servers. This report adds an executed causal overlap and repeatable negative controls. It does not close I043–I044 or I048–I055: tactic-position grids, RPC reference expiration, environment attestation, Lake launch-mode refresh, transitive imports/plugins/options, complete-generation publication, late generation completion, failure fallback, and output-set shrinkage still require their own fixtures.

## Boundaries

- **Not examined:** actual Anneal V1/V2 or MCP behavior, Lake setup, generated Aeneas modules, plugins, transitive imports, worker-only restart, interactive RPC objects, server crash, multi-client transport sharing, and filesystem publication races.
- **Unknown:** whether old request 20 was computed before or after Lean processed `didChange`. The transcript proves client-visible delivery after the edit was sent, not internal execution order.
- **Not established:** universal batch/server equivalence. The two source variants match on substantive diagnostics in this bare fixture only. Batch has no cursor-goal oracle.
- **Not established:** cancellation correctness for all request states. Isolated request 23 returned `-32800` before edit in three runs; other races can finish before cancellation takes effect.
- **Not established:** source-level claim or obligation coverage from V1's successful theorem. No Rust-side model, proof coverage, or trusted-boundary check was present.

## Evidence

- Retained executable probes: [`support/probe.py`](support/probe.py) for edit overlap and [`support/cancel-control.py`](support/cancel-control.py) for cancellation before edit. Both write source variants, open direct Lean servers, implement the tactic-file handshake, record raw message payloads, and execute batch controls.
- Three overlap transcripts: [`run 1`](support/transcript-run1.json), [`run 2`](support/transcript-run2.json), [`run 3`](support/transcript-run3.json). Three cancellation-control transcripts: [`run 1`](support/cancel-control-run1.json), [`run 2`](support/cancel-control-run2.json), [`run 3`](support/cancel-control-run3.json). Paths to the local fixture and binary are replaced with `$WORK` and `$LEAN_BIN`; message order and elapsed times remain intact.
- Lean primary source: [`Extra.lean` wait and plain-goal schemas](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Data/Lsp/Extra.lean#L37); [`RequestHandling.lean` wait implementation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/FileWorker/RequestHandling.lean#L466); [`Watchdog.lean` cancellation forwarding](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1307).
- Invocation: `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py` from the report package or any cwd. The script stores its fixture under `support/work` and uses the same binary for `--server`, `--json`, and `--version`. It requires Python 3 and the installed Lean release.

## Revalidation

Replay both scripts with the intended pinned binary and compare the `subject` event before interpreting outcomes. For the overlap probe, require `gate.entered` before the edit, V1/V2 batch controls, responses 10/20/23/11/12/21/22, and fresh-server responses 10/20. For the cancellation control, require `-32800` for request 23 before the edit event. Preserve every notification because provisional diagnostics matter. On a changed Lean revision, treat changed ordering or cancellation outcomes as new evidence and inspect both the wire trace and source implementation before changing the adapter contract.
