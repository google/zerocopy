# Early prefix edit and cancellation during direct Lean elaboration

## Summary

In one pinned Lean server run, an unsaved early definition edit entered a deterministic elaboration gate before its suffix commands. The client then sent a newer early edit, canceled the older diagnostics wait, and released the gate. The older wait returned `-32800`; only the newer version's suffix markers ran, and its goal query selected `⊢ generated = 3`. The unchanged leading marker did not rerun. This adds a bounded combined edit/cancel observation to #3731 I036; it does not establish a general cancellation guarantee or Anneal's generated-context behavior.

## Applicability

**Execution** used direct `lean --server` from the cached Lean 4.30.0-rc2 arm64 macOS release, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. One physical `Active.lean` URI stayed open in one server; its on-disk bytes stayed at valid V1 while unsaved text advanced through versions 1, 2, and 3. `LEAN_NUM_THREADS=1`. The fixture imports `Lean` only and uses `run_cmd` file side effects for a causal gate and command-execution markers. This is a tiny direct Lean fixture, not an Anneal projection or Lake/import graph.

The probe first ran fresh batch controls for V1 (`generated = 1`, target 1) and V3 (`generated = 3`, target 3). Both exited 0. It cleared those batch marker effects, opened V1 in the server, and waited for diagnostics. V2 changed the early `generated` definition to 2, inserted a blocking `run_cmd` gate immediately afterward, and retained target 1. Once the gate file appeared, the client sent V3 (definition and target 3, with the gate removed), sent `$/cancelRequest` for the pending V2 `waitForDiagnostics`, released the gate, and waited for V3.

## Findings

The command marker ledger after V1 was `A B1 C1`. V2 reached the gate with that ledger unchanged. The edit and cancel messages were sent before the gate release. After both waits replied, the ledger was `A B1 C1 B3 C3`; `B2` and `C2` did not appear at any sampled ledger point or in the retained final file. V2's wait returned JSON-RPC error `-32800`, V3's wait returned `{}`, V3's diagnostics were empty, and `plainGoal` at line 11 column 37 returned one goal, `⊢ generated = 3`. The server shut down with exit 0. **Basis: execution**, ordered `send`, `recv`, `gate_entered`, `edit_and_cancel_sent`, `gate_released`, `wait_replies`, `final_goal`, and `server_stop` events in `support/transcript.json`.

The unchanged `A` marker executed once in the server run; the V3 suffix markers executed after the early definition changed. This is evidence of a reused leading command and a recomputed suffix in this fixture. The missing V2 suffix shows it did not execute by the time V3 finished and the server exited. The result does not isolate whether the older worker was stopped by the V3 edit, the explicit `$/cancelRequest` on its wait, or both. The returned `-32800` is a cancellation result for the wait request, not proof that Lean canceled every internal computation at that moment. The gate itself is a synthetic `run_cmd` side effect and is not representative generated code. **Basis: execution plus derived interpretation of the marker and wire order.**

## Boundaries

- **Not established:** an exact internal worker cancellation point, universal absence of late stale side effects, or a transport guarantee for other request methods. The gate was released promptly and the server stopped after V3's confirmed result.
- **Not examined:** actual Anneal Rust-to-Lean generated wrappers, source maps, large imports, Lake launch, persistent model artifacts, multiple concurrent proof files, production scheduling, or broad prefix-reuse distributions. I036 remains partial.
- **Not examined:** theorem proposition fidelity under wrapper context (I037) or model/import dependency granularity and retention (I056).
- **Not established:** performance scaling. The sampled server process-tree RSS peaked at 1,388,740,608 bytes below the 1.5 GB guard; the sample may miss between-sample peaks or count shared pages more than once. The 2.63-second script wall time is one run, not a latency estimate.

## Evidence

- `support/work/V1.lean`, `V2.lean`, and `V3.lean` preserve exact source variants with relative gate/marker paths; `Active.lean` preserves V1 on disk. Their SHA-256 values are in `support/transcript.json` and asserted by `support/check.py`. `support/work/markers.txt`, `gate.entered`, and `gate.release` retain the final side effects.
- `support/probe.py` drives the direct server and writes the 69-event `support/transcript.json` (SHA-256 `09234ebeb3fbd993302ee405588d51d470ec73a5ec196572aee7e570b5817853`). It tokenizes local work and binary paths in the transcript. The probe used a 1 GB free-disk preflight, 45-second outer alarm, 10-second gate-entry deadline, 20-second reply deadline, 15-second batch deadlines, 5-second shutdown deadline, 1.5 GB sampled server process-tree RSS cap, and process-group SIGKILL fallback. No install or download occurred.
- `support/check.py` passed offline on 2026-09-29, asserting the binary/source identities, batch controls, gate/edit/cancel/release order, exact marker ledger, wait replies, V3 goal, resource cap and clean exit.
- The [wrapper context and prefix report](../anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/REPORT.md) independently records sequential suffix re-elaboration after different command edits. The [protocol race report](../anneal-3730-lean-protocol-races-v4-30-0-rc2/REPORT.md) separately records gated request cancellation and old replies. This report combines an early prefix edit, active gate, newer edit, cancellation, and execution markers in one bounded run.

## Revalidation

Run `python3 support/check.py` to validate retained evidence without starting Lean. To rerun, use the pinned cached binary with `LEAN_BIN=/absolute/path/to/lean python3 support/probe.py`, then run the checker. The probe recreates only this package's `support/work` variants and rewrites this package's transcript; it removes its own old gate and marker files first. Compare the executable hash before interpreting a replay as the same subject. Repeat with multiple gated interleavings and actual generated wrappers before deriving a production invalidation or cancellation policy.
