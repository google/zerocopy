# Direct Lean RPC session expires without keep-alive

## Summary

One pinned Lean direct server accepted an interactive-goal context reference and dereferenced it before a 42.01-second idle interval. The client sent no keep-alive or other message during that interval. Dereferencing the same reference through the old session then returned `-32900 Outdated RPC session`; a new RPC connection to the still-open document returned interactive goals. This closes a narrow direct Lean idle-expiry cell that earlier release/reopen reports left unmeasured. It does not set an Anneal retention or historical-query policy.

## Applicability

The execution used `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) with direct `lean --server`, one physical `Proof.lean` URI, `LEAN_NUM_THREADS=1`, no Lake project/import/plugin, and an intentionally unfinished theorem with one `Nat` hypothesis. A single watchdog/file worker and one RPC session were used. A `Lean.Widget.getInteractiveGoals` response supplied an `InfoWithCtx` reference to the hypothesis type. `Lean.Widget.InteractiveDiagnostics.infoToInteractive` returned a popup before the idle interval. The host reported at least 25% free memory at preflight.

Lean's pinned `src/lean/Lean/Data/Lsp/Extra.lean` documents `$/lean/rpc/keepAlive` every 10 seconds and session drop after three missed periods. The 42-second wait is longer than that documented interval; the observed `-32900` is direct protocol evidence for this one session and host schedule. There was no explicit `$/lean/rpc/release`, document edit, close, or server restart in the decisive run. This addresses #3731 I044 and #3730 C08's expiry dimension only.

## Findings

| Step | Result |
| --- | --- |
| Open document and wait for diagnostics | Completed for version 1. |
| Connect RPC session and request interactive goals | Returned a `Nat` hypothesis info reference. |
| Dereference the reference before idle | Returned an interactive popup. |
| Wait 42.01 seconds with no client message | The open source text and server process were retained. |
| Dereference through old session | `-32900 Outdated RPC session`. |
| Connect a new RPC session and request interactive goals | New session ID and successful result on the same URI. |

Basis: **execution**, exact requests, responses, source hash, tool hash, interval, and 58 chronological wire events in `support/results.json`. The probe assigns client request IDs above 1000 because this Lean server emits low-numbered server-to-client refresh requests; that separation prevents a simplistic borrowed harness from matching an unrelated server request as a client reply. The offline checker confirms the old-session error and new-session success.

The protocol consequence is that an opaque RPC reference needs a live session and keep-alive policy; storing its wire payload alone cannot make it a durable proof-context handle. This is **derived** from the observed expiry and the pinned source's session contract. The earlier `anneal-3730-lean-server-soak-context-rpc-2026-09-29` report covers explicit release and replacement; this report adds idle expiry without either action.

## Boundaries

- Only one reference, one procedure, and one idle duration were tested. There is no measured exact expiry threshold, scale curve, memory reclamation, or multiple-session interaction.
- The probe did not compare a client that sends keep-alives, nor test whether the reference could survive import changes while a session is kept alive. The source states the keep-alive rule; the execution observes the no-message case.
- The new connection returned goals, but the old reference was not reused under the new session. Its `p` value is not a cross-session identity.
- No Lean proof was completed. A successful rich RPC call supplies local elaboration context, not batch acceptance.
- No Anneal worker, MCP envelope, source/import attestation, historical store, or lease-based GC was run.

## Evidence

- `support/probe.py`, SHA-256 `27b815dade438ae3f76b811d3ef80f8ff748b7e0f6cfc13c87ae6ad6eb9e5f89`, runs the bounded idle schedule and writes the raw result. It reuses the published direct/Lake framing harness definitions; that harness's SHA-256 is retained in the result.
- `support/results.json`, SHA-256 `4c7d2562d4b6203f9bc2a21b52a0af01d07a28f64ec6e266140d2bf3809e0257`, records the source text/hash, initial connection, rich reference, successful popup, exact idle seconds, stale-session error, new connection, successful rich query, and 58 wire events.
- `support/check.py` verifies the retained protocol outcomes without launching Lean. `support/work/Proof.lean` retains the exact source.
- Pinned Lean primary source: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `src/lean/Lean/Data/Lsp/Extra.lean`, `RpcKeepAliveParams` documentation and `RpcConnectParams`/`RpcCallParams` contracts. The earlier RPC lifetime and 24-edit soak packages are separate execution controls.

## Revalidation

Run `python3 support/check.py` for the retained result. To repeat with the same cached Lean binary, run `python3 support/probe.py`, wait for its 42-second idle period, and run the checker. The probe replaces only its own `support/work` and `support/results.json`. A future Anneal client should decide its keep-alive, release, expiry, and reconnection policy, then test that old references cannot be presented as current after worker/import/source changes.
