# Revalidation

For a future Lean release, resolve the exact Lean commit selected by the toolchain. Diff the protocol overview and the server/RPC files listed in `EVIDENCE.md` for:

1. the open-document rule and worker process topology;
2. `PlainGoalParams`, `$/lean/plainGoal`, and `Lean.Widget.getInteractiveGoals`;
3. the RPC connect/call/session structures and reconnect error;
4. snapshot/InfoTree goal selection;
5. edit invalidation and pending-request cancellation;
6. dependency-staleness and worker-restart behavior;
7. synchronization methods.

Then run a minimal protocol probe at the exact toolchain. Launch the server using the toolchain's `lean --server` or the exact `lake serve` invocation whose environment is under study. Use a tiny file:

```lean
theorem demo (p : Prop) (h : p) : p := by
  exact h
```

Initialize the server, send `initialized`, and `didOpen` the file as version 1. Wait with `textDocument/waitForDiagnostics` for version 1. At a position inside the tactic proof:

1. call `$/lean/plainGoal` as a human-readable control;
2. call `$/lean/rpc/connect` for the URI;
3. call `$/lean/rpc/call` with the returned session ID, the same URI/position, method `Lean.Widget.getInteractiveGoals`, and `PlainGoalParams`;
4. preserve the raw JSON transcript and exact line/character position.

Next send a version-2 `didChange` that changes the proof, wait for version-2 diagnostics, and repeat both goal queries. Issue one query concurrently with an edit to confirm the old request is cancelled or rejected rather than reported as current. Finally restart the file worker, reuse the old RPC session as a negative control, require `RpcNeedsReconnect`, reconnect, and repeat the query.

Preserve server command, cwd, toolchain revision, Lake/setup state, document bytes and versions, every JSON-RPC message, stdout/stderr, and hashes.

This experiment establishes the concrete wire behavior and lifecycle for that revision. It does not establish performance, long-run scaling, batch/server semantic equivalence, or Rust-to-generated-Lean source correspondence.
