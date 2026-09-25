# Evidence

**Source — Lean 4 revision.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/Lean/Server/ProtocolOverview.lean`, blob `4f493fc900319113e00a0a9c0f5eac4c3e5bb8e5`: protocol inventory, open-document requirement, plain-goal request, RPC transport, interactive-goal procedure, and synchronization methods.
- `src/Lean/Server/README.md`, blob `4bac3026e17b604888324821f5725e0338f802e3`: watchdog/worker architecture, snapshot model, dependency refresh, and `lake setup-file` relationship.
- `src/Lean/Server/Watchdog.lean`, blob `68ed22f9178c9ae917c595c364d23df902d9478f`: open/change/save/close lifecycle, request routing, closed-file errors, saved-dependency staleness, and worker state.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: worker initialization, document updates, pending-request cancellation, RPC session creation/keep-alive/release, and stale-dependency diagnostic.
- `src/Lean/Server/FileWorker/RequestHandling.lean`, blob `a51b43e1894fc1d0949a60a4b789992c14d10fee`: `findGoalsAt?`, `getInteractiveGoals`, plain-goal rendering, and position-to-InfoTree selection.
- `src/Lean/Server/FileWorker/WidgetRequests.lean`, blob `cdcd967833e4e00eb1279629f5ed378063c97499`: registration of `Lean.Widget.getInteractiveGoals` as a built-in RPC procedure.
- `src/Lean/Data/Lsp/Extra.lean`, blob `073e8ce7273bb4bd90d43c59eb307aad76da5e3a`: `PlainGoalParams`, RPC connect/call/release/keep-alive structures, dependency-build mode, and synchronization request types.
- `src/Lean/Server/Rpc/Basic.lean`, blob `7949abaf53dfe5b9fb52399ed6b046065bd921fa`: `RpcRef`, `WithRpcRef`, wire formats, and the RPC object store.
- `src/Lean/Server/Rpc/RequestHandling.lean`, blob `1afc0f3e0ceddc49fd8ee5ac47e94fb27499f2d6`: `$/lean/rpc/call` dispatch, session validation, per-position user RPC lookup, and response encoding.
- `src/Lean/Server/FileWorker/Utils.lean`, blob `824a52e3de861ffbdde9597078d7946cb0306436`: RPC session state, random IDs, and 30-second expiration.
- `src/Lean/Widget/InteractiveGoal.lean`, blob `578a6496da7a973eee47531bf58c0a4f2640dc39`: structured interactive goal, hypothesis, and context result types.
- `src/Lean/Server/Test/Runner.lean`, blob `32b0736fbde42200555ece063f7752c76ab024b4`: checked-in client implementation of initialize/open, RPC connect/call, `getInteractiveGoals`, edits, synchronization, and close.
- `src/lake/Lake/Config/LeanConfig.lean`, blob `9fdd5a656c4316ee6beb45bdc9a1be4dd8d5d42a`: language-server executable form `lean --server` and Lake-provided server options.

No evidence above is fresh **execution**. The package uses upstream **documentation**, pinned **source**, and a checked-in source client. Architectural conclusions about an MCP wrapper are **derived**.
