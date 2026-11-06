# Lean LSP Rich RPC Session Lifetimes, Reference Keep-Alive and Release, InfoView Projection, and Historical Snapshot Economics

## Summary

In direct `lean --server` sessions on Lean `v4.30.0-rc2`, RPC sessions (`$/lean/rpc/connect`) and opaque context/info references (`{"p": "..."}` such as `InfoWithCtx`) are strictly scoped to the live file-worker and RPC session incarnation:
1. **Session survival vs. invalidation**: An active RPC session remains usable across in-place `textDocument/didChange` edits on the same open URI and returns updated interactive goals. However, calling `$/lean/rpc/call` on a closed URI returns JSON-RPC `-32801` (`Cannot process request to closed file`), and calling an old session after `textDocument/didClose` + `textDocument/didOpen` or across a server restart returns `-32900` (`Outdated RPC session`). New sessions frequently reuse small numeric reference payloads such as `{"p":"0"}` or `{"p":"9"}`, proving wire reference numbers are not globally unique.
2. **Idle expiry vs. keep-alive preservation**: Without client traffic, an open RPC session expires after an observed `42.01`-second idle interval (exceeding Lean's documented three-period, 10-second `$/lean/rpc/keepAlive` timeout), causing subsequent reference dereferencing via `Lean.Widget.InteractiveDiagnostics.infoToInteractive` to fail with `-32900 Outdated RPC session`. Sending five `$/lean/rpc/keepAlive` notifications (~8-second cadence) over `43.1137` seconds preserves the session and reference.
3. **Selective multi-reference release**: In a single goal with 32 distinct hypothesis `InfoWithCtx` references (`h00`..`h31`), releasing the 16 odd-indexed references via one `$/lean/rpc/release` notification and maintaining keep-alives over `43.2004` seconds causes all 16 released references to fail with `-32602` (`RPC reference '…' is not valid`) while all 16 retained even-indexed references continue resolving to their exact interactive popups.
4. **Cancellation, worker kill, and cross-incarnation late replies**: Cancelling a gated RPC request returns `-32800` while keeping the session usable. Killing a file-worker PID leaves an in-flight RPC call unresolved during a 15-second read bound until `didClose`/`didOpen` flushes `-32801` (`The file worker ... has been terminated`) and spawns a replacement worker. When an old server holds a gated `⊢ True` request and a replacement server answers `⊢ False` on the same `(URI, version 1, request ID 50)` before the old gate releases, the old `⊢ True` arrives last—requiring clients to fence responses by `(transport/worker incarnation, source digest)`.
5. **Historical snapshot retention and Rust-to-Lean InfoView projection**: Because `$/lean/plainGoal` ignores extra `textDocument.version` fields, historical goal queries require either a separate document URI (`Historical.lean`, 64 bytes, 238.8 ms warm open/wait, ~384 MB worker RSS) or retained/reconstructed Aeneas generation directories (where 1/2/4 cached Aeneas generations occupy 1,304 B Rust-only, 82,779 B Rust+LLBC, 96,704 B with generated Lean, and 295,448 B with `.olean` artifacts, and recompiling the oldest generation from generated Lean takes 4.871 s). A prototype Rust-to-Lean projection across UTF-8/UTF-16 offsets (`café 🦀`, 55 UTF-8 bytes vs. 52 UTF-16 code units) maps `$/lean/plainGoal`, `Lean.Widget.getInteractiveGoals`, `textDocument/definition`, `textDocument/references`, and `textDocument/hover` back to authored Rust comments and enforces session-expiry fences across `didClose` (`-32801`) and server restarts (`-32900`).

## Applicability

- **Evaluated Toolchain Subjects**:
  - **Lean 4 and Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` executable SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.
  - **Rust compiler `nightly`**: `rust-lang/rust` revision `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, executable SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc` (used in `support/rust-to-lean-infoview-reconnect/` to compile the host Rust file to metadata and in `support/generated-history-retention-economics/` as the upstream producer of the cached Aeneas generations).
- **Execution Environment and Subprobe Scope**:
  1. **Direct Lean RPC session lifetimes, delayed replies, and historical snapshots** (`support/lean-rpc-lifetimes-v4-30-0-rc2/`): Sequential and overlapping two-server tests on an 8 GiB arm64 macOS host (`LEAN_NUM_THREADS=1`).
  2. **RPC session idle expiry without keep-alive** (`support/rpc-idle-expiry-v4-30-0-rc2/`): 42.01-second no-message idle test with client request IDs above 1000.
  3. **RPC keep-alive positive control** (`support/rpc-keepalive-positive/`): 43.1137-second interval with five `$/lean/rpc/keepAlive` notifications (at 8.1408, 16.1996, 24.0836, 32.0991, and 40.1340 s; peak server+worker RSS 686,800,896 bytes across 272 samples).
  4. **32-reference selective release and keep-alive** (`support/many-ref-retention-release/`): 32 hypothesis `InfoWithCtx` references (`h00`..`h31`), odd-index release, and five keep-alives (at 8.1860, 16.0882, 24.1747, 32.1992, and 40.0833 s) over 43.2004 s (peak server+worker RSS 673,759,232 bytes across 400 samples, total elapsed 48.6274 s).
  5. **Rust-to-Lean InfoView position projection and reconnect** (`support/rust-to-lean-infoview-reconnect/`): Local Python locator projecting `// ` Lean lines from a `rustc`-checked Rust source file into `Projected.lean`.
  6. **Cached Aeneas generation retention and historical goal reconstruction** (`support/generated-history-retention-economics/`): Four cached Aeneas generations (base, changed body, changed trait signature, nested module move) evaluated one direct server at a time under a 3,300,000 KiB RSS guard (observed peak 2,136,720 KiB).

## Findings

### 1. RPC Session Lifetimes, Cancellation, Worker Crash, and Late-Reply Races

In `support/lean-rpc-lifetimes-v4-30-0-rc2/transcript.json` (242 events, SHA-256 `fd1bb5e7875d6ee01ae0f9509ff15e370cfe4f024fb6d5c708b6ad62d20acf51`) and `support/lean-rpc-lifetimes-v4-30-0-rc2/summary.json`:

- **In-place edit vs. reopen/restart**: Opening V1 (`n + 1 = 8`), connecting RPC session A, and calling `Lean.Widget.getInteractiveGoals` returned context reference `{"p":"9"}`. Editing the same URI to V2 (`n + 1 = 9`) and calling through **the same session A** returned the V2 `= 9` goal. After `didClose`/`didOpen` at version 1 with V3 (`n + 1 = 10`), calling through session A returned `-32900 Outdated RPC session`, while a new `$/lean/rpc/connect` session returned V3's `= 10` goal. A fresh watchdog also rejected the old session with `-32900` and issued a new session whose response again reused wire reference `{"p":"9"}` (**Basis: execution**).
- **Gated RPC cancellation**: Sending RPC request 60 while a `run_tac` gate blocked elaboration, sending `$/cancelRequest`, and releasing the gate caused request 60 to return `-32800` while a subsequent RPC call on the same session returned `⊢ True` (**Basis: execution**).
- **Worker crash and recovery**: Sending RPC request 12 and killing the file-worker PID produced progress notifications but no final reply or replacement child within a 15-second read bound. Sending `didClose` and `didOpen` then caused request 12 to return `-32801 The file worker ... has been terminated`, spawned a new worker PID, completed `waitForDiagnostics`, and allowed a fresh RPC session to return the V3 goal (**Basis: execution**).
- **Overlapping server replacement race**: Holding a gated V1 (`⊢ True`) request ID 50 in old server O while opening V2 (`⊢ False`) on replacement server N with the same `(URI, version 1, request ID 50)` returned N's `⊢ False` first and O's `⊢ True` after gate release (**Basis: execution**).
- **Separate-URI historical query construction**: While the main URI at V3 returned `= 10` (even when `plainGoal` was passed an extra `textDocument.version: 1`), opening `Historical.lean` with retained 64-byte V1 source returned `= 8` in 238.8 ms, adding a second file worker with sampled RSS 383,959,040 bytes alongside the first worker's 384,614,400 bytes (**Basis: execution**).

### 2. Idle Expiry vs. Keep-Alive Preservation and 32-Reference Selective Release

Comparing the three keep-alive/release controls on `v4.30.0-rc2`:

| Control Probe | Fixture & References | Client Messages During Interval | Interval (s) | Post-Interval Dereference (`infoToInteractive`) |
| --- | --- | --- | ---: | --- |
| Idle expiry (`support/rpc-idle-expiry-v4-30-0-rc2/results.json`) | `Proof.lean`, 1 `Nat` ref (`{"p":"0"}`) | None | 42.01 | `-32900 Outdated RPC session` (new `rpc/connect` succeeded on same URI) |
| Keep-alive positive (`support/rpc-keepalive-positive/results.json`) | `Proof.lean` (SHA-256 `fdf822ed…`), 1 `Nat` ref (`{"p":"0"}`) | 5 `$/lean/rpc/keepAlive` notifications (8.14, 16.20, 24.08, 32.10, 40.13 s) | 43.1137 | Succeeded; rendered `Nat` popup in original session |
| 32-reference release & keep-alive (`support/many-ref-retention-release/results.json`) | `Proof.lean` (SHA-256 `e7873f25…`), 32 distinct refs (`h00 : Nat = 0`..`h31 : Nat = 31`) | `$/lean/rpc/release` for 16 odd indices, then 5 `$/lean/rpc/keepAlive` (8.19, 16.09, 24.17, 32.20, 40.08 s) | 43.2004 | All 16 released odd refs returned `-32602` (`RPC reference '…' is not valid`); all 16 retained even refs returned matching interactive popups |

### 3. Rust-to-Lean InfoView Projection and Reconnect Fences

In `support/rust-to-lean-infoview-reconnect/results.json`:
- A valid Rust file compiled to metadata via `rustc` (`nightly`) contained three `// ` Lean lines with `café 🦀` preceding `helper` (55 UTF-8 bytes vs. 52 UTF-16 code units in `Projected.lean`).
- At the projected `helper` position, `$/lean/plainGoal` returned `n : Nat`, `h : n = 7`, `⊢ helper n = 8`, and `Lean.Widget.getInteractiveGoals` returned structured tagged expressions. Byte offsets inside the emoji or UTF-16 offsets splitting a surrogate pair were rejected, and synthetic `import Lean` lines had no reverse Rust mapping.
- `textDocument/definition` (1 target), `textDocument/references` (2 locations), and `textDocument/hover` (`helper (n : Nat) : Nat`) were reverse-mapped to authored `helper` snippets on the Rust comment lines.
- After `didClose`, calling the old RPC session returned `-32801` (`Cannot process request to closed file`); reopening and connecting a fresh session restored plain and rich goals. After server shutdown and restart, the old session returned `-32900` (`Outdated RPC session`) before a fresh connection succeeded (**Basis: execution**).

### 4. Cached Aeneas Generation Retention Economics and Historical Goal Recomputation

In `support/generated-history-retention-economics/results.json`, four cached Aeneas variants (base `⊢ trait_reuse.core.use_step 1#u32 = Aeneas.Std.Result.ok 2#u32`, changed body `= Aeneas.Std.Result.ok 3#u32`, changed trait signature `= Aeneas.Std.Result.ok 2#u32` with distinct `.olean` hashes, and nested module move `move_probe.moved.core.use_step`) were measured across four storage tiers:

| Most recent generations retained | Rust only | Rust + LLBC | Plus generated Lean/proof | Plus compiled OLean |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 183 B | 10,089 B | 12,249 B | 29,945 B |
| 2 | 576 B | 35,095 B | 41,202 B | 119,802 B |
| 4 | 1,304 B | 82,779 B | 96,704 B | 295,448 B |

Sequential fresh `lean --server` launch, readiness wait, and `$/lean/plainGoal` query costs across the retained generations:

| Fresh direct server | Open/wait/goal seconds from launch | Sampled server tree RSS |
| --- | ---: | ---: |
| Base | 1.818 | 2,046,528 KiB |
| Body | 1.970 | 2,095,040 KiB |
| Signature | 2.042 | 2,108,960 KiB |
| Move | 3.165 | 2,078,448 KiB |
| Restart base | 5.345 | 2,084,032 KiB |
| Restart move | 5.677 | 2,060,928 KiB |

Recompiling a generated-source-only copy of the base generation took `4.871` s for its three Lean modules, `1.569` s for fresh batch proof checking, and `1.946` s to serve the historical goal in a fresh server (**Basis: execution**).

## Boundaries

- **Not examined**: Dereferencing a retained `ctx` object across an in-place document edit or across an imported `.olean` swap while keeping the RPC session alive, or measuring OS memory reclaimed by `$/lean/rpc/release`.
- **Not examined**: Launching the actual VS Code Lean 4 InfoView webview UI or testing an end-to-end Anneal MCP historical-query broker with lease-based garbage collection.
- **Unknown**: Whether a killed Lean file worker would eventually be restarted by its watchdog after waiting longer than 15 seconds without sending `textDocument/didClose` and `textDocument/didOpen`, or the exact sub-second timeout boundary between 30 and 42 seconds for `$/lean/rpc/keepAlive` expiration.
- **Known not to apply**: Numeric RPC reference strings (`{"p":"0"}`, `{"p":"9"}`) and JSON-RPC request IDs are not globally unique across sessions or server incarnations and must never be exposed as durable cross-session MCP handles without binding them to `(server/worker incarnation, RPC session ID, document URI, source/environment digest)`.

## Evidence

- **Direct RPC lifetimes and races**: [`support/lean-rpc-lifetimes-v4-30-0-rc2/probe.py`](support/lean-rpc-lifetimes-v4-30-0-rc2/probe.py) (SHA-256 `b17723466f7ff64e8566cd1df1b861fa81b3c3b8893d365cd99a31703f6b859b`), [`support/lean-rpc-lifetimes-v4-30-0-rc2/transcript.json`](support/lean-rpc-lifetimes-v4-30-0-rc2/transcript.json) (SHA-256 `fd1bb5e7875d6ee01ae0f9509ff15e370cfe4f024fb6d5c708b6ad62d20acf51`), [`support/lean-rpc-lifetimes-v4-30-0-rc2/summarize.py`](support/lean-rpc-lifetimes-v4-30-0-rc2/summarize.py), [`support/lean-rpc-lifetimes-v4-30-0-rc2/summary.json`](support/lean-rpc-lifetimes-v4-30-0-rc2/summary.json), and [`support/lean-rpc-lifetimes-v4-30-0-rc2/work`](support/lean-rpc-lifetimes-v4-30-0-rc2/work).
- **RPC idle expiry**: [`support/rpc-idle-expiry-v4-30-0-rc2/probe.py`](support/rpc-idle-expiry-v4-30-0-rc2/probe.py) (SHA-256 `27b815dade438ae3f76b811d3ef80f8ff748b7e0f6cfc13c87ae6ad6eb9e5f89`), [`support/rpc-idle-expiry-v4-30-0-rc2/results.json`](support/rpc-idle-expiry-v4-30-0-rc2/results.json) (58 events, SHA-256 `4c7d2562d4b6203f9bc2a21b52a0af01d07a28f64ec6e266140d2bf3809e0257`), [`support/rpc-idle-expiry-v4-30-0-rc2/check.py`](support/rpc-idle-expiry-v4-30-0-rc2/check.py), and [`support/rpc-idle-expiry-v4-30-0-rc2/work`](support/rpc-idle-expiry-v4-30-0-rc2/work).
- **RPC keep-alive positive control**: [`support/rpc-keepalive-positive/probe.py`](support/rpc-keepalive-positive/probe.py), [`support/rpc-keepalive-positive/oracle.json`](support/rpc-keepalive-positive/oracle.json), [`support/rpc-keepalive-positive/results.json`](support/rpc-keepalive-positive/results.json), [`support/rpc-keepalive-positive/baseline-expiry-results.json`](support/rpc-keepalive-positive/baseline-expiry-results.json), and [`support/rpc-keepalive-positive/check.py`](support/rpc-keepalive-positive/check.py).
- **32-reference retention and selective release**: [`support/many-ref-retention-release/Proof.lean`](support/many-ref-retention-release/Proof.lean) (SHA-256 `e7873f25f83f1a85904d10b20898f781653e8ad9ca8ff65b8cb67f8e9a9890f1`), [`support/many-ref-retention-release/oracle.json`](support/many-ref-retention-release/oracle.json), [`support/many-ref-retention-release/probe.py`](support/many-ref-retention-release/probe.py), [`support/many-ref-retention-release/results.json`](support/many-ref-retention-release/results.json) (249 events), and [`support/many-ref-retention-release/check.py`](support/many-ref-retention-release/check.py).
- **Rust-to-Lean InfoView projection and reconnect**: [`support/rust-to-lean-infoview-reconnect/probe.py`](support/rust-to-lean-infoview-reconnect/probe.py), [`support/rust-to-lean-infoview-reconnect/results.json`](support/rust-to-lean-infoview-reconnect/results.json), [`support/rust-to-lean-infoview-reconnect/check.py`](support/rust-to-lean-infoview-reconnect/check.py), and [`support/rust-to-lean-infoview-reconnect/work`](support/rust-to-lean-infoview-reconnect/work).
- **Cached Aeneas generation retention economics**: [`support/generated-history-retention-economics/probe.py`](support/generated-history-retention-economics/probe.py), [`support/generated-history-retention-economics/results.json`](support/generated-history-retention-economics/results.json), [`support/generated-history-retention-economics/check.py`](support/generated-history-retention-economics/check.py), and [`support/generated-history-retention-economics/work`](support/generated-history-retention-economics/work).

## Revalidation

Verify all retained protocol transcripts, reference lifecycles, and byte-tier ledgers offline without starting Lean:

```sh
python3 support/lean-rpc-lifetimes-v4-30-0-rc2/summarize.py
python3 support/rpc-idle-expiry-v4-30-0-rc2/check.py
python3 -B support/rpc-keepalive-positive/check.py
python3 -B support/many-ref-retention-release/check.py
python3 support/rust-to-lean-infoview-reconnect/check.py
python3 support/generated-history-retention-economics/check.py
```

To reacquire any live run against the pinned `v4.30.0-rc2` `lean` binary, run the respective `probe.py` in an isolated copy of the subprobe directory (note that `rpc-idle-expiry`, `rpc-keepalive-positive`, and `many-ref-retention-release` each include a ~42–43 second real-time wait).
