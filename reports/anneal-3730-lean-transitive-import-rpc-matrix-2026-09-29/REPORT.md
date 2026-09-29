# Transitive import, option, macro, plugin, and RPC lifecycle matrix

## Summary

Against cached Lean/Lake 4.29.0 and 4.30.0-rc2, one tiny Lake project showed the same qualitative split. An already open proof worker kept evaluating a transitive import as 7, reported Lake option `pp.universes=false`, and completed an imported `probe_tac` macro after its upstream module, Lake option, and native plugin binary changed. A newly opened proof file saw value 9, option `true`, and a remaining `⊢ True` macro goal. Its failed `rfl` left `⊢ Eq.{1} transitive 7`; the old file still returned `no goals` at that exact tactic end **after** the new file and both `Base.olean` and `Mid.olean` had refreshed on disk. A separate fresh server saw the new state too. The plugin initializer marker switched from v1 to v2 on new-worker creation.

A richer RPC control decoded a real `InfoWithCtx` reference returned by `Lean.Widget.getInteractiveGoals`; it still dereferenced in the old session after the external module transition, then returned `-32602` invalid reference after `rpc/release`. A fresh server rejected the old session with `-32900`. A separate, single-watchdog gated test deliberately reused request ID 50 for two pending file workers: its fast `⊢ False` reply arrived first, then the old `⊢ True` reply after gate release. These are **direct Lean/Lake component observations**, not an Anneal MCP envelope or acceptance oracle.

## Applicability

The project had `Base.lean` → `Mid.lean` → `Proof.lean`/`New.lean`. `Base` defined `selected : Nat`, an imported `probe_tac` syntax/macro, and `Mid` defined `transitive := selected`. The proof source was byte-identical in both workers: `#eval transitive`, `transitive = 7` by `rfl`, `True` by `probe_tac`, and a separate `exact ?_` goal. A `run_cmd` logged `pp.universes` into diagnostics. The Lake package's `moreServerOptions` changed from false to true. A separately built, valid same-module native plugin dylib changed initializer marker from `plugin-v1` to `plugin-v2`; it was passed explicitly to `lake env lean --plugin=... --server`. The proof did not import the plugin module, and the plugin only wrote a marker; it did not implement the tactic. Thus the marker attests that an initializer ran after replacement, not which native code an old worker might later execute.

The exact binary subjects were Lean/Lake 4.29.0 at `leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740` (Lean SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`, Lake `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b`) and 4.30.0-rc2 at `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (Lean `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, Lake `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`). The host was macOS arm64 with 8 GiB RAM. Commands used local pinned binaries, `LEAN_NUM_THREADS=1`, `--no-cache`, and one watchdog at a time. No dependencies were installed.

A first pilot hit the 3 GiB sampled process-tree cap while reopening a third file worker and was discarded. The retained acquisition used two workers in one watchdog, shut it down, then opened a fresh watchdog for the restarted-state control. All six retained watchdog sessions exited 0. The largest sampled server tree was 3,140,616,192 bytes, below the 3 GiB cap of 3,221,225,472 bytes. Mac `ps` RSS summed across a tree can double-count shared pages and misses between-sample peaks. A simultaneous unrelated Lean process on the host was not included in those tree totals.

## Imported generation and option observations

For **both** toolchain versions:

| Phase | `#eval` diagnostic / option diagnostic | Exact `rfl`-end goal | Exact `probe_tac`-end goal | Marker |
|---|---|---|---|---|
| Old open worker | `7` / `OPTION=false` | no goals | no goals | v1 before replacement |
| Old after source/config/plugin path changed | `7` / `OPTION=false` | no goals | no goals | v1 before new worker |
| Newly opened file | `9` / `OPTION=true` | `⊢ Eq.{1} transitive 7` | `⊢ True` | v2 |
| Old worker re-queried after new ready | `7` / `OPTION=false` | no goals | no goals | shared marker file now v2 |
| Separate fresh server | `9` / `OPTION=true` | `⊢ Eq.{1} transitive 7` | `⊢ True` | v2 |

The unchanged `Proof.lean` and `New.lean` import `Mid`, so the changed `Base.lean` is transitive. Both Base and Mid OLean hashes changed by the new-file completion, and the old file still gave value 7 afterward. The `lake setup-file Proof.lean` result before/after named both transitive `Base` and direct `Mid` import artifact paths, and changed `options.pp.universes` false→true. The old worker's diagnostic remained `OPTION=false` while the new/fresh workers logged true and rendered `Eq.{1}` rather than unannotated `=`. This demonstrates the selected option's effect on this goal display; it does not establish that every Lake option change is picked up without worker replacement. **Basis: execution**, exact hashes and protocol chronology in [`support/transcript.json`](support/transcript.json).

The v1 macro expanded to `trivial`, and v2 to `skip`. The new worker's remaining `⊢ True` goal isolates the macro change from the independent `transitive=9` failed-rfl control. Fresh batch Lean with the new plugin returned exit 1 because the fixed theorem and macro goal no longer close and the scratch placeholder remains. Compiler failure is expected in this deliberately broken new generation; `waitForDiagnostics` still returned its readiness result, so readiness is not file acceptance. The plugin binary replacement was valid and initializer-bearing; its marker is an execution sentinel, not an ABI attestation. The prior plugin package separately tested wrong-initializer and malformed dylib failures.

## RPC reference and causal reply observations

The old file's `Lean.Widget.getInteractiveGoals` reply contained an opaque interactive-info reference `{"p":"0"}` in the acquired run. Passing that reference to the built-in `Lean.Widget.InteractiveDiagnostics.infoToInteractive` returned an `InfoPopup` for `Nat`. After the external module/config/plugin transition, the **same old session and reference** still returned a popup. After `$/lean/rpc/release`, the same call returned `-32602` with `RPC reference '0' is not valid`. This demonstrates actual dereference and release behavior for one reference. It does not prove that the old reference represents the new imported environment: the selected reference was for `Nat`, and the old worker itself remained on its old elaboration. A new watchdog rejected the old RPC session with `-32900 Outdated RPC session` and accepted a new connection.

The causal delay used a separate simple `Slow.lean` with a `run_tac` file gate and `Fast.lean` with a different goal. In one watchdog, the old file worker reached its gate, the client issued plain-goal request ID 50 to it, then opened the fast file and **deliberately reused ID 50 while the first request was pending**. Fast returned `⊢ False`; only after release did the earlier request return `⊢ True`. Both replies had ID 50 on the same transport in each Lean version. This is a negative client-protocol control: clients should not reuse an outstanding request number and cannot attribute these two replies by `(transport, ID)` alone. The prior RPC-lifetimes report used two separate watchdog transports for a related late reply; this run supplies a same-watchdog two-worker case. It does not demonstrate an internal watchdog replacement of one file worker or a production adapter collision.

## Exact issue residuals

| #3731 | Direct evidence here | Remaining condition |
|---|---|---|
| I041 | Latest goal and rich RPC query on old/new workers | Snapshot-specific exact-version query and per-request source/artifact echo. |
| I042 | Wait completion with knowingly failing new proof; transitive refresh | Broader pending/setup/failure timing and recoverable results. |
| I043 | Fixed exact positions at `rfl`, macro, and scratch goal | Nested/combinator/term-mode position matrix. |
| I044 | Real RPC info dereference, post-edit retention, release invalidation | Generation-specific context dereference, leak/expiry measurement, many refs/sessions. |
| I045 | Same-watchdog causally delayed replies with duplicate pending ID; stale session after fresh server | Actual one-worker replacement with late successful reply, forced crash and ID policy. |
| I046 | Error diagnostics coexist with queryable goals in this tiny proof | Broad partial elaboration matrix is in a separate report; no whole-module acceptance here. |
| I047 | Old file worker remains a queryable old imported environment | Explicit historical snapshot API, retention limits, and expiry. |
| I048 | OLean hashes, `setup-file` paths/options, semantic sentinels, plugin marker | Worker-reported complete loaded environment/plugin/dynlib identity. |
| I049 | New file triggers transitive Base and Mid rebuild under both versions | Wider dependency graphs, import cycles, concurrent edits, actual generated project. |
| I050 | Transitive import, option, macro, native plugin transition | Other tactics, notation/instances, larger plugins, ABI mismatch in this matrix. |
| I091 | Independent `setup-file` result includes transitive import arts and option change | Exact hidden setup identity used by each live worker or unsaved header. |
| I147 | This run observes source, options, macro and dylib changing together | Source-only vs OLean-only/same-mtime/byte-identical rebuild and external-model unchanged-output controls remain separate. |

## Evidence and replay

[`support/probe.py`](support/probe.py), SHA-256 `54d4478ab58cbb5665e19d41ef632c0a1ae79094f6dae6b0bfa32a71b2c1117e`, creates disposable Lake projects and plugin variants, runs one watchdog at a time, records exact wire messages, diagnostics, commands, source/OLean/dylib hashes, setup JSON, process trees, and gated reply chronology. [`support/transcript.json`](support/transcript.json), SHA-256 `08085a13121b013e9663b2407bce8e2954cd16609113b4041107597b5aa9889a`, has 588 ordered events. [`support/check.py`](support/check.py) asserts the two-version old/new/fresh goals, option diagnostics, OLean transitions, plugin marker, RPC dereference/release, stale session, delayed ID-50 replies, resource cap, and clean shutdown; it passed and wrote [`support/summary.json`](support/summary.json). The tiny final fixtures and binaries are in [`support/work`](support/work).

Replay with `python3 support/probe.py` and `python3 support/check.py` from this package. The probe replaces only its own support work and transcript. Check binary hashes and memory pressure before treating a replay as the same subject. Native dylib hashes can vary with build path; compare the exact old/new marker and protocol outcomes first. Any different result deserves a new acquisition record rather than an inference about Anneal behavior.
