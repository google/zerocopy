# Lake-launched plain and rich goals through a prepared local import

## Summary

In a tiny two-package Lean/Lake 4.30.0-rc2 project, a fresh `lake --no-cache serve` process gave matching plain and rich goal content at seven positions in a nested proof that imports a dependency. Four positions had one goal, two had no goals, and the file-end position returned `null`. On the inner tactic line, moving from its start to inside `simpa` changed the selected target from `n + 0 = depValue` to `n = depValue`; after the inner proof, the outer goal included the newly introduced `hz` hypothesis. A fresh batch Lean process accepted the exact source, reported that the theorem has no axioms, and evaluated the imported `depValue` as 7.

This adds Lake-launched, imported-module execution to the direct Lean [nested position grid](../anneal-3730-nested-tactic-position-grid-v4-30-0-rc2/REPORT.md) and [plain/rich recovery grid](../anneal-3731-rich-goal-unsaved-recovery-v4-30-0-rc2/REPORT.md). It is a bounded #3731 I043 component result. It does not run an Anneal-generated proof or establish an annotation-to-Rust cursor map.

## Applicability

The subject is installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, Lean `v4.30.0-rc2`, on macOS arm64/APFS. The local `probe_dep` package defines `depValue : Nat := 7`; `position_probe` has a complete relative path manifest, imports `Dep` into `Proof.lean`, and proves `n + 0 = depValue` from `h : n = depValue` using a nested `have`, `simpa`, and `exact`. The seven positions are zero-based UTF-16 LSP coordinates; the source is ASCII, so byte/scalar/UTF-16 columns coincide here.

The experiment began with an absent work path and no target outputs, then ran `lake -v build Proof` with artifact caching disabled. It used only the already installed local Lean/Lake binaries, an empty test home and cache, `LAKE_NO_NET=1`, `LEAN_NUM_THREADS=1`, and `/usr/bin/sandbox-exec` with network denied. Its preflight observed 48,846,319,616 free disk bytes and 21.61% free memory by the script's `vm_stat` estimate. Calls were serial with bounded command and server-response waits. No dependency was downloaded or installed.

The batch oracle is a separate `lake --no-cache env lean --json Proof.lean` process after the clean Lake build. It checks this exact source and imported artifact; it is not an independently reconstructed toolchain or a proof that local goal availability alone implies whole-file success.

## Findings

### Lake prepared the import and the fresh batch accepted the whole file

The clean Lake build reported `Built Dep` and `Built Proof`, exit 0. `lake --no-cache setup-file Proof.lean` exited 0 and identified `Proof` in package `position_probe` with `importArts.Dep` pointing to the local dependency OLean. The fresh batch process exited 0; its JSON output reported that `positioned` depends on no axioms and evaluated `depValue` to 7. The recorded `Dep.olean` and `Proof.olean` SHA-256 values are distinct. **Basis: execution**, retained build, setup, batch, source and artifact digests in `support/results.json`.

The source opened in the Lake-launched server was byte-identical to the source checked by batch. `textDocument/waitForDiagnostics` returned `{}`; the retained diagnostics notifications had no error severity, although the `#print axioms` and `#eval` commands produced information diagnostics during elaboration. One `$/lean/rpc/connect` session served the seven rich queries. The server exited 0 after shutdown. **Basis: execution**, ordered client/server events in `support/results.json`.

### Exact cursor positions select different imported proof contexts

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain and rich result |
| --- | ---: | --- |
| Outer `have` | `(3, 2)` | `n : Nat`, `h : n = depValue` ⊢ `n + 0 = depValue` |
| Inner `simpa` start | `(4, 4)` | Same incoming target and hypotheses |
| Inside `simpa` | `(4, 8)` | Same hypotheses ⊢ `n = depValue` |
| End of inner tactic line | `(4, 17)` | Empty goal list |
| Outer `exact` start | `(5, 2)` | Adds `hz : n + 0 = depValue`; target returns to `n + 0 = depValue` |
| End of `exact hz` | `(5, 10)` | Empty goal list |
| File end after `#eval` | `(8, 0)` | JSON `null` |

For all four one-goal positions, the rich RPC hypothesis names/types and target render to exactly the corresponding plain goal text after presentation tags are removed. The empty and null categories match between `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` as well. The difference between an empty goal list and `null` is preserved; the latter is not reported as a completed proof state. **Basis: execution**, seven paired responses; `support/check.py` validates the retained wire requests, responses and rendered context text.

The imported `depValue` appears in selected targets and in `h`/`hz` types. The inner start and inside positions on one source line have different selected targets, and the following tactic sees a new local hypothesis. A caller choosing a tactic state from indentation or a nearby token alone could misidentify the proof context even when the whole file later passes batch. **Basis: derived** from the exact position responses and batch control.

## Boundaries

- The fixture is a hand-written Lean project, not an Anneal-generated module, Rust proof annotation, source projection, or integrated LSP/MCP worker. It does not close I043's exact source-position mapping for authored Rust or interactive behavior under the full Anneal dependency graph.
- This run used one successful, disk-identical document version and one local dependency. Direct Lean reports separately cover unsaved error/recovery and a tactic macro; this Lake run does not repeat those cells or test edits, cancellation, stale replies, multiple imports, plugin loading, or cross-version setup.
- The local context comparison strips only rich presentation tags and checks displayed names/types. It does not validate opaque `ctx`, `info`, or `mvarId` reference lifetime, widget actions, or semantic equality of proof terms.
- The batch exit, axiom print, and imported value establish the selected file's compilation behavior. A local goal at a cursor is guidance, not a verification verdict for arbitrary other files or obligations.
- The script's network-denial profile and local-only fixture do not constitute a syscall read/write trace or a general guarantee about every Lake dependency source. Resource preflight is an admission check, not a peak-memory measurement.

## Evidence

- `support/probe.py` constructs the project and complete manifest, runs clean build, batch and setup controls, opens the exact source through Lake's server, queries both goal APIs at seven fixed positions, and records ordered protocol events. It uses only Python's standard library and the local pinned binaries.
- `support/results.json` preserves the normalized exact commands, outputs, source and artifact hashes, preflight, seven paired replies, diagnostics notifications, and server shutdown. `$WORK`, `$WORK_URI`, and `$TOOLCHAIN` replace local absolute paths in retained text. The fixture sources are separately retained at `support/fixture/Dep.lean` and `support/fixture/Proof.lean`.
- `support/check.py` is read-only and offline. It checks source hashes against preserved bytes, pinned binary hashes as recorded by the run, clean build/batch/setup controls, all seven exact positions and plain/rich context strings, wire request/response pairing, diagnostics severity, and shutdown. It printed `PASS: Lake position transcript; 7 plain/rich pairs, 4 goals, 2 empty, 1 null; clean batch and import controls`.
- Recorded binary SHA-256 values: Lake `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; Lean `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Recorded fixture SHA-256 values: `Dep.lean` `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2`; `Proof.lean` `357891c27b46563b35d8f5f314ba4c742e205b6f1a90261b204b456a33d9e699`.

## Revalidation

Run `python3 -B support/check.py` from this package to verify the retained result without starting Lean. To reacquire it with the same installed binary, run `python3 -B support/probe.py --work /new/absent/private/path --output /new/results.json`; compare the binary hashes, source bytes, build and batch exits, import path class, exact position categories and displayed contexts. A later Lake/Lean revision or an Anneal-generated proof needs a new subject-specific run. For the product-level I043 question, retain the generated source map and authored Rust version, then test the same position selection through the actual Anneal launcher with a fresh batch oracle.
