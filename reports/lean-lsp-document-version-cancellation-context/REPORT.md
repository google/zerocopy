# Lean LSP Document Versioning, Cancellation Races, Command-Prefix Reuse, and Wrapper Context Fidelity

## Summary

In Lean `v4.30.0-rc2` (`lean --server` and `lake serve`), document version management, request cancellation, elaboration prefix reuse, and wrapper context semantics exhibit five critical protocol boundaries:
1. **Unversioned goal replies and `waitForDiagnostics` version-floor semantics**: Because `textDocument/waitForDiagnostics` checks `p.version <= doc.meta.version` and `$/lean/plainGoal` ignores any extra `textDocument.version` field, a client can receive a version-1 `waitForDiagnostics` completion and a version-1 `⊢ True` goal **after** sending a version-2 `didChange`, and after version 2 completes (`⊢ False`), both `waitForDiagnostics(version=1)` and `plainGoal` (with `version: 1` or `2`) succeed and return version-2 state (`⊢ False`).
2. **Non-monotonic document versions and multi-document edit storms**: Lean's `FileWorker` processes incoming `textDocument/didChange` payloads in arrival order even when version numbers skip, repeat with new bytes, or decrease (`v1 -> v2 -> v4 -> duplicate v4 -> lower v3 -> v5`), exposing the corresponding intermediate goals (`1=1`, `2=2`, `4=4`, `40=40`, `3=3`, `5=5`). During a two-document edit burst (`v2, v4, v4, v3, v5` on `FastA.lean`) while `Slow.lean` is blocked in a `run_tac` gate and a concurrent batch `lean --json` process is active, `FastA.lean` completes `waitForDiagnostics(version=5)` in 253 ms and `plainGoal` (`⊢ 5 = 5`) in 274 ms without starvation.
3. **Command-prefix elaboration reuse and early-edit cancellation**: Editing a command at position `K` in a five-command chain (`A B C D E` representing import, namespace, option, generated definition, and proof tactic) re-elaborates only the suffix from `K` onward (`E` for tactic, `D E` for definition, `C D E` for option, `B C D E` for namespace, and `A B C D E` for import). When an early definition edit (V2) blocks at a `run_cmd` gate after `A B1 C1` and is superseded by V3 plus `$/cancelRequest` on V2's wait, V2's wait returns `-32800` and only V3's suffix (`B3 C3`) executes (`A B1 C1 B3 C3`).
4. **Wrapper context hazards (`autoImplicit`, local instances, macros, and namespaces)**: Identical theorem source text changes its elaborated proposition or truth value when surrounding context changes: moving `axiom early : later = 1` before `def later : Nat := 1` under default `autoImplicit` silently generalizes `later` to `∀ {later : Nat}, later = 1`; omitting a local `Marker` typeclass instance makes `decide` fail; changing a local macro changes the elaborated theorem from `0 = 0` to `1 = 1`; and omitting a `section` `variable` or `local notation` in a scratch proof fork breaks elaboration.
5. **Virtual URI schemes vs. `lake setup-file` and buffer/disk save-watch loops**: Both `lean --server` and `lake serve` accept unsaved buffers under `file:`, nonexistent-file `file:`, `anneal:`, and `untitled:` URIs when imports are already built, whereas `lake setup-file Absent.lean` fails unless a physical file exists on disk. In an open LSP buffer, external disk overwrites and background `.olean` builds do not alter the open buffer's diagnostics until `didClose`/`didOpen`, while `rustfmt` reflows that preserve extracted Lean comments leave the generated Lean hash unchanged.

## Applicability

- **Evaluated Toolchain Subject**: Lean 4 and Lake `v4.30.0-rc2` (`leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`) on arm64 macOS with `LEAN_NUM_THREADS=1`.
- **Subprobe Coverage**:
  1. **Direct Lean document context, imported buffers, cycles, and wrapper context** (`support/document-context-v4-30-0-rc2/`): Cross-module unsaved `A.lean`/`B.lean` buffers, neutral same-URI `LEAN_PATH` switching vs. Lake-project override, declaration-order `autoImplicit` capture, incomplete vs. full scratch wrapper context, and two-node Lake import cycles (`A <-> B`) with and without stale `.olean` files.
  2. **Save, format, overwrite, and watched build loop** (`support/editor-save-format-watch-loop/`): 8-step lifecycle combining dirty LSP buffers, invalid save, external disk overwrite, `didClose`/`didOpen` reconciliation, `/opt/homebrew/bin/rustfmt` formatting, blank-line Lean formatting edit, and `SIGKILL` build cancellation/retry with atomic `CURRENT_ARTIFACT.json` publication.
  3. **Goal-query version races and isolated cancellation** (`support/lean-protocol-races-v4-30-0-rc2/`): Three runs each of causally gated V1/V2 overlap (`probe.py`) and pre-edit cancellation (`cancel-control.py`).
  4. **Multi-document edit burst with slow gated peer and concurrent batch** (`support/lean-three-document-edit-storm/`): `Slow.lean`, `FastA.lean` (`v2, v4, v4, v3, v5` burst), and `Batch.lean` (500 ms gate; sampled server-tree RSS peak 3,566,256 KiB below the 4,600,000 KiB guard).
  5. **Virtual URI schemes, historical separate-URI queries, and dependency granularity** (`support/lean-uri-history-import-boundaries/`): `file:`, absent `file:`, `anneal:`, and `untitled:` URIs under direct and `lake serve` launch, `lake setup-file` physical-file requirement, rapid `1 -> 2 -> 3` edits vs. resident/reopened/fresh historical queries, and `Model -> Helper -> Proof` invalidation granularity.
  6. **Wrapper context fidelity and command-prefix reuse** (`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/`): Local instance, macro, and `autoImplicit` batch comparisons plus an 11-version `run_cmd` marker chain (`A B C D E`) measuring suffix re-elaboration.
  7. **Early prefix edit and cancellation** (`support/prefix-edit-cancellation-v4-30-0-rc2/`): Gated V2 early definition edit superseded by V3 and `$/cancelRequest` (sampled tree RSS peak 1,388,740,608 B below the 1.5 GB cap; wall time 2.63 s).
  8. **Stepwise non-monotonic LSP document versions** (`support/stepwise-lsp-versions/`): Step-by-step `waitForDiagnostics`, `publishDiagnostics` marker, and `plainGoal` verification across `v1 -> v2 -> v4 -> duplicate v4 -> v3 -> v5` vs. monotonic `v1..v5` (peak tree RSS 689,438,720 B across 53 samples).

## Findings

### 1. Causally Gated Version Races and Cancellation (`support/lean-protocol-races-v4-30-0-rc2/`)

Using a `run_tac` gate (`gate.entered` / `gate.release`) in V1 (`⊢ True`, SHA-256 `a84abfa4112f89dbfe60e1ed52d8e418d91323e79fcb7c0da52eb84091900331`) and an edit to V2 (`⊢ False` with `exact ?_`, SHA-256 `d87b07267df747133d8f19ecd92fe84aa367c47966d090a9b4ff1a5afd3b5d7a`), all three runs (`support/lean-protocol-races-v4-30-0-rc2/transcript-run1.json`, `support/lean-protocol-races-v4-30-0-rc2/transcript-run2.json`, `support/lean-protocol-races-v4-30-0-rc2/transcript-run3.json`) produced identical qualitative ordering (in run 1: gate entered at 3680 ms, V2 edit sent at 3680 ms, responses 10/20/23 arrived at 3694–3695 ms, V2 wait response 11 arrived at 3890 ms):

| Response ID | Request and observed result |
| --- | --- |
| 10 | V1 `waitForDiagnostics` returned `{}` **after** the client sent V2. |
| 20 | V1 `plainGoal` returned `⊢ True` **after** the client sent V2. |
| 23 | In-flight V1 `plainGoal` at a later position returned `-32800` after both an edit and explicit `$/cancelRequest` (isolated in `support/lean-protocol-races-v4-30-0-rc2/cancel-control-run1.json`, `support/lean-protocol-races-v4-30-0-rc2/cancel-control-run2.json`, and `support/lean-protocol-races-v4-30-0-rc2/cancel-control-run3.json` where `-32800` returned **before** any edit was sent). |
| 11 | V2 `waitForDiagnostics` returned `{}` after version-2 error diagnostics were published. |
| 12 | A *new* `waitForDiagnostics(version=1)`, sent only after V2 completed, returned `{}` (because `1 <= 2`). |
| 21 and 22 | `plainGoal` after V2 completion returned `⊢ False` for both supplied `textDocument.version: 1` and `version: 2`. |

Provisional empty `publishDiagnostics` notifications appeared before V2's error notification and again during `shutdown`, proving that neither the first nor the last empty diagnostic notification across a session certifies whole-file success (**Basis: execution**).

### 2. Non-Monotonic Version Sequences and Multi-Document Edit Storms

- **Stepwise non-monotonic version delivery** (`support/stepwise-lsp-versions/results.json`, `support/stepwise-lsp-versions/Proof-v1.lean` SHA-256 `976f64febc49d1f8a3c8ea7125f3d2f2ccc8f932457b75842b7d70c3506a0209`):

| Stage | Sent version | Content marker (`publishDiagnostics`) | Live `plainGoal` after marker |
| --- | ---: | --- | --- |
| Open | 1 | `missing_v1` | `⊢ 1 = 1` |
| Change | 2 | `missing_v2` | `⊢ 2 = 2` |
| Skip to | 4 | `missing_v4` | `⊢ 4 = 4` |
| Duplicate | 4 | `missing_v4dup` | `⊢ 40 = 40` |
| Lower than current | 3 | `missing_v3` | `⊢ 3 = 3` |
| Final (and after 1.5 s quiet) | 5 | `missing_v5` | `⊢ 5 = 5` |

- **Two-document burst with blocked slow document and concurrent batch** (`support/lean-three-document-edit-storm/transcript.json`): While `Slow.lean` was blocked at its `run_tac` gate and `Batch.lean` was inside a 500 ms `run_cmd` gate, `FastA.lean` received back-to-back `didChange` notifications with versions `2, 4, 4, 3, 5`. Version-5 `publishDiagnostics` arrived 243 ms after the burst, `waitForDiagnostics(version=5)` completed in 253 ms, and `plainGoal` returned `⊢ 5 = 5` in 274 ms (**Basis: execution**).

### 3. Command-Prefix Elaboration Reuse and Early-Edit Cancellation

- **Sequential command-prefix reuse** (`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/raw.json`): Using `run_cmd` file append markers `A` (after `import`), `B` (after `namespace`), `C` (after `set_option`), `D` (after `def generated`), and `E` (inside the proof tactic), each edit and reset executed only the affected suffix:

| Change from base | Newly executed marker commands | Wait latency on this tiny file |
| --- | --- | ---: |
| initial open | `A B C D E` | 726 ms |
| late proof tactic, then reset | `E`; `E` | 213; 213 ms |
| generated definition (`1 -> 2`, failing `decide`), then reset | `D E`; `D E` | 213; 213 ms |
| option, then reset | `C D E`; `C D E` | 213; 213 ms |
| namespace, then reset | `B C D E`; `B C D E` | 213; 213 ms |
| import, then reset | `A B C D E`; `A B C D E` | 891; 912 ms |

- **Early-edit gate and cancellation** (`support/prefix-edit-cancellation-v4-30-0-rc2/transcript.json`, SHA-256 `09234ebeb3fbd993302ee405588d51d470ec73a5ec196572aee7e570b5817853`): After V1 recorded `A B1 C1`, V2 modified the early definition and entered a blocking `run_cmd` gate before `B2`/`C2`. Sending V3 and `$/cancelRequest` on V2's wait before releasing the gate caused V2's wait to return `-32800`, skipped `B2 C2` entirely, and produced final marker ledger `A B1 C1 B3 C3` with V3 goal `⊢ generated = 3` (**Basis: execution**).

### 4. Wrapper Context Fidelity, Cross-Module Unsaved Buffers, and Import Cycles

Across `support/document-context-v4-30-0-rc2/raw.json` (SHA-256 `19f625d982f23ff77a075940593d962a359c5a6a268f387165f5a276c7e44069`) and `support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/raw.json`:
- **Declaration order and `autoImplicit`**: Placing `def later : Nat := 1` before `axiom early : later = 1` elaborated `axiom early : later = 1`, whereas placing the axiom before `def later` under default `autoImplicit true` silently elaborated `axiom early : ∀ {later : Nat}, later = 1` (rejected only when `set_option autoImplicit false` was set).
- **Local instances, macros, and section variables**: Keeping the exact same theorem line while omitting a local `Marker` instance caused `decide` to fail and emit `sorryAx`; changing a macro definition silently altered `#print N.proof` from `0 = 0` to `1 = 1` while both exited `0` with no axioms; and stripping `section` / `variable (n : Nat)` / `local notation "myN" => n` in a scratch proof clone caused `unknown identifier 'myN'`.
- **Cross-module unsaved buffer isolation and Lake project `LEAN_PATH` override**: Editing open `A.lean` (`marker : Nat := 7 -> 9`) at version 2 did not affect open `B.lean` (`marker = 7`, consuming `A.olean` SHA-256 `22562d8b3e1dee4dd9147b82c878beda118f3564ba91dc5225d07dbd0b70226a`) until `A.lean` was saved and rebuilt (`A.olean` SHA-256 `f834768ca2518d8a2134d7e4e97433fa6b4d9b2d14fa4c560bdf2f7f4eed5ee3`). While a neutral directory `file://$WORK/neutral/B.lean` (SHA-256 `3caf12ce355cf451fea23fa232d6579b4fde7478d4964d505549fdf2bec96f72`) respected parent `LEAN_PATH` switches between value-7 and value-9, opening `B.lean` inside a Lake project directory caused `lean --server` to select the Lake project's value-9 artifact even when parent `LEAN_PATH` pointed to value-7.
- **Lake cycle rejection**: Introducing `import B` / `import A` caused `lake build` to exit `1` with `build cycle detected` both in a clean workspace and when valid pre-existing `A.olean` and `B.olean` artifacts were present on disk (**Basis: execution**).

### 5. Virtual URI Schemes, Historical Queries, and Editor Save/Format/Watch Loops

- **URI schemes and historical boundaries** (`support/lean-uri-history-import-boundaries/results.json`):

| Component cell | Actual result | Boundary |
| --- | --- | --- |
| URI and imports | Direct `lean --server` and `lake serve` each returned `⊢ selected = 7` for an on-disk `file:` URI, nonexistent-file `file:` URI, `anneal:` URI, and `untitled:` URI carrying the same unsaved `import Dep` document. All eight `waitForDiagnostics` calls completed. | Requires prebuilt `Dep.olean` in the workspace. |
| `setup-file` | `lake setup-file Shell.lean` returned 0 with import artifacts; `lake setup-file Absent.lean` failed with a missing-file error, though the LSP had accepted the unsaved absent-file URI. | `lake setup-file` requires a physical file path on disk. |
| Rapid edit/history | Live URI advanced `1 -> 2 -> 3` (`⊢ 3 = 3`). Separate revision-1 URI returned `⊢ 1 = 1` (0.4 ms resident), failed with `-32801` after `didClose`, and restored `⊢ 1 = 1` on reopen (600.8 ms) or fresh server (624.1 ms). | Separate open URIs or fresh servers are required for historical queries. |
| Dependency granularity & 8-proof fanout | Changing one proof body (`rfl -> decide`) left `.olean` hashes unchanged; changing `Helper` rebuilt `Helper.olean` while `Model.olean` stayed byte-identical; changing `Model` (`8 -> 7`) invalidated all 8 batch proofs (`Proof0..Proof7`). | Batch dependency fanout baseline. |

- **Editor save, `rustfmt`, blank-line format, and watched build loop** (`support/editor-save-format-watch-loop/results.json`):

| Step | LSP buffer / disk | Watch/build observation | Consumed `.olean` SHA-256 prefix |
| --- | --- | --- | --- |
| Initial | Version 1 `simp`, disk same; no diagnostics | Compile succeeds | `8ea70a281294` |
| Dirty edit | Version 2 `skip`, disk remains version 1; one `unsolved goals` error | Unchanged disk hash suppresses poll | `8ea70a281294` |
| Save invalid version 2 | Buffer and disk both `skip`; same error | Batch Lean exits 1; duplicate save event suppressed | `8ea70a281294` |
| External overwrite while version 2 remains open | Disk changes to `exact Nat.add_zero n`; open buffer retains version 2 error | Disk compile succeeds | `a787e416748d` |
| Close and reopen | Version 3 opens new disk text; no diagnostics | No further build | `a787e416748d` |
| `rustfmt` on Rust specimen | Formatter changes `Source.rs`, preserving `// lean-proof: simp`; extracted Lean unchanged | Lean disk and consumed artifact unchanged | `a787e416748d` |
| Lean formatting edit | Version 4 and disk gain a blank line; no diagnostics | Rebuild succeeds; source hash changes, `.olean` and `.ilean` bytes match preceding build | `a787e416748d` |
| Cancel and retry | Version 5/disk use `simp only [Nat.add_zero]`; no diagnostics | Build process group killed with SIGKILL before completion; pointer stays old; same source retried successfully | `18fb83a0a6b6` |

## Boundaries

- **Not examined**: Production Anneal MCP queue/debounce schedulers, multi-agent fairness under sustained hours-long edit storms, or OS filesystem watcher event loss (e.g., dropped `kqueue`/`inotify` packets).
- **Not examined**: Per-annotation vs. per-file layout memory/build tradeoffs on large generated Aeneas crates (covered in the worker-pool/layout report).
- **Unknown**: Whether old request 20 in `support/lean-protocol-races-v4-30-0-rc2/` was internally computed by the Lean worker thread before or after `didChange` was parsed (the wire trace proves client-visible arrival after `didChange` was sent).
- **Known not to apply**: Neither `waitForDiagnostics(version=N)` nor `plainGoal` with an extra `version: N` field restricts the server response to exact snapshot `N` once `N+1` has been submitted; furthermore, surface theorem acceptance (`exit 0` and no axioms) does not attest proposition identity unless wrapper namespaces, options (`autoImplicit false`), local instances, macros, and declaration order are preserved.

## Evidence

- **Document context, cycles, and wrapper controls**: [`support/document-context-v4-30-0-rc2/probe.py`](support/document-context-v4-30-0-rc2/probe.py) (SHA-256 `1d5f6d29e7e91a434333f0b35e06b8de8926a30c10fad2f38199dfcfa996cced`) and [`support/document-context-v4-30-0-rc2/raw.json`](support/document-context-v4-30-0-rc2/raw.json) (SHA-256 `19f625d982f23ff77a075940593d962a359c5a6a268f387165f5a276c7e44069`).
- **Save, format, and watch loop**: [`support/editor-save-format-watch-loop/probe.py`](support/editor-save-format-watch-loop/probe.py), [`support/editor-save-format-watch-loop/verify.py`](support/editor-save-format-watch-loop/verify.py), [`support/editor-save-format-watch-loop/results.json`](support/editor-save-format-watch-loop/results.json), [`support/editor-save-format-watch-loop/fixture`](support/editor-save-format-watch-loop/fixture), and [`support/editor-save-format-watch-loop/artifacts`](support/editor-save-format-watch-loop/artifacts).
- **Protocol version races and cancellation**: [`support/lean-protocol-races-v4-30-0-rc2/probe.py`](support/lean-protocol-races-v4-30-0-rc2/probe.py), [`support/lean-protocol-races-v4-30-0-rc2/cancel-control.py`](support/lean-protocol-races-v4-30-0-rc2/cancel-control.py), [`support/lean-protocol-races-v4-30-0-rc2/transcript-run1.json`](support/lean-protocol-races-v4-30-0-rc2/transcript-run1.json), [`support/lean-protocol-races-v4-30-0-rc2/transcript-run2.json`](support/lean-protocol-races-v4-30-0-rc2/transcript-run2.json), [`support/lean-protocol-races-v4-30-0-rc2/transcript-run3.json`](support/lean-protocol-races-v4-30-0-rc2/transcript-run3.json), [`support/lean-protocol-races-v4-30-0-rc2/cancel-control-run1.json`](support/lean-protocol-races-v4-30-0-rc2/cancel-control-run1.json), [`support/lean-protocol-races-v4-30-0-rc2/cancel-control-run2.json`](support/lean-protocol-races-v4-30-0-rc2/cancel-control-run2.json), and [`support/lean-protocol-races-v4-30-0-rc2/cancel-control-run3.json`](support/lean-protocol-races-v4-30-0-rc2/cancel-control-run3.json).
- **Multi-document edit burst**: [`support/lean-three-document-edit-storm/probe.py`](support/lean-three-document-edit-storm/probe.py), [`support/lean-three-document-edit-storm/check.py`](support/lean-three-document-edit-storm/check.py), [`support/lean-three-document-edit-storm/transcript.json`](support/lean-three-document-edit-storm/transcript.json), and [`support/lean-three-document-edit-storm/work`](support/lean-three-document-edit-storm/work).
- **URI, historical query, and import boundaries**: [`support/lean-uri-history-import-boundaries/probe.py`](support/lean-uri-history-import-boundaries/probe.py), [`support/lean-uri-history-import-boundaries/check.py`](support/lean-uri-history-import-boundaries/check.py), [`support/lean-uri-history-import-boundaries/results.json`](support/lean-uri-history-import-boundaries/results.json), and [`support/lean-uri-history-import-boundaries/work`](support/lean-uri-history-import-boundaries/work).
- **Wrapper context and command-prefix reuse**: [`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/probe.py`](support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/probe.py), [`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/check.py`](support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/check.py), [`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/raw.json`](support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/raw.json), and [`support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/work`](support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/work).
- **Early prefix edit and cancellation**: [`support/prefix-edit-cancellation-v4-30-0-rc2/probe.py`](support/prefix-edit-cancellation-v4-30-0-rc2/probe.py), [`support/prefix-edit-cancellation-v4-30-0-rc2/check.py`](support/prefix-edit-cancellation-v4-30-0-rc2/check.py), [`support/prefix-edit-cancellation-v4-30-0-rc2/transcript.json`](support/prefix-edit-cancellation-v4-30-0-rc2/transcript.json) (SHA-256 `09234ebeb3fbd993302ee405588d51d470ec73a5ec196572aee7e570b5817853`), and [`support/prefix-edit-cancellation-v4-30-0-rc2/work`](support/prefix-edit-cancellation-v4-30-0-rc2/work).
- **Stepwise non-monotonic LSP document versions**: [`support/stepwise-lsp-versions/Proof-v1.lean`](support/stepwise-lsp-versions/Proof-v1.lean), [`support/stepwise-lsp-versions/oracle.json`](support/stepwise-lsp-versions/oracle.json), [`support/stepwise-lsp-versions/probe.py`](support/stepwise-lsp-versions/probe.py), [`support/stepwise-lsp-versions/results.json`](support/stepwise-lsp-versions/results.json) (169 events), and [`support/stepwise-lsp-versions/check.py`](support/stepwise-lsp-versions/check.py).

## Revalidation

Run all offline verification scripts across the retained transcripts and artifacts without starting Lean or Lake:

```sh
python3 support/editor-save-format-watch-loop/verify.py
python3 support/lean-three-document-edit-storm/check.py
python3 support/lean-uri-history-import-boundaries/check.py
python3 support/lean-wrapper-context-prefix-reuse-v4-30-0-rc2/check.py
python3 support/prefix-edit-cancellation-v4-30-0-rc2/check.py
python3 -B support/stepwise-lsp-versions/check.py
```

To re-execute any live probe on the pinned `v4.30.0-rc2` toolchain, run the corresponding `probe.py` (and `cancel-control.py` in `support/lean-protocol-races-v4-30-0-rc2/`) in an isolated copy of the subprobe directory.
