# Lean LSP Imported Artifact Invalidation, Launch-Mode Refresh, and Worker Environment Boundaries

## Summary

Across direct `lean --server`, `lake env lean --server`, and `lake serve` sessions in Lean `v4.29.0` and `v4.30.0-rc2`, an already-open file worker caches its imported module environment in memory and does not reload imported `.olean` artifacts when upstream sources or compiled artifacts change, are replaced with identical timestamps, or are unlinked from disk. Neither `workspace/didChangeWatchedFiles` notifications, resending identical proof text at a newer document version, nor editing the open proof buffer refreshes an existing worker's imported declarations, typeclass instances, notation targets, macros, server options, or native plugin initializers. Opening a new document URI in the same server watchdog, closing and reopening the existing document URI (`textDocument/didClose` followed by `textDocument/didOpen`), or starting a fresh server process forces worker initialization against the current filesystem state and restores agreement with fresh batch `lean` verification.

Conversely, when an upstream source edit (such as a comment-only edit or an equal-length hexadecimal literal rewrite `7` to `0x7`) triggers a rebuild that produces a byte-identical `.olean` artifact while changing `.ilean` and `.trace` sidecars, resident workers, newly opened workers, reopened workers, and fresh batch invocations remain in semantic agreement without requiring worker replacement for soundness. Cross-document live imports (`import A` from open buffer `B`) always resolve against compiled `.olean` artifacts on disk rather than unsaved peer LSP buffers. Under `lake serve`, rebuilding a shared dependency graph emits an "imports are out of date" diagnostic on resident workers while their `$/lean/plainGoal` tactic queries continue returning solved (`goals: []`) against the stale in-memory environment, whereas direct `lean --server` workers emit no outdated-import warning at all.

## Applicability

### Evaluated Toolchain Subjects and Shared versus Version-Specific Behavior

- **Lean 4 and Lake `v4.29.0`**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740`, `lean` executable SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`, `lake` executable SHA-256 `0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b`.
- **Lean 4 and Lake `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` executable SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`.
- **Shared Cross-Version Behavior**: Both `v4.29.0` and `v4.30.0-rc2` exhibit identical qualitative worker caching, launch-mode rebuild behavior, and refresh boundaries across clean/prepared equivalence checks, source-only versus artifact-only mutations, and transitive import/option/macro/plugin transitions. Each version built and consumed only its own `.olean` files; logical agreement across versions does not imply cross-version `.olean` binary compatibility.
- **Version Deltas**: Compiled `.olean` binary digests differ between `v4.29.0` and `v4.30.0-rc2` for identical source inputs (for example, baseline `Dep.olean` for `def depValue : Nat := 7` hashes to `f325eef7ec1d358718996207a81494ee92c3ec9d3cd4285e5ab8f0cb2520143d` on `v4.29.0` versus `3f03e66c934405d32f94a087c91e19021d71078cae3e8e33d7d9eadd3e415772` on `v4.30.0-rc2`), while protocol-level invalidation, `waitForDiagnostics` completion, `$/lean/plainGoal` selection, and `lake setup-file` JSON contracts behave identically across both pins.

### Execution Environment and Subprobe Scope

All ten constituent experiments and two harvested meta-audit control probes ran on arm64 macOS with `LEAN_NUM_THREADS=1`, offline execution (`LAKE_NO_NET=1`, `LAKE_ARTIFACT_CACHE=false`, or `sandbox-exec` network denial), and sequential server lifecycles bounded by explicit free-memory and process-tree RSS guards:

1. **Proof resend refresh barrier** (`support/proof-resend-refresh/`): Direct `lean --server` on `v4.30.0-rc2` with one private `LEAN_PATH` and one file worker, testing whether watched-file notifications, resending identical proof text at version 2, or appending a newline at version 3 refreshes an imported `Dep.olean` transition (`selected = 7` to `9`).
2. **Eight-proof live stale-oracle fanout** (`support/eight-proof-live-stale-oracle-fanout/`): Four resource-bounded two-worker waves (waves 0–1 under direct `lean --server` with `LEAN_PATH`, waves 2–3 under `lake serve` on `v4.30.0-rc2`, capped at 3.5 GiB sampled process-tree RSS) across eight unchanged proof files (`Proof0.lean`..`Proof7.lean`) importing a two-step `Model -> Helper` graph.
3. **Imported typeclass instance and notation worker split** (`support/imported-instance-notation-worker-split-v4-30-0-rc2/`): Direct `lean --server` on `v4.30.0-rc2` with client request IDs starting at 1000, testing `instance : Carrier := ⟨7⟩ -> ⟨9⟩` and `notation "selected" => left -> right` transitions.
4. **Cross-version clean/prepared and batch/live equivalence** (`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/`): 34-cell matrix across `v4.29.0` and `v4.30.0-rc2` comparing clean builds, exact copied prepared trees, source-only edits, and `.olean`-only replacements across direct batch, `lake env` batch, `lake --no-cache --no-build setup-file`, direct `lean --server`, `lake env lean --server`, and `lake serve`.
5. **Three-launch-mode refresh and `setup-file` matrix** (`support/lean-launch-refresh-matrix-v4-30-0-rc2/`): Six independent Lake workspaces on `v4.30.0-rc2` (capped at 3 GiB sampled RSS; observed peak 1,667,055,616 bytes, 44% to 38% free memory) testing source-only and older-mtime `.olean`-only transitions across `lean --server`, `lake env lean --server`, and `lake serve`, plus missing-import `didChange` and `lake setup-file` header overrides.
6. **Imported artifact deletion boundary** (`support/lean-protocol-import-deletion-v4-30-0-rc2/`): Three repetitions on direct `lean --server` (`v4.30.0-rc2`) deleting both `Dep.lean` and `Dep.olean` (`sharedValue : Nat := 3`, SHA-256 `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`) and sending `workspace/didChangeWatchedFiles` deletion type 3.
7. **Transitive import, option, macro, native plugin, and RPC matrix** (`support/lean-transitive-import-rpc-matrix/`): Evaluated on both `v4.29.0` and `v4.30.0-rc2` (sampled server-tree peak 3,140,616,192 bytes below the 3,221,225,472-byte cap) across `Base.lean -> Mid.lean -> Proof.lean`/`New.lean`, combining a transitive value change (`7 -> 9`), macro change (`probe_tac` expanding to `trivial -> skip`), Lake `moreServerOptions` (`pp.universes=false -> true`), and native plugin dylib replacement (`plugin-v1 -> plugin-v2`), plus `InfoWithCtx` RPC dereference/release and same-watchdog duplicate request-ID 50 causal delay.
8. **Live artifact unlink retention boundary** (`support/live-lean-artifact-unlink/`): Direct `lean --server` (`v4.30.0-rc2`) unlinking `Dep.olean` while `Proof.lean` stays open, querying the open document, opening a second importing document, testing fresh server/batch failure, and rebuilding `Dep.olean`.
9. **Cross-document live proof import state** (`support/live-proof-import-state/`): Direct `lean --server` (`v4.30.0-rc2`) with `A.lean` (`helper (n : Nat) : n + 0 = n`) and `B.lean` (`import A`), testing dirty unsaved `A` buffers (`unsavedOnly : True` and changed `helper` type `n + 1 = n + 1`), saved-without-rebuild `A`, rebuilt `A.olean`, empty `LEAN_PATH`, and mutually importing unbuilt source cycles.
10. **Syntax-equivalent rebuild and timestamp controls** (`support/syntax-equivalent-rebuild/`, `support/same-mtime-olean-swap/`, `support/comment-only-olean-equivalence/`): Testing equal-length syntax changes (`7` to `0x7`) and comment-only edits that rebuild byte-identical `.olean` files alongside changed `.ilean`/`.trace` files, contrasted with a same-`mtime_ns` (`1790677992350209610`) and preserved `.olean.hash` swap of a value-9 `Dep.olean`.

## Findings

### 1. Worker Refresh Barrier: Proof Resend, Edits, and Watched-File Notifications vs. Reopen

In direct `lean --server` (`v4.30.0-rc2`, `support/proof-resend-refresh/results.json`), an open `Proof.lean` (`theorem checked : selected = 7 := by rfl`) was tested across a sequence of candidate refresh actions after `Dep.olean` and `Dep.lean` were replaced on disk with `selected := 9`:

| Phase | Exact result |
| --- | --- |
| Initial artifact 7, proof version 1 | `no goals`. |
| Artifact/source replaced with 9 and both watched-file notifications sent | Existing worker still `no goals`. |
| Same proof bytes resent as version 2; `waitForDiagnostics` returned `{}` | Existing worker still `no goals`. |
| One appended newline sent as version 3; wait returned `{}` | Existing worker still `no goals`. |
| Same URI closed and reopened at version 1 | Goal `⊢ selected = 7`; diagnostic `Tactic rfl failed`. |
| Fresh server and fresh batch on the same selected artifact 9 | Fresh server gave the same open goal/error; batch exited 1 and evaluated `selected` as 9. |

Neither `workspace/didChangeWatchedFiles`, a document version increment resending identical proof text, nor a local text modification refreshes a live worker's imported `.olean` environment (**Basis: execution**, 86-event transcript in `support/proof-resend-refresh/results.json`).

### 2. Same-Mtime `.olean` Swap and Syntax-Equivalent Byte-Identical Rebuilds

To isolate whether worker import caching or rebuild equivalence depends on filesystem timestamps, `.olean.hash` sidecars, or `.olean` byte identity, three controlled probes were executed on `v4.30.0-rc2`:

- **Same-mtime `.olean` replacement control** (`support/same-mtime-olean-swap/probe.py`, `support/same-mtime-olean-swap/transcript.json`, `support/same-mtime-olean-swap/fresh-batch.json`):
  - `Dep.lean` initially defines `def val : Nat := 7` (`support/same-mtime-olean-swap/baseline-Dep.olean`, SHA-256 `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`, `mtime_ns = 1790677992350209610`).
  - While `Check.lean` (`#eval val`) is open in `lean --server`, `Dep.olean` is replaced with a compiled artifact defining `def val : Nat := 9` (`support/same-mtime-olean-swap/value9-Dep.olean`, SHA-256 `491c46d40292bf5b0e75eb9c349c3ee6218995a9ab04df31c1a9f1994e673553`), explicitly restoring `mtime_ns = 1790677992350209610` and the original `.olean.hash`.
  - Neither `workspace/didChangeWatchedFiles` nor `textDocument/didChange` on `Check.lean` causes the resident worker to observe `9` (it continues reporting `7`). Both fresh batch `lean Check.lean` (`support/same-mtime-olean-swap/fresh-batch.json`) and a `textDocument/didClose` + `textDocument/didOpen` worker restart read the new `Dep.olean` bytes and report `9`. This proves worker import caching is governed by in-memory worker state rather than `mtime_ns` or `.olean.hash` polling (**Basis: execution**).
- **Comment-only source edit with byte-identical `.olean`** (`support/comment-only-olean-equivalence/probe.py`, `support/comment-only-olean-equivalence/transcript.json`, `support/comment-only-olean-equivalence/fresh-batch.json`):
  - Changing an equal-length comment in `Dep.lean` changes the source SHA-256 (`a65f708068d277a77a351c90927ac6b9e0d36f7d42376cd84caf4fba41cfcefc` to `258b3e8a5ffffa4c7edabc080a9c1af11b2d135019c5780e7248d7e0dc33cfbb`) while rebuilding a byte-identical `Dep.olean` (`support/comment-only-olean-equivalence/comment-Dep.olean`, SHA-256 `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`). Both the live worker and fresh batch `lean` agree on `7` (**Basis: execution**).
- **Equal-length syntax edit (`7` to `0x7`) with byte-identical `.olean` and distinct `.ilean`/`.trace`** (`support/syntax-equivalent-rebuild/probe.py`, `support/syntax-equivalent-rebuild/transcript.json`):
  - Editing `def selected : Nat := 7` (24 bytes) to `def selected:Nat := 0x7` (24 bytes) and running `lake --keep-toolchain --no-cache build Dep` advances the `.olean` mtime while keeping all 4,616 bytes of `Dep.olean` identical (`support/syntax-equivalent-rebuild/baseline-Dep.olean` and `support/syntax-equivalent-rebuild/edited-Dep.olean`):

| Evidence | Baseline | Edited/rebuilt |
| --- | --- | --- |
| `Dep.lean` SHA-256 | `a65f708068d277a77a351c90927ac6b9e0d36f7d42376cd84caf4fba41cfcefc` | `258b3e8a5ffffa4c7edabc080a9c1af11b2d135019c5780e7248d7e0dc33cfbb` |
| `Dep.olean` SHA-256 | `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62` | same, byte comparison passed |
| `Dep.ilean` SHA-256 | `421fe1322bfa48a720510f38a7999947ed0c69c6d73b988305d06d848f934b3d` | `4cbf7fd491d156395a90e465c95654fa59d4e4272ea13a469a08e3b37ac84236` |
| `Dep.trace` SHA-256 | `8fb7b0023a194ac3a88db1faeb42848ada5a130fb7e732dbd5c13f570d9b5dfc` | `ea41d920856775f11ba2b49320aa2f2d6b92bfef8779dd503fa0003494e7a94c` |
| Solved `rfl` goal | `no goals` | `no goals` in resident, new, reopened, and fresh-server samples |
| Scratch goal | `⊢ selected = 7` | same in all six samples |
| Fresh batch `Check.lean` | exit 0; `#eval selected` printed 7 | exit 0; `#eval selected` printed 7 |

  - Candidate screening (`support/syntax-equivalent-rebuild/candidate-results.json`) showed that length-changing edits such as `0x7` without spacing adjustment, `(7 : Nat)`, or a longer `(7)` variant (`support/syntax-equivalent-rebuild/attempt-parentheses/`) alter `.olean` bytes (by two bytes in the `(7)` Lake attempt) because declaration source ranges are serialized into `.olean` objects (**Basis: execution**).

### 3. Launch-Mode Refresh Matrix and Cross-Version Clean/Prepared Equivalence (`v4.29.0` and `v4.30.0-rc2`)

Across both `v4.29.0` and `v4.30.0-rc2` (`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/results.json`, `support/lean-cross-version-equivalence-v4-29-v4-30-rc2/summary.json`, `support/lean-cross-version-equivalence-v4-29-v4-30-rc2/matrix.csv`), a clean built Lake tree and an exact copied prepared tree (including `.lake`) agreed across direct `lean --json`, `lake env lean --json`, `lake --no-cache --no-build setup-file`, and all three server launch modes (`lean --server`, `lake env lean --server`, `lake serve`). Checked `.olean`, `.ilean`, `.trace`, and source digests were unchanged after the prepared reads:

| Pin | Baseline `Dep.olean` SHA-256 (`depValue = 7`) | Value-9 replacement `Dep.olean` SHA-256 (`depValue = 9`) |Source-only live-rebuilt `Dep.olean` SHA-256 |
| --- | --- | --- | --- |
| `v4.29.0` | `f325eef7ec1d358718996207a81494ee92c3ec9d3cd4285e5ab8f0cb2520143d` | `f1389a240dafcea9b8cf03956cb7f877b356911b32ce4646b3b046ace5cac621` | `64adab27…` |
| `v4.30.0-rc2` | `3f03e66c934405d32f94a087c91e19021d71078cae3e8e33d7d9eadd3e415772` | `0f0fbd523ef1ce3fce88465a688f7a786beb38969ff690b97c51778d5da30ec0` | `be364799…` |

When decoupling source edits (`Dep.lean` SHA-256 `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2` at value 7 to `f24ea593a7ec12a08b2ab0c096b8babdbf9baeaef4c4a46286e12bf19959c0d0` at value 9) from `.olean` replacement across the three launch modes (`support/lean-launch-refresh-matrix-v4-30-0-rc2/transcript.json`, where baseline `Dep.olean` was `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`, older-mtime value-9 replacement `Dep.olean` was `3b0254045f93c2516915e7a26e2d3928d0472535fd876db2b81312725f8ea008`, and rebuilt source-9 `Dep.olean` was `696d7ea3fda9c4e8c0c02c84ac8d158e4a4774bb2d0f9e8ab2da6cdf2a2d7ab5`):

| Condition, in each of three launch modes | Already open `Proof` | Newly opened `New` | Old `Proof` queried again while `New` remains open | Closed/reopened `Proof` |
| --- | --- | --- | --- | --- |
| Source changed to 9; OLean initially 7 | `#eval` 7; `rfl` has no remaining goal | `#eval` 9; `rfl` fails; OLean now `696d7ea3…` | Still `#eval` 7; `rfl` has no remaining goal; disk OLean is now 9 | `#eval` 9; `rfl` fails |
| OLean replaced with valid 9; source remains 7 | `#eval` 7; `rfl` has no remaining goal, despite disk OLean 9 | `#eval` 9; `rfl` fails; replacement OLean unchanged | Still `#eval` 7; `rfl` has no remaining goal | `#eval` 9; `rfl` fails |

- **Source-only batch versus live split**: Editing `Dep.lean` to `9` without rebuilding left fresh direct `lean --json` and `lake env lean --json` batch runs succeeding with value `7` (consuming the existing `.olean`), while `lake --no-build build Dep` exited `3` (out of date). Opening a fresh document in any of the three server launch modes inside the Lake workspace triggered `lake setup-file`, rebuilt `Dep.olean` to value `9`, and failed the proof (**Basis: execution**).
- **Artifact-only replacement and `lake --no-build` blind spot**: Overwriting `Dep.olean` with a valid value-9 artifact while leaving `Dep.lean` at `7` caused fresh batch runs to fail (exit 1, reporting `sorryAx` in the recovered theorem's `#print axioms` output), yet `lake --no-cache --no-build build Dep` exited `0` (reporting up to date) and `lake --rehash setup-file Proof.lean` exited `0` without rebuilding or rejecting the overwritten `.olean` (**Basis: execution**).
- **Missing-import `setup-file` and `waitForDiagnostics` behavior**: Sending an unsaved `didChange` changing `import Dep` to `import Missing` completed `waitForDiagnostics(version=2)` with `{}` in all three launch modes while publishing `unknown module prefix 'Missing'` and returning JSON `null` at all six queried goal coordinates (`(3,2)`, `(3,5)`, `(5,2)`, `(5,4)`, `(5,10)`, `(6,0)`). Invoking `lake setup-file` on `Bad.lean` (`import Missing`) or passing an explicit unsaved `ModuleHeader` JSON override naming `Missing` exited `0` with `importArts: {}` (**Basis: source + execution**).

### 4. Eight-Proof Fanout and `lake serve` Outdated-Import Diagnostics

In the four-wave eight-proof fanout over `Model -> Helper -> Proof0..Proof7` (`support/eight-proof-live-stale-oracle-fanout/results.json`, base `Model.olean` `8c104a28…`, base `Helper.olean` `8de87e62…`, edited value-7 `Model.olean` `eb45899e…`, edited `Helper.olean` `e07f4a8c…`, initial Lake build 3.12 s, rebuilds 0.43–0.83 s, peak sampled tree RSS 1,719,320,576 bytes):

| Live launch | Proofs | Old worker after value-7 rebuild and version-2 wait | Fresh worker at value 7 |
| --- | --- | --- | --- |
| Direct Lean, wave 0 | 0–1 | Both `goals: []`; `#eval` diagnostics still 8 | Both `⊢ helper = 8`; diagnostics printed 7 and `rfl` error |
| Direct Lean, wave 1 | 2–3 | Both `goals: []`; `#eval` diagnostics still 8 | Both `⊢ helper = 8`; diagnostics printed 7 and `rfl` error |
| `lake serve`, wave 2 | 4–5 | Both `goals: []`; diagnostics still printed 8 **and warned that imports were out of date** | Both `⊢ helper = 8`; diagnostics printed 7 and `rfl` error |
| `lake serve`, wave 3 | 6–7 | Both `goals: []`; diagnostics still printed 8 **and warned that imports were out of date** | Both `⊢ helper = 8`; diagnostics printed 7 and `rfl` error |

Under `lake serve`, the diagnostic channel explicitly warned that imports were out of date after `workspace/didChangeWatchedFiles` and a version-2 proof resend, even though `$/lean/plainGoal` still returned `goals: []`. Under direct `lean --server`, no outdated-import warning was emitted (**Basis: execution**).

### 5. Semantic Import Granularity: Typeclass Instances, Notations, Transitive Imports, Options, Macros, and Plugins

- **Imported typeclass instance and notation changes** (`support/imported-instance-notation-worker-split-v4-30-0-rc2/results.json`):

| Imported change | Old model/batch | Rebuilt model/fresh batch | Resident old worker after rebuild | New URI/worker after rebuild |
| --- | --- | --- | --- | --- |
| Typeclass instance `7 → 9` | Build exit 0; proof exit 0. | Build exit 0; proof exit 1 with `rfl` failure. | `no goals`, empty diagnostics. | `⊢ selected = 7`, `rfl` diagnostic. |
| Notation target `left → right` | Build exit 0; proof exit 0. | Build exit 0; proof exit 1 with `rfl` failure. | `no goals`, empty diagnostics. | `⊢ selected = 7`, `rfl` diagnostic. |

- **Transitive module, Lake server option, imported macro, and native plugin matrix** (`support/lean-transitive-import-rpc-matrix/transcript.json`, `support/lean-transitive-import-rpc-matrix/summary.json`, reproduced identically on `v4.29.0` and `v4.30.0-rc2`):

| Phase | `#eval` diagnostic / option diagnostic | Exact `rfl`-end goal | Exact `probe_tac`-end goal | Marker |
| --- | --- | --- | --- | --- |
| Old open worker | `7` / `OPTION=false` | no goals | no goals | v1 before replacement |
| Old after source/config/plugin path changed | `7` / `OPTION=false` | no goals | no goals | v1 before new worker |
| Newly opened file | `9` / `OPTION=true` | `⊢ Eq.{1} transitive 7` | `⊢ True` | v2 |
| Old worker re-queried after new ready | `7` / `OPTION=false` | no goals | no goals | shared marker file now v2 |
| Separate fresh server | `9` / `OPTION=true` | `⊢ Eq.{1} transitive 7` | `⊢ True` | v2 |

- **Rich RPC reference survival across external transition and duplicate request-ID hazard**: In `support/lean-transitive-import-rpc-matrix/transcript.json`, an `InfoWithCtx` reference (`{"p":"0"}`) from `Lean.Widget.getInteractiveGoals` continued to resolve via `Lean.Widget.InteractiveDiagnostics.infoToInteractive` (`InfoPopup` for `Nat`) in the old worker after the external module/option/plugin transition, failed with `-32602` (`RPC reference '0' is not valid`) after `$/lean/rpc/release`, and failed with `-32900` (`Outdated RPC session`) in a fresh watchdog. In a separate two-worker test (`Slow.lean` with a `run_tac` gate and `Fast.lean`) under one watchdog, reusing JSON-RPC request ID `50` while the first request was in flight caused `Fast.lean`'s `⊢ False` reply to arrive first under ID `50` and `Slow.lean`'s `⊢ True` reply to arrive second under the same ID `50` after gate release (**Basis: execution**).

### 6. Imported Artifact Deletion, Unlink Retention, and Live Cross-Proof Imports

- **Source and `.olean` deletion with watcher notification** (`support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run1.json`, `support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run2.json`, `support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run3.json`): Across three repetitions, deleting both `Dep.lean` and `Dep.olean` and sending `workspace/didChangeWatchedFiles` (type 3) left the already-open `OldOpen.lean` worker returning `goals: []` / `rendered: "no goals"`. Opening `NewOpen.lean` in the same server, closing/reopening `OldOpen.lean` at version 2, and running fresh batch `lean --json` all produced `unknown module prefix 'Dep'` and `null` goals (batch exit 1).
- **Live `.olean` unlink and reconstruction** (`support/live-lean-artifact-unlink/results.json`):

| Observation | Exact result |
| --- | --- |
| Batch before unlink | Exit 0; no JSON diagnostics. |
| First open server document | No diagnostics; goal `⊢ depValue = 7`. |
| Same document after unlink | Same goal `⊢ depValue = 7`. |
| Second document in same server after unlink | Import diagnostic `unknown module prefix 'Dep'`; goal result `null`. |
| Fresh server and fresh batch after unlink | Same missing-import diagnostic; server goal `null`, batch exit 1. |
| Batch after rebuilding OLean | Exit 0; restored OLean SHA-256 equals the original. |

- **Live cross-document proof imports (`B` importing `A`)** (`support/live-proof-import-state/transcript.json`):

| State | A on disk / imported artifact | B result |
| --- | --- | --- |
| Initial saved A | Old source; `A.olean` SHA-256 `a9e55ecd6b98…` | Batch exit 0; open B has no diagnostics. At the tactic start, `$/lean/plainGoal` reports `n : Nat ⊢ n + 0 = n`. |
| A dirty in an open buffer | Unsaved new `helper` plus `unsavedOnly`; disk and artifact still old | Existing B remains valid. A newly opened proof that imports A and calls `unsavedOnly` gets `Unknown identifier \`unsavedOnly\`` in direct LSP and batch Lean. |
| A saved, without rebuild | New disk source; old artifact | B batch still exits 0. Saving upstream source alone did not change what this import consumed. |
| A rebuilt | New artifact SHA-256 `a901beed39bb…` | Fresh B batch exits 1 with `Type mismatch`: `helper n` now has type `n + 1 = n + 1`, while B expects `n + 0 = n`. |
| Old B worker reused | New artifact exists; B URI remained open | Its hover still reports the old imported helper type `n + 0 = n`, and its earlier no-error diagnostic state persists. |
| New or reopened B worker | New artifact exists | Each reaches the `waitForDiagnostics` barrier and reports the same type mismatch. A fresh server does too. A new worker's helper hover reports `n + 1 = n + 1`. |

  - Furthermore, setting `LEAN_PATH` to an empty directory caused batch `B` to fail with `unknown module prefix 'A'`, and two mutually importing unbuilt source modules failed in both batch and live Lean with unknown-module errors (**Basis: execution**).

## Boundaries

- **Not examined**: Multi-workspace Anneal broker scheduling, automatic dependency-graph invalidation in a production MCP adapter, and Aeneas-generated model graphs at Mathlib scale.
- **Not examined**: Concurrent `unlink` during an active kernel `open`/`mmap` import syscall, OS page-cache/mapped-file reference counting, or Windows/Linux filesystem locking semantics during `.olean` replacement.
- **Unknown**: Whether any internal Lean worker diagnostic or custom RPC can attest the exact SHA-256 digests of all currently loaded `.olean` files and native shared libraries from inside an already-running worker without external process/setup tracking (`lake setup-file` reports file paths and options, not content digests or worker incarnation IDs).
- **Known not to apply**: Neither `workspace/didChangeWatchedFiles` nor `textDocument/didChange` refreshes an already-open Lean file worker's imported `.olean` state; `textDocument/waitForDiagnostics` returning `{}` indicates elaboration completion for the attempted document state (even when imports are missing or stale), not whole-file verification or import freshness.
- **Unsupported**: Direct cross-buffer live imports between unsaved LSP documents without compiling and materializing the upstream `.olean` artifact and restarting/reopening the downstream file worker.

## Evidence

- **Proof resend refresh**: [`support/proof-resend-refresh/probe.py`](support/proof-resend-refresh/probe.py), [`support/proof-resend-refresh/results.json`](support/proof-resend-refresh/results.json), [`support/proof-resend-refresh/check.py`](support/proof-resend-refresh/check.py), and [`support/proof-resend-refresh/attempt1-invalid-path.json`](support/proof-resend-refresh/attempt1-invalid-path.json).
- **Eight-proof stale-oracle fanout**: [`support/eight-proof-live-stale-oracle-fanout/probe.py`](support/eight-proof-live-stale-oracle-fanout/probe.py), [`support/eight-proof-live-stale-oracle-fanout/results.json`](support/eight-proof-live-stale-oracle-fanout/results.json) (651 ordered events), [`support/eight-proof-live-stale-oracle-fanout/check.py`](support/eight-proof-live-stale-oracle-fanout/check.py), [`support/eight-proof-live-stale-oracle-fanout/artifacts`](support/eight-proof-live-stale-oracle-fanout/artifacts), and [`support/eight-proof-live-stale-oracle-fanout/work`](support/eight-proof-live-stale-oracle-fanout/work).
- **Imported instance and notation split**: [`support/imported-instance-notation-worker-split-v4-30-0-rc2/probe.py`](support/imported-instance-notation-worker-split-v4-30-0-rc2/probe.py) (SHA-256 `2892652c8b123259dc898df667fad29097b49fcccd0d52b01fed3e966d9473d6`), [`support/imported-instance-notation-worker-split-v4-30-0-rc2/results.json`](support/imported-instance-notation-worker-split-v4-30-0-rc2/results.json) (SHA-256 `6ce10f94b3a5f45c6411d58c35202e66f07c40639e716b41297952bada43204e`), [`support/imported-instance-notation-worker-split-v4-30-0-rc2/check.py`](support/imported-instance-notation-worker-split-v4-30-0-rc2/check.py), and [`support/imported-instance-notation-worker-split-v4-30-0-rc2/work`](support/imported-instance-notation-worker-split-v4-30-0-rc2/work).
- **Cross-version equivalence (`v4.29.0` vs. `v4.30.0-rc2`)**: [`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/probe.py`](support/lean-cross-version-equivalence-v4-29-v4-30-rc2/probe.py) (SHA-256 `2dc54391312353693ac8aceaef143cbc3e274934cf2cfa4f3ce79abfc01324d4`), [`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/results.json`](support/lean-cross-version-equivalence-v4-29-v4-30-rc2/results.json) (SHA-256 `dda8bfc937dc7e5ddb3e735a6e053289f3166fb09e175c34b02ef2a0f01c066d`), [`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/analyze.py`](support/lean-cross-version-equivalence-v4-29-v4-30-rc2/analyze.py), [`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/summary.json`](support/lean-cross-version-equivalence-v4-29-v4-30-rc2/summary.json), and [`support/lean-cross-version-equivalence-v4-29-v4-30-rc2/matrix.csv`](support/lean-cross-version-equivalence-v4-29-v4-30-rc2/matrix.csv).
- **Three-launch-mode refresh matrix**: [`support/lean-launch-refresh-matrix-v4-30-0-rc2/probe.py`](support/lean-launch-refresh-matrix-v4-30-0-rc2/probe.py) (SHA-256 `d20a5c7b20b71d7fdfec608144934f227c6a48678fc4ebff3487d1d18a7b5a01`), [`support/lean-launch-refresh-matrix-v4-30-0-rc2/transcript.json`](support/lean-launch-refresh-matrix-v4-30-0-rc2/transcript.json) (1,504 events, SHA-256 `c9bfdc571bfb555729514b548fcab4a747bab839a26c0f7463a5ec1b23a3e0b2`), [`support/lean-launch-refresh-matrix-v4-30-0-rc2/summarize.py`](support/lean-launch-refresh-matrix-v4-30-0-rc2/summarize.py), [`support/lean-launch-refresh-matrix-v4-30-0-rc2/summary.json`](support/lean-launch-refresh-matrix-v4-30-0-rc2/summary.json), and [`support/lean-launch-refresh-matrix-v4-30-0-rc2/work`](support/lean-launch-refresh-matrix-v4-30-0-rc2/work).
- **Imported artifact deletion**: [`support/lean-protocol-import-deletion-v4-30-0-rc2/probe.py`](support/lean-protocol-import-deletion-v4-30-0-rc2/probe.py), [`support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run1.json`](support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run1.json), [`support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run2.json`](support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run2.json), and [`support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run3.json`](support/lean-protocol-import-deletion-v4-30-0-rc2/transcript-run3.json).
- **Transitive import, option, macro, and plugin matrix**: [`support/lean-transitive-import-rpc-matrix/probe.py`](support/lean-transitive-import-rpc-matrix/probe.py) (SHA-256 `54d4478ab58cbb5665e19d41ef632c0a1ae79094f6dae6b0bfa32a71b2c1117e`), [`support/lean-transitive-import-rpc-matrix/transcript.json`](support/lean-transitive-import-rpc-matrix/transcript.json) (588 events, SHA-256 `08085a13121b013e9663b2407bce8e2954cd16609113b4041107597b5aa9889a`), [`support/lean-transitive-import-rpc-matrix/check.py`](support/lean-transitive-import-rpc-matrix/check.py), [`support/lean-transitive-import-rpc-matrix/summary.json`](support/lean-transitive-import-rpc-matrix/summary.json), and [`support/lean-transitive-import-rpc-matrix/work`](support/lean-transitive-import-rpc-matrix/work).
- **Live artifact unlink**: [`support/live-lean-artifact-unlink/probe.py`](support/live-lean-artifact-unlink/probe.py) (SHA-256 `d703178dad96db715f3ea59cac50c536ffa830a15fa1f065162c89a4df9edd26`), [`support/live-lean-artifact-unlink/results.json`](support/live-lean-artifact-unlink/results.json) (SHA-256 `921c2f7911f7b7f947da9cb0918c954c51be8b5cd662796ebe56c6cf25be3a74`), and [`support/live-lean-artifact-unlink/check.py`](support/live-lean-artifact-unlink/check.py).
- **Live proof import state**: [`support/live-proof-import-state/probe.py`](support/live-proof-import-state/probe.py), [`support/live-proof-import-state/transcript.json`](support/live-proof-import-state/transcript.json), [`support/live-proof-import-state/verify.py`](support/live-proof-import-state/verify.py), and [`support/live-proof-import-state/artifacts`](support/live-proof-import-state/artifacts).
- **Syntax-equivalent rebuild and mtime controls**:
  - [`support/syntax-equivalent-rebuild/probe.py`](support/syntax-equivalent-rebuild/probe.py), [`support/syntax-equivalent-rebuild/check.py`](support/syntax-equivalent-rebuild/check.py), [`support/syntax-equivalent-rebuild/transcript.json`](support/syntax-equivalent-rebuild/transcript.json), [`support/syntax-equivalent-rebuild/evidence-manifest.json`](support/syntax-equivalent-rebuild/evidence-manifest.json), [`support/syntax-equivalent-rebuild/candidate-results.json`](support/syntax-equivalent-rebuild/candidate-results.json), [`support/syntax-equivalent-rebuild/attempt-parentheses`](support/syntax-equivalent-rebuild/attempt-parentheses), [`support/syntax-equivalent-rebuild/baseline-Dep.olean`](support/syntax-equivalent-rebuild/baseline-Dep.olean), and [`support/syntax-equivalent-rebuild/edited-Dep.olean`](support/syntax-equivalent-rebuild/edited-Dep.olean).
  - [`support/same-mtime-olean-swap/probe.py`](support/same-mtime-olean-swap/probe.py), [`support/same-mtime-olean-swap/transcript.json`](support/same-mtime-olean-swap/transcript.json), [`support/same-mtime-olean-swap/fresh-batch.json`](support/same-mtime-olean-swap/fresh-batch.json), [`support/same-mtime-olean-swap/baseline-Dep.olean`](support/same-mtime-olean-swap/baseline-Dep.olean), and [`support/same-mtime-olean-swap/value9-Dep.olean`](support/same-mtime-olean-swap/value9-Dep.olean).
  - [`support/comment-only-olean-equivalence/probe.py`](support/comment-only-olean-equivalence/probe.py), [`support/comment-only-olean-equivalence/transcript.json`](support/comment-only-olean-equivalence/transcript.json), [`support/comment-only-olean-equivalence/fresh-batch.json`](support/comment-only-olean-equivalence/fresh-batch.json), [`support/comment-only-olean-equivalence/baseline-Dep.olean`](support/comment-only-olean-equivalence/baseline-Dep.olean), and [`support/comment-only-olean-equivalence/comment-Dep.olean`](support/comment-only-olean-equivalence/comment-Dep.olean).

## Revalidation

Run the offline verification suite across all retained transcripts and artifact digests without launching Lean or Lake:

```sh
python3 support/proof-resend-refresh/check.py
python3 support/eight-proof-live-stale-oracle-fanout/check.py
python3 support/imported-instance-notation-worker-split-v4-30-0-rc2/check.py
python3 support/lean-cross-version-equivalence-v4-29-v4-30-rc2/analyze.py
python3 support/lean-launch-refresh-matrix-v4-30-0-rc2/summarize.py
python3 support/lean-transitive-import-rpc-matrix/check.py
python3 support/live-lean-artifact-unlink/check.py
python3 support/live-proof-import-state/verify.py
python3 support/syntax-equivalent-rebuild/check.py
```

To reacquire live observations on a pinned Lean/Lake installation, execute each subprobe's `probe.py` against an isolated private scratch directory with `LEAN_NUM_THREADS=1` and offline sandboxing enabled, then rerun the corresponding verification script above.
