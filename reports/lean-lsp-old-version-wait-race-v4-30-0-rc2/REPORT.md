# An old-version diagnostics wait can precede a newer Lean goal result

## Summary

On Lean 4.30.0-rc2, `textDocument/waitForDiagnostics` for document version 1 returned successfully after the same open document had advanced to version 2. A following `$/lean/plainGoal` returned version 2's solved goal state, without a version field in that result. This is the expected `version ≥ requested` wait contract, but a client must associate the goal with its own current document snapshot before applying a proof patch or treating it as verification evidence.

This is executed evidence for #3725 recommendations R07 and R78.

## Applicability

This is one direct `lean --server` process on macOS arm64, using bare core Lean and a two-line theorem. The source was opened at version 1 with an unfilled proof and changed in memory to version 2 with `rfl`. The file on disk remained version 1 during the LSP exchange. Separate `lean --json` invocations checked each exact text as a batch input. The observed behavior concerns Lean's LSP request semantics; no Anneal, Lake, imported module, or proof-patch implementation was executed.

The Lean binary reported `Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)` and had SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`.

## Findings

### The deliberate old-version wait succeeded against the newer document

The client opened version 1 as `theorem demo (n : Nat) : n = n := by` with `exact ?_`, awaited version 1, and queried after that tactic. The result held the unsolved `n : Nat ⊢ n = n` goal. It then sent a full-content `didChange` at version 2 replacing the tactic with `rfl`, awaited version 2, and queried at the end of `rfl`; the result was `goals: []`, `rendered: "no goals"`.

After those completed exchanges, the client sent a new `waitForDiagnostics` request **naming version 1**. It returned `{}`. The next `plainGoal` request at the same version 2 tactic position again returned `goals: []` and `"no goals"`. Batch Lean exited 1 on version 1 with placeholder and unsolved-goals errors, and exited 0 on version 2. Thus the final goal result matches the new source, even though the immediately preceding wait named the old version.

Basis: **execution**, with the input texts and ordered JSON-RPC exchange preserved under `support/`.

### The protocol does not bind the goal response to a requested version

At this pinned revision, `WaitForDiagnosticsParams` contains a URI and version and promises completion after diagnostics for a document version *greater than or equal to* that number. Its handler explicitly accepts `p.version ≤ doc.meta.version`. `PlainGoalParams` instead extends a text-document position without a version; the observed goal reply contains goal strings and rendered text, not a document version. The experiment is therefore consistent with the documented and implemented protocol, rather than evidence that the server mislabeled a result.

Basis: **source** and **execution**. See the pinned source paths under Evidence.

### A proof-edit client needs its own snapshot guard

For a client that proposes or applies a patch from a goal query, a successful wait for an older version cannot establish that the following unversioned goal describes that old source. The client must compare its current URI, source hash, and monotonically increasing document version with those recorded when the query was started, discard any result after a newer edit, and re-query the intended snapshot. This is a **derived** integration rule from the protocol and the paired source controls; the probe did not execute a patcher.

## Boundaries

This probe uses an orderly sequence, not a timing-dependent race. It does not test simultaneous clients, incremental text ranges, a `textDocument/applyEdit` operation, a crashed server, imported dependency invalidation, or cancellation propagation. It says nothing about proof soundness beyond the two Lean batch exits. A `plainGoal` result at one position is presentation state, not proof completion for an entire generated project. The related [generated-project dependency probe](../anneal-v1-interactive-dependency-invalidation-2026-09-28/REPORT.md) examines a different stale-import path.

## Evidence

- `support/replay.py` is the executable probe. Invoke it with an absolute path to this Lean binary. It writes its own source controls and path-normalized `support/transcript.json` beside the script. No local toolchain or server log is bundled.
- `support/Generated.lean` is the on-disk version 1 document. `support/batch-v1.lean` and `support/batch-v2.lean` are the exact batch source controls. `support/transcript.json` retains their SHA-256 hashes, batch exits and JSON diagnostics, ordered client/server messages, and process exit. Local report paths are labeled `$PROBE` and the binary path `$LEAN`; event timing and process ID are intentionally omitted.
- Lean source `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`: `src/Lean/Data/Lsp/Extra.lean`, `WaitForDiagnosticsParams`, `PlainGoalParams`, and `PlainGoal`; `src/Lean/Server/FileWorker/RequestHandling.lean`, `handleWaitForDiagnostics` (around lines 466–481). The local source packaged with the installed toolchain was inspected at those paths.

## Revalidation

Run `python3 support/replay.py /absolute/path/to/lean` against the named Lean build or a newer candidate. Inspect the two batch exits, responses to request IDs 11–13 and 21–23, and the final diagnostics notification versions. The discriminating outcome is whether request 13, which names version 1 after version 2 is complete, returns successfully and whether goal request 23 reflects version 2. The replay uses no network or Lake project.
