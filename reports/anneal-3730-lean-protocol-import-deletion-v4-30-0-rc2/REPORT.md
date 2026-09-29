# Deleted imported artifact remains usable in an open Lean worker

## Summary

In a direct Lean 4.30.0-rc2 server, deleting an imported module's source and `.olean` left an already open proof worker reporting `no goals` for a proof that depended on that module. A newly opened proof worker in the **same server process**, a closed and reopened original URI, and fresh batch Lean could no longer resolve the module. The source text of the proof did not change. The open worker's local result therefore cannot attest that the module still exists in the selected filesystem generation.

This complements the corpus's changed-artifact experiment with a deletion control. It is direct Lean behavior, not an Anneal output-publication or Lake refresh test.

## Applicability

The execution used `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on arm64 macOS. The `lean` release binary SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The direct server ran as `lean --server` with `LEAN_PATH` pointing to the disposable fixture and `LEAN_NUM_THREADS=1`. No Lake project, generated Aeneas output, plugin, Mathlib, or native artifact was involved. Three identical-condition repetitions were recorded on 2026-09-29.

The fixture first compiled `Dep.lean` containing `def sharedValue : Nat := 3` into `Dep.olean` (SHA-256 `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`). `OldOpen.lean` imported `Dep` and proved `sharedValue = 3` by `rfl`. The probe then deleted both `Dep.lean` and `Dep.olean`, notified the server through `workspace/didChangeWatchedFiles` with deletion type 3, and queried the old worker, a new worker, and a reopened worker. Finally, batch `lean --json` checked the same proof text.

## Findings

### Old and new workers disagree after deletion

In all three runs, the already open `OldOpen.lean` worker returned `goals: []` / `rendered: "no goals"` both before and after the source and artifact were deleted. Opening `NewOpen.lean` with byte-identical proof text in the same server process produced a diagnostic `unknown module prefix 'Dep'`; its plain-goal query returned `null`. Closing and reopening the original URI at document version 2 produced the same import diagnostic and `null` goal. Fresh batch Lean exited 1 with the corresponding missing-module error. The transcript records the artifact hash, deletion/absence check, document versions, raw protocol messages, and batch output.

Basis: **execution** in `support/transcript-run{1,2,3}.json`. The old worker's `no goals` is an observation of its previously loaded environment; the new worker and batch outcomes show that the current filesystem no longer offers `Dep.olean`. The result does not reveal an internal loaded-artifact hash from the old worker.

### A watcher event and a version wait do not replace worker state

The deletion notification did not make the old worker re-elaborate the unchanged proof or abandon its old imported environment in this fixture. After `didClose`/`didOpen`, the same server process created a worker that resolved imports afresh and saw the missing module. This matches the source-level design in Lean's [watchdog dependency-change handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1280) and complements the prior [same-server changed-artifact report](../lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md). It does not establish that reopening is sufficient under every Lake setup, plugin, or process-global option change.

A completed goal query on an old worker is consequently an *old environment* result until the client can bind it to the selected import generation. For an intended current generation in which `Dep` is deleted, the adapter must fence or discard the old worker result. The fresh worker and batch checks provide a conservative control for this bare fixture. This design implication is **derived** from the executed contrast; it is not a built Anneal policy.

### Backlog coverage and remaining deltas

| Issue #3731 item | Evidence here | Residual question |
| --- | --- | --- |
| I048 imported-environment attestation | Same process exposes old and absent imports in distinct workers | Obtain explicit artifact/option/plugin identity or prove controlled fresh-worker construction under Lake. |
| I049 refresh matrix | Direct `lean --server`: watcher notification leaves old worker; reopen sees deletion | Repeat `lake serve`, `lake env lean --server`, and setup-file behavior. |
| I050 transitive imports/options/plugins | Direct single-module deletion is a lower-bound invalidation case | Test transitive artifact, options, plugin, and macro changes. |
| I054 failed generation/fallback | Old worker can still answer against an unavailable dependency | Expose last-known-good identity and failure state in a real generation engine. |
| I055 output-set shrinkage | Deleting both source and `.olean` distinguishes old worker from new/batch | Test coordinated multi-module generation publication, renamed imports, and obsolete artifacts left in search paths. |
| I129 goal versus verification | `no goals` coexists with a missing current import | Test obligation coverage and current Rust-level claim interpretation. |

The experiment does not address I051–I053's complete-generation publication, relocation, or late-completion races. Those need a producer/consumer workspace and controlled publication points, not only a direct Lean worker.

## Boundaries

- **Not examined:** Anneal integration, Aeneas generation, Lake, transitive imports, source/artifact mismatch with `.olean` still present, native plugins, and complete generation directories.
- **Unknown:** what minimal direct instrumentation could make an existing worker report its actual loaded `.olean` hash after import. This script knows the artifact's filesystem hash before deletion but has no worker attestation field.
- **Not established:** that `didClose`/`didOpen` is a universal refresh rule. It restored agreement with fresh batch only for this direct-server single-module case.
- **Not established:** theorem validity under a newly selected generation from the old worker's empty goal array. The proof depends on its loaded module, which was unavailable in that selected filesystem state.

## Evidence

- Replay script: [`support/probe.py`](support/probe.py), adapted from the existing direct-server dependency-generation probe. It compiles the dependency, drives JSON-RPC, deletes both files, sends the watcher event, and runs batch Lean.
- Raw observations: [`run 1`](support/transcript-run1.json), [`run 2`](support/transcript-run2.json), [`run 3`](support/transcript-run3.json). The fixture and toolchain absolute paths in these artifacts are replaced by `$FIXTURE`, `$LEAN_BIN`, and `$LEAN_HOME`; event ordering and payloads are retained.
- Primary source: [`Watchdog.lean` dependency-change handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/Lean/Server/Watchdog.lean#L1280), pinned to the examined revision.
- Command: `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py` from the report package or any cwd. The script's fixture is under `support/fixture` and the direct server uses `LEAN_PATH` there.

## Revalidation

Replay with the pinned binary and compare the version/hash before interpretation. Require the old worker's pre/post-deletion goals, an explicit source/artifact absence record, the new and reopened workers' missing-module diagnostics, and batch exit 1. Preserve distinct document and worker lifetimes; replacing the whole server before querying the old worker would remove the counterexample. For a later Lean or Lake version, rerun the same deletion and record any changed refresh behavior without retroactively changing this report's subject.
