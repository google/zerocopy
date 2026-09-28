# Generated V1 project queries retain stale imported state after a dependency rebuild

## Summary

In a real generated V1 Lean workspace, a same-process LSP query still reported “no goals” after the generated dependency’s `.olean` was rebuilt with a changed definition. Reopening the same source in a fresh Lean process exposed the changed definition and reported the previously accepted `rfl` as failing. This is direct evidence that document versioning and a dependency file-change notification were insufficient to refresh this imported environment in the tested setup; dependency identity must invalidate or restart the worker before a goal result is reused.

## Applicability

This is a small V1 `cargo-anneal generate` output for the `relocate_probe::identity` function, using the Zerocopy source revision and Lean/Aeneas subjects in `REPORT.json`. The generated project’s Lakefile was reseeded to a relative local Aeneas path after relocation, and `lake --offline build Generated` was run before the query. LSP servers were launched as `lake --offline env lean --server` from the workspace. The dependent source mutation changed `identity x := ok x` to `identity x := ok (U32.ofNat 0)`.

## Findings

### The query interface reports meaningful before/after states on the generated project

A valid open proof applied `And.intro` to a conjunction; a goal query before the tactic returned the whole conjunction and a query after it returned two named subgoals. Replacing the tactic with `exact ⟨rfl, trivial⟩` and waiting for the new document version produced “no goals” at the end of the proof. The equivalent batch check exited 0. The open two-subgoal batch control exited 1 with the two expected goals.

Basis: execution. The exact fixture sources and protocol transcript are included under `support/`.

### Rebuilding an imported module did not refresh the existing server’s accepted state

After the successful proof, the generated `Funs.lean` definition changed, `lake --offline build Generated` exited 0, a `workspace/didChangeWatchedFiles` notification was sent for the imported source, and the proof document was resent at a higher version. The same server again returned an empty goal list after `rfl`. A new Lean process opened the identical theorem source against the rebuilt dependency and emitted a type-mismatch diagnostic at `rfl`; its end-of-proof goal query returned the original conjunction goal. Running the same saved bytes through batch Lean also exited 1 and reported the mismatch.

The source hashes for `Funs.lean` before and after mutation were `27b02d8843009c22cbd74fb430b3ccc3dc9a25c7c515aa373f4f62f6e65c69eb` and `935d3ca2e5d5c5add0ec4e42c46f8606fa7b244215930c1061325b837d272149`, respectively. The transcript therefore distinguishes an unchanged document proof from a changed imported artifact.

Basis: execution. This is a negative control for stale proof-state reuse, not a theorem about all Lean server launch modes.

### The accepted result needs dependency identity, not only a document version

For this fixture, a result keyed only by the proof document bytes/version would miss the changed imported definition. The fresh process rejected the old proof; the reused process supplied no indication in its returned tactic state that the imported definition had changed. A robust result record needs at least the generated module/artifact hashes and the toolchain/project setup alongside source bytes, and it must not treat a reused “no goals” response as current after an imported dependency changes.

Basis: derived from the paired executions above.

## Boundaries

This probe does not establish that every Lean server fails to notice dependency changes, nor whether every editor sends the exact watcher sequence used here. It does not test a crash, concurrent import writers, Lake server mode, Mathlib cache publication, or real zerocopy proof obligations. Successful Lake build and goal display are not evidence of Rust-to-Lean correspondence or theorem trust: the imported Aeneas closure emitted existing `sorry` warnings. No native plugin or network service was used.

## Evidence

- Generated V1 workspace source and local fixture: `support/fixture/` (build outputs intentionally omitted).
- Versioned LSP protocol, diagnostics, goal queries, rebuild command output, and process lifecycle: `support/query-transcript.json`; paths below the local tool directory are replaced by `$ANNEAL_LOCAL_TOOLS`.
- Batch run after the changed generated dependency: `support/batch-after-dependency.json` (exit code 1, with the `rfl` mismatch).
- Probe source snapshots: `support/Probe-v1.lean`, `support/Probe-v2.lean`, and `support/dependency-mutated-Funs.lean`.
- Prior local relocation probe established why the workspace Lakefile path was reseeded; this report retains the resulting relative Lakefile entry.

## Revalidation

Copy `support/fixture/` into a scratch layout at `BASE/move-parent/moved-lean`, create `BASE/toolchain` links to the already installed local Aeneas and Lean toolchain trees so the manifest’s relative paths resolve, and run `python3 support/replay-query.py --workspace BASE/move-parent/moved-lean --evidence-dir OUT` from an environment with the matching `lake` in `PATH`. The runner builds the generated target offline, checks the open/proved batch controls, repeats the LSP version and dependency-edit sequence, and writes a full protocol transcript. The local Aeneas/Lean artifacts are prerequisites; the report does not bundle or download them.
