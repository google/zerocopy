# Imported-generation staleness within one Lean server process

## Summary

With Lean 4.30.0-rc2 launched directly as `lean --server`, rebuilding an imported `.olean` while leaving a proof document open did not change that document worker's tactic state. In the same server process, a newly opened proof worker and a closed-then-reopened worker observed the rebuilt artifact and rejected the old `rfl`; fresh batch Lean also rejected it. The server process could therefore contain workers querying different imported generations at once.

This run complements the existing `lake env lean --server` stale-import experiment. It confirms the same bounded distinction in direct-server mode and demonstrates that replacing the per-file worker was enough in this fixture; it does not establish a universal refresh contract for Lake launches or realistic Anneal projects.

## Applicability

- Lean: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`, arm64 Apple Darwin release binary).
- Launch: direct `lean --server`, working directory set to the generated fixture, `LEAN_PATH` set to that directory, `LEAN_NUM_THREADS=1`.
- Fixture: `Dep.lean` initially defines `sharedValue := 3`; one proof document contains `theorem current : sharedValue = 3 := by rfl`. The dependency is rebuilt with `sharedValue := 4` while the server stays alive.
- The transcript includes the exact artifact and proof hashes, protocol messages, goals, diagnostics, and batch result. Toolchain setup was not performed by Lake.

## Findings

### Existing open worker remained at its original imported environment

The initial imported artifact SHA-256 was `b44f5db11021e43a35d340478ec38ecf5b2e7f2b363da6d81591d3d115cfec71`. After rebuilding `Dep.olean`, its SHA-256 was `142f9093501e0337ed2634fe0070957086cead5140326fd70b7fc6c6e29bbaeb`. The proof document bytes were unchanged throughout.

Before the rebuild, querying at the end of `rfl` returned `no goals`. After the rebuild and a `workspace/didChangeWatchedFiles` notification for `Dep.lean`, the same open worker still returned `no goals`. This response was stale relative to the current artifact on disk.

Basis: **execution** in `support/transcript.json`.

### A new worker in the same process used the new imported artifact

A second document with identical proof bytes was opened after the rebuild in the still-running server. Its diagnostics reported that `rfl` failed, and a query at the same location returned the remaining goal `⊢ sharedValue = 3`. The same server process thus served an old open worker with no goals and a new worker with a failing proof.

Closing and reopening the original URI at document version 2 also produced the goal `⊢ sharedValue = 3`. A batch invocation of Lean over the unchanged proof bytes exited 1 and reported the same `rfl` mismatch.

Basis: **execution** in `support/transcript.json`; the classification as distinct imported environments follows from the changed artifact hash and contrasting server/batch outcomes.

### Worker/document freshness must include dependency and worker generation

The proof's URI, text, and version did not change when the dependency artifact changed. Those fields did not distinguish the stale open worker from the new worker. A query result therefore needs an imported-environment identity and a worker incarnation (or a conservative refresh boundary) in addition to the document identity. In this fixture, close/reopen established a fresh worker while retaining the same server process.

Basis: **derived** from the paired worker results and fresh batch control.

## Boundaries

- This probe uses direct `lean --server` and a minimal `LEAN_PATH`; it does not execute `lake serve`, `lake env lean --server`, Lake `setup-file`, Mathlib, native plugins, or a generated Anneal project.
- It changes the imported source and artifact together. It does not produce a different valid `.olean` from byte-identical source/configuration, nor test timestamp-only changes.
- Only one old and one newly opened dependent document were compared. This is not a fanout, concurrent request, crash, or scale test.
- The server's simple `$/lean/plainGoal` response is used. Rich InfoView RPC handles and their lifecycle are outside this experiment.
- A single observed refresh sequence does not establish every event needed to refresh Lean dependents. The stale worker result is evidence for this launch and fixture only.
- `workspace/didChangeWatchedFiles` is a notification with no completion acknowledgment. The next old-worker query followed the send, but this run does not prove that the watcher had finished processing it before the query.

## Evidence

- `support/probe.py` — reproducible direct-server and batch procedure. Set `LEAN_BIN` to the pinned Lean executable.
- `support/transcript.json` — causal protocol and batch transcript, with local absolute paths scrubbed.
- `support/revalidation-transcript.json` — independent replay with the same pinned Lean binary. The artifact hashes, four goal results, and batch exit code match the original run.
- `support/check.py` — offline checks for the retained transcripts, final fixture hashes, protocol chronology, goals, diagnostics, and batch result.
- `support/fixture/Dep.lean`, `Dep.olean`, `OldOpen.lean`, and `NewOpen.lean` — final fixture state; initial `Dep.lean` and artifact are represented by source/hash evidence in the transcript.

Related corpus evidence: `anneal-v1-interactive-dependency-invalidation-2026-09-28` exercises `lake env lean --server` in a generated V1 workspace; `lean-server-tactic-state-v4-30-0-rc2` documents pinned goal-query semantics. This report adds a direct-server launch case rather than replacing those findings.

Issue alignment: #3730 C03–C05, C07–C10, F08, I01–I04, and #3731 I041–I050, I098–I099, I131, I147, and I159 N02–N03 receive a narrow supplemental observation only; the companion coverage report marks each agenda item separately.

## Revalidation

Run from the package directory:

```console
python3 support/check.py
python3 support/check.py revalidation-transcript.json
LEAN_BIN=/absolute/path/to/lean python3 support/probe.py
```

Use the exact `v4.30.0-rc2` Lean binary for comparison. The probe rebuilds its fixture in place and writes `support/transcript.json`, so copy the package before rerunning it if the retained evidence must stay unchanged. The replay client now acknowledges server-to-client requests; this protocol harness correction did not change the observed artifact hashes, goals, or batch exit status in the independent replay. To compare another server mode, build an equivalent Lake workspace and vary only the launch/setup mode; do not merge those observations without preserving the mode identity.
