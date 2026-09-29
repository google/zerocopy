# Imported-generation refresh behavior across Lean 4.29 and 4.30-rc2

## Summary

The direct `lean --server` imported-generation probe produced the same stale-worker contrast under Lean 4.29.0 and Lean 4.30.0-rc2: an already-open proof worker continued to report “no goals” after its imported `.olean` changed; a new or closed/reopened worker in the same server process reported the remaining goal; fresh batch Lean failed on the same proof text.

This is a two-version, one-launch-mode comparison. It shows that the observed behavior is present in both pinned binaries, not that every refresh path or later toolchain has the same behavior.

## Applicability

- Lean 4.29.0: `leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`.
- Lean 4.30.0-rc2: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
- Both runs use direct `lean --server`, `LEAN_PATH` set to a local module directory, one imported definition, `LEAN_NUM_THREADS=1`, `textDocument/waitForDiagnostics`, and `$/lean/plainGoal`.
- The 4.29 run is reproduced in this package. The 4.30 comparison is the separately preserved `lean-same-server-dependency-generation-v4-30-0-rc2` report, run with the same procedure and fixture shape.

## Findings

### Both binaries retained stale imported state in an existing worker

In the 4.29 run, the proof `sharedValue = 3 := by rfl` initially produced no goals with `Dep.olean` built from `sharedValue := 3`. After rebuilding that artifact from `sharedValue := 4`, the old worker still returned no goals. The new artifact hash differs from the old artifact hash in the transcript, while the proof bytes remained identical.

An identical document opened in a second worker in the same server process reported `⊢ sharedValue = 3` and an `rfl` diagnostic. Closing and reopening the original URI produced the same goal. Batch Lean exited 1. The 4.30-rc2 report records the same outcome and the same launch-mode distinction.

Basis: **execution** in `support/v429/transcript.json` and the linked 4.30-rc2 report.

### The cross-version result supports a conservative refresh boundary, not a universal rule

For these two direct-server binaries and the same minimal fixture, file-worker replacement loaded the rebuilt import while leaving the server process alive. Document URI/text/version alone did not reveal that the old worker retained its prior environment. A consumer must bind query results to imported-environment and worker generation, or use a refresh transition shown reliable for its exact server mode.

Basis: **derived** from two pinned executions.

## Boundaries

- Only Lean 4.29.0 and 4.30.0-rc2 were examined. No 4.31 candidate or broader upgrade matrix was run.
- Both runs use direct `lean --server`; they do not compare `lake serve`, `lake env lean --server`, or `lake setup-file` behavior.
- The imported source and artifact change together. No valid different artifact from byte-identical source/configuration was produced.
- The fixture has one imported definition and two document workers. It does not test many open proofs, rich InfoView RPC handles, same-document concurrent requests, plugins, Mathlib, crashes, or resource scaling.
- This does not establish that every Lean release or every editor notification sequence requires close/reopen. It records the behavior observed under these exact subjects and procedure.

## Evidence

- `support/v429/probe.py` — same procedure as the v4.30-rc2 direct-server probe.
- `support/v429/transcript.json` — Lean version, artifact hashes, LSP messages, goals, diagnostics, and batch exit status.
- `support/v429/fixture/` — final fixture sources and compiled artifact.
- `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md` — the paired v4.30-rc2 observation.

Issue alignment: partial evidence for #3730 C03–C05 and #3731 I049, I131, I147, I158, and I159 N03. The related rows in the coverage audit retain their other untested dimensions.

## Revalidation

Set `LEAN_BIN` to the exact v4.29.0 Lean executable and run from this package directory:

```console
LEAN_BIN=/absolute/path/to/lean-v4.29.0/bin/lean python3 support/v429/probe.py
```

The script rebuilds the fixture and transcript. Compare its outputs with the exact v4.30-rc2 report, preserving the launch mode and separate artifact hashes. Re-run against another Lean/Lake tuple only as a separate subject, and do not generalize from version adjacency.
