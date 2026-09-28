# Negative controls and replay boundary for generated-project evidence bundles

## Summary

A small standard-library checker replayed the retained interactive-query and concurrency transcripts from copied evidence files, verified the expected changed-dependency contrast and resource guard outcomes, and rejected a deliberately altered “fresh server” goal result. This makes the evidence check itself falsifiable. The check does not rerun Lean or independently validate proof soundness; the underlying tool experiments and their prerequisites remain in the linked report packages.

## Applicability

This report checks support artifacts for the two generated-project execution reports recorded in `REPORT.json`’s source identities and linked below. It was run on a copied set of the published-format transcript files in a new temporary directory with Python’s standard library. The replay checker reads JSON only. The execution-level scripts in the linked reports additionally require local Lean/Lake, Aeneas, and the macOS process monitor toolchain.

## Findings

### Retained summaries preserve the discriminating observations

The checker requires the interactive transcript to show (a) two subgoals after `And.intro`, (b) no goals for the baseline `rfl` proof, (c) a reused-process “no goals” response after the imported generated definition changes, and (d) a fresh-process open goal plus an `rfl` type-mismatch diagnostic. It also requires the concurrency transcript to contain a two-server sample below the harness RSS limit, memory samples above its configured floor, and a zero-server sample after shutdown. The copied transcripts passed those assertions.

Basis: execution of `support/check-evidence.py` over copied transcripts.

### The harness notices a falsified fresh-process result

For a negative control, a temporary copy of the interactive transcript was changed so the fresh process returned “no goals” instead of the recorded open goal. The same checker exited nonzero and identified the missing fresh-process goal and mismatch evidence. The published transcript was not modified.

Basis: execution; the altered transcript and checker output are retained as `support/negative-control.json`.

### Replay scope is explicit but not self-contained

The transcript consistency check is fully replayable from the report package using Python alone. Re-running the underlying V1/LSP and memory experiments needs the specified local Lean/Lake and Aeneas artifacts, and the memory monitor uses macOS `proc_pidinfo` plus `memory_pressure`. Those assets were already installed locally; this report did not download or install dependencies. The report packages retain the small generated fixture, exact commands, scripts, process monitor source, and raw protocol/resource observations while omitting large Lean/Aeneas source and build trees.

Basis: source/support audit + local replay.

## Boundaries

The checker verifies only presence and consistency of selected recorded fields. It cannot prove that the transcript came from the stated binary, validate every protocol frame, reproduce a result without the linked toolchain artifacts, or establish the correctness of the theorem or the source-to-model relation. Hashes and execution provenance remain necessary. The deliberate mutation exercises one failure class, not every proposed harness negative control.

## Evidence

- Query lifecycle report: [`anneal-v1-interactive-dependency-invalidation-2026-09-28`](../anneal-v1-interactive-dependency-invalidation-2026-09-28/REPORT.md).
- Concurrent server report: [`lean-v1-concurrent-workspace-server-reuse-2026-09-28`](../lean-v1-concurrent-workspace-server-reuse-2026-09-28/REPORT.md).
- Checker: `support/check-evidence.py`; its successful run and negative-control output are retained under `support/`.

## Revalidation

Run `python3 support/check-evidence.py --query PATH_TO_QUERY_TRANSCRIPT --concurrency PATH_TO_CONCURRENCY_TRANSCRIPT`. To replay the negative control, copy the query transcript to a temporary file, replace the fresh-process empty goal with `{"goals": [], "rendered": "no goals"}`, and rerun the checker; it must fail. For actual execution revalidation, follow the procedures in the two linked reports with the exact local toolchain revisions.
