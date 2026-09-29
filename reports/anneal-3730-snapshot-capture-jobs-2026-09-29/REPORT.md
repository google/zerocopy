# Controlled snapshot capture and subprocess publication probes

## Summary

Sequentially reading and revalidating files through a mutable generation pointer accepted a mixed snapshot under a controlled A/B/A/B schedule on APFS. Resolving one immutable generation directory before reading both files kept the pair coherent across a pointer swap. Separately, a small subprocess stage adapter showed that cancellation alone cannot be the publication guard: an old stage completed after a newer one and would have replaced the current result under last-completion-wins, while a generation fence rejected it.

These are executable counterexamples and prototype contracts. The backend is deliberately fake; the result does **not** establish that Anneal, Charon, Aeneas, Lake, or Lean currently has the modeled behavior.

## Applicability

The experiment ran on macOS 26.6.2 (25G83), arm64, APFS data volume, with CPython 3.14.7. `support/host.txt` records the observed environment and `support/probe.py` hash. The filesystem test uses two complete, immutable two-file directories and atomic `os.replace` of a symlink named `current`. The job test uses eight real Python child processes as fake stages, with explicit gate files to fix completion order. Each stage receives a JSON request and writes a separate JSON result file; stdout and stderr are captured as logs.

The stage request contains a causal `epoch` and a `semantic` object holding representative subject, source, model, import, and proof digests. These fields are illustrative; their hash values are not actual compiler or Lean artifacts. The engine's current-generation and consumer checks are a prototype for issue [#3731](https://github.com/google/zerocopy/issues/3731), especially I005–I007, I010–I011, I013, I145, and I157. This package adds an actual process and filesystem interleaving to the earlier finite model in `anneal-interactive-model-probes-2026-09-29`.

## Findings

### Sequential per-file revalidation is not a coherent snapshot witness

The fixture's only complete generations are `A = (left-0, right-0)` and `B = (left-1, right-1)`. The reader opened `current/left.txt` while `current -> A`, then `current/right.txt` after the pointer switched to `B`. Its captured pair was `(left-0, right-1)`, which matches neither generation. With the pointer held at `B`, rechecking the left file detected the change (negative control). Under A/B/A/B pointer changes, sequentially rechecking left at `A` and right at `B` matched both captured bytes and falsely accepted that pair. The pair never existed under one pointer value.

This falsifies a proposed capture rule that validates independently reopened files one after another and treats all matches as proof of a common generation. It does not falsify every read-and-revalidate algorithm: a coordinator generation/epoch, a correctly checked manifest, or stronger snapshot isolation could change the result. In the paired control, the reader resolved `current` once to immutable `A`; after the pointer moved to `B`, both reads through that pinned directory returned `(left-0, right-0)`.

Basis: **execution**, `support/probe.py` `capture_probe`, `support/raw-results.json` `capture`. The design consequence is to preserve a common capture witness and avoid resolving a mutable locator separately for each source/artifact read. This partially informs I010/I011/I013/I145; it does not determine the minimum complete cross-layer identity.

### Completion order cannot authorize publication

The fake stage `old-late` began at epoch 3 with model digest A. A newer epoch 4 stage with model digest B completed first and published. Epoch 3 then completed successfully. A last-completion-wins assignment would have left digest `8a72f357...` as current, while the fenced engine retained epoch 4's digest `9d7b7af5...` and classified the late result `stale-generation`. The stdout of both successful processes deliberately began with `diagnostic-looking stdout: ERROR old-generation`; the adapter accepted only the separate structured result, checked its request echo and semantic digest, and treated logs as logs.

The result supports a narrow contract: a stage output may be reusable by content, but current publication needs a causal fence after work completes. Killing or asking a process to cancel is an optimization; the prototype's old stage was allowed to finish and could not replace the current result. This partially informs I005/I006/I007/I011/I145.

Basis: **execution** of real subprocess ordering in `jobs_probe`, with results and captured streams in `support/raw-results.json` `jobs.events` and `jobs.out_of_order`; **derived** design interpretation. It does not show an Anneal race.

### Consumer ownership, stage errors, and shell reuse have separate checks

One stage had two consumers. Cancelling `editor` left `agent` subscribed, so the completed result published. In a second run, both consumers cancelled before the child finished; the child still returned success, and the result was classified `no-consumers`. A nonzero child exit with a partial result was `process-failed`; zero exit with malformed JSON was `invalid-result`; neither published. This keeps caller cancellation, child completion, result validity, and current publication distinct in the prototype.

Two fresh one-shot shell invocations named `batch` and `live` used the same engine and fake stage contract and returned the same semantic digest for identical semantic input. This checks only that the prototype can be invoked through two shells. It does not compare Anneal's current CLI with a live driver or show Lean theorem equivalence.

Basis: **execution**, `support/raw-results.json` `jobs.events` and `paired_batch_live_semantic_digests`. The narrow design consequence is that a structured stage boundary can insulate semantic results from progress/log text and can allow shared jobs without binding child-process lifetime to one consumer. This partially informs I006/I007/I157.

## Boundaries

- **Not examined:** actual Anneal V2 orchestration, real Charon/Aeneas/Lean outputs, Lake publication, LSP/MCP transports, real source projections, and proof verification. The prototype's semantic digests are invented fixture values.
- **Not examined:** large trees, renames, generated-file deletion, symlink attack resistance, cross-filesystem atomicity, crash durability, retention/garbage collection, or a concurrent writer mutating a supposedly immutable generation directory.
- **Unknown:** whether a concrete read-and-revalidate design with a correctly managed workspace epoch can preserve coherence without immutable materialization. This probe only rejects the weaker per-file sequential check shown here.
- **Not examined:** true OS cancellation or signal handling. `cancel` removes a consumer; the child intentionally keeps running. The result proves the need for a publication check under that schedule, not child termination behavior.
- **Not examined:** the full ablation list in I145, the complete edit/cancellation matrix in I005, or current CLI comparison and reconstruction in I157. I147/I149 and the remaining I001–I040 scenarios require separate evidence.

## Evidence

- `support/probe.py` is the complete executable harness, SHA-256 `fb1a7cbdff9cdb7b66a0f36234756af52c4862508dc5010735d4263d5a1995da`.
- `support/raw-results.json` preserves the capture witness, eight child invocations' exit codes, stdout/stderr, raw result bytes, adapter classifications, and publication outcomes. `support/command.stdout` preserves the concise successful invocation output.
- `support/host.txt` records Python, macOS/kernel, filesystem mount, script hash, and parent reference checkout commit `37a0ecd080d333f93bfe900d9c7dab193608e478`. The scratch paths were under the report package's APFS data volume and removed after the run; the exact fixture generation and gate logic remains in the script.
- Issue [#3730](https://github.com/google/zerocopy/issues/3730) proposes snapshot/race/cancellation experiments; issue [#3731](https://github.com/google/zerocopy/issues/3731) consolidates them as the IDs above. The existing coverage audit's `support/investigation-matrix.csv` gives their full requested dimensions and is not modified by this package.

Reproduce from this package directory with `python3 support/probe.py`. It writes `support/raw-results.json`; the observed command output was `{"capture_aba_false_accept": true, "events": 8, "stale_completion_rejected": true}`. The `old-late` and `new-first` order is controlled by gate files, not timing sleeps; sleeps only poll child readiness.

## Revalidation

Run `python3 support/probe.py` at another host/tool pin and compare the assertions plus raw event sequence. To test an actual Anneal design, replace the fake stage with its structured Charon/Aeneas/Lake/Lean adapters and carry the same captured generation ID across each handoff; induce B-before-A completion and a source/artifact pointer ABA; compare every accepted result with a fresh batch oracle for that captured input. Do not promote the fixture's semantic digest equality to proof or source-level claim equivalence.
