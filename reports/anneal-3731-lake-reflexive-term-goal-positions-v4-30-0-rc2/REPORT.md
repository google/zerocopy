# Lake-launched tactic and term goals inside one reflexive proof

## Summary

In one pinned Lean/Lake 4.30.0-rc2 imported proof, `$/lean/plainGoal` and rich `Lean.Widget.getInteractiveGoals` agreed at nine exact positions, while `$/lean/plainTermGoal` exposed a term goal inside `Eq.refl depValue` where both tactic-goal APIs returned an empty goal list. At the `Eq.refl` expression, the term goal was `⊢ depValue = depValue` over source range `(3,8)`–`(3,24)`; within its `depValue` argument it was `⊢ Nat` over `(3,16)`–`(3,24)`. A separate fresh batch process accepted the same source text and reported no theorem axioms.

This adds one Lake-launched, local-import term-position component for #3731 I043 and the #3730 C02 plain/rich boundary. The equality is reflexive and the proof is deliberately small: it demonstrates these API responses at exact positions, not a general proof-state selection rule or an Anneal verification contract.

## Applicability

The subject is installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` Lean/Lake 4.30.0-rc2 on macOS arm64. A local `probe_dep` package defines `depValue : Nat := 7`. The `position_probe` package imports it and proves `depValue = depValue` with `by exact Eq.refl depValue`. The exact `Proof.lean` bytes opened in one Lake server matched the on-disk proof. A separate fresh `Batch-term_proof.lean` file held identical source text under the same prepared import but had a different filename.

One `lake --no-cache serve` process opened document version 1, completed `textDocument/waitForDiagnostics`, connected one rich RPC session, and answered nine sequential triples of `plainGoal`, `getInteractiveGoals`, and `plainTermGoal`. Positions and returned ranges are zero-based UTF-16 LSP coordinates; the relevant line is ASCII. No edit, worker restart, RPC reconnect, or reference dereference occurred.

The probe used only already installed local tools, `LEAN_NUM_THREADS=1`, `LAKE_NO_NET=1`, an empty test home/cache, and `/usr/bin/sandbox-exec` with network denied. Immediate preflight observed 27.23% reclaimable memory and 23,440,347,136 free disk bytes. Across 26 samples during 5.7 seconds, process-group RSS reached at most 1,023,920 KiB, below the 1.5 GiB sampled cap. A five-minute wall deadline was enforced. Sampling cannot exclude a shorter transient peak.

## Findings

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain/rich tactic goals | `plainTermGoal` |
| --- | ---: | --- | --- |
| Start of `exact` | `(3,2)` | One goal, `⊢ depValue = depValue` | Null |
| Inside `exact` | `(3,5)` | Empty lists | Null |
| Start/inside `Eq.refl` | `(3,8)`, `(3,11)` | Empty lists | `⊢ depValue = depValue`, range `(3,8)`–`(3,24)` |
| Start/inside argument `depValue` | `(3,16)`, `(3,20)` | Empty lists | `⊢ Nat`, range `(3,16)`–`(3,24)` |
| End of tactic line | `(3,24)` | Empty lists | `⊢ Nat`, same argument range |
| Next line and EOF | `(4,0)`, `(6,0)` | JSON null | Null |

The one nonempty tactic-goal pair matched between plain and rich display: the rich target rendered as `depValue = depValue` and had no hypotheses. At six positions on the tactic line, both tactic APIs returned empty lists; the term API was nonnull at five of them. The term API's result changed from the equality expected of `Eq.refl depValue` to the `Nat` expected of its argument as the cursor moved into `depValue`. These are exact observed selections. The result at `(3,24)` is a sampled end position; it does not establish a general inclusive-end rule. **Basis: execution**, nine triples and their direct replies in `support/results.json`.

The clean Lake build and setup-file exited 0 and identified a local `Dep.olean`. Fresh `lake --no-cache env lean --json Batch-term_proof.lean` exited 0, reported that `term_proof` depends on no axioms, and evaluated `depValue` to 7. Live diagnostics had only informational messages and no errors; the server shut down with exit 0. Whole-file batch acceptance is a separate observation from the cursor responses. **Basis: execution**, retained build, setup, batch, diagnostics and process events.

## Boundaries

- The theorem is a reflexive equality discharged by `Eq.refl`; its batch success and no-axiom print are controls for this fixture, not evidence about harder obligations, generalized term elaboration, or Anneal claim acceptance.
- `plainGoal` and `getInteractiveGoals` were compared for tactic-goal availability at nine positions. The rich API was not used to obtain term goals; `plainTermGoal` supplied those separately. The two returned term goals are local elaboration guidance, not a fresh verification verdict.
- One imported module, one disk-identical successful document version, one server and one RPC session were tested. Nested term forms, combinators, macros, whitespace changes, syntax errors, unsaved edits, worker/RPC reconnect, rich object dereference/expiry, cancellation and concurrent clients remain untested in this cell.
- This fixture has no Anneal launcher, generated/projected proof, Rust source map, exact-version/import fence, editor/MCP transport or complete product obligation set. It does not close I043/C02's product gate.
- The fresh batch file and opened proof have identical text but different filenames; equal elaboration under this local import does not establish equal module identity in arbitrary workspaces.

## Evidence

- `support/probe.py` creates the local Lake packages, clean build, setup and batch control, then runs one guarded server and records 27 goal requests with their replies, diagnostics and resource observations. It uses only Python's standard library and installed tools; no download or installation occurred.
- `support/results.json` retains normalized commands and outputs, source text and artifact hashes, all nine plain/rich/term triples with exact positions/ranges, diagnostics and cleanup. `$WORK`, `$WORK_URI`, and `$TOOLCHAIN` replace local absolute paths in retained text.
- `support/fixture/Dep.lean` and `support/fixture/Proof.lean` retain the exact source bytes. `support/check.py` validates those bytes, pinned binary hashes, batch/import controls, all nine triples, diagnostics, resource gates and shutdown offline.
- Recorded Lake and Lean binary SHA-256 values are `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. Retained probe/result SHA-256 values are `9f17d45428378c76bd5995e3c7ea20b31223562b0a594dd75cba52f78576fb16` and `71c94390d16bbfaa1f0e5e5c5260de689fcdd68febf40028a7f622b0149d0455`.

## Revalidation

Run `python3 -B support/check.py` from this package to validate retained evidence without starting Lean or Lake. To reacquire this one cell on the same installed pin under the stated resource gates, run `python3 -B support/probe.py --work /new/absent/private/path --output /new/results.json`, then compare source/binary hashes, build/setup/batch exits, all nine exact plain/rich/term responses and ranges, diagnostics, and shutdown. A later toolchain or Anneal-generated proof requires a new subject-specific run.
