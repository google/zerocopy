# Clean/prepared and batch/live equivalence at cached Lean 4.29 and 4.30-rc2 pins

## Summary

A tiny two-file Lean/Lake package was run separately with cached **Lean 4.29.0** and **Lean 4.30.0-rc2** on arm64 macOS. In each version, a clean built tree and an exact copied prepared tree agreed: fresh direct and `lake env` batch checks exited 0, evaluated `depValue` as 7, printed that the theorem has no axioms, and direct, `lake env lean --server`, and `lake serve` live queries returned **no goals** with the same informational diagnostics. `lake --no-cache --no-build setup-file` succeeded for both trees. The checked source/OLean/ILean/trace inventories of the prepared tree were unchanged after those reads. This establishes a small within-version equivalence cell, not a general prepared-environment contract.

The paired source/artifact controls exposed a launch-mode difference in **both** versions. Editing only `Dep.lean` from 7 to 9 while retaining the value-7 OLean left fresh direct and `lake env` batch checks successful with value 7; `lake --no-build build Dep` reported out of date (exit 3). A fresh live document opened by each of the three server modes rebuilt the dependency in its own isolated copy, then reported the remaining goal `⊢ depValue + 1 = 8`, an error that `decide` found the proposition false, and value 9. Thus “fresh process” alone does not make batch and live use the same imported generation. The operation and setup path must be part of the oracle contract.

Replacing only the OLean bytes with a valid value-9 artifact while leaving source at 7 made fresh direct and `lake env` batch fail (exit 1), report value 9, and show `sorryAx` in the failed theorem's recovery path. Lake's no-build target check nevertheless exited 0 for this overwritten object. In all three server modes, an already open worker kept answering “no goals” after an explicit watched-file notification; closing and reopening the same URI exposed one goal and the value-9 error. Fresh batch failed. This is a pin-specific stale-worker and artifact-integrity counterexample, not an Anneal implementation result.

## Applicability

The subjects are the cached executable pairs in `REPORT.json`: Lean/Lake `v4.29.0` (`98dc76e3…`) and `v4.30.0-rc2` (`3dc1a088…`). Each version built and consumed only its **own** OLean files. The same ASCII source bytes were used at both pins, but no cross-version OLean compatibility test was attempted. The host had 8 GiB RAM and 51 GiB free disk at preflight; the disposable run-4 work tree occupied 1.2 MiB. Commands were sequential, with `LEAN_NUM_THREADS=1`, a version-pinned `PATH`/`ELAN_TOOLCHAIN`, an isolated HOME and Lake cache, `LAKE_ARTIFACT_CACHE=false`, and 45-second batch-command timeouts (90 seconds for initial build). No network fetch, installation, Mathlib, native plugin, Rust, Aeneas, or Anneal generator was involved.

The fixture is:

```lean
-- Dep.lean initially
def depValue : Nat := 7

-- Generated.lean
import Dep
theorem generatedEq : depValue + 1 = 8 := by
  decide
#print axioms generatedEq
#eval depValue
```

`support/probe.py` creates the package and isolated copies, records exact commands, responses, source/artifact hashes and LSP messages in `support/results.json`; `support/analyze.py` asserts the outcomes and writes `support/summary.json` plus the 34-row `support/matrix.csv`. The work tree is scratch, not required for replay.

## Findings

### Matched clean and prepared consumers

For each version, `lake build Dep` produced the baseline import. The prepared tree was an exact copy of the clean tree, including `.lake`. Both paths passed direct `lean --json Generated.lean`, `lake env lean --json Generated.lean`, and `lake --no-cache --no-build setup-file Generated.lean`. The three live launch forms in each path completed diagnostics version 1 and returned an empty goal list. Batch diagnostics comprised the no-axioms message and `#eval` value 7; live diagnostics included both. The checked `.olean`, `.ilean`, `.trace`, source and control-file hashes were equal before and after the prepared reads. **Basis: execution.** This copy did not remove the original clean path or make producer files read-only, and the inventory does not prove absence of writes to unlisted files.

| Pin | Baseline `Dep.olean` SHA-256 | Value-9 replacement `Dep.olean` SHA-256 |
| --- | --- | --- |
| 4.29.0 | `f325eef7ec1d358718996207a81494ee92c3ec9d3cd4285e5ab8f0cb2520143d` | `f1389a240dafcea9b8cf03956cb7f877b356911b32ce4646b3b046ace5cac621` |
| 4.30.0-rc2 | `3f03e66c934405d32f94a087c91e19021d71078cae3e8e33d7d9eadd3e415772` | `0f0fbd523ef1ce3fce88465a688f7a786beb38969ff690b97c51778d5da30ec0` |

The proof source SHA-256 was `4c7906672af8fc5437d9c137ccca99c1161f902d2efa1f9ae4e415ed9408a161` in both versions. The two baseline OLean hashes differ, so logical agreement here is not byte identity across Lean versions.

### Source changes and artifact changes select different generations

In the source-only copies, `Dep.lean` changed to 9 (SHA-256 `f24ea593a7ec12a08b2ab0c096b8babdbf9baeaef4c4a46286e12bf19959c0d0`) while OLean stayed at value 7. Both fresh batch modes still exited 0 and printed value 7/no axioms. A no-build Lake target check exited 3 as out of date. Each live mode used a **separate pristine copy** of this same source-only state; opening the proof caused the copied OLean hash to change and returned value 9, one goal and the false-proposition diagnostic. The newly built OLean was `64adab27…` at 4.29.0 and `be364799…` at 4.30.0-rc2; full hashes are in `support/summary.json`. Direct `lean --server` produced a `Built Dep` progress diagnostic, so this is observed server setup behavior, not an assumption that only `lake serve` builds.

In the artifact-only copies, source stayed at 7 (SHA-256 `15bbf60d162408dade43c6e618dd0d09b28c8fdeb7528c80e40329908f12b7a2`) while OLean was replaced by a valid independently built value-9 OLean. Both fresh batch modes exited 1 with the false-proposition error and `#eval` 9. `#print axioms` then listed `sorryAx` because the failing theorem was recovered by Lean; that is **not** a successfully verified axiom-free theorem. `lake --no-cache --no-build build Dep` exited 0 and reported up to date even though the imported OLean bytes had been replaced. **Basis: execution.** This manual local substitution does not show a cache hash collision or remote-cache acceptance rule; it tests what this no-build path checks after a valid file is overwritten.

### Old live workers and reopened workers disagree after artifact replacement

In six isolated sessions (two versions × direct, `lake env`, and `lake serve`), the open proof returned no goals before and after replacing OLean and sending `workspace/didChangeWatchedFiles` for the artifact URI. A close/reopen of the same proof URI at document version 2 returned `⊢ depValue + 1 = 8` and published an error that `decide` proved the proposition false, a `sorryAx` recovery message and value 9. Fresh batch Lean exited 1. The `waitForDiagnostics` barriers completed before each goal query. **Basis: execution.** The watched-file notification was sent by this harness; it is not a test of a native filesystem watcher. Close/reopen is a demonstrated refresh workaround for this fixture at these pins, but no upgrade that removes the need for it was tested.

## Residuals for the audit agenda

| #3731 item | New evidence | Remaining work |
| --- | --- | --- |
| I131 independent batch oracle | Fresh direct and Lake batch processes plus theorem/axiom/value checks contrast with live goals. | Rebuild the real Rust→Charon→Aeneas input closure and imported Lean dependencies independently; fresh Lean here still trusts a selected OLean. |
| I132 comparator calibration | The compact comparator distinguishes same-source logical agreement from source-only and artifact-only mismatches, including `sorryAx` on a failed theorem. | Broader generated declarations, obligation sets, diagnostics provenance, benign differences and false-acceptance mutants. |
| I135 interaction matrix | Two toolchain pins × clean/prepared × batch/live launch forms, plus independent source/artifact mutations and stale/reopen controls. | Higher-order source/import/cache/plugin/worker concurrency and actual Anneal pipeline combinations. |
| I136 cross-version boundaries | The same fixture behavior reproduced on two cached pins without mixing their artifacts. | A selected later compatible release, independent host/operator and a true upgrade/migration path. |
| I158 workaround deletion | Close/reopen refresh succeeded after artifact replacement at both pins; watcher notification alone did not. | Select a newer supported tuple and re-run before deleting any workaround; this run shows no deletion justification. |
| I159 architecture challenge | Source-only batch/live divergence, stale old worker and no-build acceptance of overwritten valid OLean challenge simplistic generation/acceptance rules. | Falsify the chosen Anneal architecture with real generated workspaces, cache manifest/integrity, and concurrent failures. |

## Boundaries and evidence

The preparation comparison uses a copied local tree, not an omnibus archive, remote cache, producer-removed relocation, read-only dependency store or full semantic oracle. The theorem is tiny and has no Rust-side obligation mapping. The `#print axioms` message is only a Lean-level trust signal; it does not attest the model source. All six refresh sessions were sequential on the same machine. No claim is made about newer Lean versions, cross-version binary compatibility, Mathlib, plugins, or a production Anneal bridge.

- `support/results.json` (SHA-256 `dda8bfc937dc7e5ddb3e735a6e053289f3166fb09e175c34b02ef2a0f01c066d`) preserves sanitized commands, exits, complete LSP requests/notifications, goals, diagnostics and file hashes for run 4.
- `support/summary.json`, `support/matrix.csv` and `support/analyze.py` preserve the asserted oracle and its derivation from raw outcomes.
- `support/probe.py` (SHA-256 `2dc54391312353693ac8aceaef143cbc3e274934cf2cfa4f3ce79abfc01324d4`) regenerates the fixture using only the cached binaries. Binary hashes and exact version strings are in `REPORT.json` and `support/summary.json`.

To replay on this host, from the report package run `python3 support/probe.py --work /new/absent/conversation-scratch/path` and then `python3 support/analyze.py`. The work path must not exist; no download or installation is performed. Compare semantic outcomes and per-run hashes, not timing or cross-path artifact byte equality. Package structure can be checked with `tools/reference.py::_load_report`.
