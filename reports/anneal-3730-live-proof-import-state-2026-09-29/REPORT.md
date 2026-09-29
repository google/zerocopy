# Live proof imports require a compiled upstream generation

Observed 2026-09-29 with Lean 4.30.0-rc2 on macOS arm64. This direct Lean component experiment addresses #3730 C11 and the related #3731 I038–I040 questions about one live proof importing another. It uses tiny `A.lean` and `B.lean` modules, `lean --server`, batch `lean --json`, and controlled `.olean` rebuilds. There is no Anneal workspace, editor, annotation parser, or proof sandbox implementation in this fixture.

## Setup

Initially, `A` exports `helper (n : Nat) : n + 0 = n` and `B` imports `A` to prove the same property with `exact helper n`. `A.olean` is built before the server opens both documents. An unsaved buffer changes `A` so `helper` has type `n + 1 = n + 1` and adds `unsavedOnly : True`; later the disk source changes to the new `helper` without `unsavedOnly`. The script separately saves and rebuilds `A`, opens a new `B` URI, reopens the old `B` URI, and starts a fresh server. Both compiled A generations and their source are retained in `support/artifacts/`; `support/transcript.json` contains the complete JSON-RPC messages, readiness responses, goals, diagnostics, batch output, source text, and hashes.

## Observations

| State | A on disk / imported artifact | B result |
|---|---|---|
| Initial saved A | Old source; `A.olean` SHA-256 `a9e55ecd6b98…` | Batch exit 0; open B has no diagnostics. At the tactic start, `$/lean/plainGoal` reports `n : Nat ⊢ n + 0 = n`. |
| A dirty in an open buffer | Unsaved new `helper` plus `unsavedOnly`; disk and artifact still old | Existing B remains valid. A newly opened proof that imports A and calls `unsavedOnly` gets `Unknown identifier \`unsavedOnly\`` in direct LSP and batch Lean. |
| A saved, without rebuild | New disk source; old artifact | B batch still exits 0. Saving upstream source alone did not change what this import consumed. |
| A rebuilt | New artifact SHA-256 `a901beed39bb…` | Fresh B batch exits 1 with `Type mismatch`: `helper n` now has type `n + 1 = n + 1`, while B expects `n + 0 = n`. |
| Old B worker reused | New artifact exists; B URI remained open | Its hover still reports the old imported helper type `n + 0 = n`, and its earlier no-error diagnostic state persists. |
| New or reopened B worker | New artifact exists | Each reaches the `waitForDiagnostics` barrier and reports the same type mismatch. A fresh server does too. A new worker's helper hover reports `n + 1 = n + 1`. |

The goal query at the start of B's tactic still prints `n + 0 = n` after the import changes, because B's theorem statement did not change. It is not an import-freshness witness. The helper hover and type-mismatch diagnostic distinguish the imported generations. The transcript records exact barriers and messages, including B's `publishDiagnostics` version and ranges.

Two context controls delimit the result. With `LEAN_PATH` pointing to an empty directory, batch B reports `unknown module prefix 'A'` even though A's compiled artifact exists elsewhere. Two mutually importing but unbuilt source modules also each report an unknown imported module in both batch and live Lean; direct Lean cannot materialize that source-only cycle as an importable environment. This is a missing-artifact observation, not proof of a cycle-detection policy. A generation manager would have to reject such a dependency cycle before asking Lean to import it.

## Replay and validation

From the checkout:

```sh
python3 reports/anneal-3730-live-proof-import-state-2026-09-29/support/probe.py \
  --work /absolute/path/to/a/new-scratch-directory
python3 reports/anneal-3730-live-proof-import-state-2026-09-29/support/verify.py
```

The private work path must not exist. The probe requires at least 15 GiB free as a conservative guard and uses the already installed pinned Lean. `support/verify.py` checks the retained source/artifact SHA-256 values, exact unknown-identifier and type-mismatch messages, old/new hover types, batch exits, readiness responses, cycle failures, and server exits. No tool installation or global state change is needed.

## C11 / I038–I040 implication and residual

For this pinned direct Lean fixture, a second proof imports the upstream **compiled artifact**, not the upstream unsaved LSP buffer. A valid unsaved cross-proof reference needs an explicit materialization/build strategy or a different live dependency mechanism. Reusing an already open dependent worker after the upstream artifact changes can retain the old imported environment; the observed new/reopened/fresh workers used the new artifact. A system therefore needs provenance tying each result to the upstream generation and a refresh policy before it can claim a live proof is current.

The experiment does not test Anneal's generated proof layouts, sandbox/fork implementation, per-annotation import graph, UI save behavior, source mapping, concurrent edit races, cyclic graph rejection, or end-to-end proof acceptance. It does not establish that every Lean launch mode or future Lean version has the same worker behavior. The wrong-`LEAN_PATH` control establishes one necessary context property; it is not a complete sandbox-fidelity or security test.
