# Pinned Aeneas namespace move and Lean proof context

## Result

A Rust helper moved from `core::use_step` to `moved::core::use_step` while its body and the caller's behavior stayed the same. At the pinned Charon/Aeneas tools, the generated Lean helper changed from `move_probe.core.use_step` to `move_probe.moved.core.use_step`; `move_probe.caller` retained its name. Fresh Lean compilation and `rfl` proofs for the caller and each generation's helper passed. A fresh consumer of the moved generation rejected the old helper name as an unknown identifier. This is a distinct I084 namespace-move control beyond the prior reorder and signature fixtures.

## Scope and method

`support/probe.py` built two source variants with pinned Charon `rustc --preset aeneas`, translated each LLBC with pinned one-shot Aeneas `-backend lean -sequential -split-files -gen-lib-entry`, then compiled each complete generated module chain with Lean 4.30.0-rc2 and the cached Aeneas runtime. The complete Rust, LLBC, generated Lean, compiled OLean, proof source, CLI stdout/stderr, exit codes, and SHA-256s are retained under `support/work` and `support/raw-results.json`. Both proof outputs list only Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound` axioms; neither lists `sorryAx`.

| Variant | Generated helper | Generated caller | Fresh proof | Old helper lookup |
| --- | --- | --- | --- | --- |
| Base | `move_probe.core.use_step` | `move_probe.caller` | pass | present |
| Nested move | `move_probe.moved.core.use_step` | `move_probe.caller` | pass | unknown identifier |

The `Funs.lean` hashes differ; `Types.lean` and the entry file hashes match. A proof annotation naming the helper therefore needs an identity update across this move even though the selected caller theorem remains expressible and passes. This result does not establish an authenticated source-to-generated declaration map, automatic proof migration, stability for arbitrary moves or signatures, or Anneal integration.

## Recheck

Run `python3 support/check.py` for the retained offline check. To re-execute the pinned fixture, run `python3 support/probe.py` and then the checker. The probe clears only its own `support/work` directory. The subject is the exact local binaries and source bytes in `support/raw-results.json`; another release requires a new comparison.
