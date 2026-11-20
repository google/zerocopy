# toy-lens

Lean project of the package `lens-frame-laws-product-decomposition-and-lawful-put-classification`.
Every definition, example, main statement, supporting lemma, counterexample and non-vacuity
witness is proved.

* Lean: `leanprover/lean4:v4.34.1` (see `lean-toolchain`), no Mathlib, no dependencies.
* Build: `lake build`.
* Axiom and statement audit (after `lake build`):

      lake env lean scripts/audit/Audit.lean > /tmp/lens_audit.out
      python3 scripts/audit/check_audit.py /tmp/lens_audit.out ../audit

* Everything lives in namespace `Toy.Lens`.

| module | contents |
| --- | --- |
| `Toy/Lens/Basic.lean` | `Lens`, `GetPut`, `PutGet`, `PutPut`, `WellBehaved`, `VeryWellBehaved`; example lenses |
| `Toy/Lens/Pair.lean` | `PutIndep` (one direction), `PutComm`, `JointExt` |
| `Toy/Lens/Family.lean` | `update`, `PairwiseIndep`, `FamJointExt`, `famGet`, `coord` |
| `Toy/Lens/Decomposition.lean` | `Intertwines`, `pairGet`, `pairPut`, `IsProductDecomposition`, `IsPiDecomposition`; derived-law lemmas; **F1, F2** |
| `Toy/Lens/Complement.lean` | `Equiv`, `HasConstantComplement`, `Fiber`, `fiberFrom`, `HasGhostComplement`; **F3** |
| `Toy/Lens/Unfolded.lean` | elementary readings of the bundled conclusions |
| `Toy/Lens/Tightness.lean` | tightness witnesses for F1, F1-inverse, F1-laws, F2, F2-laws, F3; infinite-index counterexamples |
| `Toy/Lens/Partial.lean` | `PLens`, variant-scoped laws; **F5**; unscoped-law counterexamples; scoped derived laws |
| `Toy/Lens/Classification.lean` | `GetFiber`, `FiberMaps`, `FiberMaps.Coherent`, `toPut`, `ofPut`, `factorial`; **F6** and its counterexamples and edge cases |

`scripts/finite_model_checks/` holds Python scripts that test statements for refutation on tiny
finite models. They are evidence, not proofs, and are not part of the build.
