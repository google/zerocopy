# Claim-relative taint through a compiled Lean import

## Summary

With one pinned Lean 4.30.0-rc2 compiler, an imported theorem backed by an axiom made a downstream `caller` depend on that axiom; a separate `independent` theorem in the same consumer had no axiom dependency. Changing the imported source to a concrete proof without rebuilding its `.olean` left `caller` axiom-tainted. Rebuilding the artifact removed the taint. Rebuilding a `sorry` variant instead made the downstream theorem depend on `sorryAx`. All consumer Lean commands exited 0. This is a direct component acceptance-oracle control for #3731 I130, not a complete trust inventory or Anneal status implementation.

## Fixture and observations

An isolated `Dep.lean` declared `depValue : Nat := 7` and `base : depValue = 7`. The `axiom` variant proved `base` from `model`; the `concrete` variant used `decide`; the `admitted` variant used `sorry`. A fixed `Proof.lean` imported the compiled `Dep.olean`, proved `caller : depValue = 7 := base` and `independent : True := trivial`, then ran `#print axioms` for each. The script compiled each variant, recorded exact source/artifact SHA-256 values and compiler output, and checked a deliberate source/artifact clock split between axiom and concrete. One command ran at a time, each with a 15-second timeout; scratch was deleted afterward.

| Imported source and artifact | `caller` output | `independent` output |
| --- | --- | --- |
| Axiom source and axiom OLean | `depends on axioms: [model]` | `does not depend on any axioms` |
| Concrete source but retained axiom OLean | `depends on axioms: [model]` | `does not depend on any axioms` |
| Concrete source and rebuilt concrete OLean | `does not depend on any axioms` | `does not depend on any axioms` |
| Admitted source and rebuilt admitted OLean | `depends on axioms: [sorryAx]` | `does not depend on any axioms` |

The fixed proof source was byte-identical across all four checks. The stale case's concrete source hash equaled the rebuilt concrete case's source hash, while its OLean hash equaled the axiom case's artifact hash. Thus the *consumed artifact*, not the current source pathname or a successful Lean exit, determined this claim's reported axioms. The unrelated `independent` theorem is the claim-relative control. `support/results.json` retains all command streams and hashes; `support/check.py` verifies them offline. Probe SHA-256: `025d2027c85a7c144738bc8d67de9ed97392717fe076706bd6e3712ba5fa42ca`; result SHA-256: `7359ba6bdb0080698605ce1fc921cbce9f05e8700c102b31f37dfd28e5ec5f42`.

## Scope and residual

Prior acceptance and comparator reports (`anneal-3730-acceptance-oracle-matrix-2026-09-29`, `anneal-3730-cross-layer-comparator-mutants-2026-09-29`) distinguished selected axiom, concrete external model and admission cases. This experiment adds a downstream caller and intentionally reused compiled artifact with a same-module independent claim.

I130 remains partial. `#print axioms` reports Lean theorem dependencies, not semantic soundness of Rust extraction, Aeneas models, native plugins, unsafe code, kernel, or imported external assumptions. The fixture contains no Anneal generator, cache policy, agent interface, or actual source-to-obligation manifest. A product acceptance contract must bind the theorem, its consumed artifact hash, source/model generation, allowed assumption policy and native trust basis through each adapter and reused artifact.

## Revalidation

Run `python3 support/check.py` to check retained results. To rerun with the already-cached Lean pin, run `python3 support/probe.py`; this rewrites only `support/results.json`, so copy the package before reacquisition if retaining the present evidence. No dependency is downloaded or installed.
