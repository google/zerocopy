# E10: an external Lean model changes while Aeneas output stays fixed

Observed 2026-09-29 with pinned Charon, one-shot Aeneas and Lean 4.30.0-rc2. A tiny Rust function calls an `extern "C" external_double`. One LLBC input was translated twice, before and after the external-model variants were prepared. Every generated Aeneas file, including the `FunsExternal_Template.lean`, had the same byte digest in both runs. The **actual** `Source/FunsExternal.lean` model is a separate Lean file supplied by this experiment, not an Aeneas compiled external registry or an Aeneas output overwritten by regeneration.

| Fresh external Lean model | Fresh import/build result | Proof of `external_call 1 = .ok 2` | `#print axioms external_call` |
| --- | --- | --- | --- |
| Concrete `external_double x = x + x` | All modules compile | Passes | No axioms reported |
| Wrong concrete `external_double x = x + 2` | All modules compile | Fails | Standard Lean axioms listed; no external axiom |
| `axiom external_double` | All modules compile | Fails | Lists `external_double` |
| Missing declaration | `Funs` fails to compile | No proof run | Unavailable |

The generated `Funs.lean` is byte-identical across all four cases, yet the external-model source and imported OLean hashes differ. In a deliberate **negative cache control**, a directory with the wrong external-model source was given concrete-model OLean files. Direct batch Lean accepted the proof (exit 0), while a fresh wrong-model rebuild rejected it (exit 1). A key over generated-tree bytes alone therefore accepts a result from the wrong imported environment. This is an explicit forced-stale-artifact control, not an Anneal cache observation or a claim about Lake's source-traced rebuild policy.

A direct Lean server opened the concrete proof, then the external model source and dependent OLean files were rebuilt to the wrong model while that server and its file-worker child remained alive. After a proof-document edit, the old file worker still reported the concrete model's axiom information and no proof error. A clean new server/file-worker pair on the same files reported the wrong model's axiom information and the failed proof. `support/results.json` retains process trees/PIDs, exact OLean before/after hashes, JSON-RPC messages and diagnostics. This is component evidence that source/artifact replacement needs an explicit worker import-context refresh or replacement; it does not say an Anneal worker would behave this way.

**Scope.** E10 is directly exercised: unchanged generated code with independently changed external Lean source changes fresh proof acceptance and axiom dependencies. It informs I050's transitive import invalidation and I147's source/artifact versus worker-state identity. I082 remains limited to this *Lean source* model; compiled Aeneas registries, translator options, namespace collisions and library revisions were not varied. The run uses one tiny `extern` and one proof, at most one live server plus one sequential batch compiler. It does not establish general external-model semantics or Rust-level equivalence.

**Replay.** From this directory run `python3 support/probe.py`, then `python3 support/check.py`. The standard-library probe uses cached pinned binaries, a 5-GiB free-disk preflight, no installs, and replaces only this package's `support/work` and `support/results.json`. Copy the package first if retaining the original observation matters.
