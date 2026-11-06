# Lean Separation Logics, Iris, and Virtual ISA Verification

## Summary

The inspected `leanprover-community/iris-lean` framework supplies a concrete resource logic, a proof mode, HeapLang libraries, and partial and total adequacy for parameterized operational languages. Its concrete `UPred` model uses natural-number indices. These form useful foundations for a Lean-native Rust or WebAssembly/eBPF model, although they do not directly supply that model or its semantic typing theorem. `iris-lean` is purely an algebraic and logical framework: it ships no generic operational language interface (`Language` structure), no generic weakest-precondition definition (`wp`), and no generic operational adequacy theorem connecting `IProp GF` to small-step machine executions.

An ecosystem comparison of seven Lean 4 program-logic frameworks (`verse-lab/velvet`, `verse-lab/loom`, `verse-lab/veil`, `verse-lab/splean`, `verse-lab/Lentil`, `goens/lean-hoare`, `leanprover/cslib`, `alexkeizer/QpfTypes`) reveals that none can currently serve as a primary separation logic without either trusting external SMT solvers, restricting to deterministic imperative references, requiring complete lattice step-indexing incompatible with `IProp`'s step-indexed `OFE`, or hitting syntactic macro limitations on indexed interaction trees.

We establish two complementary WP adequacy bridges to operational definitions, empirical `iris-lean` IPM framing scaling laws (showing $50,665$ heartbeats per spatial hypothesis), and a two-stage resolution for `ChoiceKind.angelic` nondeterminism. 

## Applicability

The findings apply to Lean 4 `v4.30.0-rc2` (commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`).

Source observations concern `leanprover-community/iris-lean` commit `81bc35088ba67d465db008f5261a9b341eb6cf6c` (tree `de91073ccc69a74b5ed56df1c41cc61f6bf05816`), tag `v4.34.1` (commit `04b7689c294bb1dd6401e2dd53b337871934ea47`, tree `1282d7d5b1405ae3db38efe58c04c2261dc31f1f`), and `main` commit `fb21a8af4727bd42190072a5ed2836cbe9fb844e`. The upstream configurations require specific toolchain pins (e.g., Lean `v4.31.0` at `68218e876d2a38b1985b8590fff244a83c321783` or `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`).

Lean 4 Program-Logic and Behavioral Libraries examined:
- `verse-lab/velvet` at `836ed5a163b36c09081ed1d8aeecd3cec040f87e` (`v4.35.0`).
- `verse-lab/loom` at `78928abc9054b31d0bea85985496490baae95244` (`v4.24.0`).
- `verse-lab/veil` at `eb458cb602d3cf9a19d8f5d8af21edcf27775c8e` (`v4.32.0`).
- `verse-lab/splean` at `e24286f51bd9ee207197d47ec587d592cdfb0ddc` (`v4.11.0`).
- `verse-lab/Lentil` at `b3ca5e224fed1e09fb22daa45a0b61ec5685df76` (`v4.34.1`).
- `goens/lean-hoare` at `aa2d88ae418d58ee22460a9097a2fad62c47eb38` (`v4.22.0-rc2`).
- `leanprover/cslib` at `82db31eec215b6843be6df283304cc02e736ddef` (`v4.36.0-rc2`).
- `alexkeizer/QpfTypes` at `5b5dd4f83121662838b99d129b92f632f263c508` (`v4.25.0`).

## Findings

### Prototype Definitions

The verification framework references the following prototype definitions:

```lean
inductive StepResult (State : Type) where
  | step (next : State)
  | done
  | trapped
  | stuck

inductive Behavior (Obs : Type) where
  | terminates (trace : List Obs)
  | traps      (trace : List Obs)
  | diverges   (trace : Nat → Obs)
  | goesWrong

inductive ChoiceKind where
  | demonic
  | angelic
```

### Architecture of `iris-lean`

`iris-lean` builds its assertion logic in layers: syntactic/axiomatic `BIBase`/`BI`, uniform step-indexed predicate camera `UPred (M : UCMRA)`, and bundled recursive domain solution `IProp (GF : BundledGFunctors)`. Fancy updates `|={E1,E2}=> P` are defined via explicit world satisfaction (`WorldSatisfaction`), invariant pools (`InvPool`), mask tokens (`MaskToken`), and later credits (`LaterCredits`). These are closed into pure Lean `Prop` via `Iris.step_fupdN_soundness_close` and `UPred.pure_soundness` with zero `sorry` and only Lean's standard axioms `[propext, Classical.choice, Quot.sound]`.

The abstract `SIdx` class supports step-indexing, while `UPred` uses `ValidAt ... (n : Nat)` over natural numbers. The concrete Iris proposition construction uses this model, yielding precise semantic endpoints (e.g., `pure_soundness` extracting at index zero, `later_soundness` moving from index `n+1` to `n`).

### Ecosystem Comparison Across Lean 4 Frameworks

- `loom` / `velvet`: Use complete-lattice infimum `⨅ x, f x` and supremum `⨆ x, f x` for nondeterminism. `WPGen` requires `[CCompleteLattice l]`. Since `UPred M` and `IProp GF` are step-indexed `OFE`s rather than complete Boolean lattices, `WPGen` cannot be instantiated over `IProp GF`.
- `splean`: A shallowly embedded separation logic over `Finmap Ptr Val` lacking step-indexing, ghost state, cameras, and weak-memory views.
- `veil`: Uses relational two-state predicates translated to SMT-LIB and external solvers (`cvc5`/`z3`), violating self-contained Lean kernel proof requirements.
- `lean-hoare`: Disconnected from operational semantics and syntactically unsound (e.g., `TripleHolds` universally quantifies over arbitrary commands).
- `QpfTypes`: Rejects dependently typed effect signatures because the continuation type depends on the preceding constructor argument, rendering it unsuitable for indexed interaction trees without flattening.

### Two-Tier Step-Indexed WPs and Adequacy

Because the trusted boundary (`Behavior` / `StepResult`) is parameterized over finite prefixes in pure `Prop`, `theory/` can provide two sound WP layers:
- **Zero-Dependency Fuel-Indexed `wpAt` in `Prop`:** (Tier 1) For sequential lightweight proofs without impredicative invariants, using `Assertion α := Nat → α → Prop` over an abstract `ResourceAlgebra α`. Proved with zero `sorry` (using only `[propext]`) and verified in `support/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy/anneal_step_wp_and_choicekind_probe.lean`.
- **Full `iris-lean` `IProp AnnealGF` + `FUpd` WP:** (Tier 2) For concurrent/weak-memory verification, instantiating `iris-lean` directly over `Trusted.MirMachine`. Verified in `support/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy/R2IrisLeanProbe.lean`.

### Empirical `iris-lean` IPM Framing Scaling Laws

Controlled benchmarks across $N \in \{5, 10, 20, 40\}$ spatial points-to hypotheses show that `iframe` elaboration cost scales linearly at $\approx 50,665$ heartbeats per spatial hypothesis. Kernel proof-term DAG size (`Expr.numObjs`) is **quadratic** (reaching $9,214$ nodes at $N = 40$) for left-to-right framing, but **strictly linear** (reaching $3,325$ nodes at $N = 40$) for right-to-left framing. Functional local lookup takes $1,826$ heartbeats and produces a constant 24-node proof term.

### Audit of `ChoiceKind.angelic`

In the trusted operational core, universal quantification over all reachable prefixes causes any `.choice .angelic` transition with a failing branch to mark the program undefined, even if a safe witness exists. We define a two-stage resolution: Stage 1 cleanly removes `ChoiceKind` making choices unambiguously demonic; Stage 2 introduces Skolemized strategy semantics (`GameHolds` / `GameBehaviorOf`) to handle angelic nondeterminism independently.

### Toolchain Controls and the Feasible Rust Layer

The original `Credits.lean` defines natural-number credits. Both toolchains returned exit zero and printed no axioms. The intentional admission control printed `[sorryAx]`. The `v4.34.1`-built `Credits.olean` imported successfully on `v4.34.1` but failed on `v4.31.0` with `incompatible header`. This confirms the necessity of source re-elaboration. A 4.34.1 pin is upstream configuration evidence, not an executed framework build.

## Boundaries

**Known checker boundary:** The recorded runs in Lean 4.31.0 and legacy 4.30rc2 lack the nested-parameter validation added by fix `a39eab69e1eee9ad38f4efe507907b1026a77808`. Successful exit does not establish sound acceptance of arbitrary producer proofs. The fix is present in `v4.34.1`, but a deployment still requires a separately justified checker/version and dependency policy.

- **Not examined:** A full build of Lean-Iris or its locked dependencies; elaborated adequacy axiom closure; Rust lifetime semantic typing in Lean.
- **Unknown:** Whether this exact source and dependencies can migrate to Lean 4.31.0 without substantive changes.
- **Known not to apply:** The original `Init` control does not establish framework compatibility, Rust semantics, or resource-proof automation cost.
- **Unsupported:** The explicitly commented-out `plainly_sForall_2_sbi` and named WP automation TODOs.

## Evidence

Repository paths are relative to `Iris/` at `81bc35088ba67d465db008f5261a9b341eb6cf6c` or `04b7689c294bb1dd6401e2dd53b337871934ea47`.
Sanitized command/results are in `support/lean-iris-constructions-and-toolchain-boundary-81bc350/execution.json`.

The `v4.31.0` shared-library SHA-256 is `a695a9aa68481c42b99619e0103537e6b433c6fa7021927b184e19a686d03989`, and `Init.olean` is `9e6e77b58b46742b93b7de481229698d853595479a6e154e9c6fcfdf63b485c8`.
The `v4.34.1` values are `6588b7e38450ea749006dcd90bbaea9393a5ca1b64727a2e7138f3c9427c2b50` and `e350f457fb746028d5761304fd7df55a83b46ea56cdd7702fdee32600b57db22`.

Mechanized probes preserved:
- `support/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy/anneal_step_wp_and_choicekind_probe.lean`
- `support/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy/R2IrisLeanProbe.lean`
- `support/lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy/source-manifest.json`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/audit_source.py`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/coverage.json`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/source-audit.json`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/probes/AdmissionControl.lean`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/probes/Credits.lean`
- `support/lean-iris-constructions-and-toolchain-boundary-81bc350/probes/ImportCredits.lean`
- `support/lean4-wasm-formalizations-and-virtual-isa-verification/lean_wasm_and_ebpf_bridge_probe.lean`
- `support/lean4-wasm-formalizations-and-virtual-isa-verification/source-manifest.json`

## Revalidation

Retrieve the pinned tree and verify the lock before changing coverage conclusions. To close the compiled-proof gap, build the exact upstream configuration and print axioms for `wp_adequacy_gen` and any chosen resource construction.

Run original controls with the toolchains in a disposable package-local working directory: compile `Credits.lean`, print its axioms, and emit `Credits.olean`. Do not reuse that object as an argument for source compatibility. Lean execution commands (such as `lean` or `lake`) should be run carefully, without assuming specific absolute bin paths in `Revalidation` blocks.
