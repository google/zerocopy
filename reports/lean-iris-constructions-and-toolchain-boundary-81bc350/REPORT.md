# Lean-Iris constructions, adequacy premises and toolchain boundary

## Summary

The inspected Lean-Iris revision supplies a concrete resource logic, a proof mode, HeapLang libraries, and partial and total adequacy for a parameterized operational language. Its concrete `UPred` model uses natural-number indices. These are useful foundations for a Lean-native Rust model, but they do not supply that model or its semantic typing theorem.

The project pins Lean 4.34.1. A bounded original control compiled from source on both Lean 4.31.0 and 4.34.1, while its 4.34.1 object was rejected by 4.31.0 as having an incompatible header. The control establishes the object-file boundary; it does not establish compatibility of Lean-Iris itself. A comment-aware source audit found no active `sorry`, `axiom`, `native_decide`, `extern`, or `implemented_by` candidate in the inspected Iris modules. Compiled theorem axiom closure remains unmeasured.

## Applicability

Source observations concern `leanprover-community/iris-lean` commit `81bc35088ba67d465db008f5261a9b341eb6cf6c`, tree `de91073ccc69a74b5ed56df1c41cc61f6bf05816`. This commit was available on 2026-10-14. The combination specified upstream is Lean 4.34.1, Batteries `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, and Qq `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259`, as locked in `Iris/lake-manifest.json`. The dependencies themselves were not built or audited here.

The two controls used macOS arm64 release toolchains whose reported Lean commits were `68218e876d2a38b1985b8590fff244a83c321783` (4.31.0) and `5045d0056413266e57c625dcd7c365b10e377c52` (4.34.1). They use only `Init`, not Lean-Iris. The repository revision, dependency lock, and toolchain together define the proposed framework configuration; adjacent versions are not treated as equivalent.

## Findings

### F1. Concrete model and reusable construction interfaces

Basis: source + derived.

`Algebra/OFE.lean` and `CMRA.lean` define equivalence, completion, resource composition, validity, core and update laws. `COFESolver.lean` constructs a fixpoint of a contractive functor; `Algebra/IProp.lean` uses `OFunctor.Fix (UPredOF (IResF GF))` for `IPre` and defines `IProp GF` as `UPred (IResUR GF)`. The fold/unfold isomorphism supplies the recursive proposition/resource equation rather than postulating an arbitrary proposition type.

The examined tree includes `Auth`, `Agree`, `Excl`, `Frac`, `DFrac`, maps, heaps and views; ghost maps and variables; saved propositions; invariant, cancelable-invariant and non-atomic-invariant constructions; later credits and time receipts. These are independently useful interfaces for authority/fragments, exclusivity, agreement, sharing, delayed reasoning and invariant ownership. Presence is source evidence, not a replay of every construction's proof.

`Algebra/StepIndex.lean` exposes an abstract `SIdx` class, including well-foundedness, successor and limit-like cases. Nevertheless, `Algebra/UPred.lean` has `ValidAt ... (n : Nat)` and `UPred.holds : Nat → ... → Prop`; the concrete Iris proposition construction uses this model. The abstract class alone therefore does not establish a transfinite Lean-Iris instance. Lifetime-specific Rust ownership and RustBelt-style semantic type interfaces were not found as a supplied Rust layer in the inspected module inventory. This is an inventory boundary, not a claim that these interfaces cannot be constructed.

### F2. Partial adequacy returns results and non-stuckness in the chosen language

Basis: source.

`ProgramLogic/WeakestPre.lean:IrisGS_gen` requires a `Language` instance, invariant state, `stateInterp : State → Nat → List Obs → Nat → IProp GF`, a number of later credits per step, a fork postcondition, and an update proving monotonicity of the step-count component of the state interpretation. Its `wp.pre` quantifies over actual primitive steps of that language; under `NotStuck` it also requires reducibility. The recursive continuation returns an updated state interpretation and weakest preconditions for both the continuation and forked threads.

`ProgramLogic/Adequacy.lean:wp_adequacy_gen` requires an `InvGpreS` instance and a proof, for every freshly instantiated invariant ghost state and observation sequence, that a fancy update allocates a suitable state interpretation and a WP with a pure result predicate. Its conclusion is `adequate s e σ (fun v _ => φ v)`. The `adequate` structure contains (a) the result predicate for any reachable configuration where the initial thread has returned a value and (b) non-stuckness of every reachable thread, conditional on `s = NotStuck`. Choosing `MaybeStuck` does not prove non-stuckness.

The proof visibly passes through `wp_strong_adequacy_gen`, `fupd_finally_soundness`, `laterN_soundness`, and `pure_soundness`. `Instances/UPred/Instance.lean:pure_soundness` extracts a pure proposition at index zero; `later_soundness` moves from index `n+1` to `n`. These are precise semantic endpoints. “Non-stuck” means the selected language's value-or-reducible predicate. Rust UB freedom additionally requires a model in which the relevant source-invalid operations cannot count as successful reductions, plus correspondence to the accepted Rust source.

### F3. Total adequacy is stronger than partial WP and does not assume fairness

Basis: source + derived.

`ProgramLogic/TotalAdequacy.lean:twp_total` requires initialization of a state interpretation, later-credit schedule, fork postcondition and monotonicity law, and a total WP under a finite later-credit premise `£ m`. It concludes `Relation.StronglyNormalizing ErasedStep ([e], σ)` for thread-pool reduction. The proof builds a least-fixpoint thread-pool predicate and proves accessibility of reduction.

This is a termination theorem for all reduction paths represented by that relation, not eventual service under an externally fair scheduler. Partial WP proves safety and conditional postconditions and can admit divergence; total WP adds an actual progress/termination obligation. Blocking, environment intervention or fair scheduling must appear in the operational model and the chosen liveness theorem, rather than being inferred from this total-adequacy name.

### F4. Proof-mode support and the limits of the source admission audit

Basis: source + derived.

`Iris/ProofMode.lean` imports expression reification, spatial and intuitionistic contexts, framing, modality and later-credit instances, side-condition solving, synthesis and unification hints. Tactic modules implement introduction, application, specialization, splitting, case analysis, framing, invariant access, modality elimination, induction and Löb reasoning. `Tactics/Loeb.lean` synthesizes `BI.BILoeb` and constructs a term using `BI.loeb_wand_intuitionistically`; it does not create a new logical axiom for each proof.

The source audit stripped nested block comments, line comments and strings before scanning all 308 Lean files under the Iris package. It traversed the static imports of partial and total adequacy. The only unsafe-code candidates in that closure were proof-mode tactic deserialization and environment registration in `SynthInstanceAttr.lean`, including `evalConst`; these are metaprogram implementation boundaries, not proof-level assumptions. The scan is not a kernel dependency traversal, and elaborator behavior or dependency packages could introduce further assumptions.

Two concrete coverage qualifications are visible. `BI/Sbi.lean` comments out `plainly_sForall_2_sbi`, explaining that an `sForall` version of `siEmpValid_forall` is missing. Its commented `sorry` is not an active admission. `ProgramLogic/WeakestPre.lean` explicitly lists `AddModal` and `ElimAcc` instances as TODOs. Conversely, a `rocq_ignore` entry saying that a Rocq mixin or sealing artifact is unnecessary in Lean is not, by itself, evidence of a missing theorem.

No `#print axioms` result for a Lean-Iris adequacy theorem was acquired. An accepted theorem should be checked by its elaborated transitive dependencies, including standard Lean axioms allowed by the consumer's policy, rather than by package name or absence of textual `sorry`.

### F5. Toolchain controls and the feasible Rust layer

Basis: execution + source + derived.

The original `Credits.lean` defines natural-number credits, addition, and `join_comm`, proved by `Nat.add_comm`. Both toolchains returned exit zero and printed that the theorem depends on no axioms. The separate intentional admission control returned exit zero with a warning and printed `[sorryAx]`, confirming that process success alone is insufficient as a proof acceptance policy. An initial missing section-closing `end` caused ordinary errors on both versions; that source was corrected before the reported successes.

The 4.34.1-built `Credits.olean` imported successfully on 4.34.1 and failed on 4.31.0 with `incompatible header`. This supports requiring source re-elaboration and a matching dependency closure when moving a project to 4.31. It does not show that the Lean-Iris source is incompatible: that build was deliberately not attempted without its dependencies. A 4.34.1 pin is upstream configuration evidence, not an executed framework build in this investigation.

A feasible Anneal interface would instantiate `Language` with a pinned Rust operational model; define validity, provenance, allocation, initialization and observations; prove `IrisGS_gen` lifting rules for its steps; and add semantic ownership/sharing types with unsafe-library extension obligations. Each accepted library proof would identify this model and a dependency/axiom closure. This is a design derived from the existing interfaces. Implementing that layer and compiler/source correspondence is future engineering; measuring actual framework build and axiom closure on either Lean pin remains an unperformed validation task.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

- **Not examined:** a full build of Lean-Iris or its locked dependencies; executed proof-mode tests; elaborated adequacy axiom closure; library-wide construction proof coverage; Rust lifetime/prophecy semantic typing in Lean.
- **Unknown:** whether this exact source and dependencies can be migrated to Lean 4.31.0 without substantive changes, or whether other Lean 4.34 versions build it.
- **Known not to apply:** the original `Init` control does not establish framework compatibility, Rust semantics or resource-proof automation cost; the concrete natural-index proposition model does not itself validate the transfinite existential property.
- **Missing in the examined source:** the explicitly commented-out `plainly_sForall_2_sbi` and named WP automation TODOs. These are narrow findings, not a blanket “Iris unsupported” verdict.

## Evidence

All repository paths below are relative to `Iris/` at the immutable [Lean-Iris commit](https://github.com/leanprover-community/iris-lean/tree/81bc35088ba67d465db008f5261a9b341eb6cf6c). Source: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`; `Iris/Algebra/{CMRA,OFE,COFESolver,IProp,UPred,StepIndex}.lean`; `Iris/Instances/UPred/Instance.lean:pure_soundness/later_soundness`; `Iris/Instances/Lib/FUpd.lean:fupd_finally_soundness`; `Iris/ProgramLogic/{WeakestPre,Adequacy,TotalAdequacy}.lean` at the symbols above; `Iris/ProofMode.lean`, `Iris/ProofMode/Tactics/Loeb.lean`, `Iris/ProofMode/SynthInstanceAttr.lean:312–355`; `Iris/BI/Sbi.lean:635–645`. Imported source identity and scan method are summarized in `source-audit.json`; no upstream source is mirrored in this package.

Execution: package-owned original controls in `probes/`; sanitized command/results in `execution.json`. The 4.31.0 shared-library SHA-256 is `a695a9aa68481c42b99619e0103537e6b433c6fa7021927b184e19a686d03989`, and `Init.olean` is `9e6e77b58b46742b93b7de481229698d853595479a6e154e9c6fcfdf63b485c8`. The 4.34.1 values are `6588b7e38450ea749006dcd90bbaea9393a5ca1b64727a2e7138f3c9427c2b50` and `e350f457fb746028d5761304fd7df55a83b46ea56cdd7702fdee32600b57db22`. The launcher hash is identical between these versions and is insufficient alone as a version identity.

## Revalidation

Retrieve the pinned tree, verify the lock, and inspect the named declarations before changing any coverage conclusion. To close the compiled-proof gap, build the exact upstream configuration and print axioms for `wp_adequacy_gen`, `wp_strong_adequacy_gen`, `twp_total`, model soundness, and any chosen resource construction. Recheck actual transitive proof dependencies; an import scan is insufficient.

Run the original controls with the two stated toolchains in a disposable package-local working directory: compile `Credits.lean`, print its axioms, compile the admission control, emit `Credits.olean` under 4.34.1, and import it under both versions. Do not reuse that object as an argument for 4.31 source compatibility. Any Rust application needs a separate model/semantic-typing adequacy statement and source correspondence evidence.

*Authored by an AI agent acting on joshlf's behalf.*
