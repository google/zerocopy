# Observational Quotient and Erasable Hidden State

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

This package mechanizes 18 theorems in a self-contained deterministic Moore-machine model (`Toy.Obs`, Lean `leanprover/lean4:v4.34.1`, core Lean / `Std` only, no Mathlib) addressing three linked questions about state-splitting semantic frameworks: when execution-only hidden state can be erased without changing observable behavior, whether a canonical minimal semantics exists, and why some per-step non-dependence checks fail to catch hidden channels while others succeed.

**High-level answers and over-reading guards (see [Boundaries](#boundaries) for full non-claims and escape hatches):**
- **Canonical minimal semantics (Results 1a–3c):** Every deterministic Moore machine `M` admits a unique homomorphism `M.beh` into the final coalgebra `finalMachine I O` (`finalMachine_is_final`), observational equivalence `ObsEq M` is the greatest bisimulation (`obsEq_is_greatest_bisim`), and for any initial state `q₀`, the reachable behavior image `(minimalMachine M q₀, minimalInit M q₀)` is all-reachable and behavior-injective (`minimalMachine_spec`), receives a unique surjective homomorphism from every all-reachable machine with the same initial behavior (`reachable_maps_onto_minimalMachine`), and is unique up to canonical isomorphism (`reachable_behInjective_iso`).
- **What per-step checks succeed vs. fail (Results 4a–5a):** Per-step checks are not useless. Checking one-step extensional independence of *both* `out` (`OutIgnoresHidden M`) and the observable transition component (`StepFstIgnoresHidden M`) is sound and catches every hidden channel in this model at step 1 (`stepwise_nondependence_implies_behIgnoresHidden`, `stepwise_nondependence_preserves_beh`, `no_leak_under_stepwise_nondependence`). It is incomplete only when `A` itself contains observationally redundant states (`redundantTagMachine_erasable_despite_step_dependence` vs. `behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`). What fails are checks on the output alone at zero, one, or any machine-independent finite depth (`delayedChannel2_leaks_at_step_two`, `no_machine_independent_horizon_certifies_behIgnoresHidden`), or checks that `H` is never written (`step.2 = h`).
- **Exact behavioral and unwinding criteria (Results 5b–5c):** *Given an inhabitant `h₀ : H`*, uniform global erasability onto `A` (with identity correspondence on `A`) is equivalent to two-level deterministic nonleakage `BehIgnoresHidden M` and is achieved by dummy substitution `eraseHidden M h₀` (`behIgnoresHidden_iff_erasable`, 5b). *Independently of any inhabitant*, `BehIgnoresHidden M` is equivalent to the existence of a bisimulation containing `SameFst` (`behIgnoresHidden_iff_exists_unwinding_bisim`, 5c-ii; stepwise non-dependence is the special case `R = SameFst`, per `isBisim_sameFst_iff`). Without `h₀`, erasability can fail even though `BehIgnoresHidden` holds (and hence such a bisimulation exists): for `emptyHiddenMachine` (`A = Unit`, `H = Empty`, `O = Empty`), no machine `M' : Moore Unit Empty Unit` reproduces its behavior (`ce_erase_empty_hidden`; indeed none exists, since `out : Unit → Empty` cannot be defined). So "erasable onto `A`" and "has an unwinding bisimulation containing `SameFst`" are proved to coincide when `H` is inhabited; without an inhabitant they can come apart.
- **Uniform, global scope of all erasure results:** Every erasure impossibility in this package is about *uniform, global* erasure: one machine on `A` reproducing `M.beh (a, h)` for every `(a, h) : A × H`, including unreachable states. For any single initial state `(a, h)`, the behavior is realized by the pointed minimal machine `minimalMachine M (a, h)`, which has no hidden component. A machine on `A` itself for one fixed `h` exists in some cases (for example `eraseHidden delayedChannel2 h`, proved as `Toy.Obs.delayedChannel2_erasable_for_each_fixed_h`, where `H` is read-only), but not in general.

**One-sentence summary of every result (with key hypotheses; see [Boundaries](#boundaries) for every non-claim):**

1. **1a (`Toy.Obs.bisim_subset_obsEq`, T0):** For any deterministic Moore machine `M` and state relation `R` satisfying `RelPreservesOut M R` and `RelStepClosed M R`, every `R`-related pair of states is observationally equivalent (`ObsEq M`).
2. **1b (`Toy.Obs.obsEq_is_greatest_bisim`, T0):** For every deterministic Moore machine `M`, `ObsEq M` is itself a bisimulation and contains every bisimulation on `M`.
3. **2a (`Toy.Obs.hom_to_final_eq_beh`, T0):** For any deterministic Moore machine `M` and map `h : Q → (List I → O)` into `finalMachine I O` satisfying `PreservesOut` and `PreservesStep`, `h` equals `M.beh`.
4. **2b (`Toy.Obs.finalMachine_is_final`, T0):** For every deterministic Moore machine `M`, `M.beh` is a homomorphism `M → finalMachine I O` and is the unique homomorphism from `M` into `finalMachine I O`.
5. **3a (`Toy.Obs.minimalMachine_spec`, T0):** For any deterministic Moore machine `M` and initial state `q₀`, `(minimalMachine M q₀, minimalInit M q₀)` has initial behavior `M.beh q₀`, is all-reachable from `minimalInit M q₀`, and is behavior-injective.
6. **3b (`Toy.Obs.reachable_maps_onto_minimalMachine`, T0):** For any pointed machine `(M, q₀)` and any machine `(M', q₀')` satisfying `AllReachable M' q₀'` and `M'.beh q₀' = M.beh q₀`, the explicit map `toMinimalQuotient` is a surjective, initial-state-preserving homomorphism from `M'` onto `minimalMachine M q₀` and is the unique homomorphism `M' → minimalMachine M q₀`.
7. **3c (`Toy.Obs.reachable_behInjective_iso`, T0):** Any two machines `(M₁, q₁)` and `(M₂, q₂)` satisfying `AllReachable M₁ q₁`, `AllReachable M₂ q₂`, `BehInjective M₁`, `BehInjective M₂`, and `M₁.beh q₁ = M₂.beh q₂` are canonically isomorphic via the exhibited pair of `minimalIsoFun` maps, which preserves initial states, commutes with multi-step runs from `q₁`/`q₂`, and is the unique homomorphism `M₁ → M₂`.
8. **4a-i (`Toy.Obs.stepwise_nondependence_implies_behIgnoresHidden`, T0):** For any split-state Moore machine `M : Moore I O (A × H)` (including empty `H`) satisfying `OutIgnoresHidden M` and `StepFstIgnoresHidden M`, `BehIgnoresHidden M` holds.
9. **4a-ii (`Toy.Obs.stepwise_nondependence_preserves_beh`, T0):** For any split-state machine `M : Moore I O (A × H)` with `h₀ : H` satisfying `OutIgnoresHidden M` and `StepFstIgnoresHidden M`, `Prod.fst` is a homomorphism `M → eraseHidden M h₀`, `eraseHidden M h₀` preserves behavior for every `(a, h)`, `BehIgnoresHidden M` holds, and `eraseHidden M h₁ = eraseHidden M h₀` for all `h₁ : H`.
10. **4a-iii (`Toy.Obs.isBisim_sameFst_iff`, T0):** For every split-state machine `M : Moore I O (A × H)`, `CoversHidden SameFst` holds, and `IsBisim M SameFst` holds if and only if both `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold.
11. **4b (`Toy.Obs.redundantTagMachine_erasable_despite_step_dependence`, T1):** The concrete machine `redundantTagMachine` on `(Bool × Bool) × Bool` satisfies `OutIgnoresHidden`, `BehIgnoresHidden`, and global behavior preservation under `eraseHidden` for every dummy `h₀`, yet fails `StepFstIgnoresHidden` (even on reachable states) and admits no machine on `Bool × Bool` for which `Prod.fst` is a homomorphism.
12. **4c (`Toy.Obs.behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`, T1):** For any split-state machine `M : Moore I O (A × H)` satisfying `ObsInjectiveFst M`, `BehIgnoresHidden M` holds if and only if both `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold.
13. **5a-0 (`Toy.Obs.no_leak_under_stepwise_nondependence`, T0):** For any `I`, `O`, `A`, `H`, there is no `M : Moore I O (A × H)` satisfying `OutIgnoresHidden M`, `StepFstIgnoresHidden M`, and `¬ BehIgnoresHidden M`.
14. **5a-i (`Toy.Obs.delayedChannel2_leaks_at_step_two`, T1):** The concrete shift register `delayedChannel2` on `(Bool × Bool) × Bool` satisfies `OutIgnoresHidden`, `OneStepOutIgnoresHidden`, `BoundedBehIgnoresHidden 2`, agreement with `eraseHidden` on words of length `< 2`, and read-only `H` (`step.2 = h`), yet violates `StepFstIgnoresHidden`, leaks `H` at word `[(), ()]` (`¬ BehIgnoresHidden`), and admits no uniform reduced machine on `Bool × Bool`.
15. **5a-ii (`Toy.Obs.no_machine_independent_horizon_certifies_behIgnoresHidden`, T1):** For every `k : Nat`, the `(k + 2)`-slot shift register `delayedChannel k` satisfies `OutIgnoresHidden`, `OneStepOutIgnoresHidden`, `BoundedBehIgnoresHidden (k + 2)`, and agreement with `eraseHidden` on words of length `< k + 2`, yet violates `StepFstIgnoresHidden`, fails `BehIgnoresHidden`, and admits no uniform reduced machine on `Fin (k + 2) → Bool`.
16. **5b (`Toy.Obs.behIgnoresHidden_iff_erasable`, T1):** For any split-state machine `M : Moore I O (A × H)` and inhabitant `h₀ : H`, `BehIgnoresHidden M` holds if and only if `eraseHidden M h₀` preserves behavior uniformly for all `(a, h)`, and also if and only if some reduced machine `M' : Moore I O A` preserves behavior uniformly for all `(a, h)`.
17. **5c-i (`Toy.Obs.unwinding_bisim_implies_behIgnoresHidden`, T0):** For any split-state machine `M : Moore I O (A × H)` and state relation `R` satisfying `CoversHidden R`, `RelPreservesOut M R`, and `RelStepClosed M R`, `BehIgnoresHidden M` holds.
18. **5c-ii (`Toy.Obs.behIgnoresHidden_iff_exists_unwinding_bisim`, T0):** For every split-state machine `M : Moore I O (A × H)`, `BehIgnoresHidden M` holds if and only if there exists a state relation `R` on `A × H` satisfying `CoversHidden R`, `RelPreservesOut M R`, and `RelStepClosed M R`.

## Applicability

**Model fidelity (toy model, not production definitions).** All definitions and theorems live in namespace `Toy.Obs` inside the self-contained Lake package `lean/` (`lean-toolchain`: `leanprover/lean4:v4.34.1`, `lakefile.toml`: single `[[lean_lib]] name = "Toy"`, zero `[[require]]` entries, core Lean and `Std` only, **no Mathlib**). None of the definitions mirror a production compiler, verification framework, or runtime; they form a clean mathematical model of total, deterministic Moore machines (`Moore I O Q`, consisting of `step : Q → I → Q` and `out : Q → O`) whose observable behavior `M.beh q : List I → O` records `M.out (M.run q w)` on every finite input list `w : List I`.

**Target real-world concepts and known modeling gaps.** The definitions are meant to capture:
- **Semantic state splitting (`Q = A × H`):** distinguishing an observable state component `A` from execution-only bookkeeping, ghost state, or auxiliary state `H` in operational semantics and verification abstractions;
- **Observational quotients and canonical minimal semantics:** collapsing observationally indistinguishable states via bisimulation (`ObsEq M`) and constructing a canonical minimal state machine (`minimalMachine M q₀`);
- **Two-level deterministic nonleakage and unwinding:** certifying that hidden initial data `H` never affects externally observable outputs (`BehIgnoresHidden M`), either via one-step extensional independence (`OutIgnoresHidden ∧ StepFstIgnoresHidden`, i.e., `IsBisim M SameFst`) or via a coarser unwinding bisimulation `R ⊇ SameFst`.

Known gaps between `Toy.Obs` and real software or operational-semantics frameworks:
1. **Total deterministic Moore transitions only:** Every state emits an output in `O` on `[]`, and `step q i` is total and deterministic. Systems with partial/stuck transitions, undefined behavior, silent (`τ`) internal steps, nondeterminism (where trace equivalence is strictly coarser than bisimilarity), probabilistic transitions, Mealy-style input-dependent immediate outputs without initial state observations, or covert timing/physical side channels fall outside this model.
2. **Action-free two-level nonleakage rather than purge-based noninterference:** All inputs `i : I` are treated uniformly without security-domain labels or high-only actions, so there is no "locally respects" condition and no intransitive policy graph. `BehIgnoresHidden` models secrecy of initial hidden state `H` during execution (two-level deterministic nonleakage, von Oheimb 2004), not Goguen–Meseguer action-purge noninterference.
3. **Identity correspondence on a fixed global split `A × H`:** In Results 4–5, "a reduced machine `M' : Moore I O A`" means a machine on the existing carrier `A` whose state `a` reproduces `(a, h)` for every `h` simultaneously (`∀ a h, M'.beh a = M.beh (a, h)`). Re-encodings of `A`, reduced machines on alternative carriers, choosing a split `A × H`, and mode-dependent bookkeeping are not modeled.
4. **No bridge between pointed minimization (Results 1–3) and global split erasure (Results 4–5):** Results 1–3 construct a pointed minimal realization `(minimalMachine M q₀, minimalInit M q₀)` from a single initial state `q₀` (discarding unreachable states and dropping any product decomposition), whereas Results 4–5 study global erasure over all `(a, h) : A × H` (including unreachable states). No theorem in this package identifies `minimalMachine M (a₀, h₀)` with `eraseHidden M h₀` or characterizes reachable-only erasability under an invariant linking `a` and `h`.
5. **Extensional vs. syntactic independence:** `OutIgnoresHidden` and `StepFstIgnoresHidden` are extensional equalities (`∀ a h₁ h₂, ...`), not syntactic checks over source code. A syntactic taint/type check or auxiliary-variable discipline forbidding `out` and `step.1` from reading `H` is a strictly stronger special case.
6. **Non-constructive isomorphism and non-algorithmic minimization:** `minimalIsoFun` uses `Classical.choice` (`Classical.choose`) to extract reaching words from `AllReachable`, and `minimalMachine` is a semantic subtype rather than a finite-state partition-refinement algorithm.

**Relationship among `REPORT.json` subjects.** The Lean 4 toolchain (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`) is the proof assistant and kernel that checks every Lean file in `lean/`. The cited papers, the journal article, and the Archive of Formal Proofs (AFP) entries are the primary literature whose results this package re-derives in uniform Moore-machine vocabulary (`T0`) or makes precise as concrete characterizations and counterexamples (`T1`). The 2011 AFP entry `Myhill-Nerode` and the 2014 journal article by the same authors are listed as separate subjects because they have different titles and identities (see [Evidence](#evidence)).

**Not a subject.** Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`) is not listed in `REPORT.json`: it is cited only as a prior-art comparison in `## Findings` and `## Evidence`, and this package has no dependency on it.

**Evidence-role convention.** Every formal theorem checked by Lean carries `Basis: execution (Lean kernel check)`. Any statement connecting a `Toy.Obs` theorem to real operational semantics, verification tools, or design guidelines is stated separately with `Basis: derived (modeling bridge)` and its reasoning.

## Findings

### Core Definitions (`Toy.Obs.Defs`)

Every structural property is defined as a separate named `Prop` so each theorem names its exact hypotheses. Every core definition carries fully proved positive and negative examples in `lean/Toy/Obs/Examples.lean` (`Basis: execution (Lean kernel check)`).

```lean
structure Moore (I : Type v) (O : Type w) (Q : Type u) where
  step : Q → I → Q
  out  : Q → O

def Moore.run (M : Moore I O Q) : Q → List I → Q
  | q, []     => q
  | q, i :: w => M.run (M.step q i) w

def Moore.beh (M : Moore I O Q) (q : Q) : List I → O :=
  fun w => M.out (M.run q w)
```
- **Captures:** Total deterministic state machines with state-based observation (`out`) and finite-trace black-box behavior (`beh`).
- **Definition examples:** `ex_pos_moore_beh` (positive), `ex_neg_moore_beh` (negative).

```lean
def ObsEq (M : Moore I O Q) (q₁ q₂ : Q) : Prop := M.beh q₁ = M.beh q₂
def RelPreservesOut (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  ∀ q₁ q₂, R q₁ q₂ → M.out q₁ = M.out q₂
def RelStepClosed (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  ∀ q₁ q₂, R q₁ q₂ → ∀ i, R (M.step q₁ i) (M.step q₂ i)
def IsBisim (M : Moore I O Q) (R : Q → Q → Prop) : Prop :=
  RelPreservesOut M R ∧ RelStepClosed M R
```
- **Captures:** Observational equivalence and deterministic bisimulation (without requiring reflexivity, symmetry, or transitivity).
- **Definition examples:** `ex_pos_obsEq` / `ex_neg_obsEq`; `ex_pos_relPreservesOut` / `ex_neg_relPreservesOut`; `ex_pos_relStepClosed` / `ex_neg_relStepClosed`; `ex_pos_isBisim` / `ex_neg_isBisim_fails_out`, `ex_neg_isBisim_fails_step`.

```lean
def PreservesOut (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  ∀ q, M₂.out (f q) = M₁.out q
def PreservesStep (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  ∀ q i, f (M₁.step q i) = M₂.step (f q) i
def IsHom (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (f : Q₁ → Q₂) : Prop :=
  PreservesOut M₁ M₂ f ∧ PreservesStep M₁ M₂ f
def PreservesInit (q₁ : Q₁) (q₂ : Q₂) (f : Q₁ → Q₂) : Prop := f q₁ = q₂
def Surjective (f : α → β) : Prop := ∀ b : β, ∃ a : α, f a = b
def IsIso (M₁ : Moore I O Q₁) (M₂ : Moore I O Q₂) (toFun : Q₁ → Q₂) (invFun : Q₂ → Q₁) : Prop :=
  IsHom M₁ M₂ toFun ∧ IsHom M₂ M₁ invFun ∧
  (∀ q₁, invFun (toFun q₁) = q₁) ∧ (∀ q₂, toFun (invFun q₂) = q₂)

def finalMachine (I : Type v) (O : Type w) : Moore I O (List I → O) where
  step f i := fun w => f (i :: w)
  out  f   := f []
```
- **Captures:** Coalgebra morphisms for the Moore functor `Q ↦ O × (I → Q)`, two-sided structural isomorphisms, and the final Moore coalgebra of all behaviors with left-derivative transitions.
- **Definition examples:** `ex_pos_preservesOut` / `ex_neg_preservesOut`; `ex_pos_preservesStep` / `ex_neg_preservesStep`; `ex_pos_isHom` / `ex_neg_isHom`; `ex_pos_preservesInit` / `ex_neg_preservesInit`; `ex_pos_surjective` / `ex_neg_surjective`; `ex_pos_isIso` / `ex_neg_isIso`; `ex_pos_finalMachine` / `ex_neg_finalMachine`.

```lean
def Reachable (M : Moore I O Q) (q₀ q : Q) : Prop := ∃ w : List I, M.run q₀ w = q
def AllReachable (M : Moore I O Q) (q₀ : Q) : Prop := ∀ q : Q, Reachable M q₀ q
def BehInjective (M : Moore I O Q) : Prop := ∀ q₁ q₂ : Q, M.beh q₁ = M.beh q₂ → q₁ = q₂
abbrev ReachableBeh (M : Moore I O Q) (q₀ : Q) : Type (max v w) :=
  { f : List I → O // ∃ w : List I, M.beh (M.run q₀ w) = f }
def minimalMachine (M : Moore I O Q) (q₀ : Q) : Moore I O (ReachableBeh M q₀) where
  step s i := ⟨(finalMachine I O).step s.1 i, ...⟩   -- `...`: proof that the result is reachable (via `w ++ [i]`)
  out s := s.1 []
def minimalInit (M : Moore I O Q) (q₀ : Q) : ReachableBeh M q₀ := ⟨M.beh q₀, ⟨[], rfl⟩⟩
def toMinimalQuotient (M : Moore I O Q) (q₀ : Q) (M' : Moore I O Q') (q₀' : Q')
    (hReach : AllReachable M' q₀') (hInitBeh : M'.beh q₀' = M.beh q₀) (q' : Q') :
    ReachableBeh M q₀ := ⟨M'.beh q', ...⟩
noncomputable def minimalIsoFun (M₁ : Moore I O Q₁) (q₁ : Q₁) (M₂ : Moore I O Q₂) (q₂ : Q₂)
    (hReach₁ : AllReachable M₁ q₁) : Q₁ → Q₂ :=
  fun q => M₂.run q₂ (Classical.choose (hReach₁ q))
```
- **Captures:** Reachability from an initial state, reducedness (observability), the canonical reachable-behavior minimal realization, its universal quotient map, and the canonical word-transport isomorphism.
- **Definition examples:** `ex_pos_reachable` / `ex_neg_reachable`; `ex_pos_allReachable` / `ex_neg_allReachable`; `ex_pos_behInjective` / `ex_neg_behInjective`; `ex_pos_reachableBeh` / `ex_neg_reachableBeh`; `ex_pos_minimalMachine_step` / `ex_neg_minimalMachine_step`; `ex_pos_toMinimalQuotient` / `ex_neg_toMinimalQuotient_not_injective`; `ex_pos_minimalIsoFun` / `ex_neg_minimalIsoFun`.

```lean
def OutIgnoresHidden (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)
def StepFstIgnoresHidden (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1
def ObsInjectiveFst (M : Moore I O (A × H)) : Prop :=
  ∀ a₁ a₂ h, M.beh (a₁, h) = M.beh (a₂, h) → a₁ = a₂
def OneStepOutIgnoresHidden (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂ i, M.out (M.step (a, h₁) i) = M.out (M.step (a, h₂) i)
def BoundedBehIgnoresHidden (M : Moore I O (A × H)) (k : Nat) : Prop :=
  ∀ a h₁ h₂ w, w.length < k → M.beh (a, h₁) w = M.beh (a, h₂) w
def BehIgnoresHidden (M : Moore I O (A × H)) : Prop :=
  ∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)
def SameFst (p₁ p₂ : A × H) : Prop := p₁.1 = p₂.1
def CoversHidden (R : (A × H) → (A × H) → Prop) : Prop := ∀ a h₁ h₂, R (a, h₁) (a, h₂)
def eraseHidden (M : Moore I O (A × H)) (h₀ : H) : Moore I O A where
  step a i := (M.step (a, h₀) i).1
  out  a   := M.out (a, h₀)
```
- **Captures:** One-step extensional independence (`OutIgnoresHidden`, `StepFstIgnoresHidden`, corresponding to von Oheimb's functional independence), observational injectivity of `A` (`ObsInjectiveFst`), finite-depth output checks (`OneStepOutIgnoresHidden`, `BoundedBehIgnoresHidden`), global two-level deterministic nonleakage (`BehIgnoresHidden`), low-state projection (`SameFst`), unwinding coverage (`CoversHidden`), and dummy-substitution erasure (`eraseHidden`).
- **Definition examples:** `ex_pos_outIgnoresHidden` / `ex_neg_outIgnoresHidden`; `ex_pos_stepFstIgnoresHidden` / `ex_neg_stepFstIgnoresHidden`; `ex_pos_obsInjectiveFst`, `ex_pos_obsInjectiveFst_delayedChannel2` / `ex_neg_obsInjectiveFst`; `ex_pos_oneStepOutIgnoresHidden` / `ex_neg_oneStepOutIgnoresHidden`; `ex_pos_boundedBehIgnoresHidden` / `ex_neg_boundedBehIgnoresHidden`; `ex_pos_behIgnoresHidden` / `ex_neg_behIgnoresHidden`; `ex_pos_sameFst` / `ex_neg_sameFst`; `ex_pos_coversHidden` / `ex_neg_coversHidden`; `ex_pos_eraseHidden` / `ex_neg_eraseHidden`.

### Witness Machines and Relations (`Toy.Obs.Machines`, `Toy.Obs.Examples`, `Toy.Obs.Witnesses`)

The concrete machines and relations named in the Findings and Boundaries are defined below, quoted from `lean/Toy/Obs/Machines.lean` (except `threeStateBisimRel`, from `Examples.lean`, and `toggleClosedForm` and `redundantTagUnwindingRel`, from `Witnesses.lean`; all in namespace `Toy.Obs`). `redundantTagMachine`, `delayedChannel2`, and `delayedChannel k` are quoted with Results 4b, 5a-i, and 5a-ii.

```lean
def toggleMachine : Moore Unit Bool Bool where
  step b _ := !b
  out b := b

def dualToggleMachine : Moore Unit Bool Bool where
  step b _ := !b
  out b := !b

def idBoolMachine : Moore Unit Bool Bool where
  step b _ := b
  out b := b

def toggleClosedForm : Bool → List Unit → Bool :=
  fun q w => if w.length % 2 = 0 then q else !q

inductive ThreeState where
  | s0
  | s1
  | s2
  deriving DecidableEq

def threeStateToggle : Moore Unit Bool ThreeState where
  step
    | .s0, _ => .s2
    | .s1, _ => .s2
    | .s2, _ => .s1
  out
    | .s0 => false
    | .s1 => false
    | .s2 => true

def threeStateBisimRel (q₁ q₂ : ThreeState) : Prop :=
  (q₁ = .s0 ∨ q₁ = .s1) ∧ (q₂ = .s0 ∨ q₂ = .s1) ∨ (q₁ = .s2 ∧ q₂ = .s2)

def syntacticIndependentMachine : Moore Unit Bool (Bool × Nat) where
  step p _ := (!p.1, p.2 + 1)
  out p := p.1

def emptyHiddenMachine : Moore Unit Empty (Unit × Empty) where
  step p _ := nomatch p.2
  out p := nomatch p.2

def gatedLeak : Moore Unit Bool (Bool × Bool) where
  step p _ := p
  out p := p.1 && p.2

def delayedChannelFixed (k : Nat) : Moore Unit Bool ((Fin (k + 2) → Bool) × Bool) where
  step p _ :=
    (fun j => if hlt : j.val + 1 < k + 2 then p.1 ⟨j.val + 1, hlt⟩ else false, p.2)
  out p := p.1 ⟨0, Nat.zero_lt_succ _⟩

def redundantTagUnwindingRel (p₁ p₂ : (Bool × Bool) × Bool) : Prop :=
  p₁.1.1 = p₂.1.1
```

Roles (each property below is proved by the named theorem; `Basis: execution (Lean kernel check)`):
- `toggleMachine` (from `false`) and `dualToggleMachine` (from `true`) are two state encodings of the alternating behavior `false, true, false, …`; both are all-reachable and behavior-injective (`Toy.Obs.nv_reachable_behInjective_iso`).
- `idBoolMachine` is behavior-injective but not all-reachable from `false` (`true` is never reached), yet `id` is an isomorphism from it to itself (`Toy.Obs.iso_without_reachability`).
- `toggleClosedForm` is a closed-form parity map, syntactically different from `toggleMachine.beh`, satisfying `PreservesOut` and `PreservesStep` into `finalMachine Unit Bool` (`Toy.Obs.nv_hom_to_final_eq_beh`).
- `threeStateToggle` runs `s0 → s2 → s1 → s2 → s1 → …`; it is all-reachable from `s0`, its states `s0 ≠ s1` have the same behavior (so it is not behavior-injective), and `s0` and `s2` have different behaviors (`Toy.Obs.nv_obsEq_is_greatest_bisim`, `Toy.Obs.nv_minimalMachine_spec`, `Toy.Obs.nv_reachable_maps_onto_minimalMachine`). `threeStateBisimRel` is a bisimulation on it that relates `s0` and `s1` (`Toy.Obs.nv_bisim_subset_obsEq`).
- `syntacticIndependentMachine` has a hidden counter `H = Nat` that neither `out` nor the observable update reads, so `OutIgnoresHidden` and `StepFstIgnoresHidden` hold (`Toy.Obs.nv_stepwise_nondependence_implies_behIgnoresHidden`).
- `emptyHiddenMachine` has `H = Empty` and `O = Empty`: every hidden-state law holds vacuously, yet no machine `M' : Moore Unit Empty Unit` reproduces its behavior (`Toy.Obs.ce_erase_empty_hidden`); indeed no machine of that type exists, because its `out : Unit → Empty` cannot be defined.
- `gatedLeak` never changes state; from every `(false, h)` its output is constantly `false`, while at `a = true` its output is `h`, so `BehIgnoresHidden` fails globally although the hidden bit is invisible from every state reachable from `(false, h)` (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`).
- `delayedChannelFixed k` is `delayedChannel k` with slot `k + 1` loaded from the constant `false` instead of `h`; it satisfies `StepFstIgnoresHidden` and `BehIgnoresHidden` (`Toy.Obs.pc_bounded_horizon_with_step_consistency`).
- `redundantTagUnwindingRel` relates states of `redundantTagMachine` that have the same observable bit `x = p.1.1`, ignoring the tag bit `t` and the hidden bit; it covers the hidden state and is a bisimulation (`Toy.Obs.nv_unwinding_bisim_implies_behIgnoresHidden`).

---

### 1a. `bisim_subset_obsEq` (`Toy.Obs.bisim_subset_obsEq`)

- **Kind:** `theorem` (unbundled soundness half of `obsEq_is_greatest_bisim`)
- **Tier:** `T0` — re-derivation of the coinductive bisimulation soundness principle for deterministic Moore machines (Park 1981; Milner 1980, 1989; Rutten 1998, 2000; Jacobs 2016).
- **Depth:** `shallow` (direct induction on `w : List I`).
- **Plain claim:** For any deterministic Moore machine `M` and any state relation `R` that preserves immediate outputs (`RelPreservesOut M R`) and is closed under single-step transitions (`RelStepClosed M R`), every `R`-related pair of states is observationally equivalent (`ObsEq M`) (unbundled soundness half of `obsEq_is_greatest_bisim`).
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem bisim_subset_obsEq
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (R : Q → Q → Prop)
    (hOut : RelPreservesOut M R)
    (hStep : RelStepClosed M R) :
    ∀ q₁ q₂, R q₁ q₂ → ObsEq M q₁ q₂
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q) (R : Q → Q → Prop),
  (∀ q₁ q₂, R q₁ q₂ → M.out q₁ = M.out q₂) →
  (∀ q₁ q₂, R q₁ q₂ → ∀ i, R (M.step q₁ i) (M.step q₂ i)) →
  ∀ q₁ q₂, R q₁ q₂ → (fun w => M.out (M.run q₁ w)) = (fun w => M.out (M.run q₂ w))
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hOut : RelPreservesOut M R` | Ensures `R`-related states emit identical outputs on `[]` (base case of word induction). | `tight`: `Toy.Obs.ce_bisim_subset_obsEq_no_out` |
| `hStep : RelStepClosed M R` | Preserves `R` across single-step transitions so output equality extends to arbitrary finite words. | `tight`: `Toy.Obs.ce_bisim_subset_obsEq_no_step` |

- **Non-vacuity witness:** `Toy.Obs.nv_bisim_subset_obsEq` (`threeStateToggle` with `threeStateBisimRel` relating distinct states `s0 ≠ s1` while separating them from `s2`).
- **Prior art:** Park (1981, DOI `10.1007/BFb0017309`); Milner (1980, DOI `10.1007/3-540-10235-3`; 1989, ISBN `978-0131150072`); Rutten (1998, DOI `10.1007/BFb0055624`; 2000, §3, Theorem 9.2, Example 9.5, DOI `10.1016/S0304-3975(00)00056-6`); Jacobs (2016, Ch. 3, DOI `10.1017/CBO9781316823187`); Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`: `Stream'.eq_of_bisim` in `Mathlib/Data/Stream/Init.lean` and `PFunctor.M.bisim` in `Mathlib/Data/PFunctor/Univariate/M.lean`).
- **Design question:** Reference point (unbundled form of `obsEq_is_greatest_bisim`): provides the local single-step proof principle for showing two states have identical observable behavior without inducting directly over unbounded input traces each time.
- `Basis: derived (modeling bridge)` — In a deterministic state-transition semantics whose externally visible behavior is modeled as a Moore observation at every step, exhibiting any relation closed under outputs and single steps justifies observational equivalence without requiring the relation to be an equivalence relation.

---

### 1b. `obsEq_is_greatest_bisim` (`Toy.Obs.obsEq_is_greatest_bisim`)

- **Kind:** `characterization`
- **Tier:** `T0` — re-derivation of observational equivalence as the greatest bisimulation on deterministic Moore machines.
- **Depth:** `shallow` (two-line combination of word projection and `bisim_subset_obsEq`).
- **Plain claim:** For every deterministic Moore machine `M`, observational equivalence (`ObsEq M`) is itself a bisimulation and contains every bisimulation on `M`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem obsEq_is_greatest_bisim
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) :
    IsBisim M (ObsEq M) ∧
    (∀ R : Q → Q → Prop, IsBisim M R → ∀ q₁ q₂, R q₁ q₂ → ObsEq M q₁ q₂)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q),
  ((∀ q₁ q₂, M.beh q₁ = M.beh q₂ → M.out q₁ = M.out q₂) ∧
   (∀ q₁ q₂, M.beh q₁ = M.beh q₂ → ∀ i, M.beh (M.step q₁ i) = M.beh (M.step q₂ i))) ∧
  (∀ R,
    ((∀ q₁ q₂, R q₁ q₂ → M.out q₁ = M.out q₂) ∧
     (∀ q₁ q₂, R q₁ q₂ → ∀ i, R (M.step q₁ i) (M.step q₂ i))) →
    ∀ q₁ q₂, R q₁ q₂ → M.beh q₁ = M.beh q₂)
```

- **Hypothesis ledger:** None (unconditional over every `M : Moore I O Q`).
- **Non-vacuity witness:** `Toy.Obs.nv_obsEq_is_greatest_bisim` (`threeStateToggle`, where `s0 ≠ s1`, `ObsEq threeStateToggle s0 s1` holds, and `ObsEq threeStateToggle s0 s2` fails).
- **Prior art:** Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`); Park (1981, DOI `10.1007/BFb0017309`); Rutten (1998, DOI `10.1007/BFb0055624`; 2000, §3, Theorem 9.2, Example 9.5, DOI `10.1016/S0304-3975(00)00056-6`); Jacobs (2016, Ch. 3, DOI `10.1017/CBO9781316823187`).
- **Design question:** Reference point: establishes that coinductive bisimulation is both sound and complete for observational equivalence of deterministic Moore machines, justifying bisimulation-based quotienting and unwinding criteria.
- `Basis: derived (modeling bridge)` — Any deterministic transition semantics that fits `Moore I O Q` admits a sound and complete coinductive characterization of trace equivalence; this bridge fails for nondeterministic systems where trace equivalence is strictly coarser than bisimilarity.

---

### 2a. `hom_to_final_eq_beh` (`Toy.Obs.hom_to_final_eq_beh`)

- **Kind:** `theorem` (unbundled uniqueness half of `finalMachine_is_final`)
- **Tier:** `T0` — re-derivation of uniqueness of coalgebra morphisms into the final Moore coalgebra `List I → O` (Rutten 1998, 2000; Jacobs 2016).
- **Depth:** `shallow` (induction on `w : List I`).
- **Plain claim:** For any deterministic Moore machine `M` and any state map `h : Q → (List I → O)` into `finalMachine I O` that preserves immediate outputs (`PreservesOut`) and single-step transitions (`PreservesStep`), `h` equals `M.beh` (unbundled uniqueness half of `finalMachine_is_final`).
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem hom_to_final_eq_beh
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (h : Q → (List I → O))
    (hOut : PreservesOut M (finalMachine I O) h)
    (hStep : PreservesStep M (finalMachine I O) h) :
    h = M.beh
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q) (h : Q → (List I → O)),
  (∀ q, h q [] = M.out q) →
  (∀ q i, h (M.step q i) = fun w => h q (i :: w)) →
  h = fun q w => M.out (M.run q w)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hOut : PreservesOut M (finalMachine I O) h` | Fixes `h q [] = M.out q` at the base case of word induction. | `tight`: `Toy.Obs.ce_hom_to_final_no_out` |
| `hStep : PreservesStep M (finalMachine I O) h` | Forces `h q (i :: w) = h (M.step q i) w` so `h` agrees with `M.beh` on all nonempty words. | `tight`: `Toy.Obs.ce_hom_to_final_no_step` |

- **Non-vacuity witness:** `Toy.Obs.nv_hom_to_final_eq_beh` (`toggleMachine` with the explicit closed-form parity map `toggleClosedForm := fun q w => if w.length % 2 = 0 then q else !q`, syntactically distinct from `toggleMachine.beh`).
- **Prior art:** Rutten (1998, DOI `10.1007/BFb0055624`; 2000, §3, Example 9.5, Example 10.2(5), DOI `10.1016/S0304-3975(00)00056-6`); Jacobs (2016, Chs. 2 and 4, DOI `10.1017/CBO9781316823187`); Traytel (2013, AFP `Coinductive_Languages`; 2017, DOI `10.23638/LMCS-13(3:28)2017`).
- **Design question:** Reference point (unbundled form of `finalMachine_is_final`): shows that any denotational interpretation into `List I → O` respecting one-step observations and derivatives is uniquely determined to be `M.beh`.

---

### 2b. `finalMachine_is_final` (`Toy.Obs.finalMachine_is_final`)

- **Kind:** `characterization`
- **Tier:** `T0` — re-derivation of finality of the Moore coalgebra `(List I → O, (· []), fun f i w => f (i :: w))` (Rutten 2000, Example 10.2(5)).
- **Depth:** `shallow`.
- **Plain claim:** For every deterministic Moore machine `M` over inputs `I` and outputs `O`, `M.beh` is a homomorphism from `M` into `finalMachine I O` and is the unique homomorphism from `M` into `finalMachine I O`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem finalMachine_is_final
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) :
    IsHom M (finalMachine I O) M.beh ∧
    (∀ h : Q → (List I → O), IsHom M (finalMachine I O) h → h = M.beh)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q),
  ((∀ q, M.beh q [] = M.out q) ∧
   (∀ q i, M.beh (M.step q i) = fun w => M.beh q (i :: w))) ∧
  (∀ h : Q → (List I → O),
    ((∀ q, h q [] = M.out q) ∧ (∀ q i, h (M.step q i) = fun w => h q (i :: w))) →
    h = M.beh)
```

- **Hypothesis ledger:** None (unconditional over every `M : Moore I O Q`).
- **Non-vacuity witness:** `Toy.Obs.nv_finalMachine_is_final` (`toggleMachine`, whose two states have distinct behaviors in `finalMachine Unit Bool`).
- **Prior art:** Rutten (1998, DOI `10.1007/BFb0055624`; 2000, §3, Example 9.5, Example 10.2(5), DOI `10.1016/S0304-3975(00)00056-6`); Jacobs (2016, Chs. 2 and 4, DOI `10.1017/CBO9781316823187`); Traytel (2013, AFP `Coinductive_Languages`); Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`: `Mathlib/Data/Stream/Init.lean` covers the `I = Unit` stream coalgebra special case).
- **Design question:** Reference point: identifies `List I → O` with left-derivative transitions as the canonical ambient semantic domain in which all Moore-machine semantics compare unambiguously via `M.beh`.

---

### 3a. `minimalMachine_spec` (`Toy.Obs.minimalMachine_spec`)

- **Kind:** `theorem`
- **Tier:** `T0` — re-derivation of the derivative/reachable-behavior minimal realization of a pointed Moore machine (Moore 1956; Myhill 1957; Nerode 1958; Goguen 1972; Arbib and Manes 1974).
- **Depth:** `shallow` (reduces to `(minimalMachine M q₀).beh s = s.1` by word induction).
- **Plain claim:** For any deterministic Moore machine `M` with an initial state `q₀`, the reachable behavior-image machine `(minimalMachine M q₀, minimalInit M q₀)` has initial behavior `M.beh q₀`, is all-reachable from `minimalInit M q₀`, and is behavior-injective.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem minimalMachine_spec
    {I : Type v} {O : Type w} {Q : Type u}
    (M : Moore I O Q) (q₀ : Q) :
    (minimalMachine M q₀).beh (minimalInit M q₀) = M.beh q₀ ∧
    AllReachable (minimalMachine M q₀) (minimalInit M q₀) ∧
    BehInjective (minimalMachine M q₀)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q) (q₀ : Q),
  (minimalMachine M q₀).beh ⟨M.beh q₀, ⟨[], rfl⟩⟩ = M.beh q₀ ∧
  (∀ s : ReachableBeh M q₀, ∃ w : List I, (minimalMachine M q₀).run ⟨M.beh q₀, ⟨[], rfl⟩⟩ w = s) ∧
  (∀ s₁ s₂ : ReachableBeh M q₀,
    (minimalMachine M q₀).beh s₁ = (minimalMachine M q₀).beh s₂ → s₁ = s₂)
```

- **Hypothesis ledger:** None (unconditional over any `M : Moore I O Q` and `q₀ : Q`).
- **Non-vacuity witness:** `Toy.Obs.nv_minimalMachine_spec` (`threeStateToggle` at `s0`, which is not behavior-injective and has alternating output).
- **Prior art:** Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`); Myhill (1957, WADC TR-57-624, pp. 112–137); Nerode (1958, DOI `10.1090/S0002-9939-1958-0135681-9`); Goguen (1972, DOI `10.1090/S0002-9904-1972-13032-5`); Arbib and Manes (1974, DOI `10.1137/1016026`); Rutten (1998, DOI `10.1007/BFb0055624`); Wu, Zhang, and Urban (2011, AFP `Myhill-Nerode`; 2014, DOI `10.1007/s10817-013-9297-2`); Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`: `Mathlib/Computability/MyhillNerode.lean` and `Mathlib/Computability/DFA.lean`, constructing `Language.toDFA` for Boolean-accepting DFAs).
- **Design question:** Reference point: constructs an explicit canonical minimal semantics (`minimalMachine M q₀`) for any pointed deterministic transition semantics, eliminating both unreachable states and observationally redundant bookkeeping.
- `Basis: derived (modeling bridge)` — For any single initial state of a deterministic system whose observations fit `Moore I O Q`, a reduced realization exists on the behavior-derivative carrier `ReachableBeh M q₀` without any separate hidden-state component, though this construction does not preserve a given state representation `A`.

---

### 3b. `reachable_maps_onto_minimalMachine` (`Toy.Obs.reachable_maps_onto_minimalMachine`)

- **Kind:** `theorem`
- **Tier:** `T0` — re-derivation of the universal surjective-quotient property of the minimal realization (Goguen 1972; Arbib and Manes 1974; Rutten 2000).
- **Depth:** `shallow`.
- **Plain claim:** For any pointed Moore machine `(M, q₀)` and any all-reachable Moore machine `(M', q₀')` having the same initial behavior (`M'.beh q₀' = M.beh q₀`), the explicit map `toMinimalQuotient M q₀ M' q₀' hReach hInitBeh` is a surjective, initial-state-preserving homomorphism from `M'` onto `minimalMachine M q₀` and is the unique homomorphism `M' → minimalMachine M q₀`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem reachable_maps_onto_minimalMachine
    {I : Type v} {O : Type w} {Q : Type u₁} {Q' : Type u₂}
    (M : Moore I O Q) (q₀ : Q)
    (M' : Moore I O Q') (q₀' : Q')
    (hReach : AllReachable M' q₀')
    (hInitBeh : M'.beh q₀' = M.beh q₀) :
    let φ := toMinimalQuotient M q₀ M' q₀' hReach hInitBeh
    IsHom M' (minimalMachine M q₀) φ ∧
    PreservesInit q₀' (minimalInit M q₀) φ ∧
    Surjective φ ∧
    (∀ ψ : Q' → ReachableBeh M q₀, IsHom M' (minimalMachine M q₀) ψ → ψ = φ)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O Q) (q₀ : Q) (M' : Moore I O Q') (q₀' : Q')
  (hReach : ∀ q', ∃ w, M'.run q₀' w = q')
  (hInitBeh : M'.beh q₀' = M.beh q₀),
  let φ := fun q' => (⟨M'.beh q', ...⟩ : ReachableBeh M q₀)
  ((∀ q', (φ q').1 [] = M'.out q') ∧
   (∀ q' i, φ (M'.step q' i) = (minimalMachine M q₀).step (φ q') i)) ∧
  (φ q₀' = ⟨M.beh q₀, ⟨[], rfl⟩⟩) ∧
  (∀ s : ReachableBeh M q₀, ∃ q' : Q', φ q' = s) ∧
  (∀ ψ : Q' → ReachableBeh M q₀,
    ((∀ q', (ψ q').1 [] = M'.out q') ∧
     (∀ q' i, ψ (M'.step q' i) = (minimalMachine M q₀).step (ψ q') i)) →
    ψ = φ)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hReach : AllReachable M' q₀'` | Argument of `toMinimalQuotient`; ensures every state of `M'` has behavior in `ReachableBeh M q₀`. | `tight`: with `hReach` dropped, `φ` cannot be formed; `Toy.Obs.ce_reachable_maps_onto_minimal_no_reach` shows that no homomorphism `M' → minimalMachine M q₀` exists at all. |
| `hInitBeh : M'.beh q₀' = M.beh q₀` | Argument of `toMinimalQuotient`; aligns reachable behavior derivatives and initial states of `(M', q₀')` and `(M, q₀)`. | `tight`: with `hInitBeh` dropped, `φ` cannot be formed; `Toy.Obs.ce_reachable_maps_onto_minimal_no_initBeh` shows that no homomorphism `M' → minimalMachine M q₀` exists at all. |

- **Non-vacuity witness:** `Toy.Obs.nv_reachable_maps_onto_minimalMachine` (`M = toggleMachine` at `false`, `M' = threeStateToggle` at `s0`; the theorem proves both hypotheses, `AllReachable threeStateToggle .s0` and `threeStateToggle.beh .s0 = toggleMachine.beh false`). The resulting map `φ` is non-injective: `φ s0 = φ s1 ≠ φ s2`, proved separately as `Toy.Obs.ex_pos_toMinimalQuotient`.
- **Proved boundary witness:** `Toy.Obs.toMinimalQuotient_injective_iff` (characterizes injectivity of `toMinimalQuotient` as equivalent to `BehInjective M'`).
- **Prior art:** Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`); Goguen (1972, DOI `10.1090/S0002-9904-1972-13032-5`); Arbib and Manes (1974, DOI `10.1137/1016026`); Rutten (2000, §3, Example 9.5, Example 10.2(5), DOI `10.1016/S0304-3975(00)00056-6`); Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`: `Mathlib/Computability/MyhillNerode.lean`, comparison only: it constructs the left-quotient automaton `Language.toDFA` and proves `accepts_toDFA` and `isRegular_iff_finite_range_leftQuotient`; it contains no minimality, universal-quotient, or uniqueness-up-to-isomorphism theorem at this commit).
- **Design question:** Reference point: establishes the universal minimality property that every reachable semantic presentation realizing the same initial behavior factors canonically and surjectively onto the minimal observational quotient.

---

### 3c. `reachable_behInjective_iso` (`Toy.Obs.reachable_behInjective_iso`)

- **Kind:** `theorem`
- **Tier:** `T0` — re-derivation of Myhill–Nerode / Moore uniqueness of minimal deterministic machines up to unique isomorphism.
- **Depth:** `shallow`.
- **Plain claim:** Any two all-reachable, behavior-injective Moore machines `(M₁, q₁)` and `(M₂, q₂)` with identical initial behavior (`M₁.beh q₁ = M₂.beh q₂`) are canonically isomorphic via the exhibited inverse pair `(minimalIsoFun M₁ q₁ M₂ q₂ hReach₁, minimalIsoFun M₂ q₂ M₁ q₁ hReach₂)`, which preserves initial states, commutes with multi-step runs from the initial states, and is the unique homomorphism `M₁ → M₂`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem reachable_behInjective_iso
    {I : Type v} {O : Type w} {Q₁ : Type u₁} {Q₂ : Type u₂}
    (M₁ : Moore I O Q₁) (q₁ : Q₁)
    (M₂ : Moore I O Q₂) (q₂ : Q₂)
    (hReach₁ : AllReachable M₁ q₁)
    (hReach₂ : AllReachable M₂ q₂)
    (hInj₁ : BehInjective M₁)
    (hInj₂ : BehInjective M₂)
    (hInitBeh : M₁.beh q₁ = M₂.beh q₂) :
    let f := minimalIsoFun M₁ q₁ M₂ q₂ hReach₁
    let g := minimalIsoFun M₂ q₂ M₁ q₁ hReach₂
    IsIso M₁ M₂ f g ∧
    PreservesInit q₁ q₂ f ∧
    PreservesInit q₂ q₁ g ∧
    (∀ w : List I, f (M₁.run q₁ w) = M₂.run q₂ w) ∧
    (∀ φ : Q₁ → Q₂, IsHom M₁ M₂ φ → φ = f)
```
**Key definitions unfolded:**
```lean
∀ (M₁ : Moore I O Q₁) (q₁ : Q₁) (M₂ : Moore I O Q₂) (q₂ : Q₂)
  (hReach₁ : ∀ q, ∃ w, M₁.run q₁ w = q)
  (hReach₂ : ∀ q, ∃ w, M₂.run q₂ w = q)
  (hInj₁ : ∀ x y, M₁.beh x = M₁.beh y → x = y)
  (hInj₂ : ∀ x y, M₂.beh x = M₂.beh y → x = y)
  (hInitBeh : M₁.beh q₁ = M₂.beh q₂),
  let f := fun q => M₂.run q₂ (Classical.choose (hReach₁ q))
  let g := fun q => M₁.run q₁ (Classical.choose (hReach₂ q))
  (IsHom M₁ M₂ f ∧ IsHom M₂ M₁ g ∧ (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)) ∧
  (f q₁ = q₂) ∧ (g q₂ = q₁) ∧
  (∀ w : List I, f (M₁.run q₁ w) = M₂.run q₂ w) ∧
  (∀ φ : Q₁ → Q₂, IsHom M₁ M₂ φ → φ = f)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hReach₁ : AllReachable M₁ q₁` | Argument of `minimalIsoFun M₁ q₁ M₂ q₂ hReach₁`; excludes dead states in `M₁`. | `tight`: with `hReach₁` dropped, `f` cannot be formed; `Toy.Obs.ce_minimal_iso_no_reach1` shows that no isomorphism `IsIso M₁ M₂ f g` exists at all. |
| `hReach₂ : AllReachable M₂ q₂` | Argument of `minimalIsoFun M₂ q₂ M₁ q₁ hReach₂`; excludes dead states in `M₂`. | `tight`: with `hReach₂` dropped, `g` cannot be formed; `Toy.Obs.ce_minimal_iso_no_reach2` shows that no isomorphism `IsIso M₁ M₂ f g` exists at all. |
| `hInj₁ : BehInjective M₁` | Excludes observationally duplicate states in `M₁` so `g` is well-defined and left-inverse. | `tight`: `Toy.Obs.ce_minimal_iso_no_inj1` |
| `hInj₂ : BehInjective M₂` | Excludes observationally duplicate states in `M₂` so `f` is well-defined, right-inverse, and unique. | `tight`: `Toy.Obs.ce_minimal_iso_no_inj2` |
| `hInitBeh : M₁.beh q₁ = M₂.beh q₂` | Aligns the observable behaviors of the two pointed machines. | `tight`: `Toy.Obs.ce_minimal_iso_no_initBeh` |

- **Non-vacuity witness:** `Toy.Obs.nv_reachable_behInjective_iso` (`toggleMachine` at `false` and `dualToggleMachine` at `true`, isomorphic via `Bool.not`).
- **Proved boundary witness:** `Toy.Obs.iso_without_reachability` (`idBoolMachine` at `false` fails `AllReachable`, yet is isomorphic to itself via `id`).
- **Prior art:** Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`); Myhill (1957); Nerode (1958, DOI `10.1090/S0002-9939-1958-0135681-9`); Goguen (1972, DOI `10.1090/S0002-9904-1972-13032-5`); Arbib and Manes (1974, DOI `10.1137/1016026`); Doczkal, Kaiser, and Smolka (2013, CPP 2013, LNCS 8307, pp. 82–97, DOI `10.1007/978-3-319-03545-1_6`, Coq uniqueness of minimal DFAs); Paulson (2015, AFP `Finite_Automata_HF`, Isabelle/HOL uniqueness of minimal DFAs); Lean Mathlib4 (`leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`, `Mathlib/Computability/MyhillNerode.lean`, comparison only: left-quotient automaton `Language.toDFA` only; no minimality or uniqueness-up-to-isomorphism theorem at this commit, unlike the two mechanizations just cited).
- **Design question:** Reference point: guarantees that a canonical minimal semantics is unique up to a unique isomorphism, so any two fully reduced, reachable deterministic semantic models with the same observable behavior are structurally identical.

---

### 4a-i. `stepwise_nondependence_implies_behIgnoresHidden` (`Toy.Obs.stepwise_nondependence_implies_behIgnoresHidden`)

- **Kind:** `theorem`
- **Tier:** `T0` — re-derivation of two-level functional independence implying nonleakage (von Oheimb 2004; Owicki and Gries 1976; Goguen and Meseguer 1984).
- **Depth:** `shallow` (induction on `w : List I`).
- **Plain claim:** For any split-state Moore machine `M : Moore I O (A × H)` (whether or not `H` is inhabited), if `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold, then `BehIgnoresHidden M` (two-level deterministic nonleakage of `H`) holds.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem stepwise_nondependence_implies_behIgnoresHidden
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (hOut : OutIgnoresHidden M)
    (hStepFst : StepFstIgnoresHidden M) :
    BehIgnoresHidden M
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)),
  (∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)) →
  (∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1) →
  ∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hOut : OutIgnoresHidden M` | Ensures immediate outputs `M.out (a, h)` do not depend extensionally on `h`. | `tight`: `Toy.Obs.ce_stepwise_no_out` |
| `hStepFst : StepFstIgnoresHidden M` | Ensures `(M.step (a, h) i).1` does not depend extensionally on `h` across each step. | `tight`: `Toy.Obs.ce_stepwise_no_stepFst` |

- **Non-vacuity witness:** `Toy.Obs.nv_stepwise_nondependence_implies_behIgnoresHidden` (`syntacticIndependentMachine` on `Bool × Nat` and `emptyHiddenMachine` on `Unit × Empty`, where no `h₀ : Empty` exists).
- **Prior art:** von Oheimb (2004, ESORICS 2004, LNCS 3193, pp. 225–243, DOI `10.1007/978-3-540-30108-0_14`); Owicki and Gries (1976, DOI `10.1007/BF00268134`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Filliâtre, Gondelman, and Paskevich (2016, DOI `10.1007/s10703-016-0243-x`, type-and-effect non-interference discipline for ghost code, with ghost-code erasure proved sound via bisimulation).
- **Design question:** Shows without any inhabitant assumption on `H` that per-step extensional independence of both `out` and `step.1` is a sound sufficient condition for nonleakage of `H` (`BehIgnoresHidden M`).
- `Basis: derived (modeling bridge)` — In a deterministic semantics with an explicit observable/bookkeeping split, a syntactic check guaranteeing that neither observations nor updates to the observable state read the bookkeeping state implies `OutIgnoresHidden` and `StepFstIgnoresHidden`, and therefore suffices for global behavioral nonleakage.

---

### 4a-ii. `stepwise_nondependence_preserves_beh` (`Toy.Obs.stepwise_nondependence_preserves_beh`)

- **Kind:** `theorem`
- **Tier:** `T0` — re-derivation of auxiliary-variable erasure / fixed-relation unwinding (`SameFst`) for split-state deterministic Moore machines (von Oheimb 2004; Owicki and Gries 1976; Goguen and Meseguer 1984; Abadi and Lamport 1991; Filliâtre, Gondelman, and Paskevich 2016).
- **Depth:** `shallow`.
- **Plain claim:** For any split-state Moore machine `M : Moore I O (A × H)` with a dummy hidden value `h₀ : H`, if `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold, then `Prod.fst` is a homomorphism `M → eraseHidden M h₀`, `eraseHidden M h₀` preserves behavior for every `(a, h)`, `BehIgnoresHidden M` holds, and `eraseHidden M h₁` is independent of the dummy value `h₁ : H`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem stepwise_nondependence_preserves_beh
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (h₀ : H)
    (hOut : OutIgnoresHidden M)
    (hStepFst : StepFstIgnoresHidden M) :
    IsHom M (eraseHidden M h₀) Prod.fst ∧
    (∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h)) ∧
    BehIgnoresHidden M ∧
    (∀ h₁, eraseHidden M h₁ = eraseHidden M h₀)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)) (h₀ : H),
  (∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)) →
  (∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1) →
  (IsHom M { step := fun a i => (M.step (a, h₀) i).1, out := fun a => M.out (a, h₀) } Prod.fst) ∧
  (∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h)) ∧
  (∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)) ∧
  (∀ h₁, eraseHidden M h₁ = eraseHidden M h₀)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `h₀ : H` | Argument of `eraseHidden M h₀` in the conclusion. `BehIgnoresHidden M` itself needs no `h₀` (`stepwise_nondependence_implies_behIgnoresHidden`), and the *choice* of `h₀` is irrelevant (fourth conjunct), but the *existence* of an inhabitant is necessary for any erased machine on `A` when `O` is empty and `A` is nonempty. | `tight`: with `h₀` dropped, `eraseHidden M h₀` cannot be formed; `Toy.Obs.ce_erase_empty_hidden` refutes the strongest formable statement: `emptyHiddenMachine` satisfies `OutIgnoresHidden` and `StepFstIgnoresHidden`, yet no machine `M' : Moore Unit Empty Unit` reproduces its behavior, so in particular none has `Prod.fst` as a homomorphism onto it. |
| `hOut : OutIgnoresHidden M` | Ensures `M.out (a, h)` is extensionally independent of `h`, yielding `PreservesOut` for `Prod.fst`. | `tight`: `Toy.Obs.ce_stepwise_erase_no_out` |
| `hStepFst : StepFstIgnoresHidden M` | Ensures `(M.step (a, h) i).1` is extensionally independent of `h`, yielding `PreservesStep` for `Prod.fst`. | `tight`: `Toy.Obs.ce_stepwise_erase_no_stepFst` |

- **Non-vacuity witness:** `Toy.Obs.nv_stepwise_nondependence_preserves_beh` (`syntacticIndependentMachine` on `Bool × Nat` with `h₀ = 0`).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Owicki and Gries (1976, DOI `10.1007/BF00268134`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Abadi and Lamport (1991, DOI `10.1016/0304-3975(91)90224-P`); Filliâtre, Gondelman, and Paskevich (2016, DOI `10.1007/s10703-016-0243-x`).
- **Design question:** Gives the local per-step sufficient condition (on both `out` and `step.1`) under which hidden state `H` can be deleted via dummy substitution `eraseHidden M h₀` with `Prod.fst` as an explicit Moore homomorphism.

---

### 4a-iii. `isBisim_sameFst_iff` (`Toy.Obs.isBisim_sameFst_iff`)

- **Kind:** `characterization`
- **Tier:** `T0` — re-derivation of the equivalence between two-level functional independence and preservation of low-state equality `SameFst` (von Oheimb 2004; Goguen and Meseguer 1984).
- **Depth:** `definitional` (zero axioms; direct unpacking of pair projections).
- **Plain claim:** For every split-state Moore machine `M : Moore I O (A × H)`, the observable-projection relation `SameFst` satisfies `CoversHidden SameFst`, and `IsBisim M SameFst` holds if and only if `OutIgnoresHidden M` and `StepFstIgnoresHidden M` both hold.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem isBisim_sameFst_iff
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) :
    CoversHidden (SameFst : (A × H) → (A × H) → Prop) ∧
    (IsBisim M SameFst ↔ OutIgnoresHidden M ∧ StepFstIgnoresHidden M)
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)),
  (∀ a h₁ h₂, (a, h₁).1 = (a, h₂).1) ∧
  (((∀ p₁ p₂, p₁.1 = p₂.1 → M.out p₁ = M.out p₂) ∧
    (∀ p₁ p₂, p₁.1 = p₂.1 → ∀ i, (M.step p₁ i).1 = (M.step p₂ i).1)) ↔
   ((∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)) ∧
    (∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1)))
```

- **Hypothesis ledger:** None (unconditional over every `M : Moore I O (A × H)`).
- **Non-vacuity witness:** `Toy.Obs.nv_isBisim_sameFst_iff` (`syntacticIndependentMachine` satisfies `IsBisim _ SameFst`, while `redundantTagMachine` violates it).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`, equating functional independence with preservation of low-state equality); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`).
- **Design question:** Formalizes the exact bridge between Results 4a and 5c: per-step extensional non-dependence (`OutIgnoresHidden ∧ StepFstIgnoresHidden`) is literally unwinding with the fixed relation `R = SameFst`.

---

### 4b. `redundantTagMachine_erasable_despite_step_dependence` (`Toy.Obs.redundantTagMachine_erasable_despite_step_dependence`)

- **Kind:** `counterexample`
- **Tier:** `T1` — folklore in information flow and ghost-code erasure made precise as a concrete mechanized counterexample over `Moore Bool Bool ((Bool × Bool) × Bool)`.
- **Depth:** `shallow`.
- **Plain claim:** The concrete machine `redundantTagMachine` on `(Bool × Bool) × Bool` satisfies `OutIgnoresHidden`, `BehIgnoresHidden`, and global behavior preservation under `eraseHidden` for every dummy `h₀`, yet fails `StepFstIgnoresHidden` (even on states reachable from `((false, false), false)`) and admits no reduced machine on `Bool × Bool` for which `Prod.fst` is a homomorphism.
- `Basis: execution (Lean kernel check)`

**Lean statement (with `redundantTagMachine` definition quoted):**
```lean
-- def redundantTagMachine : Moore Bool Bool ((Bool × Bool) × Bool) where
--   step p i := ((!p.1.1, p.2), i)
--   out  p   := p.1.1
theorem redundantTagMachine_erasable_despite_step_dependence :
    OutIgnoresHidden redundantTagMachine ∧
    ¬ StepFstIgnoresHidden redundantTagMachine ∧
    BehIgnoresHidden redundantTagMachine ∧
    (∀ h₀ a h, (eraseHidden redundantTagMachine h₀).beh a = redundantTagMachine.beh (a, h)) ∧
    (¬ ∃ M' : Moore Bool Bool (Bool × Bool), IsHom redundantTagMachine M' Prod.fst) ∧
    (∃ a h₁ h₂ i,
      Reachable redundantTagMachine ((false, false), false) (a, h₁) ∧
      Reachable redundantTagMachine ((false, false), false) (a, h₂) ∧
      (redundantTagMachine.step (a, h₁) i).1 ≠ (redundantTagMachine.step (a, h₂) i).1)
```

- **Hypothesis ledger:** None (unconditional counterexample).
- **Non-vacuity witness:** `Toy.Obs.nv_redundantTagMachine_nontrivial` (`redundantTagMachine` emits `false` on `[]` and `true` on `[false]`).
- **Proved boundary witness:** `Toy.Obs.redundantTag_has_other_hom` (`((x, _t), _h) ↦ (x, false)` is a homomorphism from `redundantTagMachine` onto `eraseHidden redundantTagMachine false`, showing only `Prod.fst` fails).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Filliâtre, Gondelman, and Paskevich (2016, DOI `10.1007/s10703-016-0243-x`).
- **Design question:** Demonstrates that per-step checks forbidding `H` from affecting `step.1` are incomplete when `A` itself carries observationally redundant states: `H` can flow into unobserved representation details of `A` while remaining globally erasable.
- `Basis: derived (modeling bridge)` — In a real semantic framework where the nominal "observable" state `A` retains internal representation fields (padding, allocation tags, cached hashes) that never affect external outputs, a flow from hidden bookkeeping `H` into those unobserved fields fails strict `StepFstIgnoresHidden` checks even though `H` is semantically erasable.

---

### 4c. `behIgnoresHidden_iff_stepwise_of_obsInjectiveFst` (`Toy.Obs.behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`)

- **Kind:** `characterization`
- **Tier:** `T1` — exact converse of stepwise non-dependence under observational injectivity of `A`.
- **Depth:** `shallow`.
- **Plain claim:** For any split-state Moore machine `M : Moore I O (A × H)` whose observable component `A` has no distinct observationally equivalent states at any fixed hidden state (`ObsInjectiveFst M`), behavioral non-dependence (`BehIgnoresHidden M`) holds if and only if both `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem behIgnoresHidden_iff_stepwise_of_obsInjectiveFst
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (hInjA : ObsInjectiveFst M) :
    BehIgnoresHidden M ↔ OutIgnoresHidden M ∧ StepFstIgnoresHidden M
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)),
  (∀ a₁ a₂ h, M.beh (a₁, h) = M.beh (a₂, h) → a₁ = a₂) →
  ((∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)) ↔
   ((∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)) ∧
    (∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1)))
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hInjA : ObsInjectiveFst M` | Rules out distinct observationally equivalent states in `A` at a fixed `h` so equal successor behaviors force equal next `A`-states. | `tight`: `Toy.Obs.ce_stepwise_iff_no_obsInjectiveFst` |

- **Non-vacuity witness:** `Toy.Obs.nv_behIgnoresHidden_iff_stepwise_of_obsInjectiveFst` (`syntacticIndependentMachine` satisfies `ObsInjectiveFst` and both sides of the equivalence; `delayedChannel2` satisfies `ObsInjectiveFst` and violates both sides).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`).
- **Design question:** Identifies the exact boundary of incompleteness in `redundantTagMachine_erasable_despite_step_dependence`: once the observable state `A` is observationally reduced (`ObsInjectiveFst M`), the per-step check `OutIgnoresHidden M ∧ StepFstIgnoresHidden M` is both necessary and sufficient for `BehIgnoresHidden M`.
- `Basis: derived (modeling bridge)` — Whenever the observable component `A` of a deterministic model is already quotiented to remove redundant representation states, no coarser unwinding relation than `SameFst` is needed for global two-level nonleakage.

---

### 5a-0. `no_leak_under_stepwise_nondependence` (`Toy.Obs.no_leak_under_stepwise_nondependence`)

- **Kind:** `impossibility`
- **Tier:** `T0` — immediate negative corollary of `stepwise_nondependence_implies_behIgnoresHidden`.
- **Depth:** `shallow`.
- **Plain claim:** For any alphabets `I`, `O` and state components `A`, `H`, there does not exist a Moore machine `M : Moore I O (A × H)` that satisfies both `OutIgnoresHidden M` and `StepFstIgnoresHidden M` while failing `BehIgnoresHidden M`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem no_leak_under_stepwise_nondependence
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂} :
    ¬ ∃ M : Moore I O (A × H),
      OutIgnoresHidden M ∧ StepFstIgnoresHidden M ∧ ¬ BehIgnoresHidden M
```
**Key definitions unfolded:**
```lean
¬ ∃ M : Moore I O (A × H),
  (∀ a h₁ h₂, M.out (a, h₁) = M.out (a, h₂)) ∧
  (∀ a h₁ h₂ i, (M.step (a, h₁) i).1 = (M.step (a, h₂) i).1) ∧
  ¬ (∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂))
```

- **Hypothesis ledger:** None (unconditional across all types `I`, `O`, `A`, `H`).
- **Non-vacuity witness:** `Toy.Obs.nv_no_leak_under_stepwise_nondependence` (`syntacticIndependentMachine` satisfies `OutIgnoresHidden ∧ StepFstIgnoresHidden`; `delayedChannel2` satisfies `OutIgnoresHidden ∧ ¬ BehIgnoresHidden`).
- **Positive control:** `Toy.Obs.pc_leak_when_stepFst_dropped` — dropping `StepFstIgnoresHidden` while keeping `OutIgnoresHidden` and `OneStepOutIgnoresHidden` allows `delayedChannel2` to leak `H` (`¬ BehIgnoresHidden delayedChannel2`).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`).
- **Design question:** Resolves the ambiguity in "per-step checks fail to catch hidden channels": a per-step check covering both `out` and the `A`-component of `step` never misses a leak (no machine can satisfy every single-step law including `StepFstIgnoresHidden` and still leak `H`); what fails are checks on the output alone at any machine-independent depth, or checks that `H` is never written.

---

### 5a-i. `delayedChannel2_leaks_at_step_two` (`Toy.Obs.delayedChannel2_leaks_at_step_two`)

- **Kind:** `counterexample`
- **Tier:** `T1` — folklore in unwinding and multi-step covert channels made precise in Moore-machine vocabulary.
- **Depth:** `shallow`.
- **Plain claim:** The concrete two-slot shift register `delayedChannel2` on `(Bool × Bool) × Bool` satisfies `OutIgnoresHidden`, `OneStepOutIgnoresHidden`, `BoundedBehIgnoresHidden 2`, agreement with `eraseHidden` on all words of length `< 2`, and read-only `H` (`step.2 = h`), yet violates `StepFstIgnoresHidden`, fails `BehIgnoresHidden` at the two-step word `[(), ()]`, and admits no uniform reduced machine on `Bool × Bool` preserving its behavior across all `(a, h)`.
- `Basis: execution (Lean kernel check)`

**Lean statement (with `delayedChannel2` definition quoted):**
```lean
-- def delayedChannel2 : Moore Unit Bool ((Bool × Bool) × Bool) where
--   step p _ := ((p.1.2, p.2), p.2)
--   out  p   := p.1.1
theorem delayedChannel2_leaks_at_step_two :
    OutIgnoresHidden delayedChannel2 ∧
    OneStepOutIgnoresHidden delayedChannel2 ∧
    ¬ StepFstIgnoresHidden delayedChannel2 ∧
    BoundedBehIgnoresHidden delayedChannel2 2 ∧
    (∀ h₀ a h w, w.length < 2 →
      (eraseHidden delayedChannel2 h₀).beh a w = delayedChannel2.beh (a, h) w) ∧
    (∀ a h i, (delayedChannel2.step (a, h) i).2 = h) ∧
    ¬ BehIgnoresHidden delayedChannel2 ∧
    (¬ ∃ M' : Moore Unit Bool (Bool × Bool),
      ∀ a h, M'.beh a = delayedChannel2.beh (a, h)) ∧
    delayedChannel2.beh ((false, false), false) [(), ()] ≠
      delayedChannel2.beh ((false, false), true) [(), ()]
```

- **Hypothesis ledger:** None (unconditional counterexample).
- **Non-vacuity witness:** `Toy.Obs.nv_delayedChannel2_nontrivial` (`delayedChannel2` outputs `true` at `[]` and `false` at `[()]` from `((true, false), false)`).
- **Proved boundary witness:** `Toy.Obs.delayedChannel2_erasable_for_each_fixed_h` (for each fixed `h : Bool`, `eraseHidden delayedChannel2 h` reproduces `delayedChannel2.beh (a, h)` for all `a`).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Goguen and Meseguer (1982, DOI `10.1109/SP.1982.10014`; 1984, DOI `10.1109/SP.1984.10019`); Rushby (1992, SRI TR CSL-92-02).
- **Design question:** Shows concretely why checks on the output alone at 0 or 1 steps, as well as checks that `H` is read-only, fail to catch hidden channels: `H` violates `StepFstIgnoresHidden` on step 1 by flowing into an unexposed buffer bit of `A`, surfacing at `out` only on step 2.
- `Basis: derived (modeling bridge)` — Audits that inspect only immediate observation functions or read-only annotations on auxiliary state miss delayed flows where hidden state is staged into internal observable-state buffers and read out on later transitions.

---

### 5a-ii. `no_machine_independent_horizon_certifies_behIgnoresHidden` (`Toy.Obs.no_machine_independent_horizon_certifies_behIgnoresHidden`)

- **Kind:** `impossibility`
- **Tier:** `T1` — insufficiency of machine-independent finite-horizon observational checks made precise via an explicit parametric `(k + 2)`-slot shift-register family.
- **Depth:** `shallow` (induction on `w.length`).
- **Plain claim:** For every natural number `k`, the `(k + 2)`-slot shift register `delayedChannel k` satisfies `OutIgnoresHidden`, `OneStepOutIgnoresHidden`, `BoundedBehIgnoresHidden (k + 2)`, and agreement with `eraseHidden` on all words of length `< k + 2`, yet violates `StepFstIgnoresHidden`, fails `BehIgnoresHidden`, and admits no uniform behavior-preserving reduced machine on `Fin (k + 2) → Bool`.
- `Basis: execution (Lean kernel check)`

**Lean statement (with `delayedChannel` definition quoted):**
```lean
-- def delayedChannel (k : Nat) : Moore Unit Bool ((Fin (k + 2) → Bool) × Bool) where
--   step p _ := (fun j => if hlt : j.val + 1 < k + 2 then p.1 ⟨j.val + 1, hlt⟩ else p.2, p.2)
--   out  p   := p.1 ⟨0, Nat.zero_lt_succ _⟩
theorem no_machine_independent_horizon_certifies_behIgnoresHidden (k : Nat) :
    OutIgnoresHidden (delayedChannel k) ∧
    OneStepOutIgnoresHidden (delayedChannel k) ∧
    ¬ StepFstIgnoresHidden (delayedChannel k) ∧
    BoundedBehIgnoresHidden (delayedChannel k) (k + 2) ∧
    (∀ h₀ a h w, w.length < k + 2 →
      (eraseHidden (delayedChannel k) h₀).beh a w = (delayedChannel k).beh (a, h) w) ∧
    ¬ BehIgnoresHidden (delayedChannel k) ∧
    (¬ ∃ M' : Moore Unit Bool (Fin (k + 2) → Bool),
      ∀ a h, M'.beh a = (delayedChannel k).beh (a, h))
```

- **Hypothesis ledger:** None (holds for every `k : Nat`).
- **Non-vacuity witness:** `Toy.Obs.nv_no_machine_independent_horizon` (`BoundedBehIgnoresHidden (delayedChannel 3) 5` paired with an explicit leak at the length-5 word `[(), (), (), (), ()]`).
- **Positive controls:**
  - `Toy.Obs.pc_machine_dependent_horizon_detects_leak` — allowing the horizon to depend on the machine (`k + 3` for `delayedChannel k`) detects the leak (`¬ BoundedBehIgnoresHidden (delayedChannel k) (k + 3)` for every `k`).
  - `Toy.Obs.pc_bounded_horizon_with_step_consistency` — replacing the hidden feed in slot `k + 1` with constant `false` (`delayedChannelFixed k`) restores `StepFstIgnoresHidden`, yielding `BehIgnoresHidden` and uniform erasure via `eraseHidden` for all word lengths.
- **Prior art:** Moore (1956, pp. 129–154, DOI `10.1515/9781400882618-006`); von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Rushby (1992, SRI TR CSL-92-02).
- **Design question:** Shows that no single machine-independent finite horizon `k` can certify `BehIgnoresHidden` across machines of unbounded state-buffer depth, because an unexposed shift register of depth `k + 2` hides `H` for `k + 1` steps before emitting it.
- `Basis: derived (modeling bridge)` — Fixed-depth bounded model checking or trace testing with a machine-independent step bound cannot certify nonleakage across systems whose observable-state pipeline depth is not bounded below that horizon; certification requires either a machine-dependent bound (for finite state spaces) or a transition-level proof principle (`StepFstIgnoresHidden` or an unwinding bisimulation).

---

### 5b. `behIgnoresHidden_iff_erasable` (`Toy.Obs.behIgnoresHidden_iff_erasable`)

- **Kind:** `characterization`
- **Tier:** `T1` — exact behavioral characterization of uniform global hidden-state erasability onto `A` in Moore machines, including universality of dummy substitution `eraseHidden M h₀`.
- **Depth:** `shallow` (induction on `w : List I`).
- **Plain claim:** For any split-state Moore machine `M : Moore I O (A × H)` and any inhabitant `h₀ : H`, behavioral non-dependence (`BehIgnoresHidden M`) holds if and only if the concrete erased machine `eraseHidden M h₀` preserves behavior uniformly for all `(a, h)`, and also if and only if some reduced machine `M' : Moore I O A` preserves behavior uniformly for all `(a, h)`.
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem behIgnoresHidden_iff_erasable
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) (h₀ : H) :
    (BehIgnoresHidden M ↔ ∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h)) ∧
    (BehIgnoresHidden M ↔ ∃ M' : Moore I O A, ∀ a h, M'.beh a = M.beh (a, h))
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)) (h₀ : H),
  ((∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)) ↔
   (∀ a h, (eraseHidden M h₀).beh a = M.beh (a, h))) ∧
  ((∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)) ↔
   (∃ M' : Moore I O A, ∀ a h, M'.beh a = M.beh (a, h)))
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `h₀ : H` | Argument of `eraseHidden M h₀` in the first equivalence, and guarantees a reduced machine `M' : Moore I O A` exists even when `O` may be empty. | `tight`: with `h₀` dropped, `eraseHidden M h₀` cannot be formed; `Toy.Obs.ce_erase_empty_hidden` refutes the second equivalence (when `O` is empty and `A` nonempty, no reduced machine `M' : Moore I O A` exists at all). |

- **Non-vacuity witness:** `Toy.Obs.nv_behIgnoresHidden_iff_erasable` (`redundantTagMachine` with `h₀ = false`, where `BehIgnoresHidden` and global erasure via `eraseHidden` hold even though `StepFstIgnoresHidden` fails).
- **Proved boundary witness:** `Toy.Obs.gatedLeak_reachable_erasable_but_not_global` (`gatedLeak` is erasable on every state reachable from `(false, h)` yet fails global `BehIgnoresHidden` at `a = true`).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Goguen and Meseguer (1982, DOI `10.1109/SP.1982.10014`); Abadi and Lamport (1991, DOI `10.1016/0304-3975(91)90224-P`); Filliâtre, Gondelman, and Paskevich (2016, DOI `10.1007/s10703-016-0243-x`).
- **Design question:** Gives the exact necessary and sufficient behavioral condition for uniform global hidden-state erasure onto `A`, and shows that naive dummy substitution (`eraseHidden M h₀`) works whenever any uniform reduced machine on `A` (with identity correspondence on `A`) exists.
- `Basis: derived (modeling bridge)` — Under the identity state correspondence on a fixed split `A × H` with inhabited `H`, no clever transition synthesis on `A` can succeed where plugging in a fixed placeholder `h₀` fails; either `BehIgnoresHidden` holds and dummy substitution works, or no uniform machine on `A` exists.

---

### 5c-i. `unwinding_bisim_implies_behIgnoresHidden` (`Toy.Obs.unwinding_bisim_implies_behIgnoresHidden`)

- **Kind:** `theorem` (split-state corollary of `bisim_subset_obsEq`)
- **Tier:** `T0` — re-derivation of two-level deterministic nonleakage unwinding soundness (von Oheimb 2004; Mantel 2000; background: Goguen and Meseguer 1984; Rushby 1992).
- **Depth:** `shallow` (`bisim_subset_obsEq` composed with `CoversHidden`).
- **Plain claim:** For any split-state Moore machine `M : Moore I O (A × H)` and any state relation `R` on `A × H` satisfying `CoversHidden R`, `RelPreservesOut M R`, and `RelStepClosed M R` (a bisimulation containing `SameFst`), behavioral non-dependence (`BehIgnoresHidden M`, two-level deterministic nonleakage of `H`) holds (split-state corollary of `bisim_subset_obsEq`).
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem unwinding_bisim_implies_behIgnoresHidden
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H))
    (R : (A × H) → (A × H) → Prop)
    (hCov : CoversHidden R)
    (hOut : RelPreservesOut M R)
    (hStep : RelStepClosed M R) :
    BehIgnoresHidden M
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)) (R : (A × H) → (A × H) → Prop),
  (∀ a h₁ h₂, R (a, h₁) (a, h₂)) →
  (∀ p₁ p₂, R p₁ p₂ → M.out p₁ = M.out p₂) →
  (∀ p₁ p₂, R p₁ p₂ → ∀ i, R (M.step p₁ i) (M.step p₂ i)) →
  ∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)
```

**Hypothesis ledger:**

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hCov : CoversHidden R` | Ensures `R` contains `SameFst`, relating every pair `(a, h₁)`, `(a, h₂)` sharing observable component `a`. | `tight`: `Toy.Obs.ce_unwinding_no_coversHidden` |
| `hOut : RelPreservesOut M R` | Output consistency for `R`: related states emit the same immediate output. | `tight`: `Toy.Obs.ce_unwinding_no_out` |
| `hStep : RelStepClosed M R` | Step consistency for `R`: single-step transitions preserve `R`, ruling out delayed multi-step channels. | `tight`: `Toy.Obs.ce_unwinding_no_step` |

- **Non-vacuity witness:** `Toy.Obs.nv_unwinding_bisim_implies_behIgnoresHidden` (`redundantTagMachine` with `redundantTagUnwindingRel`, comparing only the observable toggling bit `x`, even though `StepFstIgnoresHidden` fails).
- **Prior art:** von Oheimb (2004, ESORICS 2004, LNCS 3193, pp. 225–243, DOI `10.1007/978-3-540-30108-0_14`, primary analogue); Mantel (2000, ESORICS 2000, LNCS 1895, pp. 238–254, DOI `10.1007/10722599_15`); Murray, Matichuk, Brassil, Gammie, and Klein (2012, CPP 2012, LNCS 7679, pp. 126–142, DOI `10.1007/978-3-642-35308-6_12`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Rushby (1992, SRI TR CSL-92-02).
- **Design question:** Corollary of `bisim_subset_obsEq` showing that an unwinding relation is simply a bisimulation containing `SameFst`: given a candidate `R` coarser than `SameFst` (compare `isBisim_sameFst_iff`), checking output and step preservation in a single step certifies `BehIgnoresHidden` even when `A` has redundant states.

---

### 5c-ii. `behIgnoresHidden_iff_exists_unwinding_bisim` (`Toy.Obs.behIgnoresHidden_iff_exists_unwinding_bisim`)

- **Kind:** `characterization` (split-state corollary of `obsEq_is_greatest_bisim`)
- **Tier:** `T0` — re-derivation of soundness and completeness of two-level deterministic nonleakage unwinding (von Oheimb 2004; Mantel 2000; background: Goguen and Meseguer 1984; Rushby 1992).
- **Depth:** `shallow` (soundness is `unwinding_bisim_implies_behIgnoresHidden`; completeness with `R = ObsEq M` is definitional via `behIgnoresHidden_iff_coversHidden_obsEq := Iff.rfl`).
- **Plain claim:** For every split-state Moore machine `M : Moore I O (A × H)`, `BehIgnoresHidden M` holds if and only if there exists a state relation `R` on `A × H` satisfying `CoversHidden R`, `RelPreservesOut M R`, and `RelStepClosed M R` (equivalently, some bisimulation on `M` contains `SameFst`; corollary of `obsEq_is_greatest_bisim`).
- `Basis: execution (Lean kernel check)`

**Lean statement:**
```lean
theorem behIgnoresHidden_iff_exists_unwinding_bisim
    {I : Type v} {O : Type w} {A : Type u₁} {H : Type u₂}
    (M : Moore I O (A × H)) :
    BehIgnoresHidden M ↔
      ∃ R : (A × H) → (A × H) → Prop,
        CoversHidden R ∧ RelPreservesOut M R ∧ RelStepClosed M R
```
**Key definitions unfolded:**
```lean
∀ (M : Moore I O (A × H)),
  (∀ a h₁ h₂, M.beh (a, h₁) = M.beh (a, h₂)) ↔
  ∃ R : (A × H) → (A × H) → Prop,
    (∀ a h₁ h₂, R (a, h₁) (a, h₂)) ∧
    (∀ p₁ p₂, R p₁ p₂ → M.out p₁ = M.out p₂) ∧
    (∀ p₁ p₂, R p₁ p₂ → ∀ i, R (M.step p₁ i) (M.step p₂ i))
```

- **Hypothesis ledger:** None (unconditional over every `M : Moore I O (A × H)`, including empty `H`).
- **Non-vacuity witness:** `Toy.Obs.nv_behIgnoresHidden_iff_exists_unwinding_bisim` (`redundantTagMachine`, witnessed by `redundantTagUnwindingRel`, where fixed-relation `SameFst` bisimulation fails).
- **Proved boundary witness:** `Toy.Obs.behIgnoresHidden_iff_coversHidden_obsEq` (`BehIgnoresHidden M ↔ CoversHidden (ObsEq M) := Iff.rfl`, exhibiting that the completeness direction is definitional once `ObsEq M` is known to be a bisimulation).
- **Prior art:** von Oheimb (2004, DOI `10.1007/978-3-540-30108-0_14`); Mantel (2000, DOI `10.1007/10722599_15`); Goguen and Meseguer (1984, DOI `10.1109/SP.1984.10019`); Rushby (1992, SRI TR CSL-92-02); van der Meyden (2007, DOI `10.1007/978-3-540-74835-9_16`; 2015, DOI `10.3233/JCS-140516`); Noce (2015, AFP `Noninterference_Generic_Unwinding`).
- **Design question:** Corollary of `obsEq_is_greatest_bisim` comparing fixed-relation `SameFst` bisimulation (`isBisim_sameFst_iff`, sufficient only unless `ObsInjectiveFst M` holds) with general bisimulations containing `SameFst` (sound and complete for `BehIgnoresHidden M`).

## Boundaries

### Non-Claims (Read First)

#### Package-Level Non-Claims and Over-Reading Guards
- **Uniform, global erasure only — not single-run or per-`h` impossibility:** Every erasure impossibility (`5a-i`, `5a-ii`) and characterization (`5b`) concerns *uniform, global* erasure: a single machine on `A` matching `M.beh (a, h)` for every `(a, h) : A × H` simultaneously, including states unreachable from an initial state of interest (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`). For any single initial state `(a, h)`, the behavior is always realized without a hidden component by `minimalMachine M (a, h)` (`3a`). A reduced machine on `A` itself for a single fixed `h` exists in some cases (e.g., `eraseHidden delayedChannel2 h` in `Toy.Obs.delayedChannel2_erasable_for_each_fixed_h`, where `H` is read-only), but **not in general** (unformalized remark: for a 2-state hidden clock on `Unit × Bool` with `step ((), h) _ = ((), !h)` and `out ((), h) = h`, no `Moore Unit Bool Unit` can reproduce the alternating behavior from `((), false)`).
- **Transition-level per-step checks do NOT miss hidden channels:** No result shows that per-step checks in general are unsound. Checking *both* `OutIgnoresHidden` and `StepFstIgnoresHidden` catches every hidden channel in this model at step 1 (`4a-i`, `5a-0`). What fails are checks on `out` alone at zero, one, or any machine-independent finite depth (`5a-i`, `5a-ii`), or checks that `H` is never written (`step.2 = h`).
- **Extensional, not syntactic:** `OutIgnoresHidden` and `StepFstIgnoresHidden` are extensional equalities (von Oheimb's functional independence). A code-level syntactic check forbidding reads of `H` implies them, not conversely.
- **No claim that inductive relations are strictly necessary:** `5a-ii` has quantifier order `∀ horizon ∃ machine` (ruling out a machine-independent bound). For a fixed finite machine with `n = |A × H|` states, checking words of length `≤ n - 1` suffices (unformalized classical remark: Moore 1956, reported via secondary literature as Theorem 6), and within `delayedChannel k`, horizon `k + 3` detects the leak (`Toy.Obs.pc_machine_dependent_horizon_detects_leak`).
- **Two-level deterministic nonleakage only:** Nothing in this package formalizes action-purge noninterference, intransitive security policies, nondeterministic systems, or CSP unwinding.

#### Per-Result Non-Claims
- **1a (`bisim_subset_obsEq`):** Unbundled soundness half of `obsEq_is_greatest_bisim`; does not establish completeness on its own. Does not require `R` to be reflexive, symmetric, or transitive, and proving `ObsEq` via `R` does not make `R` an equivalence relation. Applies only to total, deterministic Moore machines within a single machine `M` (not nondeterministic LTSs, partial transitions, `τ` moves, probabilistic systems, or cross-machine relations directly).
- **1b (`obsEq_is_greatest_bisim`):** Does not provide an algorithm or finite decision procedure for computing `ObsEq M` on infinite or unenumerable state spaces. Does not extend to nondeterministic systems where trace equivalence is strictly coarser than bisimilarity. Does not assert that a fixed projection relation such as `SameFst` equals `ObsEq M`.
- **2a (`hom_to_final_eq_beh`):** Unbundled uniqueness half of `finalMachine_is_final`. Does not claim uniqueness of homomorphisms into arbitrary Moore machines `M₂` (only into `finalMachine I O`; uniqueness into a general `M₂` holds when `BehInjective M₂`, an unformalized sufficient condition that is not necessary when `Q` is empty). Does not assert `h` is injective or surjective onto `List I → O`. Does not apply to Mealy machines or nondeterministic coalgebras.
- **2b (`finalMachine_is_final`):** Does not claim `finalMachine I O` is finite or computable when `I` or `O` is nonempty (unformalized remark: by Cantor's diagonal argument, `List I → O` is uncountable whenever `I` is nonempty and `|O| ≥ 2`). Does not claim every function `List I → O` is realized by a finite-state Moore machine (regularity requires finitely many left derivatives). Does not state uniqueness of final coalgebras up to isomorphism on its own.
- **3a (`minimalMachine_spec`):** Does not require `M` to be finite, all-reachable, or behavior-injective, and does not assert `minimalMachine M q₀` is finite when `Q` is infinite. Does not provide a constructive finite-state minimization algorithm (such as Moore's partition refinement or Hopcroft's algorithm). Discards states of `M` unreachable from `q₀`. Constructs a pointed minimal realization on `ReachableBeh M q₀`, not a global split-state erasure on `A`.
- **3b (`reachable_maps_onto_minimalMachine`):** Does not require `M` to be all-reachable or behavior-injective. Does not claim `toMinimalQuotient` is injective in general (injectivity holds iff `BehInjective M'`, proved as `Toy.Obs.toMinimalQuotient_injective_iff`). Does not establish a homomorphism from an unreachable `M'` with dead states outside `ReachableBeh M q₀`. Does not imply existence of a section homomorphism `minimalMachine M q₀ → M'`.
- **3c (`reachable_behInjective_iso`):** Tightness is existential: dropping a hypothesis admits a counterexample, but does not make every violating pair non-isomorphic (`Toy.Obs.iso_without_reachability` shows `idBoolMachine` at `false` fails `AllReachable` yet is isomorphic to itself via `id`). Uses `Classical.choose` in `minimalIsoFun`, so it does not construct a computable bijection without constructive reachability witnesses. Does not extend to nondeterministic automata (minimal NFAs need not be unique up to isomorphism).
- **4a-i (`stepwise_nondependence_implies_behIgnoresHidden`):** Captures one-step extensional independence (a code-level syntactic check is strictly stronger). Does not construct a reduced machine `M' : Moore I O A` when `H` and `O` are empty (`Toy.Obs.ce_erase_empty_hidden`). Does not claim `OutIgnoresHidden` and `StepFstIgnoresHidden` are necessary when `A` has redundant states (`4b`; necessity holds under `ObsInjectiveFst M` by `4c`). Equivalent to unwinding soundness at `R = SameFst` (`4a-iii` + `5c-i`). Does not cover reachable-only erasability under an invariant linking `a` and `h`.
- **4a-ii (`stepwise_nondependence_preserves_beh`):** Same extensionality, necessity, and reachable-only non-claims as `4a-i`. Also does not guarantee `eraseHidden M h₀` is minimal (`A` may still carry observationally equivalent states). Does not show that stepwise non-dependence alone yields a machine on `A`: the inhabitant `h₀ : H` is a `tight` hypothesis, and when `H` and `O` are empty but `A` is not, no erased machine on `A` exists (`Toy.Obs.ce_erase_empty_hidden`, with `A = Unit`); only the *choice* of `h₀` is irrelevant.
- **4a-iii (`isBisim_sameFst_iff`):** Purely structural bridge; does not assert `SameFst` is the only bisimulation covering hidden state (`redundantTagMachine` admits `redundantTagUnwindingRel` while failing `IsBisim _ SameFst`). Does not construct an erased machine on `A` without `h₀ : H`.
- **4b (`redundantTagMachine_erasable_despite_step_dependence`):** Does not show stepwise non-dependence is too strong in general: under `ObsInjectiveFst M`, `BehIgnoresHidden M` implies `StepFstIgnoresHidden M` (`4c`); the counterexample works only because the tag bit `t` of `A` is never observed. Does not show no homomorphism from `redundantTagMachine` onto a machine on `A` exists — only `Prod.fst` fails (`((x, t), h) ↦ (x, false)` is a homomorphism onto `eraseHidden redundantTagMachine false`, proved as `Toy.Obs.redundantTag_has_other_hom`). Erasability here is global over all `(a, h)`, not reachable-only (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`). Does not refute the necessity of `OutIgnoresHidden` (which always follows from `BehIgnoresHidden` at `[]`).
- **4c (`behIgnoresHidden_iff_stepwise_of_obsInjectiveFst`):** Fails when `A` contains observationally redundant states (`Toy.Obs.ce_stepwise_iff_no_obsInjectiveFst`). `ObsInjectiveFst M` requires injectivity of `a ↦ M.beh (a, h)` at each fixed `h`, which is strictly weaker than full `BehInjective M` on `A × H` (unformalized remark: `BehInjective M` implies `ObsInjectiveFst M`, strictly as witnessed by `syntacticIndependentMachine`; and when `A` is inhabited, `BehInjective M ∧ BehIgnoresHidden M` forces `H` to be a subsingleton). Characterizes uniform global `BehIgnoresHidden`, not reachable-only erasability.
- **5a-0 (`no_leak_under_stepwise_nondependence`):** Applies only when *both* `OutIgnoresHidden M` and `StepFstIgnoresHidden M` hold; dropping `StepFstIgnoresHidden M` allows multi-step leaks (`Toy.Obs.pc_leak_when_stepFst_dropped`). Does not claim `StepFstIgnoresHidden M` is necessary for `BehIgnoresHidden M` when `A` has redundant states (`4b`).
- **5a-i (`delayedChannel2_leaks_at_step_two`):** Does not show per-step non-dependence checks miss this channel: `StepFstIgnoresHidden` fails at step 1 (proved in `5a-i` and `ce_stepwise_erase_no_stepFst`); only checks on output alone (0-step, 1-step, or bounded depth) or read-only `H` are defeated. "Admits no reduced machine on `A`" means no single machine on `A` matches every `(a, h)` simultaneously; for `delayedChannel2` specifically (where `H` is read-only), `eraseHidden delayedChannel2 h` works for each fixed `h` (`Toy.Obs.delayedChannel2_erasable_for_each_fixed_h`), and every initial state has a pointed minimal realization (`minimalMachine`), though a per-`h` machine on `A` need not exist for arbitrary machines. Erasability here is global (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`). Does not address timing or physical side channels outside `out`.
- **5a-ii (`no_machine_independent_horizon_certifies_behIgnoresHidden`):** Rules out only a machine-independent horizon (`∀ horizon ∃ machine`); for a fixed finite machine with `n = |A × H|` states, words of length `≤ n - 1` suffice (unformalized classical remark: Moore 1956, Theorem 6 via secondary literature), and within `delayedChannel k`, horizon `k + 3` detects the leak (`Toy.Obs.pc_machine_dependent_horizon_detects_leak`). Does not show inductive relations are necessary. "Admits no reduced machine on `A`" is uniform in `h` and global over all `(a, h)`: every initial state has a pointed minimal realization (`minimalMachine`), and for a fixed `h` a machine on `A` exists for `delayedChannel2` (`Toy.Obs.delayedChannel2_erasable_for_each_fixed_h`; unformalized remark: similarly via `eraseHidden (delayedChannel k) h` for every `k`), though not for arbitrary Moore machines in general. `StepFstIgnoresHidden` fails at step 1 for every `delayedChannel k`, and restoring it in `delayedChannelFixed k` eliminates the leak (`Toy.Obs.pc_bounded_horizon_with_step_consistency`).
- **5b (`behIgnoresHidden_iff_erasable`):** "Some reduced machine `M' : Moore I O A`" requires uniformity in `h` with the identity correspondence on `A` (re-encodings of `A`, other carriers such as `ReachableBeh M q₀`, and per-`h` realizations are not covered). Characterizes global erasability over all `(a, h)`, not reachable-only erasability (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`). Does not claim `Prod.fst` is a homomorphism `M → eraseHidden M h₀` (`4b`). Does not claim `eraseHidden M h₀ = eraseHidden M h₁` syntactically under `BehIgnoresHidden M` alone (only behavioral agreement). **`h₀` is needed for the second equivalence only when `O` is empty (and `A` nonempty); if `O` is inhabited, `BehIgnoresHidden M ↔ ∃ M' : Moore I O A, ∀ a h, M'.beh a = M.beh (a, h)` holds for every `H` without supplying `h₀ : H` (unformalized remark).**
- **5c-i (`unwinding_bisim_implies_behIgnoresHidden`):** Two-level deterministic nonleakage unwinding (von Oheimb 2004), obtained as `bisim_subset_obsEq` composed with `CoversHidden`. Dropping equivalence-relation axioms on `R` is standard (Mantel 2000; von Oheimb 2004). Finding `R` is as hard as deciding `BehIgnoresHidden`, so "checkable" means single-step checkable *given* a candidate `R`. Omits a "locally respects" condition because all inputs are modeled uniformly without domain labels. Does not automate discovery of `R`.
- **5c-ii (`behIgnoresHidden_iff_exists_unwinding_bisim`):** Same two-level nonleakage and candidate-`R` caveats as `5c-i`; completeness with `R = ObsEq M` is definitional via `Toy.Obs.behIgnoresHidden_iff_coversHidden_obsEq`. Whether unwinding is complete in richer security models depends on the security definition: Rushby's intransitive unwinding is sound and complete for TA-security (van der Meyden 2007, 2015), while Noce (2015) exhibits a secure CSP process admitting no domain-relation map for the generic CSP unwinding condition; nothing about intransitive policies or CSP is formalized here. Because `H` need not be inhabited, `5c-ii` alone does not construct a reduced machine on `A` without `h₀ : H`.

### Escape Hatches

- **Defeating `5a-0` (`no_leak_under_stepwise_nondependence`):** Dropping `StepFstIgnoresHidden` while retaining `OutIgnoresHidden` and `OneStepOutIgnoresHidden` permits multi-step leaks (`Toy.Obs.pc_leak_when_stepFst_dropped`).
- **Defeating `5a-ii` (`no_machine_independent_horizon_certifies_behIgnoresHidden`):**
  1. Allowing the horizon to depend on the machine (`k + 3` for `delayedChannel k`, proved in `Toy.Obs.pc_machine_dependent_horizon_detects_leak`; or classically `≤ |A × H| - 1` for finite machines, unformalized remark).
  2. Restoring `StepFstIgnoresHidden` (`Toy.Obs.pc_bounded_horizon_with_step_consistency` on `delayedChannelFixed k`).
  3. Relaxing uniform global erasure on `A` to a single initial state (`minimalMachine_spec`) or, when `H` is read-only, a fixed `h` (`Toy.Obs.delayedChannel2_erasable_for_each_fixed_h`).
- **Defeating `4b` (`redundantTagMachine_erasable_despite_step_dependence`):** Requiring the observable carrier `A` to be observationally reduced (`ObsInjectiveFst M`) makes `OutIgnoresHidden ∧ StepFstIgnoresHidden` exact (`4c`).
- **Defeating `5b`'s `h₀ : H` requirement (`Toy.Obs.ce_erase_empty_hidden`):** Requiring `[Inhabited O]` (or `A` empty) makes the second equivalence `BehIgnoresHidden M ↔ ∃ M' : Moore I O A, ∀ a h, M'.beh a = M.beh (a, h)` hold for every `H`, including `H = Empty` (unformalized remark).

### Scope Classification (`known not to apply` / `not examined` / `unknown` / `unsupported`)

- **Known not to apply:**
  - `BehIgnoresHidden` as a characterization of reachable-only erasability from a fixed initial state (`Toy.Obs.gatedLeak_reachable_erasable_but_not_global`).
  - Per-`h` realizability on `A` itself for arbitrary Moore machines (fails for a hidden clock on `Unit × Bool`, unformalized remark).
  - Necessity of `StepFstIgnoresHidden` when `A` has observationally redundant states (`4b`).
  - Coincidence of bisimilarity and trace equivalence (`1b`) on nondeterministic systems.
- **Not examined:**
  - Non-identity correspondences or carrier re-encodings of `A` in erasure theorems.
  - Bridges connecting pointed `minimalMachine M (a₀, h₀)` with fixed-split `eraseHidden M h₀`, choosing a split `A × H`, mode-dependent bookkeeping, or invariant-relative reachable erasability characterizations.
  - Partial/stuck transitions, Mealy machines, silent (`τ`) steps, nondeterministic or probabilistic systems, action-labeled noninterference, intransitive security policies, CSP unwinding, and timing/physical side channels.
  - Constructive finite-state minimization algorithms, formalizing Moore's `n - 1` finite-state bound, and formalizing uncountability of `List I → O`.
- **Unknown tightness hypotheses:** None. Every hypothesis across all 18 results is classified: all 21 are `tight`, each backed by a proved canonical counterexample in `Toy/Obs/Witnesses.lean` (20 distinct counterexample declarations; `Toy.Obs.ce_erase_empty_hidden` serves the `h₀ : H` rows of both `4a-ii` and `5b`), and none is labeled `harmless`.
- **Unsupported:** External Lean libraries (Mathlib is intentionally excluded to keep the core dependency-free); computable isomorphism extraction from `AllReachable` without constructive reachability witnesses (`minimalIsoFun` uses `Classical.choice`).
- **Disproved or dropped statements:** No Lean statement was dropped or found false; all 18 statements are proved as specified with standard axioms only. **Refuted candidate claim:** the natural strong reading "some machine satisfies every single-step non-dependence law, including `StepFstIgnoresHidden`, yet leaks `H`" is false: no machine satisfies `OutIgnoresHidden`, `StepFstIgnoresHidden`, and `¬ BehIgnoresHidden` (Result `5a-0`, `Toy.Obs.no_leak_under_stepwise_nondependence`). The leaking examples `5a-i` and `5a-ii` necessarily violate `StepFstIgnoresHidden`.

## Evidence

### Toolchain and Package Artifacts

- **Lean toolchain:** `leanprover/lean4:v4.34.1` (GitHub repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).
- **Lake project (`lean/`):** `lakefile.toml` declares one `[[lean_lib]]` (`name = "Toy"`, the default target) and zero `[[require]]` dependencies. Library modules: `Toy.lean`, `Toy/Obs.lean`, `Toy/Obs/Defs.lean`, `Toy/Obs/Machines.lean`, `Toy/Obs/Examples.lean`, `Toy/Obs/Witnesses.lean`, `Toy/Obs/Results.lean`. The directory also contains `RevalidationAudit.lean`, a read-only audit program that is not part of the `Toy` target (`lake build` does not compile it and no library module imports it); see [Revalidation](#revalidation).
- **Preserved machine-readable artifacts:** `results.json` (one machine-readable record per result, 18 records), `audit/axioms.json` (249 declarations audited across all `Toy.*` modules), and `audit/statements.json` (65 statement and definition-closure SHA-256 records).
- **Preserved revalidation programs:** `support/revalidate.py` (Python 3 standard library only; builds a temporary copy of `lean/` and recomputes everything in `audit/statements.json`) and `lean/RevalidationAudit.lean` (prints per-declaration axioms and the exact hashed texts). Both implement the definitions in [Statement and closure hashes](#statement-and-closure-hashes).
- **Full environment axiom summary (`audit/axioms.json`):** 249 non-internal declarations audited; 0 `sorry` / `sorryAx`, 0 `axiom` or `opaque` declarations, 0 `native_decide` / `ofReduceBool` / `ofReduceNat`; the axioms used anywhere in the package are contained in `{Classical.choice, Quot.sound, propext}`, and their union over all declarations equals that set (`Toy.Obs.reachable_behInjective_iso`, `Toy.Obs.ex_pos_minimalIsoFun`, and `Toy.Obs.ex_neg_minimalIsoFun` use all three). Among the 18 main results, only `Toy.Obs.reachable_behInjective_iso` uses `Classical.choice` (via `minimalIsoFun`), `Toy.Obs.isBisim_sameFst_iff` uses no axioms, and the remaining 16 main results use at most `propext` and `Quot.sound`.

### Statement and closure hashes

The `Statement SHA-256` and `Closure SHA-256 (size)` columns below, and the records in `audit/statements.json`, are change-detection fingerprints. They are recomputed by `support/revalidate.py` (or by `lean/RevalidationAudit.lean` plus the short Python snippet in [Revalidation](#revalidation)) in the environment obtained by `import Lean` and `import Toy` under `leanprover/lean4:v4.34.1`, as follows:

- **Statement text** of a declaration `n`: `toString (repr ci.type)`, where `ci` is the kernel `ConstantInfo` of `n` and `repr` is Lean's derived `Repr Expr` instance. This is the fully elaborated kernel type (constants, universe levels, de Bruijn indices, binder names and binder kinds), not the pretty-printed source. `statement_sha256` is the SHA-256 of its UTF-8 encoding.
- **Library constant:** a constant declared in the module `Toy` or in a module whose name begins with `Toy.`. Constants from core Lean and `Std` are not library constants.
- **Definition closure** of `n`: the least set of library constants that contains every library constant occurring in `ci.type` and is closed under three rules. For each member `c`, add the library constants occurring in the type of `c`. If `c` is not a theorem and has a value, also add the library constants occurring in that value. This covers definitions and abbreviations, including any proof terms inside their bodies, and auxiliary definitions generated during elaboration (such as `Toy.Obs.Moore.run.match_1` and `Toy.Obs.Moore.run._f`). If `c` is an inductive type, also add its constructors. Non-library constants are neither included nor traversed. Theorem proofs are never traversed, so re-proving a theorem changes no hash.
- **Closure text:** one line per member `c`, namely `c : <toString (repr type)>`, followed by ` := <toString (repr value)>` when `c` is not a theorem and has a value. Lines are sorted by Lean's `String` order (lexicographic by Unicode code point) and joined with `\n`, with no trailing newline. `closure_sha256` is the SHA-256 of its UTF-8 encoding, and `closure_size` is the number of lines.
- **Recorded names:** all 65 Lean names that `results.json` uses as a result, proved boundary witness, non-vacuity witness, positive control, or tightness counterexample.

Under the pinned toolchain, a match certifies that each recorded statement, and every package definition it depends on, is unchanged in kernel form. Changes to theorem proofs, doc comments, or unrelated declarations do not alter any hash. A match says nothing about the accuracy of the prose. Under a different Lean version, `repr Expr` or elaboration details may change, so a hash mismatch there does not by itself show that a statement changed; compare the printed statement texts instead.

### Kernel-Check Audit Records (`audit/axioms.json`, `audit/statements.json`)

#### Main Results (18)

| Lean Declaration | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Obs.bisim_subset_obsEq` | Result 1a (`theorem`) | `Quot.sound` | `a35af76cb05e65a5bea43dc2cea3ba74acdd09edb58f4f0a4af093d8d39f8193` | `b10b78ce5acbdd7b203d133a5f31fd4a83903da170393031be81e8f1bfeba988` (11) |
| `Toy.Obs.obsEq_is_greatest_bisim` | Result 1b (`characterization`) | `Quot.sound` | `b6f8fde41e02bd59975db5aa291687431db83900ab0393e4f1c4f5d0437a6fb3` | `2e321605e8a74e552157d464de95e359130b4d08dab4b085e3f75af87f3b2b76` (12) |
| `Toy.Obs.hom_to_final_eq_beh` | Result 2a (`theorem`) | `Quot.sound` | `1594e794822769073b979a234d4468412281916a42d9279920d8e61b2c54891d` | `d4c6966bd47bca2716e8ebf364e3b0bf1305419c9ea4ce0422056f8a9bd3264f` (11) |
| `Toy.Obs.finalMachine_is_final` | Result 2b (`characterization`) | `Quot.sound` | `df6ba75f5ecd6aa2db2f59b23f886a6d687a32779cc66ed84cf935140a26b05c` | `0e61299cbc02d44d3a05e2ab5df6f6d2cf27c8d71d8fdc51f2257d54bd397e3d` (12) |
| `Toy.Obs.minimalMachine_spec` | Result 3a (`theorem`) | `Quot.sound`, `propext` | `9c88d71d98f41775d5ab1a0c7180f7f97d6b791627b470492ec3cadaad2649fa` | `4e2e2aff0785bdb1e1a968464e8311d1453eb52679bdebc7f97a4510aa5eec8b` (17) |
| `Toy.Obs.reachable_maps_onto_minimalMachine` | Result 3b (`theorem`) | `Quot.sound`, `propext` | `2e950b0610cadf1e49b86347e70ed57196739499038f39940e8b913ddcb30d1a` | `82f2260c09b20c9380863a7850f174076ce856ef014e2aa587be7793b78b034b` (23) |
| `Toy.Obs.reachable_behInjective_iso` | Result 3c (`theorem`) | `Classical.choice`, `Quot.sound`, `propext` | `40a84939e3872055d2c880867cf7e356fdbc2fb288ace17955b57f158ca6b76e` | `3d5783844a3c315077f09263d9d3f25954ba6d7370c55ccb6cb8f1c5ed115237` (17) |
| `Toy.Obs.stepwise_nondependence_implies_behIgnoresHidden` | Result 4a-i (`theorem`) | `Quot.sound` | `d3377e655dcf37582f685a519bccf46deb3f119b362b0a946b4c164e50fa4037` | `faf7b213f318de967c4a9153f035ef3830b0ab423f2be67d2e697568f620d312` (11) |
| `Toy.Obs.stepwise_nondependence_preserves_beh` | Result 4a-ii (`theorem`) | `Quot.sound` | `41b42c0f77203c20b3008b1f5626e26505460ea49f520e16ab394dc6daa89650` | `1c87052029cf6f78d7b1095308ec45fdebbb8f552a26920b3a084b7f4f864118` (15) |
| `Toy.Obs.isBisim_sameFst_iff` | Result 4a-iii (`characterization`) | none | `9a1d1577742ed75dc5fe5ef36ad99d6213a80d5de876edbd450ac4d0ccc7c139` | `0b4d07d2fe949d4576a0712a9040b968a7108cbf9c8e5184e5b9db4267138354` (11) |
| `Toy.Obs.redundantTagMachine_erasable_despite_step_dependence` | Result 4b (`counterexample`) | `Quot.sound`, `propext` | `5bb197ae33654a507af46d926cc87a3918f527bad2950fbf43fba1e59e0ebbfe` | `f6c89804aba723ef6a5051b8ff59d9d59d7128f817036cf2b285ef9d6965180b` (17) |
| `Toy.Obs.behIgnoresHidden_iff_stepwise_of_obsInjectiveFst` | Result 4c (`characterization`) | `Quot.sound` | `5712651459361f5ac42522bfef5e58b61a2c239e3e079661f881524ca8afc437` | `2fb81bb7bfe2f3ccb8d98dcedf256d2160d2da9f3dc24387726aa3262421cdb3` (12) |
| `Toy.Obs.no_leak_under_stepwise_nondependence` | Result 5a-0 (`impossibility`) | `Quot.sound` | `47f48ce79d86a849c4c57fabd020071ac75e482fcc79289735190dd5b776a2b8` | `faf7b213f318de967c4a9153f035ef3830b0ab423f2be67d2e697568f620d312` (11) |
| `Toy.Obs.delayedChannel2_leaks_at_step_two` | Result 5a-i (`counterexample`) | `Quot.sound`, `propext` | `59c59bb177d63a9ce10fd4b9044e605afb823ee706352d6f729baf3ab869e1ea` | `b64ba667b64f6631c63483311db0ad0d1e8b650e69a34efaae195fd40d87346f` (15) |
| `Toy.Obs.no_machine_independent_horizon_certifies_behIgnoresHidden` | Result 5a-ii (`impossibility`) | `Quot.sound`, `propext` | `c789a0fea616c23215ee7d6084660e84f0dac818a60e0484b9f3d2042bb6c363` | `6a41d86c92ce6091158bb0dab69c6f21e2b05e3d4f9f83ea5af2f7138d572c1f` (16) |
| `Toy.Obs.behIgnoresHidden_iff_erasable` | Result 5b (`characterization`) | `Quot.sound` | `5171457e62c48511a2b8cb04d9b4dbb88c31bd000720c2aad3285cc702c168c3` | `a00bf4451d68c5d835cf8b890888861f5edeb37bb712fcf1cc839e094ad64552` (10) |
| `Toy.Obs.unwinding_bisim_implies_behIgnoresHidden` | Result 5c-i (`theorem`) | `Quot.sound` | `d666f096e5412aeadab0b31be956102241376881b00c7282fd97e02e8150c08f` | `d88f5ebdcf266d231e5305b40652d778ffd3b495d06d35e7ab2ed4c89558df34` (12) |
| `Toy.Obs.behIgnoresHidden_iff_exists_unwinding_bisim` | Result 5c-ii (`characterization`) | `Quot.sound` | `514c6f75b0655234ea00f572fc772a759bd941e343808fbad2738b6f936559c3` | `d88f5ebdcf266d231e5305b40652d778ffd3b495d06d35e7ab2ed4c89558df34` (12) |

#### Proved Boundary Witnesses (`lean_names`, 6)

| Lean Declaration | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Obs.toMinimalQuotient_injective_iff` | Boundary witness (3b) | `Quot.sound`, `propext` | `653bb76bc21bb6fc7052f28a1304c315252f3759e5d5f71ba3ee811d8ab0e2d4` | `704aa5763c120b2df575e6a5fe312f5134f19d4e406aa692e84a0cccb95803cb` (14) |
| `Toy.Obs.iso_without_reachability` | Boundary witness (3c) | none | `17ec3cb5d41b744f5d75c5db48a8c4f4886af7b97cf73f082abcf033c55a50ec` | `a753a9968991d86f168dcf56f2ef0dbd72e79bfdb71c3f59893642e860373cd6` (16) |
| `Toy.Obs.redundantTag_has_other_hom` | Boundary witness (4b) | none | `11a8cfe7032bea7c0b2a333863a930f887f2dae97ce3b6629538d67b11974e3d` | `19ce8b88926e44f6943f943d906ab1f665df8fec9007ca85d5dd10d60bd9d0a5` (9) |
| `Toy.Obs.delayedChannel2_erasable_for_each_fixed_h` | Boundary witness (5a-i) | `Quot.sound` | `bf9219bf4a03d591e2dec4ffbb3d79202f3879d48860ded7869efce654936da9` | `4b63fdda2f8529efe28d858b59b17180299dbfe616a2889e700bc30af140cb84` (9) |
| `Toy.Obs.gatedLeak_reachable_erasable_but_not_global` | Boundary witness (5b) | `Quot.sound` | `cc19e9fdf4bd701b0f763b3a03ee5202e5db2b26d36ba67c821d34074c84a59f` | `7708feaa9b5ed76607854030c10eb545aacd30b53820ac1b9313118aec2573ca` (11) |
| `Toy.Obs.behIgnoresHidden_iff_coversHidden_obsEq` | Boundary witness (5c-ii) | none | `0a55413984562832890e0624a3f281815388718dda461572a0904b1502beb923` | `ea57413235db2dc339e76ed17623aa28d913101f805c90dcb0e8b340cb275488` (11) |

#### Non-Vacuity Witnesses (18)

| Lean Declaration | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Obs.nv_bisim_subset_obsEq` | Non-vacuity (1a) | `propext` | `2f8dc2c04897bf49696d65518ecd4eb58beb283b9f5b788de0ebdf6c81567b8c` | `58059be95ca3f083560dcab42a12ffa7b802b9441752ca174aadda3335e5c956` (16) |
| `Toy.Obs.nv_obsEq_is_greatest_bisim` | Non-vacuity (1b) | `Quot.sound` | `af5d3ee9890b35c7cded4825f559885a6c4148fad17351b14f9548486e4aef4c` | `dc56a50356effda8bd64445aaa221b851ac611bbb55b29fdeeef74a9881b6728` (18) |
| `Toy.Obs.nv_hom_to_final_eq_beh` | Non-vacuity (2a) | `Quot.sound`, `propext` | `01984de23cfd501b4b506663c89d8167b93a564f3de14f7c31b16f8f68d74746` | `99a90e836a111f70c8a5fc6654b5eddad02f95ffb270954cb16b30917a92d10f` (9) |
| `Toy.Obs.nv_finalMachine_is_final` | Non-vacuity (2b) | none | `a413de25e3b3a99071b147bed90e4da4aefcdb86d665493d96b87f1bfe10ddbb` | `0b608bbc5857b79515ef0cbd9fc2474cb669bb390545b564dd228a48a8ae3663` (9) |
| `Toy.Obs.nv_minimalMachine_spec` | Non-vacuity (3a) | `Quot.sound` | `2d2de2a3e4f744a9134bc2ab45650676751a71daee82475f509cc27d997626e0` | `b5735c900f8983cf82618b2d592527867334d93224d8667e6d431c6fe74a2d6f` (18) |
| `Toy.Obs.nv_reachable_maps_onto_minimalMachine` | Non-vacuity (3b) | `Quot.sound` | `6cd12add0ad602e56dd52b746ec3e1a459f9dbc2d647955f0086b621334b79fd` | `c74f4bb69fa5910ef235ddc5d0cfaa15bec06251ad170f4a30b326550f9c2df9` (20) |
| `Toy.Obs.nv_reachable_behInjective_iso` | Non-vacuity (3c) | `Quot.sound` | `edffa077ca285af0fca70ec8ea3d7f799b811f6c79519054a77b923c0a0222f8` | `ebeca52671f6fd930e6ecab05bec90d95a062c23953d94e165fee8dd5199bfd8` (13) |
| `Toy.Obs.nv_stepwise_nondependence_implies_behIgnoresHidden` | Non-vacuity (4a-i) | none | `c417d23e0881dc3835cab2b05bfbb5051c90c358702df382d46af806a10b00bf` | `d25776cc0ddb00f5d7696f57404b64f70c2671da0f3a3250d47a611e593d0c8b` (9) |
| `Toy.Obs.nv_stepwise_nondependence_preserves_beh` | Non-vacuity (4a-ii) | none | `7db43da13cea93b930991999f83b40358a6cccfccd838efae9462e25106eb964` | `6e0450af238079140c97f8302ef0439d3f30a2d6601faec5e6e8fa421fd2ea96` (7) |
| `Toy.Obs.nv_isBisim_sameFst_iff` | Non-vacuity (4a-iii) | none | `64797615fc1c961dd9e56b10c1e3aaf55d6897a365ff4f657ad89a75b718f1d5` | `eedf5e5a7956ac4c4b298d165062f253a328b4908c1e946aa353ec0b2797a40b` (10) |
| `Toy.Obs.nv_redundantTagMachine_nontrivial` | Non-vacuity (4b) | none | `a3e5f159c21243753aa0e0d52137fe0684efcde64dd48a1d18a415321622cf72` | `9b2035e35f9d2d1f2622c95d77e5ba2b9cd84ed91f26e8ce7af193bff9e5f91b` (9) |
| `Toy.Obs.nv_behIgnoresHidden_iff_stepwise_of_obsInjectiveFst` | Non-vacuity (4c) | `Quot.sound` | `6193d03eb0eb358ab887340f5cf90ce8ffee5ce8c5d77f6a2ace793e413e8a0d` | `c6d55cc539e08096e84eb32db5957d4fad3f57d82744fa81a76d7f66102e427f` (13) |
| `Toy.Obs.nv_no_leak_under_stepwise_nondependence` | Non-vacuity (5a-0) | none | `130bb195a5e31e426458bb589ee96e5a80597e74c40075638b55fcd4bccc7e1a` | `00ddb2cf43323b715fa732847de72c36c45dd8f0f5ea1d9e282a25eeab59c92f` (13) |
| `Toy.Obs.nv_delayedChannel2_nontrivial` | Non-vacuity (5a-i) | none | `ca68d312553dbe16c9519f74bdcd79178b8d70fdc401db8a0c75aafec0789e0a` | `4b63fdda2f8529efe28d858b59b17180299dbfe616a2889e700bc30af140cb84` (9) |
| `Toy.Obs.nv_no_machine_independent_horizon` | Non-vacuity (5a-ii) | `Quot.sound`, `propext` | `bc58ffaa0fa6efd95f443b9681865b08f50c0d22ea832a379b14c8ffc2f13a69` | `a7d88cd7533435091b269a70864189f59e2ea46938c50723e70b4bd561215018` (11) |
| `Toy.Obs.nv_behIgnoresHidden_iff_erasable` | Non-vacuity (5b) | `Quot.sound`, `propext` | `0723e338123b03b8a2639f275bb3ad73379fbe0da0b331d28191194e22f0ae9e` | `912c8321b1b09cc326889af18e7fb8eb01017f958a8f33f7078e8eb1dc9dd1f0` (11) |
| `Toy.Obs.nv_unwinding_bisim_implies_behIgnoresHidden` | Non-vacuity (5c-i) | none | `eae2c3c559b456861cc3710aba15e38d5165c9415926b9c2f8b30c29b78b9aa7` | `9e508bd23dd9087cb067973c2acf6eb58e198659336dc7d17a2f21846e30558b` (10) |
| `Toy.Obs.nv_behIgnoresHidden_iff_exists_unwinding_bisim` | Non-vacuity (5c-ii) | none | `62c7113b1ae7a1d0afd49b9ef48a7a5f10df6bff4cd792d3f8ac15bd0f3c9016` | `f5dd6ccef587d243ee9dc4a0ca7e5796b916006e54be18f3af9966bb5fc48a6c` (9) |

#### Tightness Counterexamples (20 declarations covering the 21 `tight` hypotheses)

| Lean Declaration | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Obs.ce_bisim_subset_obsEq_no_out` | Tightness CE (1a: `hOut`) | none | `3cd53a757bf46e5b8dc600254adba204a6031e13c234ab955bb8344f50a20caf` | `da92a44185bf95fc947e750739f8c0211d405e64fd64a10dc205678d0dc7ca8d` (11) |
| `Toy.Obs.ce_bisim_subset_obsEq_no_step` | Tightness CE (1a: `hStep`) | none | `45b6f0dca29fb4e7cb6f3cd084b99d6a944dc6b5971c1f88eed0d37bb5b1d883` | `2246e3ae287b227c7d90b84e5917740ecb3ff0dfc585b7010d3e4bfa512eaf5e` (19) |
| `Toy.Obs.ce_hom_to_final_no_out` | Tightness CE (2a: `hOut`) | none | `644aeade5f0e9fc1b142bf633fe693bf21ca62d773669e620e8b1721581c0b6b` | `1b4de8d12170ad31d08f459e85887a5ef6efcb44df83dc55b9cc0a00c12d915b` (11) |
| `Toy.Obs.ce_hom_to_final_no_step` | Tightness CE (2a: `hStep`) | none | `115a7dd3c08901b7cd66c3047c801f67c6520650bd9e4d95ecd4487442d700a7` | `2b82f0bc22078014e5341b7542a7f97138609f3777ee5debc29f2e75747317de` (11) |
| `Toy.Obs.ce_reachable_maps_onto_minimal_no_reach` | Tightness CE (3b: `hReach`) | `Quot.sound`, `propext` | `8a8c75f54d2af8cb9457486d4b5afe5a58bc1a261ef5d7212f1244d38397fe52` | `934d62873efe9ceb9a612c719b289c2dbb81399a61c1068c2313ac8d9a12884b` (17) |
| `Toy.Obs.ce_reachable_maps_onto_minimal_no_initBeh` | Tightness CE (3b: `hInitBeh`) | `Quot.sound`, `propext` | `e8ff9b3054fe0a8ff9eb77f9fee61f8c860bc45f8381c6c136daafb249bcf94e` | `8eb185d672e98edcf9192dc917b26eaa5c68d0e41a07828351233e7f41a237f4` (19) |
| `Toy.Obs.ce_minimal_iso_no_reach1` | Tightness CE (3c: `hReach₁`) | `Quot.sound` | `8e5b893bd010a6533d078df10e7e770bc8bd6f2e10eb0f92b934c269eca19811` | `6c0dec47af95e9938cddb3fdd71aa999bed8fad3b736c70459b3e480475c2299` (17) |
| `Toy.Obs.ce_minimal_iso_no_reach2` | Tightness CE (3c: `hReach₂`) | `Quot.sound` | `6ae470dd9631f717982eea52d555bdcfd52b071ce946f0727c5942a0e07a53ef` | `6c0dec47af95e9938cddb3fdd71aa999bed8fad3b736c70459b3e480475c2299` (17) |
| `Toy.Obs.ce_minimal_iso_no_inj1` | Tightness CE (3c: `hInj₁`) | `Quot.sound` | `cc69850a0be545da278bcb9bbb3688fb4c79f247db5a3447291bef523cffc030` | `c5fc024f3ff1102b1612ab7c61f6d988b0adcc86211f77a4993cc60f0b623eea` (17) |
| `Toy.Obs.ce_minimal_iso_no_inj2` | Tightness CE (3c: `hInj₂`) | `Quot.sound` | `ca712ef3d07825226c4cda05616e5309088d36a7fc8a1b623fb1bd815d9b29fa` | `c5fc024f3ff1102b1612ab7c61f6d988b0adcc86211f77a4993cc60f0b623eea` (17) |
| `Toy.Obs.ce_minimal_iso_no_initBeh` | Tightness CE (3c: `hInitBeh`) | none | `43556607401440cc29ee95c16ab52293ecf2411d079c3da1c3805be85c11bd1f` | `9a4eb3f4ba27ead9428b55d9c080a21548fccdaa4d931915d270622f06c9ee2d` (17) |
| `Toy.Obs.ce_stepwise_no_out` | Tightness CE (4a-i: `hOut`) | none | `2473074623c179c9ba204baaf7d12edaf683724988e0317018035a855f0cfdfb` | `2ab3d9167552d1bb8109f594523c0bac8f8e70dc99b6cf142b653efaa58d9949` (11) |
| `Toy.Obs.ce_stepwise_no_stepFst` | Tightness CE (4a-i: `hStepFst`) | none | `610b0a92e91f28d504fa53805cf0a0a3cc8d9701469f13c66d398f5e5654f2ef` | `f3814c67043bcf7bac4f0dcd8b0721cc1f396ba9cf944fa075fb922df3d408fa` (11) |
| `Toy.Obs.ce_stepwise_erase_no_out` | Tightness CE (4a-ii: `hOut`) | none | `69c6483676c4ee8e55af8acc653eab53b0edd95b1ab33f7bacb76b5ae7b5a4e8` | `c65011d0cec7a0245afb7704bb7c13d5aeaf6bc68ee434d6803b75ba6fc13b17` (15) |
| `Toy.Obs.ce_stepwise_erase_no_stepFst` | Tightness CE (4a-ii: `hStepFst`) | none | `3bc96a383336a4739f3bb0a7920cf8d0fc5131eb4877f8d2f0a4fa6e9ef92323` | `3484381b7372451ef55c8ad97454f6a8715e5e283135273555b4b0b2ea2e5fbf` (15) |
| `Toy.Obs.ce_stepwise_iff_no_obsInjectiveFst` | Tightness CE (4c: `hInjA`) | `Quot.sound`, `propext` | `76da175c722935c0b9d2c0bcbe0736632031b915380e8b81ca09576967523ca0` | `06dc4b65356b0e1d2cb1fcc3fc515c5fe6f6690c771bd8ddc4f65cae32c28fcc` (13) |
| `Toy.Obs.ce_erase_empty_hidden` | Tightness CE (4a-ii: `h₀`; 5b: `h₀`) | none | `824844ddfc5b5505f1978c82ef7866d3434538e68d410d4cd78db0d0ba34d995` | `09d659800932a8ffab815622b38e6b32a24c7b7026c58796661d46e3c5fd43c0` (13) |
| `Toy.Obs.ce_unwinding_no_coversHidden` | Tightness CE (5c-i: `hCov`) | none | `bf39b49989b5176ef84f5e908edf876a1c10d92fb2d0ba5f2bc172246d521f7b` | `cc75b91ace680803ccf97490b1c8e5d3e2b76e1441c2ce003a765508324b2a29` (12) |
| `Toy.Obs.ce_unwinding_no_out` | Tightness CE (5c-i: `hOut`) | none | `6124feefefd6f21e536dfbf9955aced770c92568f71a69f24b85ca08f4789dcc` | `0e3aa653fd7ba49b5ee7b7ec0c4e1430f6047d5706597955c5295b808934678a` (12) |
| `Toy.Obs.ce_unwinding_no_step` | Tightness CE (5c-i: `hStep`) | none | `0b02f1d8c449d189a029d168b65476ecd4d02ae6490ec0db64821694631e0e81` | `80ce1e8c56a50e0d3e87d34658c2e16da48edf25df2a5fca621eeebf09f4d6a0` (13) |

#### Positive Controls (3)

| Lean Declaration | Role | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Obs.pc_leak_when_stepFst_dropped` | Positive control (5a-0) | none | `f1fb0f160a188e2bfb08880a6d2f2e0b47876877f1e98859e72cc790d47e4ca3` | `508dd51eda099bfb3195bdd3aa1985b84789c7e1c6325122bed70b7f520d7bc3` (13) |
| `Toy.Obs.pc_machine_dependent_horizon_detects_leak` | Positive control (5a-ii) | `Quot.sound`, `propext` | `4f4e046c2afa925c0e3057de90e5191ab476cf5f7049961f77e4776d68efc302` | `a7d88cd7533435091b269a70864189f59e2ea46938c50723e70b4bd561215018` (11) |
| `Toy.Obs.pc_bounded_horizon_with_step_consistency` | Positive control (5a-ii) | `Quot.sound`, `propext` | `b0f5b9c1d01fc3c1177311bc704a5f36130911f2d13df9394b1ddca10e4b4d0c` | `7c8f4bd18f167c5381b761722ab7e54f79b1ec2962883014e1c60bebaf035038` (15) |

### Primary Sources and Prior-Art Records

Each citation below records its exact bibliographic identifiers and how it was verified (Crossref metadata, publisher/author page, full text, GitHub API, or secondary sources):

*Identity of Archive of Formal Proofs (AFP) entries.* An AFP entry has no DOI. It is maintained across Isabelle releases, and its URL shows the latest version. The entries cited here (items 18, 21, 22, 23) are therefore identified in `REPORT.json` by entry name and original submission date as well as URL. On 2026-11-20 each of the four entry pages listed `afp-<entry>-2026-10-26` (Isabelle2026) as its latest release archive. No release archive was examined: what this report takes from AFP entries (titles, authors, abstracts) comes from the entry pages.

1. **E. F. Moore (1956):** "Gedanken-experiments on sequential machines," in *Automata Studies*, Annals of Mathematics Studies No. 34, eds. C. E. Shannon and J. McCarthy, Princeton University Press, 1956, pp. 129–154. DOI: `10.1515/9781400882618-006`. *(Crossref verified for bibliographic metadata and page range 129–154; finite distinguishability bound "Theorem 6" confirmed via secondary literature only.)*
2. **J. Myhill (1957):** "Finite Automata and the Representation of Events," WADC Technical Report 57-624, Wright Air Development Center, 1957, pp. 112–137. *(No DOI; bibliographic record and Myhill congruence content confirmed via secondary sources only.)*
3. **A. Nerode (1958):** "Linear automaton transformations," *Proceedings of the American Mathematical Society* 9(4), 1958, pp. 541–544. DOI: `10.1090/S0002-9939-1958-0135681-9`. *(Crossref verified.)*
4. **J. A. Goguen (1972):** "Minimal realization of machines in closed categories," *Bulletin of the American Mathematical Society* 78(5), 1972, pp. 777–783. DOI: `10.1090/S0002-9904-1972-13032-5`. *(Crossref verified; full text not accessed.)*
5. **M. A. Arbib and E. G. Manes (1974):** "Machines in a Category: An Expository Introduction," *SIAM Review* 16(2), 1974, pp. 163–192. DOI: `10.1137/1016026`. *(Crossref verified; paywalled full text not accessed.)*
6. **S. S. Owicki and D. Gries (1976):** "An axiomatic proof technique for parallel programs I," *Acta Informatica* 6(4), 1976, pp. 319–340. DOI: `10.1007/BF00268134`. *(Crossref verified; auxiliary-variable rule confirmed via secondary sources.)*
7. **R. Milner (1980, 1989):** *A Calculus of Communicating Systems*, LNCS Vol. 92, Springer, 1980, DOI: `10.1007/3-540-10235-3` *(Crossref verified)*; and *Communication and Concurrency*, Prentice Hall, 1989, ISBN `978-0131150072` *(ISBN confirmed via web bibliographic listings)*.
8. **D. Park (1981):** "Concurrency and automata on infinite sequences," *Theoretical Computer Science (5th GI-Conference)*, LNCS Vol. 104, Springer, 1981, pp. 167–183. DOI: `10.1007/BFb0017309`. *(Crossref verified for title, author, LNCS series, and pages; volume 104 / year 1981 standard.)*
9. **J. A. Goguen and J. Meseguer (1982):** "Security Policies and Security Models," *Proc. 1982 IEEE Symposium on Security and Privacy*, pp. 11–20. DOI: `10.1109/SP.1982.10014`. *(Crossref verified for title, authors, venue, year, and start page 11; Crossref records no end page, so the range 11–20 is the conventionally cited range and was not independently verified; full text not accessed.)*
10. **J. A. Goguen and J. Meseguer (1984):** "Unwinding and Inference Control," *Proc. 1984 IEEE Symposium on Security and Privacy*, p. 75ff. DOI: `10.1109/SP.1984.10019`. *(Crossref verified for title, authors, venue, year, and start page 75; Crossref records no end page; full text not accessed.)*
11. **M. Abadi and L. Lamport (1991):** "The existence of refinement mappings," *Theoretical Computer Science* 82(2), 1991, pp. 253–284. DOI: `10.1016/0304-3975(91)90224-P`. *(Crossref verified.)*
12. **J. Rushby (1992):** "Noninterference, Transitivity, and Channel-Control Security Policies," Technical Report CSL-92-02, SRI International, December 1992. URL: `http://www.csl.sri.com/papers/csl-92-2/`. *(SRI landing page and abstract read; PDF not fetched.)*
13. **J. J. M. M. Rutten (1998):** "Automata and coinduction (an exercise in coalgebra)," *CONCUR '98*, LNCS Vol. 1466, Springer, 1998, pp. 194–218. DOI: `10.1007/BFb0055624`. *(Crossref verified.)*
14. **J. J. M. M. Rutten (2000):** "Universal coalgebra: a theory of systems," *Theoretical Computer Science* 249(1), 2000, pp. 3–80. DOI: `10.1016/S0304-3975(00)00056-6`. *(Crossref and full text verified: §3 Moore machines, Theorem 9.2, Example 9.5, Example 10.2(5) for the final Moore coalgebra `A^(B*)`.)*
15. **H. Mantel (2000):** "Unwinding Possibilistic Security Properties," *Computer Security – ESORICS 2000*, LNCS Vol. 1895, Springer, 2000, pp. 238–254. DOI: `10.1007/10722599_15`. *(Crossref verified.)*
16. **D. von Oheimb (2004):** "Information Flow Control Revisited: Noninfluence = Noninterference + Nonleakage," *Computer Security – ESORICS 2004*, LNCS Vol. 3193, Springer, 2004, pp. 225–243. DOI: `10.1007/978-3-540-30108-0_14`. *(Crossref, author page, and talk slides verified: non-equivalence unwinding relations, two-level functional independence `S_L(x₁, y) = S_L(x₂, y)`, low-state equality, nonleakage unwinding, and Isabelle mechanization.)*
17. **R. van der Meyden (2007, 2015):** "What, Indeed, Is Intransitive Noninterference?," *ESORICS 2007*, LNCS Vol. 4734, pp. 235–250, DOI: `10.1007/978-3-540-74835-9_16`; journal version *Journal of Computer Security* 23(2), 2015, pp. 197–228, DOI: `10.3233/JCS-140516`. *(Crossref and JCS abstract verified: soundness and completeness of Rushby's intransitive unwinding for TA-security.)*
18. **C. Wu, X. Zhang, and C. Urban (2011, 2014):** "The Myhill-Nerode Theorem Based on Regular Expressions," *Archive of Formal Proofs*, entry `Myhill-Nerode`, submitted 2011-08-26, `https://isa-afp.org/entries/Myhill-Nerode.html`; and the journal article "A Formalisation of the Myhill-Nerode Theorem Based on Regular Expressions," *Journal of Automated Reasoning* 52(4), 2014, pp. 451–480, DOI: `10.1007/s10817-013-9297-2`. *(AFP entry page verified, including entry name and submission date; Crossref verified for the journal title, authors, volume, issue, pages, and year.)*
19. **T. Murray, D. Matichuk, M. Brassil, P. Gammie, and G. Klein (2012):** "Noninterference for Operating System Kernels," *Certified Programs and Proofs (CPP 2012)*, LNCS Vol. 7679, Springer, 2012, pp. 126–142. DOI: `10.1007/978-3-642-35308-6_12`. *(Crossref verified.)*
20. **C. Doczkal, J.-O. Kaiser, and G. Smolka (2013):** "A Constructive Theory of Regular Languages in Coq," *Certified Programs and Proofs (CPP 2013)*, LNCS Vol. 8307, Springer, 2013, pp. 82–97. DOI: `10.1007/978-3-319-03545-1_6`. *(Crossref and author abstract verified.)*
21. **D. Traytel (2013, 2017):** "A Codatatype of Formal Languages," *Archive of Formal Proofs*, entry `Coinductive_Languages`, submitted 2013-11-15, `https://isa-afp.org/entries/Coinductive_Languages.html`; and "Formal Languages, Formally and Coinductively," *Logical Methods in Computer Science* 13(3:28), 2017, DOI: `10.23638/LMCS-13(3:28)2017`. *(AFP entry page verified, including entry name and submission date; Crossref verified.)*
22. **L. C. Paulson (2015):** "Finite Automata in Hereditarily Finite Set Theory," *Archive of Formal Proofs*, entry `Finite_Automata_HF`, submitted 2015-02-05, `https://isa-afp.org/entries/Finite_Automata_HF.html`. *(AFP entry page verified, including entry name and submission date.)*
23. **P. Noce (2015):** "The Generic Unwinding Theorem for CSP Noninterference Security," *Archive of Formal Proofs*, entry `Noninterference_Generic_Unwinding`, submitted 2015-06-11, `https://isa-afp.org/entries/Noninterference_Generic_Unwinding.html`. *(AFP entry page verified, including entry name and submission date.)*
24. **B. Jacobs (2016):** *Introduction to Coalgebra: Towards Mathematics of States and Observation*, Cambridge University Press, 2016, ISBN `9781107177895`, DOI: `10.1017/CBO9781316823187`. *(Crossref and publisher chapter listing verified.)*
25. **J.-C. Filliâtre, L. Gondelman, and A. Paskevich (2016):** "The spirit of ghost code," *Formal Methods in System Design* 48(3), 2016, pp. 152–174. DOI: `10.1007/s10703-016-0243-x`. *(Crossref and Springer abstract verified.)*
26. **Lean Mathlib4 prior-art comparison (not a dependency):** `leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`: `Mathlib/Computability/DFA.lean` (blob `41dbd3003b864976aac26b052797e38f922e9e93`), `Mathlib/Computability/MyhillNerode.lean` (blob `d1226288f751d8fa1235e5d1727b5cd22ea1aba2`), `Mathlib/Data/Stream/Init.lean` (blob `6e5fe776a42451b6a8135f77ee2c19dac9c9b90c`), and `Mathlib/Data/PFunctor/Univariate/M.lean` (blob `7a054f77e3e23d7311a6e070c0c6dee2ff27be27`). *(Verified via GitHub API.)* At this commit, `MyhillNerode.lean` declares `Language.leftQuotient` and lemmas about it, `Language.toDFA` with `accepts_toDFA`, and `isRegular_iff_finite_range_leftQuotient`; it contains no minimality, universal-quotient, or uniqueness-up-to-isomorphism theorem (file read at the pinned commit; its git blob hash matches the one recorded above).

## Revalidation

**Requirements.** `elan`, the Lean toolchain manager: through it, `lake` uses the toolchain pinned in `lean/lean-toolchain` (`leanprover/lean4:v4.34.1`) and downloads it on first use. `python3`, standard library only. Nothing else is needed: the Lake project has no `[[require]]` entries.

### Primary check

From the package directory:

```bash
python3 support/revalidate.py .
```

The script never modifies the package. It:
1. scans every `.lean` file under `lean/`, with comments removed, for `sorry`, `admit`, `native_decide`, and `axiom` declarations;
2. copies `lean/` to a temporary directory and runs `lake build` there;
3. writes and runs, with `lake env lean`, a Lean metaprogram that computes `Lean.collectAxioms` for every non-internal declaration of a `Toy` module, and fails if any axiom outside `{propext, Classical.choice, Quot.sound}` appears;
4. in the same metaprogram, prints the statement text and closure text of every Lean name referenced by `results.json` and of every name recorded in `audit/statements.json`, exactly as defined in [Statement and closure hashes](#statement-and-closure-hashes); Python then recomputes `statement_sha256`, `closure_sha256`, and `closure_size` and compares them with `audit/statements.json`.

Expected output (observed on 2026-11-20 with `leanprover/lean4:v4.34.1`), with exit status `0`:

```text
ok   lake build
ok   axioms (249 declarations)
ok   statement hashes (65 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

A pass establishes three things: the package builds; every declaration uses only the three standard axioms; and every recorded statement and its definition closure is unchanged in kernel form. It does not compare per-declaration axiom lists with `audit/axioms.json` (the manual check below does). It does not re-check any prose either. If a hash changes, re-read the plain claim, hypothesis ledger, non-claims, and Evidence rows of every affected result against the Lean source.

### Manual equivalent (without the script)

These steps run the same checks one at a time, from the package directory. `lean/RevalidationAudit.lean` is a self-contained audit program shipped in the package. It is outside the `Toy` library target, only reads the environment, and lists the 65 recorded names explicitly. It prints a single `REVALIDATION_JSON` line that contains, for every `Toy` declaration, its kind and axioms, and, for every recorded name, its `type_repr` (statement text) and `closure` (sorted closure lines). The inline Python snippet hashes these and compares them with `audit/axioms.json` and `audit/statements.json`:

```bash
cd lean
lake build                     # expect: Build completed successfully (9 jobs).
OUT="$(mktemp)"
lake env lean RevalidationAudit.lean > "$OUT"
cd ..
python3 - "$OUT" <<'EOF'
import hashlib, json, sys
line = next(l for l in open(sys.argv[1], encoding="utf-8") if l.startswith("REVALIDATION_JSON "))
out = json.loads(line[len("REVALIDATION_JSON "):])
allowed = {"propext", "Classical.choice", "Quot.sound"}
rec_ax = json.load(open("audit/axioms.json", encoding="utf-8"))["declarations"]
rec_st = json.load(open("audit/statements.json", encoding="utf-8"))["statements"]
got_ax = {d["name"]: sorted(d["axioms"]) for d in out["decls"]}
bad = [d["name"] for d in out["decls"] if d["kind"] in ("axiom", "opaque") or set(d["axioms"]) - allowed]
got_st = {s["name"]: {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
                      "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
                      "closure_size": len(s["closure"])}
          for s in out["stmts"] if not s.get("missing")}
for n in sorted(set(got_st) | set(rec_st)):
    if got_st.get(n) != rec_st.get(n):
        print("MISMATCH", n)
print(f"{len(got_ax)} declarations; {len(bad)} with axiom/opaque kind or non-standard axioms; "
      f"axioms equal audit/axioms.json: {got_ax == rec_ax}")
print(f"{len(got_st)} statements hashed; equal to audit/statements.json: {got_st == rec_st}")
sys.exit(0 if not bad and got_ax == rec_ax and got_st == rec_st else 1)
EOF
```

Expected output, with exit status `0`:

```text
249 declarations; 0 with axiom/opaque kind or non-standard axioms; axioms equal audit/axioms.json: True
65 statements hashed; equal to audit/statements.json: True
```

For each recorded name whose recomputed record differs from `audit/statements.json`, or is missing, the snippet also prints a `MISMATCH <name>` line. To see exactly what was hashed for a name, read its entry in the `REVALIDATION_JSON` line in `"$OUT"`. This path does not repeat the script's source-token scan. That scan is redundant for soundness, because `sorry` and `native_decide` introduce the axioms `sorryAx` and `Lean.ofReduceBool`, which the axiom comparison rejects, and the snippet reports every `axiom` declaration.

### Narrow checks

These need a prior `lake build` in `lean/`. To inspect `#print axioms` for every main result and proved boundary witness directly (expect each printed list to equal the Axioms column of the corresponding row in [Evidence](#evidence); `isBisim_sameFst_iff`, `iso_without_reachability`, `redundantTag_has_other_hom`, and `behIgnoresHidden_iff_coversHidden_obsEq` print that they do not depend on any axioms):

```bash
cd lean
lake env lean --stdin <<'EOF'
import Toy
#print axioms Toy.Obs.bisim_subset_obsEq
#print axioms Toy.Obs.obsEq_is_greatest_bisim
#print axioms Toy.Obs.hom_to_final_eq_beh
#print axioms Toy.Obs.finalMachine_is_final
#print axioms Toy.Obs.minimalMachine_spec
#print axioms Toy.Obs.reachable_maps_onto_minimalMachine
#print axioms Toy.Obs.reachable_behInjective_iso
#print axioms Toy.Obs.stepwise_nondependence_implies_behIgnoresHidden
#print axioms Toy.Obs.stepwise_nondependence_preserves_beh
#print axioms Toy.Obs.isBisim_sameFst_iff
#print axioms Toy.Obs.redundantTagMachine_erasable_despite_step_dependence
#print axioms Toy.Obs.behIgnoresHidden_iff_stepwise_of_obsInjectiveFst
#print axioms Toy.Obs.no_leak_under_stepwise_nondependence
#print axioms Toy.Obs.delayedChannel2_leaks_at_step_two
#print axioms Toy.Obs.no_machine_independent_horizon_certifies_behIgnoresHidden
#print axioms Toy.Obs.behIgnoresHidden_iff_erasable
#print axioms Toy.Obs.unwinding_bisim_implies_behIgnoresHidden
#print axioms Toy.Obs.behIgnoresHidden_iff_exists_unwinding_bisim
#print axioms Toy.Obs.toMinimalQuotient_injective_iff
#print axioms Toy.Obs.iso_without_reachability
#print axioms Toy.Obs.redundantTag_has_other_hom
#print axioms Toy.Obs.delayedChannel2_erasable_for_each_fixed_h
#print axioms Toy.Obs.gatedLeak_reachable_erasable_but_not_global
#print axioms Toy.Obs.behIgnoresHidden_iff_coversHidden_obsEq
EOF
```

To run a self-contained full-environment axiom audit across every non-internal declaration in the `Toy` library (confirming zero `sorryAx`, zero `axiom`/`opaque` declarations, and only axioms in `{propext, Classical.choice, Quot.sound}`):

```bash
cd lean
lake env lean --stdin <<'EOF'
import Lean
import Toy
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]! && !n.isInternal then
        count := count + 1
        match ci with
        | .axiomInfo _ | .opaqueInfo _ => throwError "forbidden declaration kind: {n}"
        | _ => pure ()
        let axs ← collectAxioms n
        let bad := axs.filter (fun a => !allowed.contains a)
        unless bad.isEmpty do throwError "{n} uses disallowed axioms: {bad.toList}"
  IO.println s!"OK: {count} Toy.* declarations audited; standard axioms only"
EOF
```

Expected output: `OK: 249 Toy.* declarations audited; standard axioms only`.

### After a toolchain change

If `lean/lean-toolchain` is moved past `v4.34.1`, rerun the checks above. The build and axiom checks keep their meaning. Hash mismatches, however, may come from changes to `repr Expr` or to elaboration rather than from a changed statement. In that case, compare the `type_repr` texts printed under both toolchains, and re-read the affected results against the Lean source.
