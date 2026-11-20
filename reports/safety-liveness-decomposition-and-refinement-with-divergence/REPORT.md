# Safety and liveness on infinite traces: decomposition, machine closure, and refinement with explicit divergence (Lean 4)

## Summary

This package is a self-contained, Mathlib-free Lean 4 development of the Alpern–Schneider theory of safety and liveness for linear-time properties of infinite traces (`Nat → α`), of machine closure, and of three refinement notions: inclusion of infinite-trace sets (`StreamRefines`), inclusion of prefix-closed finite-trace sets (`FinRefines`, applied directly or to `finPrefixes`), and inclusion of complete observable behaviors with explicit termination and divergence (`ObsRefines` over `ObsBehavior`). All 13 results are kernel-checked re-derivations of known results (tier T0). One sentence per result:

1. **alpern-schneider-decomposition** (`alpernSchneider_decomposition_of_nonempty`, theorem): Over any nonempty alphabet α, every linear-time infinite-trace property P equals the intersection PropInter (Closure P) (LivenessPart P) of its prefix closure Closure P (a safety property) and its explicit liveness component LivenessPart P (a liveness property).
2. **safety-iff-closure-eq** (`isSafety_iff_closure_eq`, characterization): For any alphabet α (including Empty) and any infinite-trace property P, P is a safety property if and only if P equals its finite-prefix closure Closure P.
3. **safety-and-liveness-iff-univ** (`isSafety_and_isLiveness_iff_eq_univ_of_nonempty`, characterization): Over any nonempty alphabet α, an infinite-trace property P is both a safety property and a liveness property if and only if P equals the universal property UnivProp.
4. **stream-refines-preserves-all** (`streamRefines_preserves_all_properties`, theorem): Baseline reference point: for any alphabet α, stream systems Impl and Spec, and infinite-trace property P, if Impl stream-refines Spec (Impl ⊆ Spec) and Spec satisfies P, then Impl satisfies P.
5. **do-nothing-fin-refines-all** (`doNothingFin_refines_every_prefixClosed_nonempty`, theorem): Over any alphabet α, the do-nothing finite-trace system doNothingFin ({[]}) finite-trace refines every finite-trace system Spec that satisfies the traces-model healthiness conditions IsPrefixClosed Spec and IsNonemptyFin Spec.
6. **fin-refines-no-progress-preservation** (`finRefines_cannot_preserve_property_rejecting_doNothing`, impossibility): If a finite-trace system predicate Φ holds for at least one prefix-closed nonempty specification Spec and rejects doNothingFin ({[]}), then Φ is not preserved by finite-trace refinement across prefix-closed nonempty systems.
7. **fin-trace-refines-preserves-safety** (`finPrefixes_refines_preserves_safety`, theorem): For any stream systems Impl and Spec and any safety property P, if every finite prefix of Impl is a finite prefix of Spec (FinRefines (finPrefixes Impl) (finPrefixes Spec)) and Spec satisfies P, then Impl satisfies P.
8. **fin-trace-refines-fails-nontrivial-liveness** (`finPrefixes_refines_fails_every_nontrivial_liveness`, impossibility): For every nontrivial liveness property P (satisfying IsLiveness P and rejecting some concrete infinite trace s₀), the explicit nonempty stream systems Impl = {s₀} and Spec = P satisfy Satisfies Spec P and FinRefines (finPrefixes Impl) (finPrefixes Spec), yet Impl fails to satisfy P.
9. **obs-refines-separates-do-nothing** (`obsRefines_separates_doNothing_from_finRefines`, theorem): In complete observable-behavior semantics (explicit terminates, diverges, and reacts constructors), every nonempty implementation Impl whose finite prefixes lie in {[]} passes finite-trace refinement against every nonempty specification Spec satisfying EmitsEvent, yet fails complete-behavior refinement ObsRefines Impl Spec.
10. **obs-refines-rejects-new-divergence** (`obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges`, theorem): Whenever some finite trace u is an observable prefix of Spec (obsFinPrefixes Spec u) and Spec forbids silent divergence at u (¬ Spec (.diverges u)), the implementation {ObsBehavior.diverges u} passes finite-trace refinement against Spec on obsFinPrefixes yet fails complete-behavior refinement ObsRefines.
11. **closure-inter-eq-iff-safety-and-machine-closed** (`closure_propInter_eq_iff_isSafety_and_machineClosed`, characterization): For arbitrary infinite-trace properties S and L over any alphabet α, Closure (PropInter S L) = S holds if and only if S is a safety property and the pair (S, L) is machine-closed.
12. **alpern-schneider-machine-closed** (`alpernSchneider_is_machineClosed`, theorem): Supporting reference point: for any alphabet α (including Empty) and any infinite-trace property P, the canonical Alpern–Schneider decomposition pair (Closure P, LivenessPart P) is machine-closed.
13. **non-machine-closed-consistent-spec** (`nonMachineClosed_consistent_spec_counterexample`, counterexample): On Bool, pairing StartsFalseStaysFalse (fun s => s 0 = false → ∀ i, s i = false, a safety property) with EventuallyTrue (fun s => ∃ i, s i = true, a liveness property) yields a satisfiable conjunction explicitly admitting constTrue (fun _ => true), yet the pair is not machine-closed and Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse.

Each result's non-claims, escape hatches, and tightness status are listed under **Boundaries**; read them before relying on a result. In particular: safety and liveness here follow Alpern and Schneider (arbitrary predicates on infinite traces, no stuttering closure); inclusion of finite-prefix sets preserves every safety property, and for every non-safety property some pair of systems shows it is not preserved (`finPrefixes_refines_fails_of_not_isSafety`); every preservation statement is specific to the refinement notion and property class it names.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity: this is a toy model.** The definitions are small, self-contained Lean definitions written for this package
(namespace `Toy.SafetyLiveness`); they do not mirror any production code base.

- **Traces.** An execution is a total infinite sequence `InfTrace α := Nat → α` over an arbitrary observation alphabet `α`.
  A linear-time property is any predicate `TraceProp α := InfTrace α → Prop`, and a system is a set of infinite traces
  (`StreamSystem α`). This is meant to capture the infinite-run semantics of reactive or transition systems as used in the
  Alpern–Schneider theory and in model-checking textbooks. Known gaps: there are no states, transition relations, or
  reachability; finite maximal runs (deadlock or termination) do not exist in this model unless encoded into the alphabet;
  properties are not required to be closed under stuttering (unlike Lamport's and Abadi–Lamport's definitions); there is
  no fairness, no relative liveness, no branching-time or multi-trace (hyperproperty) content, and no change of alphabet,
  hiding, or internal steps between implementation and specification.
- **Finite traces.** A finite-trace system is `FinTraceSystem α := List α → Prop`; `IsPrefixClosed` and `IsNonemptyFin`
  are the healthiness conditions of the traces model of CSP, and `doNothingFin = {[]}` plays the role of `STOP`.
  CSP alphabets, the termination event, refusals, and divergences are not modeled.
- **Complete observable behaviors.** `ObsBehavior α` has three constructors, `terminates u`, `diverges u`, and `reacts s`,
  following the `Terminates / Diverges / Reacts` split of the `program_behavior` type in CompCert's Coq development
  (repository `AbsInt/CompCert`, file `common/Behaviors.v`, pinned under **Evidence**), which also has a fourth
  constructor `Goes_wrong`. The compiler article (Leroy, 2009, §3.4) instead uses three behaviors `converges(t, n)`,
  `diverges(T)`, and `goeswrong(t)`, with a single finite-or-infinite trace `T` for divergence. Known gaps: no exit
  code on termination, no `Goes_wrong` behavior or undefined-behavior wildcard, closed whole programs only (no linking or
  open modules), and no operational semantics or simulation proofs; behaviors are given extensionally.
- **Relationship among the subjects.** The Lean toolchain is the checker of every theorem. The papers and book listed in
  `REPORT.json` are the published sources of the results re-derived here; the cards give locators where available. No
  claim is made that a cited source uses exactly these definitions; differences that matter are recorded as non-claims.
  The two source-repository revisions listed in `REPORT.json` (`AbsInt/CompCert`, and `isabelle-prover/mirror-afp-devel`,
  a mirror of the Isabelle Archive of Formal Proofs) are the exact revisions at which the cited Coq and Isabelle
  declarations were read; they are points of comparison, not dependencies of the Lean development.
- **Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only (no Mathlib and no
  other Lake dependency; the sources import only each other). Axioms used by any declaration are at most `propext`,
  `Classical.choice`, and `Quot.sound` (see **Evidence**). Classical logic is used freely (for example `LivenessPart` uses
  classical negation of `Closure`), so no result gives a decision procedure.
- **Exact observation vs. broader applicability.** Every finding labeled `Basis: execution (Lean kernel check)` is exactly
  the quoted Lean statement under this toolchain. Statements about real systems appear only on separate lines labeled
  `Basis: derived (modeling bridge)`, with the reasoning and the gaps that limit them.

## Findings

### Core definitions (quoted verbatim from the Lean sources)

`Toy/SafetyLiveness/Core.lean`:

```lean
abbrev InfTrace (α : Type u) : Type u := Nat → α

abbrev TraceProp (α : Type u) : Type u := InfTrace α → Prop

def takePrefix {α : Type u} (s : InfTrace α) (n : Nat) : List α :=
  List.ofFn (fun i : Fin n => s i.val)

def HasPrefix {α : Type u} (s : InfTrace α) (u : List α) : Prop :=
  ∀ (i : Nat) (h : i < u.length), s i = u[i]

def appendPrefix {α : Type u} (u : List α) (t : InfTrace α) : InfTrace α :=
  fun i => if h : i < u.length then u[i] else t (i - u.length)

def PropInter {α : Type u} (P Q : TraceProp α) : TraceProp α :=
  fun s => P s ∧ Q s

def UnivProp {α : Type u} : TraceProp α :=
  fun _ => True

def EmptyProp {α : Type u} : TraceProp α :=
  fun _ => False

def IsSafety {α : Type u} (P : TraceProp α) : Prop :=
  ∀ s : InfTrace α, ¬ P s →
    ∃ n : Nat, ∀ s' : InfTrace α, HasPrefix s' (takePrefix s n) → ¬ P s'

def IsLiveness {α : Type u} (P : TraceProp α) : Prop :=
  ∀ u : List α, ∃ s : InfTrace α, HasPrefix s u ∧ P s

def Closure {α : Type u} (P : TraceProp α) : TraceProp α :=
  fun s => ∀ n : Nat, ∃ s' : InfTrace α, HasPrefix s' (takePrefix s n) ∧ P s'

def LivenessPart {α : Type u} (P : TraceProp α) : TraceProp α :=
  fun s => P s ∨ ¬ Closure P s

abbrev StreamSystem (α : Type u) : Type u := InfTrace α → Prop

def Satisfies {α : Type u} (S : StreamSystem α) (P : TraceProp α) : Prop :=
  ∀ s : InfTrace α, S s → P s

def StreamRefines {α : Type u} (Impl Spec : StreamSystem α) : Prop :=
  ∀ s : InfTrace α, Impl s → Spec s

def IsNonemptyStream {α : Type u} (S : StreamSystem α) : Prop :=
  ∃ s : InfTrace α, S s

def constFalse : InfTrace Bool := fun _ => false

def constTrue : InfTrace Bool := fun _ => true

def AlwaysFalse : TraceProp Bool := fun s => ∀ i : Nat, s i = false

def EventuallyTrue : TraceProp Bool := fun s => ∃ i : Nat, s i = true

def EventuallyFalse : TraceProp Bool := fun s => ∃ i : Nat, s i = false

def StartsTrue : TraceProp Bool := fun s => s 0 = true

def StartsTrueAndEventuallyFalse : TraceProp Bool :=
  fun s => s 0 = true ∧ ∃ i : Nat, s i = false

def StartsFalseStaysFalse : TraceProp Bool :=
  fun s => s 0 = false → ∀ i : Nat, s i = false
```

`Toy/SafetyLiveness/Decomposition.lean` (a witness used by `alpernSchneider_nonunique_components`):

```lean
def AlwaysFalseOrTwoTrues : TraceProp Bool :=
  fun s => AlwaysFalse s ∨ ∃ i : Nat, s i = true ∧ s (i + 1) = true
```

`Toy/SafetyLiveness/Refinement.lean`:

```lean
def IsPrefix {α : Type u} (u v : List α) : Prop :=
  ∃ w : List α, u ++ w = v

abbrev FinTraceSystem (α : Type u) : Type u := List α → Prop

def IsPrefixClosed {α : Type u} (T : FinTraceSystem α) : Prop :=
  ∀ u v : List α, IsPrefix u v → T v → T u

def IsNonemptyFin {α : Type u} (T : FinTraceSystem α) : Prop :=
  ∃ u : List α, T u

def FinRefines {α : Type u} (TImpl TSpec : FinTraceSystem α) : Prop :=
  ∀ u : List α, TImpl u → TSpec u

def doNothingFin {α : Type u} : FinTraceSystem α :=
  fun u => u = []

def finPrefixes {α : Type u} (S : StreamSystem α) : FinTraceSystem α :=
  fun u => ∃ s : InfTrace α, S s ∧ HasPrefix s u

def FinRefinesPreserves {α : Type u} (Φ : FinTraceSystem α → Prop) : Prop :=
  ∀ T₁ T₂ : FinTraceSystem α,
    IsPrefixClosed T₁ → IsNonemptyFin T₁ →
    IsPrefixClosed T₂ → IsNonemptyFin T₂ →
    FinRefines T₁ T₂ → Φ T₂ → Φ T₁

def emitTrueFin : FinTraceSystem Bool :=
  fun u => u = [] ∨ u = [true]

def FinHasNonemptyTrace : FinTraceSystem Bool → Prop :=
  fun T => ∃ u : List Bool, T u ∧ u ≠ []
```

`Toy/SafetyLiveness/Divergence.lean`:

```lean
inductive ObsBehavior (α : Type u) : Type u where
  | terminates (trace : List α) : ObsBehavior α
  | diverges (trace : List α) : ObsBehavior α
  | reacts (stream : InfTrace α) : ObsBehavior α

abbrev ObsProp (α : Type u) : Type u := ObsBehavior α → Prop

abbrev ObsSystem (α : Type u) : Type u := ObsBehavior α → Prop

def ObsSatisfies {α : Type u} (S : ObsSystem α) (Q : ObsProp α) : Prop :=
  ∀ b : ObsBehavior α, S b → Q b

def ObsRefines {α : Type u} (Impl Spec : ObsSystem α) : Prop :=
  ∀ b : ObsBehavior α, Impl b → Spec b

def IsNonemptyObs {α : Type u} (S : ObsSystem α) : Prop :=
  ∃ b : ObsBehavior α, S b

def ObsRefinesPreserves {α : Type u} (Φ : ObsSystem α → Prop) : Prop :=
  ∀ T₁ T₂ : ObsSystem α,
    IsNonemptyObs T₁ → IsNonemptyObs T₂ →
    ObsRefines T₁ T₂ → Φ T₂ → Φ T₁

def behaviorPrefixes {α : Type u} : ObsBehavior α → FinTraceSystem α
  | .terminates u => fun v => IsPrefix v u
  | .diverges u   => fun v => IsPrefix v u
  | .reacts s     => fun v => HasPrefix s v

def obsFinPrefixes {α : Type u} (S : ObsSystem α) : FinTraceSystem α :=
  fun v => ∃ b : ObsBehavior α, S b ∧ behaviorPrefixes b v

def EmitsEvent {α : Type u} : ObsProp α
  | .terminates u => u ≠ []
  | .diverges u   => u ≠ []
  | .reacts _     => True

def ObsCanEmit {α : Type u} (S : ObsSystem α) : Prop :=
  ∃ b : ObsBehavior α, S b ∧ EmitsEvent b

def NoDivergence {α : Type u} : ObsProp α
  | .terminates _ => True
  | .diverges _   => False
  | .reacts _     => True

def silentDivergeObs {α : Type u} : ObsSystem α :=
  fun b => b = .diverges []

def immediateHaltObs {α : Type u} : ObsSystem α :=
  fun b => b = .terminates []

def embedStreams {α : Type u} (S : StreamSystem α) : ObsSystem α
  | .reacts s => S s
  | _         => False

def emitTrueObs : ObsSystem Bool :=
  fun b => b = .terminates [true]

def divergeAfterTrueObs : ObsSystem Bool :=
  fun b => b = .diverges [true]
```

`Toy/SafetyLiveness/MachineClosure.lean`:

```lean
def MachineClosed {α : Type u} (S L : TraceProp α) : Prop :=
  ∀ u : List α, (∃ s : InfTrace α, HasPrefix s u ∧ S s) →
    ∃ s' : InfTrace α, HasPrefix s' u ∧ S s' ∧ L s'

def EventuallyAlwaysTrue : TraceProp Bool :=
  fun s => ∃ k : Nat, ∀ i : Nat, k ≤ i → s i = true

def EventuallyAlwaysFalse : TraceProp Bool :=
  fun s => ∃ k : Nat, ∀ i : Nat, k ≤ i → s i = false
```

`EventuallyAlwaysTrue` and `EventuallyAlwaysFalse` ("from some index on, always `true`" / "always `false`", i.e. `∃ k, ∀ i ≥ k`, not "infinitely often") are the witnesses of `machineClosed_not_closed_under_propInter`: each is live, but no trace satisfies both (from index `max k₁ k₂` on it would have to be both `true` and `false`), so their conjunction is empty and `(UnivProp, PropInter EventuallyAlwaysTrue EventuallyAlwaysFalse)` is not machine-closed.

Most core definitions are accompanied in the same files by proved positive and negative examples (theorems whose names contain `_pos_` or `_neg_`). For `IsSafety`, `IsLiveness`, and `MachineClosed`, the files also prove the following named instances. They illustrate the definitions and are not card results; `startsTrue_eventuallyFalse_machineClosed` is also a companion of `non-machine-closed-consistent-spec` and is hashed in `audit/statements.json`, while the other five are not listed there (the axioms of all six are recorded in `audit/axioms.json`, which covers every library declaration).

```lean
theorem Toy.SafetyLiveness.alwaysFalse_isSafety : IsSafety AlwaysFalse

theorem Toy.SafetyLiveness.eventuallyTrue_not_isSafety : ¬ IsSafety EventuallyTrue

theorem Toy.SafetyLiveness.eventuallyTrue_isLiveness : IsLiveness EventuallyTrue

theorem Toy.SafetyLiveness.alwaysFalse_not_isLiveness : ¬ IsLiveness AlwaysFalse

theorem Toy.SafetyLiveness.startsTrue_eventuallyFalse_machineClosed :
    MachineClosed StartsTrue EventuallyFalse

theorem Toy.SafetyLiveness.alwaysFalse_eventuallyTrue_not_machineClosed :
    IsSafety AlwaysFalse ∧
      IsLiveness EventuallyTrue ∧
      ¬ MachineClosed AlwaysFalse EventuallyTrue
```

Card fields used below: *hypothesis ledger* (each hypothesis, why it is needed, tightness, and the counterexample theorem, which states that all other hypotheses hold and the conclusion fails); *non-vacuity witness* (a concrete instance where all hypotheses hold); *positive control* (for impossibility results, a nearby setting where the conclusion fails); *companion declarations* (proved lemmas cited by the card's ledger or non-claims; their statements are hashed in `audit/statements.json`).

### 1. `alpern-schneider-decomposition`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.alpernSchneider_decomposition_of_nonempty` in `Toy/SafetyLiveness/Decomposition.lean`.
- **Plain claim:** Over any nonempty alphabet α, every linear-time infinite-trace property P equals the intersection PropInter (Closure P) (LivenessPart P) of its prefix closure Closure P (a safety property) and its explicit liveness component LivenessPart P (a liveness property).

Lean statement:

```lean
theorem Toy.SafetyLiveness.alpernSchneider_decomposition_of_nonempty
    {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    IsSafety (Closure P) ∧ IsLiveness (LivenessPart P) ∧
      PropInter (Closure P) (LivenessPart P) = P
```

With the key definitions unfolded:

```lean
-- IsSafety (Closure P):
∀ s, ¬ Closure P s → ∃ n, ∀ s', HasPrefix s' (takePrefix s n) → ¬ Closure P s'
-- IsLiveness (LivenessPart P):
∀ u : List α, ∃ s, HasPrefix s u ∧ (P s ∨ ¬ Closure P s)
-- PropInter (Closure P) (LivenessPart P) = P   (equality of predicates on Nat → α):
(fun s => Closure P s ∧ (P s ∨ ¬ Closure P s)) = P
-- where Closure P s := ∀ n, ∃ s', HasPrefix s' (takePrefix s n) ∧ P s'
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hα : Nonempty α` | Ensures every finite prefix u : List α (in particular the empty prefix []) can be padded into an infinite trace when proving IsLiveness (LivenessPart P) (proved separately as Toy.SafetyLiveness.isLiveness_livenessPart_of_nonempty); the other two conjuncts IsSafety (Closure P) and PropInter (Closure P) (LivenessPart P) = P hold unconditionally over every alphabet α via Toy.SafetyLiveness.closure_isSafety and Toy.SafetyLiveness.propInter_closure_livenessPart_eq. | tight: counterexample `emptyAlphabet_tight_alpernSchneider` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.emptyAlphabet_tight_alpernSchneider :
    ¬ (IsSafety (Closure (EmptyProp : TraceProp Empty)) ∧
       IsLiveness (LivenessPart (EmptyProp : TraceProp Empty)) ∧
       PropInter (Closure (EmptyProp : TraceProp Empty))
         (LivenessPart (EmptyProp : TraceProp Empty)) = EmptyProp)
```

**Non-vacuity witness:** On the nonempty alphabet Bool, StartsTrueAndEventuallyFalse is a nontrivial property that is neither a safety property nor a liveness property. (`alpernSchneider_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.alpernSchneider_nonvacuity :
    Nonempty Bool ∧
      ¬ IsSafety StartsTrueAndEventuallyFalse ∧
      ¬ IsLiveness StartsTrueAndEventuallyFalse
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.alpernSchneider_nonunique_components :
    (IsSafety AlwaysFalse ∧ IsLiveness (UnivProp : TraceProp Bool) ∧ IsLiveness AlwaysFalseOrTwoTrues ∧
      PropInter AlwaysFalse UnivProp = AlwaysFalse ∧
      PropInter AlwaysFalse AlwaysFalseOrTwoTrues = AlwaysFalse ∧
      (UnivProp : TraceProp Bool) ≠ AlwaysFalseOrTwoTrues) ∧
    (IsSafety StartsTrue ∧ IsSafety StartsFalseStaysFalse ∧ IsLiveness EventuallyTrue ∧
      PropInter StartsTrue UnivProp = StartsTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue ∧
      StartsFalseStaysFalse ≠ StartsTrue)

theorem Toy.SafetyLiveness.closure_isSafety {α : Type u} (P : TraceProp α) : IsSafety (Closure P)

theorem Toy.SafetyLiveness.emptyAlphabet_no_liveness (L : TraceProp Empty) : ¬ IsLiveness L

theorem Toy.SafetyLiveness.isLiveness_livenessPart_of_nonempty {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    IsLiveness (LivenessPart P)

theorem Toy.SafetyLiveness.machineClosed_not_closed_under_propInter :
    IsLiveness EventuallyAlwaysTrue ∧
      IsLiveness EventuallyAlwaysFalse ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysTrue ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysFalse ∧
      ¬ MachineClosed (UnivProp : TraceProp Bool)
          (PropInter EventuallyAlwaysTrue EventuallyAlwaysFalse)

theorem Toy.SafetyLiveness.propInter_closure_livenessPart_eq {α : Type u} (P : TraceProp α) :
    PropInter (Closure P) (LivenessPart P) = P

theorem Toy.SafetyLiveness.stepDiffers_isSafety : IsSafety (fun s : InfTrace Bool => s 0 ≠ s 1)
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0 (Theorem 1).
- Bowen Alpern and Fred B. Schneider, 'Recognizing safety and liveness', Distributed Computing 2(3):117-126, 1987, DOI: 10.1007/BF01782772 (automata-theoretic decomposition of ω-regular properties).
- Leslie Lamport, 'Proving the Correctness of Multiprocess Programs', IEEE Transactions on Software Engineering SE-3(2):125-143, March 1977, DOI: 10.1109/TSE.1977.229904 (informal origin of the terms safety and liveness).
- Mack W. Alford, Leslie Lamport, and Geoff P. Mullery, 'Basic Concepts', in Distributed Systems: Methods and Tools for Specification, LNCS 190, pp. 7-43, Springer, 1985, DOI: 10.1007/3-540-15216-4_12 (the formal definition of safety that Alpern and Schneider, 1985, cite as 'L. Lamport, Basic concepts'; Alpern, Demers, and Schneider, 1986, give a formalization that also covers properties not invariant under stuttering).
- Bowen Alpern, Alan J. Demers, and Fred B. Schneider, 'Safety without stuttering', Information Processing Letters 23(4):177-180, 1986, DOI: 10.1016/0020-0190(86)90132-8.
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.4.2 'Safety vs. Liveness Properties': Theorem 3.37 Decomposition Theorem and Lemma 3.38 Sharpest Decomposition).
- Panagiotis Manolios and Richard Trefler, 'A Lattice-Theoretic Characterization of Safety and Liveness', PODC 2003, pp. 325-333, ACM, 2003, DOI: 10.1145/872035.872083.
- Ekkart Kindler, 'Safety and Liveness Properties: A Survey', Bulletin of the EATCS 53:268-272, June 1994.
- Stefan Friedrich, 'Topology' (theory LList_Topology: itrace_top.alpern_schneider with A ≠ {} and infliveness_empty) and 'Lazy Lists II' (theory LList2: infsafety, infliveness), Archive of Formal Proofs, April 26, 2004, https://isa-afp.org/entries/Topology.html and https://isa-afp.org/entries/Lazy-Lists-II.html.
- Peter Gammie, 'ConcurrentHOL' (theory Safety_Closure: tls.Safe, tls.Live, tls.decomp), Archive of Formal Proofs, April 16, 2024, https://isa-afp.org/entries/ConcurrentHOL.html.

**Design question:** Separates any target infinite-trace specification into its canonical safety hull Closure P (which survives finite-prefix refinement) and its residual liveness obligation LivenessPart P (which requires stronger refinement semantics).

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). A specification that is faithfully modeled as a set of total infinite observation sequences over a nonempty alphabet can be split into a part decided by finite prefixes (Closure P) and a part no finite prefix can refute (LivenessPart P). Reasoning: the theorem is stated for an arbitrary predicate P on Nat → α, so it applies to any such model; it does not apply to specifications whose meaning depends on finite maximal runs, stuttering closure, branching structure, or sets of traces.

### 2. `safety-iff-closure-eq`

- **Tier:** T0 (re-derivation of a known result). **Kind:** characterization. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.isSafety_iff_closure_eq` in `Toy/SafetyLiveness/Decomposition.lean`.
- **Plain claim:** For any alphabet α (including Empty) and any infinite-trace property P, P is a safety property if and only if P equals its finite-prefix closure Closure P.

Lean statement:

```lean
theorem Toy.SafetyLiveness.isSafety_iff_closure_eq
    {α : Type u} (P : TraceProp α) :
    IsSafety P ↔ Closure P = P
```

With the key definitions unfolded:

```lean
(∀ s, ¬ P s → ∃ n, ∀ s', HasPrefix s' (takePrefix s n) → ¬ P s')
  ↔ (fun s => ∀ n, ∃ s', HasPrefix s' (takePrefix s n) ∧ P s') = P
```

**Hypothesis ledger:** the statement has no hypotheses beyond its universally quantified parameters.

**Non-vacuity witness:** On Bool, AlwaysFalse is a safety property (both sides hold) and EventuallyTrue is not a safety property (both sides fail). (`isSafety_iff_closure_eq_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.isSafety_iff_closure_eq_nonvacuity :
    IsSafety AlwaysFalse ∧ ¬ IsSafety EventuallyTrue
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.closure_minimal_of_isSafety {α : Type u} {P S : TraceProp α}
    (hSafe : IsSafety S) (hSub : ∀ s : InfTrace α, P s → S s) :
    ∀ s : InfTrace α, Closure P s → S s

theorem Toy.SafetyLiveness.emptyAlphabet_tight_isLiveness_iff_closure_eq_univ :
    Closure (EmptyProp : TraceProp Empty) = UnivProp ∧
      ¬ IsLiveness (EmptyProp : TraceProp Empty) ∧
      ¬ (IsLiveness (EmptyProp : TraceProp Empty) ↔
          Closure (EmptyProp : TraceProp Empty) = UnivProp)

theorem Toy.SafetyLiveness.isLiveness_iff_closure_eq_univ_of_nonempty {α : Type u} (hα : Nonempty α)
    (P : TraceProp α) :
    IsLiveness P ↔ Closure P = UnivProp

theorem Toy.SafetyLiveness.stepDiffers_isSafety : IsSafety (fun s : InfTrace Bool => s 0 ≠ s 1)
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0 (§4 topological characterization).
- Bowen Alpern, Alan J. Demers, and Fred B. Schneider, 'Safety without stuttering', Information Processing Letters 23(4):177-180, 1986, DOI: 10.1016/0020-0190(86)90132-8.
- Martín Abadi and Leslie Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2):253-284, 1991, DOI: 10.1016/0304-3975(91)90224-P (Section 2.2).
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.3.2 'Safety Properties': Definition 3.26 Prefix and Closure, and Lemma 3.27 Alternative Characterization of Safety Properties, P is a safety property iff closure(P) = P).
- Stefan Friedrich, 'Topology' (theory LList_Topology: infsafety_closed_iff) and 'Lazy Lists II' (theory LList2), Archive of Formal Proofs, April 26, 2004, https://isa-afp.org/entries/Topology.html and https://isa-afp.org/entries/Lazy-Lists-II.html.
- Peter Gammie, 'ConcurrentHOL' (theory Safety_Closure), Archive of Formal Proofs, April 16, 2024, https://isa-afp.org/entries/ConcurrentHOL.html.

**Design question:** Explains why safety properties are completely determined by their finite prefixes (Closure P = P) and therefore survive finite-prefix refinement without divergence or fairness obligations.

Basis: execution (Lean kernel check)

No claim about real systems is made for this result beyond the mathematical statement.

### 3. `safety-and-liveness-iff-univ`

- **Tier:** T0 (re-derivation of a known result). **Kind:** characterization. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.isSafety_and_isLiveness_iff_eq_univ_of_nonempty` in `Toy/SafetyLiveness/Decomposition.lean`.
- **Plain claim:** Over any nonempty alphabet α, an infinite-trace property P is both a safety property and a liveness property if and only if P equals the universal property UnivProp.

Lean statement:

```lean
theorem Toy.SafetyLiveness.isSafety_and_isLiveness_iff_eq_univ_of_nonempty
    {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    (IsSafety P ∧ IsLiveness P) ↔ P = UnivProp
```

With the key definitions unfolded:

```lean
((∀ s, ¬ P s → ∃ n, ∀ s', HasPrefix s' (takePrefix s n) → ¬ P s') ∧
 (∀ u : List α, ∃ s, HasPrefix s u ∧ P s))
  ↔ P = (fun _ => True)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hα : Nonempty α` | Required for the reverse direction (IsLiveness UnivProp) so that the empty prefix [] extends to an infinite trace; the forward implication IsSafety P → IsLiveness P → P = UnivProp holds over every alphabet α without Nonempty α (proved in Toy.SafetyLiveness.eq_univ_of_isSafety_of_isLiveness). | tight: counterexample `emptyAlphabet_tight_safety_liveness_iff_univ` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.emptyAlphabet_tight_safety_liveness_iff_univ :
    ¬ ((IsSafety (UnivProp : TraceProp Empty) ∧ IsLiveness (UnivProp : TraceProp Empty)) ↔
       (UnivProp : TraceProp Empty) = UnivProp)
```

**Non-vacuity witness:** On Bool (nonempty), UnivProp satisfies both sides of the equivalence and AlwaysFalse falsifies both sides. (`isSafety_and_isLiveness_iff_eq_univ_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.isSafety_and_isLiveness_iff_eq_univ_nonvacuity :
    Nonempty Bool ∧
      (IsSafety (UnivProp : TraceProp Bool) ∧ IsLiveness (UnivProp : TraceProp Bool)) ∧
      (¬ IsLiveness AlwaysFalse ∧ AlwaysFalse ≠ UnivProp)
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.alpernSchneider_nonvacuity :
    Nonempty Bool ∧
      ¬ IsSafety StartsTrueAndEventuallyFalse ∧
      ¬ IsLiveness StartsTrueAndEventuallyFalse

theorem Toy.SafetyLiveness.alwaysFalse_safety_entails_nontrivial_liveness_eventuallyFalse :
    IsSafety AlwaysFalse ∧ IsLiveness EventuallyFalse ∧ EventuallyFalse ≠ UnivProp ∧
      (∀ s : InfTrace Bool, AlwaysFalse s → EventuallyFalse s) ∧
      Satisfies (fun s => s = constFalse) AlwaysFalse ∧
      Satisfies (fun s => s = constFalse) EventuallyFalse

theorem Toy.SafetyLiveness.alwaysFalse_tight_liveness_of_unique :
    IsSafety AlwaysFalse ∧ AlwaysFalse ≠ UnivProp

theorem Toy.SafetyLiveness.eq_univ_of_isSafety_of_isLiveness
    {α : Type u} {P : TraceProp α}
    (hSafe : IsSafety P) (hLive : IsLiveness P) :
    P = UnivProp

theorem Toy.SafetyLiveness.eventuallyTrue_tight_safety_of_unique :
    IsLiveness EventuallyTrue ∧ EventuallyTrue ≠ UnivProp

theorem Toy.SafetyLiveness.propInter_startsTrue_eventuallyFalse_neither_safety_nor_liveness :
    IsSafety StartsTrue ∧ IsLiveness EventuallyFalse ∧
      ¬ IsSafety (PropInter StartsTrue EventuallyFalse) ∧
      ¬ IsLiveness (PropInter StartsTrue EventuallyFalse)
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0 (p. 184).
- Nancy A. Lynch, Distributed Algorithms, Morgan Kaufmann, 1996, ISBN 1-55860-348-4 (Section 8.5.3, Theorem 8.8).
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.4.2 'Safety vs. Liveness Properties': Lemma 3.35 Intersection of Safety and Liveness Properties).
- Peter Gammie, 'ConcurrentHOL' (theory Safety_Closure: tls.live.inf_safety_eq_top), Archive of Formal Proofs, April 16, 2024, https://isa-afp.org/entries/ConcurrentHOL.html.

**Design question:** Shows that no nontrivial liveness property is itself a safety property (the two classes meet only in UnivProp), so a nontrivial liveness requirement can never be restated as an equivalent safety requirement and has no finite bad prefix.

Basis: execution (Lean kernel check)

No claim about real systems is made for this result beyond the mathematical statement.

### 4. `stream-refines-preserves-all`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** definitional.
- **Lean:** `Toy.SafetyLiveness.streamRefines_preserves_all_properties` in `Toy/SafetyLiveness/Refinement.lean`.
- **Plain claim:** Baseline reference point: for any alphabet α, stream systems Impl and Spec, and infinite-trace property P, if Impl stream-refines Spec (Impl ⊆ Spec) and Spec satisfies P, then Impl satisfies P.

Lean statement:

```lean
theorem Toy.SafetyLiveness.streamRefines_preserves_all_properties
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hRef : StreamRefines Impl Spec) (hSpec : Satisfies Spec P) :
    Satisfies Impl P
```

With the key definitions unfolded:

```lean
(∀ s, Impl s → Spec s) → (∀ s, Spec s → P s) → ∀ s, Impl s → P s
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hRef : StreamRefines Impl Spec` | Provides inclusion Impl ⊆ Spec on infinite traces. | tight: counterexample `streamRefines_preserves_tight_refines` |
| `hSpec : Satisfies Spec P` | Establishes that every infinite trace of Spec lies in P. | tight: counterexample `streamRefines_preserves_tight_satisfies` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.streamRefines_preserves_tight_refines :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := EventuallyTrue
    Satisfies Spec EventuallyTrue ∧ ¬ Satisfies Impl EventuallyTrue

theorem Toy.SafetyLiveness.streamRefines_preserves_tight_satisfies :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := fun s => s = constFalse
    StreamRefines Impl Spec ∧ ¬ Satisfies Impl EventuallyTrue
```

**Non-vacuity witness:** On Bool, {constTrue} stream-refines EventuallyTrue and EventuallyTrue satisfies EventuallyTrue. (`streamRefines_preserves_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.streamRefines_preserves_nonvacuity :
    StreamRefines (fun s : InfTrace Bool => s = constTrue) EventuallyTrue ∧
      Satisfies EventuallyTrue EventuallyTrue
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.emptyStreamSystem_refines_all {α : Type u} (Spec : StreamSystem α) :
    StreamRefines EmptyProp Spec

theorem Toy.SafetyLiveness.no_nonempty_streamSystem_refines_all_nonempty :
    ¬ ∃ Impl : StreamSystem Bool, IsNonemptyStream Impl ∧
        ∀ Spec : StreamSystem Bool, IsNonemptyStream Spec → StreamRefines Impl Spec

theorem Toy.SafetyLiveness.streamRefines_fails_possibility :
    IsNonemptyStream (fun s : InfTrace Bool => s = constFalse) ∧
      IsNonemptyStream (UnivProp : StreamSystem Bool) ∧
      StreamRefines (fun s : InfTrace Bool => s = constFalse) UnivProp ∧
      (∃ s : InfTrace Bool, (UnivProp : StreamSystem Bool) s ∧ s 0 = true) ∧
      ¬ (∃ s : InfTrace Bool, s = constFalse ∧ s 0 = true)

theorem Toy.SafetyLiveness.unit_streamSystem_refines_all_nonempty (Impl Spec : StreamSystem Unit)
    (hSpec : IsNonemptyStream Spec) : StreamRefines Impl Spec
```

**Prior art:**

- Martín Abadi and Leslie Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2):253-284, 1991, DOI: 10.1016/0304-3975(91)90224-P (Section 2).
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.2.4 'Trace Equivalence and Linear-Time Properties': Theorem 3.15 Trace Inclusion and LT Properties, for transition systems without terminal states).

**Design question:** Baseline reference point contrasting with finite-trace inclusion: stream inclusion preserves every universal linear-time property by definition, and among nonempty systems over alphabets with at least two observations (such as Bool), stream inclusion admits no universal do-nothing refiner (Toy.SafetyLiveness.no_nonempty_streamSystem_refines_all_nonempty).

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). For systems whose semantics is a set of infinite runs over one shared alphabet, inclusion of run sets transfers every single-run (linear-time) property. Reasoning: the theorem is transitivity of inclusion for arbitrary predicates; it does not apply to properties of sets of runs or to systems with terminating runs that are not encoded as infinite runs.

### 5. `do-nothing-fin-refines-all`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.doNothingFin_refines_every_prefixClosed_nonempty` in `Toy/SafetyLiveness/Refinement.lean`.
- **Plain claim:** Over any alphabet α, the do-nothing finite-trace system doNothingFin ({[]}) finite-trace refines every finite-trace system Spec that satisfies the traces-model healthiness conditions IsPrefixClosed Spec and IsNonemptyFin Spec.

Lean statement:

```lean
theorem Toy.SafetyLiveness.doNothingFin_refines_every_prefixClosed_nonempty
    {α : Type u} {Spec : FinTraceSystem α}
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec) :
    FinRefines doNothingFin Spec
```

With the key definitions unfolded:

```lean
(∀ u v : List α, (∃ w, u ++ w = v) → Spec v → Spec u) →   -- IsPrefixClosed Spec
(∃ u, Spec u) →                                           -- IsNonemptyFin Spec
∀ u : List α, u = [] → Spec u                             -- FinRefines doNothingFin Spec
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hClosed : IsPrefixClosed Spec` | Traces-model healthiness condition ensuring any trace in Spec yields [] ∈ Spec; individually tight relative to IsNonemptyFin Spec, while the pair (hClosed, hNonempty) is jointly replaceable by the exact condition Spec [] (Toy.SafetyLiveness.doNothingFin_finRefines_iff_nil_mem, Toy.SafetyLiveness.doNothingFin_finRefines_without_prefixClosed). | tight: counterexample `singletonTrueTrace_tight_prefixClosed` |
| `hNonempty : IsNonemptyFin Spec` | Traces-model healthiness condition ruling out the vacuously prefix-closed empty set ∅, which omits []; individually tight relative to IsPrefixClosed Spec (and jointly replaceable with hClosed by Spec []). | tight: counterexample `emptyFinSystem_tight_nonempty` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.singletonTrueTrace_tight_prefixClosed :
    IsNonemptyFin (fun u : List Bool => u = [true]) ∧
      ¬ FinRefines doNothingFin (fun u : List Bool => u = [true])

theorem Toy.SafetyLiveness.emptyFinSystem_tight_nonempty :
    IsPrefixClosed (fun _ : List Bool => False) ∧
      ¬ FinRefines doNothingFin (fun _ : List Bool => False)
```

**Non-vacuity witness:** On Bool, emitTrueFin ({[], [true]}) is both prefix-closed and nonempty. (`doNothingFin_refines_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.doNothingFin_refines_nonvacuity :
    IsPrefixClosed emitTrueFin ∧ IsNonemptyFin emitTrueFin
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.doNothingFin_finRefines_iff_nil_mem {α : Type u} (Spec : FinTraceSystem α) :
    FinRefines doNothingFin Spec ↔ Spec []

theorem Toy.SafetyLiveness.doNothingFin_finRefines_without_prefixClosed :
    let Spec : FinTraceSystem Bool := fun v => v = [] ∨ v = [true, false]
    ¬ IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ FinRefines doNothingFin Spec

theorem Toy.SafetyLiveness.finPrefixes_refines_preserves_safety
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hSafe : IsSafety P)
    (hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec))
    (hSpec : Satisfies Spec P) :
    Satisfies Impl P

theorem Toy.SafetyLiveness.finRefinesPreserves_linearTime {α : Type u} (Q : List α → Prop) :
    FinRefinesPreserves (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v)

theorem Toy.SafetyLiveness.obsRefines_separates_doNothing_from_finRefines
    {α : Type u} {Impl Spec : ObsSystem α}
    (hImplNE : IsNonemptyObs Impl)
    (hSpecNE : IsNonemptyObs Spec)
    (hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin)
    (hProgress : ObsSatisfies Spec EmitsEvent) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec) ∧ ¬ ObsRefines Impl Spec
```

**Prior art:**

- C. A. R. Hoare, Communicating Sequential Processes, Prentice Hall, 1985, ISBN 0-13-153271-5 (traces model where traces(STOP) = {⟨⟩}).
- Stephen D. Brookes, C. A. R. Hoare, and A. W. Roscoe, 'A Theory of Communicating Sequential Processes', Journal of the ACM 31(3):560-599, 1984, DOI: 10.1145/828.833.
- A. W. Roscoe, The Theory and Practice of Concurrency, Prentice Hall, 1997, ISBN 0-13-674409-5 (Chapters 1-2, STOP trace-refines every process).
- Benoît Ballenghien, Safouan Taha, Burkhart Wolff, and Lina Ye, 'HOL-CSP Version 2.0' (theory CSP_Refinements: leT_STOP and leDT_STOP), Archive of Formal Proofs, April 26, 2019, https://isa-afp.org/entries/HOL-CSP.html.

**Design question:** Identifies the exact mechanism by which prefix-closed finite-trace refinement silently admits a do-nothing implementation: every healthy specification contains [], so {[]} is a valid refinement of every healthy specification.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). In the traces model of CSP, a process denotes a nonempty prefix-closed set of finite traces and STOP denotes {⟨⟩}; the theorem re-derives that STOP trace-refines every process. Reasoning: IsPrefixClosed and IsNonemptyFin are exactly the traces-model healthiness conditions and doNothingFin is the trace set of STOP. Event alphabets, the termination event, refusals, and divergences are not modeled.

### 6. `fin-refines-no-progress-preservation`

- **Tier:** T0 (re-derivation of a known result). **Kind:** impossibility. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.finRefines_cannot_preserve_property_rejecting_doNothing` in `Toy/SafetyLiveness/Refinement.lean`.
- **Plain claim:** If a finite-trace system predicate Φ holds for at least one prefix-closed nonempty specification Spec and rejects doNothingFin ({[]}), then Φ is not preserved by finite-trace refinement across prefix-closed nonempty systems.

Lean statement:

```lean
theorem Toy.SafetyLiveness.finRefines_cannot_preserve_property_rejecting_doNothing
    {α : Type u} {Spec : FinTraceSystem α} {Φ : FinTraceSystem α → Prop}
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec)
    (hSpec : Φ Spec) (hReject : ¬ Φ doNothingFin) :
    ¬ FinRefinesPreserves Φ
```

With the key definitions unfolded:

```lean
-- for an arbitrary predicate Φ on finite-trace systems (List α → Prop):
IsPrefixClosed Spec → IsNonemptyFin Spec → Φ Spec → ¬ Φ (fun u => u = []) →
¬ (∀ T₁ T₂ : List α → Prop,
     IsPrefixClosed T₁ → IsNonemptyFin T₁ → IsPrefixClosed T₂ → IsNonemptyFin T₂ →
     (∀ u, T₁ u → T₂ u) → Φ T₂ → Φ T₁)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hClosed : IsPrefixClosed Spec` | Places Spec in the prefix-closed domain of FinRefinesPreserves and ensures [] ∈ Spec. | tight: counterexample `finRefines_impossibility_tight_prefixClosed` |
| `hNonempty : IsNonemptyFin Spec` | Places Spec in the nonempty domain of FinRefinesPreserves and ensures [] ∈ Spec. | tight: counterexample `finRefines_impossibility_tight_nonempty` |
| `hSpec : Φ Spec` | Ensures Φ holds on at least one healthy specification (ruling out the vacuously preserved false predicate). | tight: counterexample `finRefines_impossibility_tight_spec` |
| `hReject : ¬ Φ doNothingFin` | States that Φ rejects the do-nothing system {[]}. | tight: counterexample `finRefines_impossibility_tight_reject` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.finRefines_impossibility_tight_prefixClosed :
    let Spec : FinTraceSystem Bool := fun u => u = [true]
    let Φ : FinTraceSystem Bool → Prop := fun T => ∀ u, T u → u ≠ []
    IsNonemptyFin Spec ∧ Φ Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ

theorem Toy.SafetyLiveness.finRefines_impossibility_tight_nonempty :
    let Spec : FinTraceSystem Bool := fun _ => False
    let Φ : FinTraceSystem Bool → Prop := fun T => ¬ T []
    IsPrefixClosed Spec ∧ Φ Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ

theorem Toy.SafetyLiveness.finRefines_impossibility_tight_spec :
    let Spec : FinTraceSystem Bool := doNothingFin
    let Φ : FinTraceSystem Bool → Prop := fun _ => False
    IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ

theorem Toy.SafetyLiveness.finRefines_impossibility_tight_reject :
    let Spec : FinTraceSystem Bool := doNothingFin
    let Φ : FinTraceSystem Bool → Prop := fun _ => True
    IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ Φ Spec ∧ FinRefinesPreserves Φ
```

**Non-vacuity witness:** On Bool, emitTrueFin is prefix-closed and nonempty, satisfies FinHasNonemptyTrace, and doNothingFin fails FinHasNonemptyTrace. (`finRefines_cannot_preserve_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.finRefines_cannot_preserve_nonvacuity :
    IsPrefixClosed emitTrueFin ∧
      IsNonemptyFin emitTrueFin ∧
      FinHasNonemptyTrace emitTrueFin ∧
      ¬ FinHasNonemptyTrace doNothingFin
```

**Positive control:** `obsRefinesPreserves_emitsEvent_rejects_doNothing`

```lean
theorem Toy.SafetyLiveness.obsRefinesPreserves_emitsEvent_rejects_doNothing :
    ObsRefinesPreserves (fun S : ObsSystem Bool => ObsSatisfies S EmitsEvent) ∧
      IsNonemptyObs emitTrueObs ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ ObsSatisfies (silentDivergeObs : ObsSystem Bool) EmitsEvent ∧
      ¬ ObsSatisfies (immediateHaltObs : ObsSystem Bool) EmitsEvent
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.finPrefixes_eq_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (UnivProp : StreamSystem α) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      finPrefixes (UnivProp : StreamSystem α) = finPrefixes P ∧
      ¬ Satisfies (UnivProp : StreamSystem α) P

theorem Toy.SafetyLiveness.finRefinesPreserves_linearTime {α : Type u} (Q : List α → Prop) :
    FinRefinesPreserves (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v)

theorem Toy.SafetyLiveness.linearTime_never_meets_impossibility_hyps
    {α : Type u} (Q : List α → Prop) (Spec : FinTraceSystem α) :
    ¬ (IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧
        (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v) Spec ∧
        ¬ (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v) doNothingFin)

theorem Toy.SafetyLiveness.linearTime_pred_accepts_doNothing_of_accepts_healthy
    {α : Type u} {Spec : FinTraceSystem α} (Q : List α → Prop)
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec)
    (hSpec : ∀ v : List α, Spec v → Q v) :
    ∀ v : List α, doNothingFin v → Q v

theorem Toy.SafetyLiveness.obsRefines_fails_possibility_canEmit :
    let Spec : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [true]
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs Spec ∧
      ObsRefines silentDivergeObs Spec ∧
      ObsCanEmit Spec ∧
      ¬ ObsCanEmit (silentDivergeObs : ObsSystem Bool)

theorem Toy.SafetyLiveness.streamRefines_fails_possibility :
    IsNonemptyStream (fun s : InfTrace Bool => s = constFalse) ∧
      IsNonemptyStream (UnivProp : StreamSystem Bool) ∧
      StreamRefines (fun s : InfTrace Bool => s = constFalse) UnivProp ∧
      (∃ s : InfTrace Bool, (UnivProp : StreamSystem Bool) s ∧ s 0 = true) ∧
      ¬ (∃ s : InfTrace Bool, s = constFalse ∧ s 0 = true)
```

**Prior art:**

- C. A. R. Hoare, Communicating Sequential Processes, Prentice Hall, 1985, ISBN 0-13-153271-5.
- Stephen D. Brookes and A. W. Roscoe, 'An Improved Failures Model for Communicating Processes', Seminar on Concurrency (LNCS 197):281-305, Springer, 1985, DOI: 10.1007/3-540-15670-4_14.
- A. W. Roscoe, The Theory and Practice of Concurrency, Prentice Hall, 1997, ISBN 0-13-674409-5 (Chapters 2-3 & 8, inadequacy of traces refinement for deadlock-freedom and progress).
- Benoît Ballenghien, Safouan Taha, Burkhart Wolff, and Lina Ye, 'HOL-CSP Version 2.0' (theory CSP_Refinements: leT_STOP and leDT_STOP; theory CSP_Assertions: deadlock_free_mono_FD), Archive of Formal Proofs, April 26, 2019, https://isa-afp.org/entries/HOL-CSP.html.

**Design question:** Shows that in prefix-closed finite-trace semantics, no universal linear-time predicate can reject {[]} for a healthy specification, and any non-universal predicate that rejects {[]} fails downward preservation; preserving event-emission progress by inclusion requires moving to complete behaviors (ObsRefines) or refusals.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). A verification method whose correctness criterion is inclusion of prefix-closed finite trace sets (for example CSP trace refinement) cannot guarantee, by that inclusion alone, any property that the do-nothing trace set {[]} violates. Reasoning: such a criterion is an instance of FinRefines on healthy trace sets, {[]} is healthy, and it is included in every healthy specification; guaranteeing such a property needs additional observations (termination or divergence tags, refusals) or a separate argument.

### 7. `fin-trace-refines-preserves-safety`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.finPrefixes_refines_preserves_safety` in `Toy/SafetyLiveness/Refinement.lean`.
- **Plain claim:** For any stream systems Impl and Spec and any safety property P, if every finite prefix of Impl is a finite prefix of Spec (FinRefines (finPrefixes Impl) (finPrefixes Spec)) and Spec satisfies P, then Impl satisfies P.

Lean statement:

```lean
theorem Toy.SafetyLiveness.finPrefixes_refines_preserves_safety
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hSafe : IsSafety P)
    (hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec))
    (hSpec : Satisfies Spec P) :
    Satisfies Impl P
```

With the key definitions unfolded:

```lean
IsSafety P →
(∀ u, (∃ s, Impl s ∧ HasPrefix s u) → ∃ s, Spec s ∧ HasPrefix s u) →   -- FinRefines (finPrefixes Impl) (finPrefixes Spec)
(∀ s, Spec s → P s) →
∀ s, Impl s → P s
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hSafe : IsSafety P` | Ensures any infinite trace violating P has a finite bad prefix that would be exposed by finPrefixes Impl ⊆ finPrefixes Spec. | tight: counterexample `eventuallyTrue_tight_finPrefixes_safety` |
| `hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec)` | Forces every finite prefix of every infinite trace in Impl to appear as a finite prefix of some infinite trace in Spec. | tight: counterexample `finPrefixes_safety_tight_refines` |
| `hSpec : Satisfies Spec P` | Ensures every infinite trace of Spec lies in P, so no bad prefix of P can appear in finPrefixes Spec. | tight: counterexample `finPrefixes_safety_tight_satisfies` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.eventuallyTrue_tight_finPrefixes_safety :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := EventuallyTrue
    FinRefines (finPrefixes Impl) (finPrefixes Spec) ∧
      Satisfies Spec EventuallyTrue ∧
      ¬ Satisfies Impl EventuallyTrue

theorem Toy.SafetyLiveness.finPrefixes_safety_tight_refines :
    let Impl : StreamSystem Bool := fun s => s = constTrue
    let Spec : StreamSystem Bool := AlwaysFalse
    IsSafety AlwaysFalse ∧
      Satisfies Spec AlwaysFalse ∧
      ¬ Satisfies Impl AlwaysFalse

theorem Toy.SafetyLiveness.finPrefixes_safety_tight_satisfies :
    let Impl : StreamSystem Bool := fun s => s = constTrue
    let Spec : StreamSystem Bool := fun s => s = constTrue
    IsSafety AlwaysFalse ∧
      FinRefines (finPrefixes Impl) (finPrefixes Spec) ∧
      ¬ Satisfies Impl AlwaysFalse
```

**Non-vacuity witness:** On Bool, {constFalse} refines AlwaysFalse on finite prefixes, and AlwaysFalse is a safety property satisfying itself. (`finPrefixes_preserves_safety_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.finPrefixes_preserves_safety_nonvacuity :
    IsSafety AlwaysFalse ∧
      FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes AlwaysFalse) ∧
      Satisfies AlwaysFalse AlwaysFalse
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.finPrefixes_refines_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P

theorem Toy.SafetyLiveness.finPrefixes_refines_fails_of_not_isSafety
    {α : Type u} {P : TraceProp α} (hNotSafe : ¬ IsSafety P) :
    ∃ s₀ : InfTrace α,
      IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P

theorem Toy.SafetyLiveness.streamRefines_closure_of_finPrefixes_refines
    {α : Type u} {Impl Spec : StreamSystem α}
    (hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec)) :
    StreamRefines Impl (Closure Spec)
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0.
- A. W. Roscoe, The Theory and Practice of Concurrency, Prentice Hall, 1997, ISBN 0-13-674409-5 (traces refinement preserves safety).
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.3.3 'Trace Equivalence and Safety Properties': Theorem 3.28 Finite Trace Inclusion and Safety Properties, for transition systems without terminal states).

**Design question:** Explains why infinite-stream safety properties ('nothing bad happens at any finite step') are preserved automatically whenever an implementation's finite prefixes are included in a specification's finite prefixes.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). For systems whose runs are all infinite (for example transition systems without terminal states), inclusion of finite trace sets transfers every safety property from specification to implementation. Reasoning: the theorem holds for arbitrary run sets Impl and Spec; terminating or crashing runs are covered only if termination and faults are encoded as infinite runs over the alphabet.

### 8. `fin-trace-refines-fails-nontrivial-liveness`

- **Tier:** T0 (re-derivation of a known result). **Kind:** impossibility. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.finPrefixes_refines_fails_every_nontrivial_liveness` in `Toy/SafetyLiveness/Refinement.lean`.
- **Plain claim:** For every nontrivial liveness property P (satisfying IsLiveness P and rejecting some concrete infinite trace s₀), the explicit nonempty stream systems Impl = {s₀} and Spec = P satisfy Satisfies Spec P and FinRefines (finPrefixes Impl) (finPrefixes Spec), yet Impl fails to satisfy P.

Lean statement:

```lean
theorem Toy.SafetyLiveness.finPrefixes_refines_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P
```

With the key definitions unfolded:

```lean
-- with Impl := fun s => s = s₀ and Spec := P:
IsLiveness P → ¬ P s₀ →
  (∃ s, s = s₀) ∧ (∃ s, P s) ∧ (∀ s, P s → P s) ∧
  (∀ u, (∃ s, s = s₀ ∧ HasPrefix s u) → ∃ s, P s ∧ HasPrefix s u) ∧
  ¬ (∀ s, s = s₀ → P s)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hLive : IsLiveness P` | Forces finPrefixes P to equal all of List α, so every arbitrary s₀ ∉ P satisfies FinRefines (finPrefixes {s₀}) (finPrefixes P); tight only for that universal choice of s₀ ∉ P (existential failure holds for every non-safety property via Toy.SafetyLiveness.finPrefixes_refines_fails_of_not_isSafety). | tight: counterexample `alwaysFalse_tight_finPrefixes_liveness` |
| `hNotP : ¬ P s₀` | Witnesses nontriviality of P (P ≠ UnivProp) and supplies the concrete violating implementation trace s₀. | tight: counterexample `univ_tight_finPrefixes_liveness` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.alwaysFalse_tight_finPrefixes_liveness :
    ¬ AlwaysFalse constTrue ∧
      ¬ (IsNonemptyStream (fun s => s = constTrue) ∧
         IsNonemptyStream AlwaysFalse ∧
         Satisfies AlwaysFalse AlwaysFalse ∧
         FinRefines (finPrefixes (fun s => s = constTrue)) (finPrefixes AlwaysFalse) ∧
         ¬ Satisfies (fun s => s = constTrue) AlwaysFalse)

theorem Toy.SafetyLiveness.univ_tight_finPrefixes_liveness :
    IsLiveness (UnivProp : TraceProp Bool) ∧
      ¬ (IsNonemptyStream (fun s => s = constFalse) ∧
         IsNonemptyStream (UnivProp : StreamSystem Bool) ∧
         Satisfies (UnivProp : StreamSystem Bool) UnivProp ∧
         FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes UnivProp) ∧
         ¬ Satisfies (fun s => s = constFalse) UnivProp)
```

**Non-vacuity witness:** On Bool, EventuallyTrue is a liveness property and rejects constFalse. (`finPrefixes_fails_liveness_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.finPrefixes_fails_liveness_nonvacuity :
    IsLiveness EventuallyTrue ∧ ¬ EventuallyTrue constFalse
```

**Positive control:** `streamRefines_rejects_constFalse_for_eventuallyTrue`

```lean
theorem Toy.SafetyLiveness.streamRefines_rejects_constFalse_for_eventuallyTrue :
    FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes EventuallyTrue) ∧
      ¬ StreamRefines (fun s => s = constFalse) EventuallyTrue ∧
      ¬ ObsRefines (embedStreams (fun s => s = constFalse)) (embedStreams EventuallyTrue)
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.finPrefixes_eq_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (UnivProp : StreamSystem α) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      finPrefixes (UnivProp : StreamSystem α) = finPrefixes P ∧
      ¬ Satisfies (UnivProp : StreamSystem α) P

theorem Toy.SafetyLiveness.finPrefixes_refines_fails_of_not_isSafety
    {α : Type u} {P : TraceProp α} (hNotSafe : ¬ IsSafety P) :
    ∃ s₀ : InfTrace α,
      IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P

theorem Toy.SafetyLiveness.streamRefines_preserves_all_properties
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hRef : StreamRefines Impl Spec) (hSpec : Satisfies Spec P) :
    Satisfies Impl P
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0 (liveness properties are dense, so their finite-prefix set is universal).
- Martin Rem, 'A Personal Perspective of the Alpern–Schneider Characterization of Safety and Liveness', in Beauty Is Our Business, Springer, 1990, pp. 365-372, DOI: 10.1007/978-1-4612-4476-9_44.
- A. W. Roscoe, The Theory and Practice of Concurrency, Prentice Hall, 1997, ISBN 0-13-674409-5.
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.4.1 'Liveness Properties': Definition 3.33, P is a liveness property iff pref(P) = (2^AP)*).

**Design question:** Demonstrates that comparing infinite-trace systems solely by their finite prefixes (even up to prefix-set equality) erases every nontrivial liveness guarantee when Spec = P.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). A refinement check that compares only the finite prefixes of systems with infinite runs cannot certify any nontrivial liveness requirement on its own. Reasoning: for every such requirement P the theorem exhibits an implementation with a single run violating P that passes finite-prefix inclusion against the specification P itself.

### 9. `obs-refines-separates-do-nothing`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.obsRefines_separates_doNothing_from_finRefines` in `Toy/SafetyLiveness/Divergence.lean`.
- **Plain claim:** In complete observable-behavior semantics (explicit terminates, diverges, and reacts constructors), every nonempty implementation Impl whose finite prefixes lie in {[]} passes finite-trace refinement against every nonempty specification Spec satisfying EmitsEvent, yet fails complete-behavior refinement ObsRefines Impl Spec.

Lean statement:

```lean
theorem Toy.SafetyLiveness.obsRefines_separates_doNothing_from_finRefines
    {α : Type u} {Impl Spec : ObsSystem α}
    (hImplNE : IsNonemptyObs Impl)
    (hSpecNE : IsNonemptyObs Spec)
    (hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin)
    (hProgress : ObsSatisfies Spec EmitsEvent) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec) ∧ ¬ ObsRefines Impl Spec
```

With the key definitions unfolded:

```lean
-- ObsBehavior α ::= terminates (u : List α) | diverges (u : List α) | reacts (s : Nat → α)
-- obsFinPrefixes S v := ∃ b, S b ∧ behaviorPrefixes b v, where behaviorPrefixes
--   (terminates u) v = IsPrefix v u, (diverges u) v = IsPrefix v u, (reacts s) v = HasPrefix s v
-- EmitsEvent (terminates u) = (u ≠ []), EmitsEvent (diverges u) = (u ≠ []), EmitsEvent (reacts _) = True
(∃ b, Impl b) → (∃ b, Spec b) →
(∀ v, obsFinPrefixes Impl v → v = []) →
(∀ b, Spec b → EmitsEvent b) →
  (∀ v, obsFinPrefixes Impl v → obsFinPrefixes Spec v) ∧ ¬ (∀ b, Impl b → Spec b)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hImplNE : IsNonemptyObs Impl` | Serves the ¬ ObsRefines conjunct: rules out the empty/miraculous implementation ∅, which vacuously satisfies ObsRefines ∅ Spec. | tight: counterexample `obsEmpty_tight_implNE` |
| `hSpecNE : IsNonemptyObs Spec` | Serves the FinRefines conjunct (Toy.SafetyLiveness.finRefines_obsFinPrefixes_of_doNothing): ensures obsFinPrefixes Spec contains [] so finite-trace refinement succeeds. | tight: counterexample `obsSpecEmpty_tight_specNE` |
| `hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin` | Serves both conjuncts: forces obsFinPrefixes Impl ⊆ {[]} for FinRefines acceptance and ensures every behavior in Impl fails EmitsEvent; for ¬ ObsRefines alone, a single silent behavior ∃ b, Impl b ∧ ¬ EmitsEvent b suffices (proved in Toy.SafetyLiveness.not_obsRefines_of_silent_behavior and Toy.SafetyLiveness.mixedSilentAndEmit_not_obsRefines_without_doNothing). | tight: counterexample `obsEmitTrue_tight_doNothing` |
| `hProgress : ObsSatisfies Spec EmitsEvent` | Serves the ¬ ObsRefines conjunct (Toy.SafetyLiveness.not_obsRefines_of_silent_behavior): requires every behavior of Spec to emit at least one event. | tight: counterexample `obsAllowDiverge_tight_progress` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.obsEmpty_tight_implNE :
    let Impl : ObsSystem Bool := fun _ => False
    IsNonemptyObs emitTrueObs ∧
      FinRefines (obsFinPrefixes Impl) doNothingFin ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes Impl) (obsFinPrefixes emitTrueObs) ∧
         ¬ ObsRefines Impl emitTrueObs)

theorem Toy.SafetyLiveness.obsSpecEmpty_tight_specNE :
    let Spec : ObsSystem Bool := fun _ => False
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ObsSatisfies Spec EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (silentDivergeObs : ObsSystem Bool) Spec)

theorem Toy.SafetyLiveness.obsEmitTrue_tight_doNothing :
    IsNonemptyObs emitTrueObs ∧
      IsNonemptyObs emitTrueObs ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes emitTrueObs) (obsFinPrefixes emitTrueObs) ∧
         ¬ ObsRefines emitTrueObs emitTrueObs)

theorem Toy.SafetyLiveness.obsAllowDiverge_tight_progress :
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ¬ (FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool))
          (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) ∧
         ¬ ObsRefines (silentDivergeObs : ObsSystem Bool) silentDivergeObs)
```

**Non-vacuity witness:** On Bool, silentDivergeObs ({.diverges []}) and emitTrueObs ({.terminates [true]}) satisfy all four hypotheses. (`obsRefines_separates_doNothing_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.obsRefines_separates_doNothing_nonvacuity :
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs emitTrueObs ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ObsSatisfies emitTrueObs EmitsEvent
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.divergeAfterTrue_separates_sameTrace_terminates :
    obsFinPrefixes divergeAfterTrueObs = obsFinPrefixes emitTrueObs ∧
      ¬ ObsRefines divergeAfterTrueObs emitTrueObs ∧
      ¬ ObsRefines emitTrueObs divergeAfterTrueObs

theorem Toy.SafetyLiveness.finRefines_obsFinPrefixes_of_doNothing
    {α : Type u} {Impl Spec : ObsSystem α}
    (hSpecNE : IsNonemptyObs Spec)
    (hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec)

theorem Toy.SafetyLiveness.mixedSilentAndEmit_not_obsRefines_without_doNothing :
    let Impl : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [false]
    (∃ b : ObsBehavior Bool, Impl b ∧ ¬ EmitsEvent b) ∧
      ¬ FinRefines (obsFinPrefixes Impl) doNothingFin ∧
      ¬ ObsRefines Impl emitTrueObs

theorem Toy.SafetyLiveness.not_obsRefines_of_silent_behavior
    {α : Type u} {Impl Spec : ObsSystem α}
    (hSilent : ∃ b : ObsBehavior α, Impl b ∧ ¬ EmitsEvent b)
    (hProgress : ObsSatisfies Spec EmitsEvent) :
    ¬ ObsRefines Impl Spec

theorem Toy.SafetyLiveness.obsRefines_fails_possibility_canEmit :
    let Spec : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [true]
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs Spec ∧
      ObsRefines silentDivergeObs Spec ∧
      ObsCanEmit Spec ∧
      ¬ ObsCanEmit (silentDivergeObs : ObsSystem Bool)

theorem Toy.SafetyLiveness.obsRefines_implies_finRefines
    {α : Type u} {Impl Spec : ObsSystem α}
    (hRef : ObsRefines Impl Spec) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec)

theorem Toy.SafetyLiveness.obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges
    {α : Type u} {Spec : ObsSystem α} {u : List α}
    (hPrefix : obsFinPrefixes Spec u)
    (hNotDiv : ¬ Spec (.diverges u)) :
    FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
      ¬ ObsRefines (fun b => b = .diverges u) Spec
```

**Prior art:**

- Xavier Leroy, 'A Formally Verified Compiler Back-end', Journal of Automated Reasoning 43(4):363-446, 2009, DOI: 10.1007/s10817-009-9155-4 (Section 2.1 Definitions 2-3 backward simulation / behavioral inclusion; Section 3.4 converges / diverges / goeswrong).
- Xavier Leroy et al., CompCert verified C compiler, Coq module common/Behaviors.v (repository AbsInt/CompCert, commit 2685140bf72c959446981fb99b5e44a8975021bc, lines 41-45), https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Behaviors.v#L41-L45 (four-constructor program_behavior: Terminates, Diverges, Reacts, Goes_wrong).
- Xavier Leroy and Hervé Grall, 'Coinductive big-step operational semantics', Information and Computation 207(2):284-304, 2009, DOI: 10.1016/j.ic.2007.12.004.
- Daniel Patterson and Amal Ahmed, 'The Next 700 Compiler Correctness Theorems', Proceedings of the ACM on Programming Languages 3(ICFP), 2019, DOI: 10.1145/3341689.
- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic, 'Interaction Trees: Representing Recursive and Impure Programs in Coq', PACMPL 4(POPL), Article 51, 2020, DOI: 10.1145/3371119.
- A. W. Roscoe, The Theory and Practice of Concurrency, Prentice Hall, 1997, ISBN 0-13-674409-5 (alternative interactive fix via failures–divergences refinement; mechanized in HOL-CSP).

**Design question:** Shows how closed-program compiler verification closes the finite-trace do-nothing loophole: recording complete behaviors (rather than prefix-closed finite traces) makes ObsRefines reject both silentDivergeObs and immediateHaltObs against any event-emitting specification whenever Impl is nonempty.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). In closed-program compiler correctness stated as inclusion of whole-program behaviors with explicit termination and divergence (as in CompCert's program_behavior), a compiled program that halts or hangs without output is rejected whenever every source behavior emits an event, while a criterion phrased only over prefix-closed finite I/O traces accepts it. Reasoning: ObsBehavior keeps the terminates/diverges/reacts split of CompCert's behaviors; it omits exit codes and the goes-wrong behavior, so the bridge does not cover undefined-behavior wildcards.

### 10. `obs-refines-rejects-new-divergence`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges` in `Toy/SafetyLiveness/Divergence.lean`.
- **Plain claim:** Whenever some finite trace u is an observable prefix of Spec (obsFinPrefixes Spec u) and Spec forbids silent divergence at u (¬ Spec (.diverges u)), the implementation {ObsBehavior.diverges u} passes finite-trace refinement against Spec on obsFinPrefixes yet fails complete-behavior refinement ObsRefines.

Lean statement:

```lean
theorem Toy.SafetyLiveness.obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges
    {α : Type u} {Spec : ObsSystem α} {u : List α}
    (hPrefix : obsFinPrefixes Spec u)
    (hNotDiv : ¬ Spec (.diverges u)) :
    FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
      ¬ ObsRefines (fun b => b = .diverges u) Spec
```

With the key definitions unfolded:

```lean
-- Impl := fun b => b = ObsBehavior.diverges u
obsFinPrefixes Spec u → ¬ Spec (ObsBehavior.diverges u) →
  (∀ v, obsFinPrefixes (fun b => b = .diverges u) v → obsFinPrefixes Spec v) ∧
  ¬ (∀ b, b = .diverges u → Spec b)
```

**Hypothesis ledger:**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `hPrefix : obsFinPrefixes Spec u` | Ensures u (and by prefix-closure every prefix of u) belongs to obsFinPrefixes Spec, so {ObsBehavior.diverges u} passes finite-trace refinement against Spec. | tight: counterexample `obsSeparatesDiverges_tight_prefix` |
| `hNotDiv : ¬ Spec (.diverges u)` | Minimal point-level condition stating that silent divergence at u is newly introduced relative to Spec (strictly weaker than global ObsSatisfies Spec NoDivergence), making ObsRefines fail. | tight: counterexample `obsSeparatesDiverges_tight_notDiv` |

Counterexample statements:

```lean
theorem Toy.SafetyLiveness.obsSeparatesDiverges_tight_prefix :
    let Spec : ObsSystem Bool := immediateHaltObs
    let u : List Bool := [true]
    ¬ Spec (.diverges u) ∧
      ¬ (FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (fun b => b = .diverges u) Spec)

theorem Toy.SafetyLiveness.obsSeparatesDiverges_tight_notDiv :
    let Spec : ObsSystem Bool := divergeAfterTrueObs
    let u : List Bool := [true]
    obsFinPrefixes Spec u ∧
      ¬ (FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (fun b => b = .diverges u) Spec)
```

**Non-vacuity witness:** On Bool with Spec = emitTrueObs ({.terminates [true]}) and u = [true], [true] lies in obsFinPrefixes emitTrueObs and emitTrueObs rejects .diverges [true] (exercising .diverges vs. .terminates on the identical complete trace [true]; see also Toy.SafetyLiveness.divergeAfterTrue_separates_sameTrace_terminates). (`obsSeparatesDiverges_sameTrace_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.obsSeparatesDiverges_sameTrace_nonvacuity :
    obsFinPrefixes emitTrueObs [true] ∧ ¬ emitTrueObs (.diverges [true])
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.divergeAfterTrue_separates_sameTrace_terminates :
    obsFinPrefixes divergeAfterTrueObs = obsFinPrefixes emitTrueObs ∧
      ¬ ObsRefines divergeAfterTrueObs emitTrueObs ∧
      ¬ ObsRefines emitTrueObs divergeAfterTrueObs

theorem Toy.SafetyLiveness.obsRefines_rejects_divergence_of_noDivergence
    {α : Type u} {Impl Spec : ObsSystem α} {u : List α}
    (hDiv : Impl (.diverges u))
    (hNoDiv : ObsSatisfies Spec NoDivergence) :
    ¬ ObsRefines Impl Spec
```

**Prior art:**

- Xavier Leroy, 'A Formally Verified Compiler Back-end', Journal of Automated Reasoning 43(4):363-446, 2009, DOI: 10.1007/s10817-009-9155-4 (Sections 2.1, 3.4, and 3.5).
- Xavier Leroy et al., CompCert verified C compiler, Coq module common/Behaviors.v (repository AbsInt/CompCert, commit 2685140bf72c959446981fb99b5e44a8975021bc, lines 41-45), https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Behaviors.v#L41-L45 (Terminates vs. Diverges on identical finite trace).
- Xavier Leroy and Hervé Grall, 'Coinductive big-step operational semantics', Information and Computation 207(2):284-304, 2009, DOI: 10.1016/j.ic.2007.12.004.
- Stephen D. Brookes and A. W. Roscoe, 'An Improved Failures Model for Communicating Processes', Seminar on Concurrency (LNCS 197):281-305, Springer, 1985, DOI: 10.1007/3-540-15670-4_14.

**Design question:** Pinpoints why finite-prefix (prefix-closed) tracking is insufficient to reject newly introduced divergence: an implementation that emits a valid trace u and then hangs (.diverges u) has exactly the same finite prefixes as {.terminates u}, so only explicit divergence observation rejects post-prefix hangs. When Spec = {.terminates u}, the result directly exercises the constructor tag distinction between .diverges u and .terminates u on the identical trace u (Toy.SafetyLiveness.divergeAfterTrue_separates_sameTrace_terminates), unlike do-nothing separation at [] against nonempty traces.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). A transformation that turns 'emit u, then stop' into 'emit u, then loop silently' passes prefix-closed I/O trace inclusion but fails behavior inclusion with an explicit divergence tag. Reasoning: obsFinPrefixes forgets the terminates/diverges tag, and the theorem's hypotheses hold for Spec = {terminates u}.

### 11. `closure-inter-eq-iff-safety-and-machine-closed`

- **Tier:** T0 (re-derivation of a known result). **Kind:** characterization. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.closure_propInter_eq_iff_isSafety_and_machineClosed` in `Toy/SafetyLiveness/MachineClosure.lean`.
- **Plain claim:** For arbitrary infinite-trace properties S and L over any alphabet α, Closure (PropInter S L) = S holds if and only if S is a safety property and the pair (S, L) is machine-closed.

Lean statement:

```lean
theorem Toy.SafetyLiveness.closure_propInter_eq_iff_isSafety_and_machineClosed
    {α : Type u} (S L : TraceProp α) :
    Closure (PropInter S L) = S ↔ IsSafety S ∧ MachineClosed S L
```

With the key definitions unfolded:

```lean
-- MachineClosed S L := ∀ u : List α, (∃ s, HasPrefix s u ∧ S s) → ∃ s', HasPrefix s' u ∧ S s' ∧ L s'
(fun s => ∀ n, ∃ s', HasPrefix s' (takePrefix s n) ∧ S s' ∧ L s') = S
  ↔ IsSafety S ∧ MachineClosed S L
```

**Hypothesis ledger:** the statement has no hypotheses beyond its universally quantified parameters.

**Non-vacuity witness:** On Bool, (StartsTrue, EventuallyFalse) satisfies both sides while (StartsFalseStaysFalse, EventuallyTrue) falsifies both sides. (`closure_propInter_eq_iff_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.closure_propInter_eq_iff_nonvacuity :
    (IsSafety StartsTrue ∧ MachineClosed StartsTrue EventuallyFalse) ∧
      ¬ (IsSafety StartsFalseStaysFalse ∧ MachineClosed StartsFalseStaysFalse EventuallyTrue)
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.eventuallyTrue_tight_machineClosed_iff :
    ¬ (MachineClosed EventuallyTrue UnivProp ↔
       Closure (PropInter EventuallyTrue UnivProp) = EventuallyTrue)

theorem Toy.SafetyLiveness.machineClosed_iff_closure_propInter_eq_of_isSafety
    {α : Type u} {S L : TraceProp α} (hS : IsSafety S) :
    MachineClosed S L ↔ Closure (PropInter S L) = S

theorem Toy.SafetyLiveness.machineClosed_not_closed_under_propInter :
    IsLiveness EventuallyAlwaysTrue ∧
      IsLiveness EventuallyAlwaysFalse ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysTrue ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysFalse ∧
      ¬ MachineClosed (UnivProp : TraceProp Bool)
          (PropInter EventuallyAlwaysTrue EventuallyAlwaysFalse)

theorem Toy.SafetyLiveness.machineClosed_without_liveness_witness :
    IsSafety AlwaysFalse ∧ ¬ IsLiveness AlwaysFalse ∧ MachineClosed AlwaysFalse AlwaysFalse
```

**Prior art:**

- Martín Abadi and Leslie Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2):253-284, 1991, DOI: 10.1016/0304-3975(91)90224-P (Section 2.3 'Specifications', machine closure M = Closure(M ∩ L) and Lemma 1; Section 7 completeness theorem).
- Krzysztof R. Apt, Nissim Francez, and Shmuel Katz, 'Appraising fairness in languages for distributed programming', Distributed Computing 2(4):226-241, 1988, DOI: 10.1007/BF01872848 (feasibility of fairness).
- Frank Dederichs and Rainer Weber, 'Safety and liveness from a methodological point of view', Information Processing Letters 36(1):25-30, 1990, DOI: 10.1016/0020-0190(90)90181-V (relative liveness).
- Martín Abadi, Bowen Alpern, Krzysztof R. Apt, Nissim Francez, Shmuel Katz, Leslie Lamport, and Fred B. Schneider, 'Preserving Liveness: Comments on "Safety and Liveness from a Methodological Point of View"', Information Processing Letters 40(3):141-142, 1991, DOI: 10.1016/0020-0190(91)90168-H.
- Thomas A. Henzinger, 'Sooner is safer than later', Information Processing Letters 43(3):135-141, 1992, DOI: 10.1016/0020-0190(92)90005-G (congruousness).
- Leslie Lamport, Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers, Addison-Wesley, 2002, ISBN 0-321-14306-X (Chapter 8, Liveness and Fairness).
- Gudmund Grov and Stephan Merz, 'A Definitional Encoding of TLA* in Isabelle/HOL', Archive of Formal Proofs, November 19, 2011, https://isa-afp.org/entries/TLA.html.

**Design question:** Characterizes exactly when layering a fairness or liveness requirement L onto a transition specification S leaves its finite-prefix safety behavior unchanged (Closure (PropInter S L) = S) rather than sneaking in hidden safety constraints.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). In specifications written as a safety part S conjoined with a fairness or liveness part L (as in Abadi and Lamport's state machine plus supplementary property), adding L leaves the allowed finite prefixes unchanged exactly when S is a safety property and (S, L) is machine-closed. Reasoning: Closure (PropInter S L) is the set of runs all of whose prefixes are prefixes of the full specification; S and L are arbitrary predicates here and stuttering invariance is not required, so the match with stuttering-closed state-machine specifications is one-directional (they are a special case).

### 12. `alpern-schneider-machine-closed`

- **Tier:** T0 (re-derivation of a known result). **Kind:** theorem. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.alpernSchneider_is_machineClosed` in `Toy/SafetyLiveness/MachineClosure.lean`.
- **Plain claim:** Supporting reference point: for any alphabet α (including Empty) and any infinite-trace property P, the canonical Alpern–Schneider decomposition pair (Closure P, LivenessPart P) is machine-closed.

Lean statement:

```lean
theorem Toy.SafetyLiveness.alpernSchneider_is_machineClosed
    {α : Type u} (P : TraceProp α) :
    MachineClosed (Closure P) (LivenessPart P)
```

With the key definitions unfolded:

```lean
∀ u : List α, (∃ s, HasPrefix s u ∧ Closure P s) →
  ∃ s', HasPrefix s' u ∧ Closure P s' ∧ (P s' ∨ ¬ Closure P s')
```

**Hypothesis ledger:** the statement has no hypotheses beyond its universally quantified parameters.

**Non-vacuity witness:** On Bool, StartsTrueAndEventuallyFalse is a nontrivial property that is neither safety nor liveness. (`alpernSchneider_is_machineClosed_nonvacuity`)

```lean
theorem Toy.SafetyLiveness.alpernSchneider_is_machineClosed_nonvacuity :
    ¬ IsSafety StartsTrueAndEventuallyFalse ∧ ¬ IsLiveness StartsTrueAndEventuallyFalse
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.alpernSchneider_nonunique_components :
    (IsSafety AlwaysFalse ∧ IsLiveness (UnivProp : TraceProp Bool) ∧ IsLiveness AlwaysFalseOrTwoTrues ∧
      PropInter AlwaysFalse UnivProp = AlwaysFalse ∧
      PropInter AlwaysFalse AlwaysFalseOrTwoTrues = AlwaysFalse ∧
      (UnivProp : TraceProp Bool) ≠ AlwaysFalseOrTwoTrues) ∧
    (IsSafety StartsTrue ∧ IsSafety StartsFalseStaysFalse ∧ IsLiveness EventuallyTrue ∧
      PropInter StartsTrue UnivProp = StartsTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue ∧
      StartsFalseStaysFalse ≠ StartsTrue)

theorem Toy.SafetyLiveness.emptyAlphabet_no_liveness (L : TraceProp Empty) : ¬ IsLiveness L

theorem Toy.SafetyLiveness.nonMachineClosed_consistent_spec_counterexample :
    IsSafety StartsFalseStaysFalse ∧
      IsLiveness EventuallyTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue constTrue ∧
      ¬ MachineClosed StartsFalseStaysFalse EventuallyTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse
```

**Prior art:**

- Bowen Alpern and Fred B. Schneider, 'Defining Liveness', Information Processing Letters 21(4):181-185, 1985, DOI: 10.1016/0020-0190(85)90056-0.
- Martín Abadi and Leslie Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2):253-284, 1991, DOI: 10.1016/0304-3975(91)90224-P (Section 2.3).
- Christel Baier and Joost-Pieter Katoen, Principles of Model Checking, MIT Press, 2008, ISBN 978-0-262-02649-9 (§3.4.2 'Safety vs. Liveness Properties': Lemma 3.38 Sharpest Decomposition).

**Design question:** Supporting reference point bridging Alpern–Schneider decomposition and machine closure: decomposing P via its canonical safety hull Closure P never introduces safety/liveness mismatch.

Basis: execution (Lean kernel check)

No claim about real systems is made for this result beyond the mathematical statement.

### 13. `non-machine-closed-consistent-spec`

- **Tier:** T0 (re-derivation of a known result). **Kind:** counterexample. **Depth:** shallow.
- **Lean:** `Toy.SafetyLiveness.nonMachineClosed_consistent_spec_counterexample` in `Toy/SafetyLiveness/MachineClosure.lean`.
- **Plain claim:** On Bool, pairing StartsFalseStaysFalse (fun s => s 0 = false → ∀ i, s i = false, a safety property) with EventuallyTrue (fun s => ∃ i, s i = true, a liveness property) yields a satisfiable conjunction explicitly admitting constTrue (fun _ => true), yet the pair is not machine-closed and Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse.

Lean statement:

```lean
theorem Toy.SafetyLiveness.nonMachineClosed_consistent_spec_counterexample :
    IsSafety StartsFalseStaysFalse ∧
      IsLiveness EventuallyTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue constTrue ∧
      ¬ MachineClosed StartsFalseStaysFalse EventuallyTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse
```

With the key definitions unfolded:

```lean
-- StartsFalseStaysFalse s := s 0 = false → ∀ i, s i = false      (a safety property)
-- EventuallyTrue s       := ∃ i, s i = true                       (a liveness property)
-- constTrue              := fun _ => true
IsSafety StartsFalseStaysFalse ∧ IsLiveness EventuallyTrue ∧
(StartsFalseStaysFalse constTrue ∧ EventuallyTrue constTrue) ∧
¬ (∀ u, (∃ s, HasPrefix s u ∧ StartsFalseStaysFalse s) →
        ∃ s', HasPrefix s' u ∧ StartsFalseStaysFalse s' ∧ EventuallyTrue s') ∧
Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse
```

**Hypothesis ledger:** the statement has no hypotheses beyond its universally quantified parameters.

**Non-vacuity witness:** Self-witnessing concrete counterexample on Bool exposing PropInter StartsFalseStaysFalse EventuallyTrue constTrue while refuting extension of prefix [false] from constFalse. (`nonMachineClosed_consistent_spec_counterexample`)

```lean
theorem Toy.SafetyLiveness.nonMachineClosed_consistent_spec_counterexample :
    IsSafety StartsFalseStaysFalse ∧
      IsLiveness EventuallyTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue constTrue ∧
      ¬ MachineClosed StartsFalseStaysFalse EventuallyTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse
```

**Companion declarations cited by this card:**

```lean
theorem Toy.SafetyLiveness.closure_propInter_startsFalseStaysFalse_eventuallyTrue_eq_startsTrue :
    PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) = StartsTrue

theorem Toy.SafetyLiveness.startsTrue_eventuallyFalse_machineClosed :
    MachineClosed StartsTrue EventuallyFalse
```

**Prior art:**

- Martín Abadi and Leslie Lamport, 'The existence of refinement mappings', Theoretical Computer Science 82(2):253-284, 1991, DOI: 10.1016/0304-3975(91)90224-P (Section 2.3, specifications whose supplementary clause adds safety constraints).
- Frank Dederichs and Rainer Weber, 'Safety and liveness from a methodological point of view', Information Processing Letters 36(1):25-30, 1990, DOI: 10.1016/0020-0190(90)90181-V.
- Martín Abadi, Bowen Alpern, Krzysztof R. Apt, Nissim Francez, Shmuel Katz, Leslie Lamport, and Fred B. Schneider, 'Preserving Liveness: Comments on "Safety and Liveness from a Methodological Point of View"', Information Processing Letters 40(3):141-142, 1991, DOI: 10.1016/0020-0190(91)90168-H.
- Krzysztof R. Apt, Nissim Francez, and Shmuel Katz, 'Appraising fairness in languages for distributed programming', Distributed Computing 2(4):226-241, 1988, DOI: 10.1007/BF01872848.
- Leslie Lamport, Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers, Addison-Wesley, 2002, ISBN 0-321-14306-X (Chapter 8).

**Design question:** Demonstrates on a concrete satisfiable specification how conjoining a liveness requirement with a safety invariant can silently rule out finite prefixes permitted by the safety invariant alone, creating a hidden safety obligation.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge). A specification that conjoins a safety invariant with a liveness requirement can forbid finite behaviors that the safety invariant alone allows. Reasoning: for the concrete Bool pair, the prefix [false] extends to a run of StartsFalseStaysFalse but to no run of the conjunction, so a finite-prefix check against the safety part alone accepts a prefix that the full specification makes irremediably bad.

## Boundaries

### Non-claims

Each item is backed in one of three ways. An item that cites a `Toy.SafetyLiveness.*` declaration is backed by that kernel-checked declaration (the stronger reading is **known not to apply**). An item that cites a published source rests on that source. An item with neither citation states a scope limit of the model (**not examined** in Lean) or a remark that follows immediately from the quoted definitions and statements (for example, that a statement holds vacuously for an empty property); such remarks are not separately proved as Lean theorems.

**1. `alpern-schneider-decomposition`**

- Does not claim uniqueness of the decomposition P = PropInter S L: neither the safety component (without machine closure) nor the liveness component (even fixing S = Closure P) is unique in general, as proved by Toy.SafetyLiveness.alpernSchneider_nonunique_components.
- Does not hold over an empty alphabet α = Empty because no property over Empty is live (the empty prefix [] has no infinite extension in InfTrace Empty; Toy.SafetyLiveness.emptyAlphabet_no_liveness), so the conclusion fails for EmptyProp over Empty (Toy.SafetyLiveness.emptyAlphabet_tight_alpernSchneider).
- Does not imply that liveness components are closed under intersection: conjoining liveness properties from two decompositions need not remain live, and whenever α has at least two elements, every property (including EmptyProp and every safety property) is the intersection of two liveness properties (Alpern & Schneider, 1985, Theorem 2; see also Toy.SafetyLiveness.machineClosed_not_closed_under_propInter).
- Does not require properties to be closed under stuttering: IsSafety and IsLiveness follow Alpern and Schneider (1985) over arbitrary predicates on Nat → α, diverging from Lamport (in Alford, Lamport, and Mullery, 1985) and Abadi and Lamport (1991) on non-stuttering-closed properties (see Toy.SafetyLiveness.stepDiffers_isSafety).
- Does not apply to relative liveness (extension restricted to reachable prefixes of a transition system rather than all of List α).
- Does not provide a decidable or automata-theoretic construction (such as Büchi automaton decomposition); LivenessPart P uses classical negation of Closure P.
- Does not apply to hyperproperties (sets of sets of traces) or branching-time properties; it applies strictly to linear-time predicates on InfTrace α.

**2. `safety-iff-closure-eq`**

- Does not require stuttering invariance: non-stuttering-closed sets such as fun s => s 0 ≠ s 1 satisfy IsSafety here (Toy.SafetyLiveness.stepDiffers_isSafety), whereas Lamport (in Alford, Lamport, and Mullery, 1985) and Abadi and Lamport (1991) restrict safety properties to stuttering-closed sets.
- Does not claim that IsLiveness P ↔ Closure P = UnivProp holds without Nonempty α: that equivalence is proved over every nonempty alphabet (Toy.SafetyLiveness.isLiveness_iff_closure_eq_univ_of_nonempty), but over α = Empty, Closure EmptyProp = UnivProp holds vacuously while IsLiveness EmptyProp is false (Toy.SafetyLiveness.emptyAlphabet_tight_isLiveness_iff_closure_eq_univ).
- Does not claim that every safety property is decidable or expressible by a finite-state invariant; IsSafety captures topological closedness in the prefix topology (with minimality of Closure P established separately in Toy.SafetyLiveness.closure_minimal_of_isSafety).
- Does not apply directly to finite-trace systems without lifting via finPrefixes.

**3. `safety-and-liveness-iff-univ`**

- Does not mean that safety facts about a system can never establish a liveness property of that system: a safety property can be contained in a nontrivial liveness property (e.g. AlwaysFalse ⊆ EventuallyFalse, with EventuallyFalse ≠ UnivProp), so a system proved to satisfy AlwaysFalse also satisfies the liveness property EventuallyFalse (proved in Toy.SafetyLiveness.alwaysFalse_safety_entails_nontrivial_liveness_eventuallyFalse). The theorem is about the classes of properties, not about entailment between them.
- The biconditional fails without Nonempty α: over Empty, UnivProp = UnivProp holds trivially while IsLiveness UnivProp is false (though the forward implication IsSafety P → IsLiveness P → P = UnivProp still holds vacuously via Toy.SafetyLiveness.eq_univ_of_isSafety_of_isLiveness, with individual tightness counterexamples Toy.SafetyLiveness.eventuallyTrue_tight_safety_of_unique and Toy.SafetyLiveness.alwaysFalse_tight_liveness_of_unique).
- Does not mean every property is either safety or liveness: mixed properties such as StartsTrueAndEventuallyFalse are neither (Toy.SafetyLiveness.alpernSchneider_nonvacuity).
- Does not mean a specification combining safety and liveness constraints is trivial: PropInter S L can be neither safety nor liveness; for example, the conjunction PropInter StartsTrue EventuallyFalse of the safety property StartsTrue and the liveness property EventuallyFalse is neither (Toy.SafetyLiveness.propInter_startsTrue_eventuallyFalse_neither_safety_nor_liveness).
- Does not apply to relative liveness (liveness restricted to prefixes of a transition system rather than all of List α).

**4. `stream-refines-preserves-all`**

- Does not prevent a vacuous empty implementation: EmptyProp stream-refines every Spec (Toy.SafetyLiveness.emptyStreamSystem_refines_all) and vacuously satisfies every P unless IsNonemptyStream Impl is established separately.
- Over a one-element alphabet (Unit), every nonempty stream system refines every other nonempty stream system (Toy.SafetyLiveness.unit_streamSystem_refines_all_nonempty); the absence of a universal nonempty refiner (Toy.SafetyLiveness.no_nonempty_streamSystem_refines_all_nonempty) requires at least two distinct observations.
- Does not preserve existential possibility predicates (such as 'some trace starts with true', Toy.SafetyLiveness.streamRefines_fails_possibility) or general multi-trace hyperproperties.
- Does not account for stuttering, internal (silent) steps, or alphabet translation between compiler intermediate languages: StreamRefines compares infinite traces step-for-step over a single shared alphabet α.
- Does not by itself capture terminating or silently diverging executions unless they are explicitly encoded (for example, via ObsBehavior).

**5. `do-nothing-fin-refines-all`**

- IsPrefixClosed Spec and IsNonemptyFin Spec are sufficient domain healthiness conditions rather than necessary conditions for the conclusion: FinRefines doNothingFin Spec holds if and only if Spec [] (Toy.SafetyLiveness.doNothingFin_finRefines_iff_nil_mem), which also holds for non-prefix-closed sets containing [] (Toy.SafetyLiveness.doNothingFin_finRefines_without_prefixClosed).
- Does not model CSP failures–divergences divergence (⊥ / div): in the CSP traces model STOP has trace set {[]} and trace-refines every process, and under operational prefix projection silent divergence also maps to {[]}, whereas in CSP's failures–divergences model divergence is chaotic (trace set Σ*) and sits at the bottom of the refinement order.
- Does not claim that finite-trace refinement preserves nothing: it preserves every universal linear-time finite-trace predicate (Toy.SafetyLiveness.finRefinesPreserves_linearTime) and every stream safety property (Toy.SafetyLiveness.finPrefixes_refines_preserves_safety).
- Does not apply to refinement relations that record explicit termination, divergence, or refusals (see Toy.SafetyLiveness.obsRefines_separates_doNothing_from_finRefines).

**6. `fin-refines-no-progress-preservation`**

- Every predicate Φ to which this impossibility applies is necessarily not of universal linear-time form T ↦ ∀ u, T u → Q u: every predicate of that form that accepts a prefix-closed nonempty Spec also accepts doNothingFin (Toy.SafetyLiveness.linearTime_pred_accepts_doNothing_of_accepts_healthy, Toy.SafetyLiveness.linearTime_never_meets_impossibility_hyps), and every such predicate is preserved by finite-trace refinement (Toy.SafetyLiveness.finRefinesPreserves_linearTime).
- Complete observable-behavior refinement (ObsRefines) and stream refinement (StreamRefines) also fail to preserve existential possibility predicates such as FinHasNonemptyTrace or ObsCanEmit ('some execution emits an event') across nonempty systems (Toy.SafetyLiveness.obsRefines_fails_possibility_canEmit, Toy.SafetyLiveness.streamRefines_fails_possibility); switching to ObsRefines resolves the progress problem because explicit termination and divergence turn 'every execution emits an event' (ObsSatisfies · EmitsEvent) into a universal linear-time predicate that holds on emitTrueObs, rejects both silentDivergeObs and immediateHaltObs, and is preserved by ObsRefines across nonempty systems, as proved by the positive control Toy.SafetyLiveness.obsRefinesPreserves_emitsEvent_rejects_doNothing.
- Note on CSP refinements: in CSP, tracking divergences alongside traces without refusals (⊑_DT) still admits STOP: P ⊑_DT STOP holds for every process P (HOL-CSP lemma leDT_STOP); rejecting STOP in CSP requires refusals (⊑_F / ⊑_FD), whereas ObsRefines rejects immediateHaltObs by tagging termination explicitly.

**7. `fin-trace-refines-preserves-safety`**

- Does not preserve any non-safety property across all systems (see Toy.SafetyLiveness.finPrefixes_refines_fails_of_not_isSafety and Toy.SafetyLiveness.finPrefixes_refines_fails_every_nontrivial_liveness).
- Does not preserve safety properties of terminating or crashing executions (such as 'if the program halts, its exit status is 0' or 'never halts before emitting an event') unless termination and fault outcomes are explicitly encoded into the finite trace alphabet; Impl and Spec here are purely infinite StreamSystems.
- Does not handle stuttering, silent internal transitions, or alphabet changes across compiler passes: finPrefixes requires step-for-step alignment over one shared alphabet α.
- Guarantees only StreamRefines Impl (Closure Spec) (Toy.SafetyLiveness.streamRefines_closure_of_finPrefixes_refines), not StreamRefines Impl Spec: when Spec = PropInter S L is non-machine-closed, finite-prefix refinement against Spec enforces the strictly stronger hidden safety constraint Closure (PropInter S L), whereas finite-prefix refinement against S alone enforces only S.
- Does not preserve multi-trace hypersafety properties unless lifted to tuples of prefixes, and does not establish IsNonemptyStream Impl (EmptyProp vacuously refines every Spec).

**8. `fin-trace-refines-fails-nontrivial-liveness`**

- Dropping IsLiveness P in favor of a mixed non-safety property (such as StartsTrueAndEventuallyFalse) does NOT rescue finite-trace refinement: preservation across all (Impl, Spec) holds if and only if IsSafety P (see Toy.SafetyLiveness.finPrefixes_refines_fails_of_not_isSafety). The hypothesis IsLiveness P is tight only for the stronger claim that every arbitrary trace s₀ ∉ P yields a counterexample against Spec = P.
- Does not mean bidirectional finite-trace equality rescues liveness: even finPrefixes Impl = finPrefixes Spec fails to preserve every nontrivial liveness property P (over a nonempty alphabet, Impl = UnivProp and Spec = P share the universal prefix set Σ* while Impl violates P; proved in Toy.SafetyLiveness.finPrefixes_eq_fails_every_nontrivial_liveness).
- Does not apply to the trivial liveness property UnivProp, which rejects no trace, so the hypothesis ¬ P s₀ cannot be met; with s₀ = constFalse and P = UnivProp the conclusion fails (Toy.SafetyLiveness.univ_tight_finPrefixes_liveness).

**9. `obs-refines-separates-do-nothing`**

- Does not protect against an empty/uninhabited implementation Impl = ∅ (see Toy.SafetyLiveness.obsEmpty_tight_implNE): totality/nonemptiness of the compiled semantics must be established separately (e.g., via target determinism or forward-to-backward simulation).
- Does not model return values / exit codes on termination: ObsBehavior.terminates carries only an I/O event trace List α, so pure value-returning programs that emit no I/O events collapse into immediateHaltObs ({.terminates []}) and fail EmitsEvent.
- EmitsEvent does not rule out silent divergence after a nonempty prefix: .diverges (a :: u) satisfies EmitsEvent (forbidding post-prefix divergence requires NoDivergence or ¬ Spec (.diverges u); see Toy.SafetyLiveness.obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges).
- Does not itself exercise the distinction between .terminates u and .diverges u: rejecting doNothingFin against EmitsEvent relies only on comparing complete finite traces rather than prefix-closed sets; the terminates-vs.-diverges tag is exercised only when comparing .terminates u against .diverges u on the same trace u (see Toy.SafetyLiveness.obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges and Toy.SafetyLiveness.divergeAfterTrue_separates_sameTrace_terminates).
- Does not rule out do-nothing implementations when Spec is nondeterministic and permits .diverges [] (or .terminates []) as one allowed branch alongside event-emitting behaviors (Toy.SafetyLiveness.obsRefines_fails_possibility_canEmit), nor when undefined-behavior wildcards (such as CompCert's Goes_wrong under behavior_improves) allow unsafe source programs to refine to arbitrary target behaviors.
- Does not establish operational simulation soundness for multi-pass compilers: proving ObsRefines via step-by-step pass simulations additionally requires a well-founded stuttering measure to preserve divergence (Leroy, 2009, §3.5) and target determinism to turn forward simulation into backward behavioral inclusion (Leroy, 2009, §2.1).
- Does not provide compositional refinement for open modules, separate compilation, or concurrent linking: ObsBehavior models closed whole-program executions only (contrast Patterson & Ahmed, 2019; CSP failures–divergences). Monotonicity of obsFinPrefixes under ObsRefines is established separately in Toy.SafetyLiveness.obsRefines_implies_finRefines.

**10. `obs-refines-rejects-new-divergence`**

- Does not require global divergence-freedom ObsSatisfies Spec NoDivergence: Spec may legitimately diverge after some other trace v ≠ u while still forbidding divergence at u (global NoDivergence rejection is recorded separately as helper Toy.SafetyLiveness.obsRefines_rejects_divergence_of_noDivergence).
- Does not rule out infinite reactive chatter (an infinite stream .reacts s that never reaches a desired event); rejecting chatter requires constraining .reacts s in Spec.
- Does not establish operational simulation soundness without a well-founded stuttering measure (Leroy, 2009, §3.5) and target determinism (Leroy, 2009, §2.1), nor open-module compositionality (Patterson & Ahmed, 2019).

**11. `closure-inter-eq-iff-safety-and-machine-closed`**

- Does not require or imply IsLiveness L: Closure (PropInter S L) = S can hold when L is itself a safety property (Toy.SafetyLiveness.machineClosed_without_liveness_witness). When IsSafety S is assumed upfront, the specialized equivalence MachineClosed S L ↔ Closure (PropInter S L) = S holds (Toy.SafetyLiveness.machineClosed_iff_closure_propInter_eq_of_isSafety), where IsSafety S is strictly tight (Toy.SafetyLiveness.eventuallyTrue_tight_machineClosed_iff).
- Machine closure is NOT closed under conjunction or specification composition: even when (S, L₁) and (S, L₂) are both machine-closed with live L₁ and L₂, (S, PropInter L₁ L₂) need not be machine-closed (proved in Toy.SafetyLiveness.machineClosed_not_closed_under_propInter).
- Does not detect deadlocked finite executions of an underlying transition system: MachineClosed S L quantifies only over finite prefixes that already extend to some infinite trace in S (so deadlocked prefixes with no infinite continuation in S are invisible unless encoded via infinite stuttering as in Abadi & Lamport, 1991, or explicit finite traces; in particular, S = EmptyProp satisfies both sides vacuously).
- Does not require stuttering invariance of S or L (unlike Abadi & Lamport, 1991, §§2.2–2.3, and Grov & Merz, 2011).
- Does not imply that non-machine-closed specifications are always erroneous: as argued by Abadi et al. (1991, IPL 40:141–142), non-machine-closed specifications remain legitimate at high/abstract specification levels; machine closure is specifically required on the lower-level (implementation) specification in Abadi and Lamport's refinement-mapping completeness theorem (which also requires finite invisible nondeterminism and internal continuity of the abstract specification, plus history and prophecy variables).

**12. `alpern-schneider-machine-closed`**

- Holds vacuously when P = EmptyProp (since Closure EmptyProp = EmptyProp admits no infinite traces), and does not detect transition-system deadlocks without infinite continuations in Closure P.
- Does not imply IsLiveness (LivenessPart P) without Nonempty α: over Empty, MachineClosed (Closure P) (LivenessPart P) holds vacuously (this card's theorem Toy.SafetyLiveness.alpernSchneider_is_machineClosed has no hypothesis on α) even though LivenessPart P is not live (Toy.SafetyLiveness.emptyAlphabet_no_liveness).
- Does not provide a computable or constructive repair for non-machine-closed specifications: while (Closure P, LivenessPart P) is always machine-closed semantically, computing Closure (PropInter S L) from an arbitrary specification pair (S, L) is generally undecidable and does not automatically yield an executable state machine.
- Does not imply that every (S, L) decomposition of P with IsSafety S and IsLiveness L is machine-closed (see Toy.SafetyLiveness.nonMachineClosed_consistent_spec_counterexample and Toy.SafetyLiveness.alpernSchneider_nonunique_components).

**13. `non-machine-closed-consistent-spec`**

- Does not claim that combining safety and liveness always fails machine closure: (StartsTrue, EventuallyFalse) is a nontrivial machine-closed pair (Toy.SafetyLiveness.startsTrue_eventuallyFalse_machineClosed).
- Does not claim that PropInter StartsFalseStaysFalse EventuallyTrue is unimplementable; rather, its effective safety hull is strictly stronger than StartsFalseStaysFalse (namely StartsTrue: the conjunction equals StartsTrue, and so does its closure; Toy.SafetyLiveness.closure_propInter_startsFalseStaysFalse_eventuallyTrue_eq_startsTrue).
- Does not imply that non-machine-closed specifications should always be prohibited: non-machine-closed pairs are useful as high-level abstract specifications (Abadi et al., 1991, IPL 40:141–142), though they violate the machine-closure hypothesis required of lower-level implementations in refinement-mapping completeness theorems (Abadi & Lamport, 1991, Section 2.3 & Section 7).

### Escape hatches

Hypotheses or modeling choices whose removal or weakening defeats an impossibility result:

- **6. `fin-refines-no-progress-preservation`:** Escape hatch (prefix-closure): dropping IsPrefixClosed and comparing only complete/maximal finite traces defeats the impossibility (because [] is not equal to [true]).
- **6. `fin-refines-no-progress-preservation`:** Escape hatch (bidirectional equivalence): strengthening one-sided inclusion FinRefines T₁ T₂ to finite-trace equality T₁ = T₂ defeats this finite-trace impossibility (since {[]} ≠ {[], [true]}), though finite-trace equality still fails infinite-trace liveness (see Toy.SafetyLiveness.finPrefixes_eq_fails_every_nontrivial_liveness).
- **6. `fin-refines-no-progress-preservation`:** Escape hatch (restricted implementation domain): restricting T₁ in FinRefinesPreserves to implementations separately guaranteed to emit an event (excluding doNothingFin) defeats the impossibility.
- **8. `fin-trace-refines-fails-nontrivial-liveness`:** Escape hatch (tighter specification): restricting Spec to a strict subset of P whose closure lies inside P (Closure Spec ⊆ P, e.g. Spec = {constTrue} for P = EventuallyTrue) defeats the counterexample for that fixed Spec.
- **8. `fin-trace-refines-fails-nontrivial-liveness`:** Escape hatch (stronger refinement domain): replacing FinRefines (finPrefixes Impl) (finPrefixes Spec) with full stream refinement StreamRefines Impl Spec (or ObsRefines on embedStreams) defeats the impossibility: StreamRefines preserves every infinite-trace property (Toy.SafetyLiveness.streamRefines_preserves_all_properties), and the positive control Toy.SafetyLiveness.streamRefines_rejects_constFalse_for_eventuallyTrue shows that both StreamRefines and ObsRefines on embedStreams reject the concrete witness pair ({constFalse}, EventuallyTrue) that finite-prefix inclusion accepts.

### Tightness status

Every hypothesis of every result is labeled `tight` and has a proved counterexample theorem. No hypothesis is labeled `harmless` or `unknown`. Two qualifications recorded in the ledgers: in `do-nothing-fin-refines-all`, the pair (`hClosed`, `hNonempty`) is individually tight but jointly replaceable by the exact condition `Spec []`; in `fin-trace-refines-fails-nontrivial-liveness`, `hLive` is tight only for the universal choice of `s₀ ∉ P` (existential failure holds for every non-safety property).

### Statements found false or left unproved

None. Every result listed in this report is proved without `sorry`; no statement was found false.

### Not examined (package-wide)

- Stuttering-closed (Lamport / Abadi–Lamport) safety and liveness, and refinement up to stuttering or with internal steps.
- Fairness constraints, relative liveness (liveness relative to the reachable prefixes of a transition system), and transition systems with finite maximal runs (deadlock) or terminal states.
- Hyperproperties, branching-time properties, and probabilistic properties.
- Refusal-based (failures, failures–divergences) refinement, and compositional or open-system refinement.
- Automata-theoretic or decidable versions of the decomposition (for example for ω-regular properties).
- Operational semantics, simulation proofs, and compiler passes; `ObsBehavior` systems are given extensionally.

## Evidence

### Kernel-check record

- Toolchain: `leanprover/lean4:v4.34.1`, repository `leanprover/lean4`, tag `v4.34.1` = commit `5045d0056413266e57c625dcd7c365b10e377c52` (the tag points directly at this commit). No Mathlib; no Lake dependencies.
- Build: `lake build` of `lean/` (library `Toy`, modules `Toy.SafetyLiveness.{Core, Decomposition, Refinement, Divergence, MachineClosure, LivenessClosure}`) succeeds with no warnings; the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, or `unsafe`.
- Axioms: all 304 declarations of the library were audited with Lean's `collectAxioms`; each depends on at most `propext`, `Classical.choice`, and `Quot.sound` (per-declaration list in `audit/axioms.json`).
- Statement hash = SHA-256 of Lean's `repr` of the declaration's type. Closure hash = SHA-256 of the sorted, newline-joined list of `name : repr(type)` (plus ` := repr(value)` for non-theorems) over every package-local constant reachable from the statement through types, definition bodies, and inductive constructors (theorem bodies excluded). Both are recorded in `audit/statements.json`.

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `alpernSchneider_decomposition_of_nonempty` | result `alpern-schneider-decomposition` | `Classical.choice`, `Quot.sound`, `propext` | `8ec3798b8ddf2a720de981a7845de06110df854a2729761456c121a74160ed99` | `036c2d3d288f6317914584d549a12c970e80dd2d7278cb6408dda336fe0fe020` (9) |
| `emptyAlphabet_tight_alpernSchneider` | counterexample `alpern-schneider-decomposition`/`hα` | (none) | `8ad6311a27aa9d4dc2db31e17f5dc005601c1873d1b10e5f0f8eb19584e78d06` | `8ab5b5ffa9aa5fede76c2c703625b3427af02ddfde9dc4d9e883dfd878b4ead5` (10) |
| `alpernSchneider_nonvacuity` | non-vacuity `alpern-schneider-decomposition`; companion `safety-and-liveness-iff-univ` | `propext` | `8d76b9d42a792b136e99cabb77ba4b3032761044acbcfae258fac13561d06d7b` | `dfdfb241b55d18570e7ff1d1ee2cc4c68009509725c1ec0623e04dc75459da26` (7) |
| `alpernSchneider_nonunique_components` | companion `alpern-schneider-decomposition`; companion `alpern-schneider-machine-closed` | `Classical.choice`, `Quot.sound`, `propext` | `84f1fdb2e5cde4c0b2956ca4bc36fa9f91038f96e549c23c9690dd9bcb0182ae` | `05376b9bd98d6f9e17ceadbe67399a6260720e5e3702a46950a37bd55206f489` (13) |
| `closure_isSafety` | companion `alpern-schneider-decomposition` | `Classical.choice`, `Quot.sound`, `propext` | `cebf4a771b75462c1fd4f52e84f5a52bb3340fdfe7f0baf28459dcb0feec66a9` | `2cebb585660e760b7db77cfea450178a3e81e6af6be04381e98de2b09b682253` (6) |
| `emptyAlphabet_no_liveness` | companion `alpern-schneider-decomposition`; companion `alpern-schneider-machine-closed` | (none) | `488e903489b75081eb22a213e4a999e92d0962296f5cf48ee5b3e66ef58c241f` | `5ecce43f1744144763f25bb868934529d1968cc82da1fa13fb374b555b274e91` (4) |
| `isLiveness_livenessPart_of_nonempty` | companion `alpern-schneider-decomposition` | `Classical.choice`, `Quot.sound`, `propext` | `aa03153119fb03353d93604c5f2797d80be83c9f51cc5fce808332b2c021f8ab` | `8c5711506299ad8cc13c5e1884900ba42a4085742727ad94f588a6c6b2539063` (7) |
| `machineClosed_not_closed_under_propInter` | companion `alpern-schneider-decomposition`; companion `closure-inter-eq-iff-safety-and-machine-closed` | `Quot.sound`, `propext` | `0daa19f75b990107d7293ba23ff40315bf3e4473bd23dce9c346ff7b3d3150b4` | `dc5a53b713059de68969418cc168da67f229072217582630ba830a40c320c0f3` (9) |
| `propInter_closure_livenessPart_eq` | companion `alpern-schneider-decomposition` | `Quot.sound`, `propext` | `94704975f6cae40065611bf8049a97ec040944523f6f644cfd78fcafba3fe4ac` | `834b0d3c0450d04ad6616277969436808855353c7f8ad66178ff6b4a8caf678e` (7) |
| `stepDiffers_isSafety` | companion `alpern-schneider-decomposition`; companion `safety-iff-closure-eq` | `propext` | `b58743e73db8b23e81f369bbb0691fab6bc879f53f95a78b21021c062c62c384` | `7a3a57b78b6f6fbcbb06d20e3822236eeee9b912ce9274c48bf142590238eec9` (5) |
| `isSafety_iff_closure_eq` | result `safety-iff-closure-eq` | `Classical.choice`, `Quot.sound`, `propext` | `79e82eb1a3358bc7dc4878cba644feb6b1ef6d02d1ed659dc5330ed731912dde` | `2cebb585660e760b7db77cfea450178a3e81e6af6be04381e98de2b09b682253` (6) |
| `isSafety_iff_closure_eq_nonvacuity` | non-vacuity `safety-iff-closure-eq` | `Classical.choice`, `Quot.sound`, `propext` | `7e9721ef37abff53303f509b555b5e330cac7f14304a7dab9302890c7386fc90` | `570dae84a246d19427c7b92621f57e1215de8798a10c91f76281f3a03a028f3e` (7) |
| `closure_minimal_of_isSafety` | companion `safety-iff-closure-eq` | `Classical.choice`, `Quot.sound`, `propext` | `26df79f18f68b830fdbd9f1a63b70698a8b4b4ebcb3a1cae29d04320495d24e1` | `2cebb585660e760b7db77cfea450178a3e81e6af6be04381e98de2b09b682253` (6) |
| `emptyAlphabet_tight_isLiveness_iff_closure_eq_univ` | companion `safety-iff-closure-eq` | `Quot.sound` | `8845c1f1c941538256a8bfdfaf82e65cb9f6af7fe311b5aae6d9bb11d8a572ce` | `b5c27c5c64bdaf96e5809e479ea7816ae09805c40b4c066274eeef4abbb28947` (8) |
| `isLiveness_iff_closure_eq_univ_of_nonempty` | companion `safety-iff-closure-eq` | `Quot.sound`, `propext` | `88fc32eb5c34f532c5197b6ffeac36515508e9a1fa96fb6aefcf8d25e7f15dbc` | `9c579266c89659dfd67aeae67be02f3c9c3ff659376ee915d4243dd9269c0d8a` (7) |
| `isSafety_and_isLiveness_iff_eq_univ_of_nonempty` | result `safety-and-liveness-iff-univ` | `Classical.choice`, `Quot.sound`, `propext` | `38f0c402025c8cd77283a79d17a6100e56527b42dc139352a5cba6681e9b0380` | `37feba165b8c901ffc838fead7a0387baed8dd6d94ff0223e01512184fef1924` (7) |
| `emptyAlphabet_tight_safety_liveness_iff_univ` | counterexample `safety-and-liveness-iff-univ`/`hα` | (none) | `5aa23fa2050b469481ed700ad47ed7f21520e8ea6f94b6917448e67f21ecbe8e` | `37feba165b8c901ffc838fead7a0387baed8dd6d94ff0223e01512184fef1924` (7) |
| `isSafety_and_isLiveness_iff_eq_univ_nonvacuity` | non-vacuity `safety-and-liveness-iff-univ` | `propext` | `15895b114998c36e7b5caf3598ca714434393e076927f5dd520f5da58adf618a` | `a0857eb69ebccfc72276f3fd59a9139ad76f09f74f8f61fac4d7c9df6e9dad2b` (8) |
| `alwaysFalse_safety_entails_nontrivial_liveness_eventuallyFalse` | companion `safety-and-liveness-iff-univ` | `Classical.choice`, `Quot.sound`, `propext` | `55a7798136ad69382da334e73751701dd67eb5614f00075c800f09f37bbe76cf` | `3288cdf5c0690ce2ef11ffdbf152b4fd63956d048117a2edb74b74b458a2621e` (12) |
| `alwaysFalse_tight_liveness_of_unique` | companion `safety-and-liveness-iff-univ` | `Classical.choice`, `Quot.sound`, `propext` | `60ac4ea0df2cd76cedacfddcf88b842c899d491a4f49c86b3f5b9880f56348b8` | `52756bfd568e38187ea50d7bd3410b7afd174ca27da39eb4ab31fc03a19a7347` (7) |
| `eq_univ_of_isSafety_of_isLiveness` | companion `safety-and-liveness-iff-univ` | `Classical.choice`, `Quot.sound`, `propext` | `71f318c0fe56d58aa212ed80e86f5c578283d65060692a98fe4e78a28b2ef733` | `37feba165b8c901ffc838fead7a0387baed8dd6d94ff0223e01512184fef1924` (7) |
| `eventuallyTrue_tight_safety_of_unique` | companion `safety-and-liveness-iff-univ` | `propext` | `760f3648edaa5dab22e1d73b6729ed69c116e999c8aa4f652805507a09a78798` | `34b6b852ed81a5d39c5ef7824b9f4b1cd785c307b212d08a00dcfc294bc8d77b` (6) |
| `propInter_startsTrue_eventuallyFalse_neither_safety_nor_liveness` | companion `safety-and-liveness-iff-univ` | `propext` | `5a44b98b00488a6ce2746c21744c7861a97b65354ae3216696948507cec2b005` | `11a87b2de1da785090f3bd92ccc759b9bdec5e7226a9006744020f065f143573` (9) |
| `streamRefines_preserves_all_properties` | result `stream-refines-preserves-all`; companion `fin-trace-refines-fails-nontrivial-liveness` | (none) | `f9884ff4cc64f802d65b303f9ced09efa81da8477cfbe67cdafe06a8f2a019db` | `5834e662ec83ec408c4dff5431dcc359c51e662291da567ea54e667f9fd84d98` (5) |
| `streamRefines_preserves_tight_refines` | counterexample `stream-refines-preserves-all`/`hRef` | `propext` | `0133c6b7620ac01a610c0dc79eb62c0890d675261f4e6a635e7d4fa7a5000210` | `3800d127cb39bb3b6c960c117e4dd879fc7bfc68903e87a74d4cb57e7809a565` (6) |
| `streamRefines_preserves_tight_satisfies` | counterexample `stream-refines-preserves-all`/`hSpec` | `propext` | `8aa97c3626093f4d0cc0752f8d18f8ee2ccf7cebac8ef4bf62e0048753e582ea` | `39917fdd839c1977749525d5d5695a0324f7b309329281b34a5a90bb4fc19fd4` (7) |
| `streamRefines_preserves_nonvacuity` | non-vacuity `stream-refines-preserves-all` | (none) | `abccb3f49a290116f0fc118927d26b960ea06b6a5ab72a4fc79b9ba688793233` | `c71f8c7a54093c40c9255ee21f0d68bc72c8e4e6e2ccb055bc09cf0aa8872cd2` (7) |
| `emptyStreamSystem_refines_all` | companion `stream-refines-preserves-all` | (none) | `3e8b9556d300a51d7b4248cf3bcc75e39e5eabf7b93dfe00461eb5e62c6f3574` | `f37afee4a48f0919587c38886aa39bfe62e0b7a9b17a7aa821dae9eccd7598f1` (5) |
| `no_nonempty_streamSystem_refines_all_nonempty` | companion `stream-refines-preserves-all` | `propext` | `2e60335e7241942b8730ff758c8e512e7ce402d965f9f8acb5c97973cdfbb3cc` | `3e11b3ea6f8701908d4409c5262bab309bb5f8c4a81d0bc6198ac2bca7666809` (4) |
| `streamRefines_fails_possibility` | companion `stream-refines-preserves-all`; companion `fin-refines-no-progress-preservation` | (none) | `06bbf7e0888cd4ce6625e7b52cb95d311a75fa54681da1e5a674c6350e451069` | `ed0e26ac7de0a52025ddd2ee3830a1268a1e7c0ccb49de3c76b2d8d5cab7f193` (7) |
| `unit_streamSystem_refines_all_nonempty` | companion `stream-refines-preserves-all` | `Quot.sound` | `762b81d0f2619576e89456d02019d97b4bd5fe15fb4651bb2bee736d4f259efd` | `3e11b3ea6f8701908d4409c5262bab309bb5f8c4a81d0bc6198ac2bca7666809` (4) |
| `doNothingFin_refines_every_prefixClosed_nonempty` | result `do-nothing-fin-refines-all` | (none) | `7956989345b18ffacfb09c835d92e1eb3a6c872c574f0e1bf32376d6c8ad973c` | `89ed23ff61f27d76b55c339f6666f4bd9ca68d55f8d293442e53d45f762adf34` (6) |
| `singletonTrueTrace_tight_prefixClosed` | counterexample `do-nothing-fin-refines-all`/`hClosed` | (none) | `0d1a2deb108292a11a302254f2db6fc359a1652f323014df9603354d2ff85bb5` | `0a0ecb505d726f72ddc8d01fcaa31dcbecd82b962e194094ec25931a79c6a4c4` (4) |
| `emptyFinSystem_tight_nonempty` | counterexample `do-nothing-fin-refines-all`/`hNonempty` | (none) | `19975925c003874443d835a714d30071c9ab64b8d8d3419be4bea20e60b29ee7` | `4b0ab1e7ad938ff63bdc66dd83da4031a26221a01d6744384dbb9659e66b4820` (5) |
| `doNothingFin_refines_nonvacuity` | non-vacuity `do-nothing-fin-refines-all` | `propext` | `61af6bf86f1d1a93421ffc201e6ee37ba815248c60f0d26b822d729573edfb47` | `0bbbecda84d19e525d89581d92a798857670e7a18da2a474ac53400a7a426d51` (5) |
| `doNothingFin_finRefines_iff_nil_mem` | companion `do-nothing-fin-refines-all` | (none) | `539e9ce25941e223712cc7d6ec020e224a86923812683faeed7e224c70a0319f` | `8cd70438f2aff1e215577874ea19fb1cf3a9b34bc76e977d85ad58f0022a7f6f` (3) |
| `doNothingFin_finRefines_without_prefixClosed` | companion `do-nothing-fin-refines-all` | (none) | `e6f8aed53a06e377562081999894647e747606d5cb11d4308a73c63ea6bb738f` | `89ed23ff61f27d76b55c339f6666f4bd9ca68d55f8d293442e53d45f762adf34` (6) |
| `finPrefixes_refines_preserves_safety` | companion `do-nothing-fin-refines-all`; result `fin-trace-refines-preserves-safety` | `Classical.choice`, `Quot.sound`, `propext` | `564e82efa7e8f6645e24c4d8b61d17be38a299e11038448ca64ece0a9c142379` | `2b10d55d450a820c520af309742b4800505027f51d2d5b2dd1d41c277569ddf4` (10) |
| `finRefinesPreserves_linearTime` | companion `do-nothing-fin-refines-all`; companion `fin-refines-no-progress-preservation` | (none) | `b3536a401ef6e80f55ef72a24c1f04efa1cdd88bd5f69a880761e7d124a21037` | `e89ca58d8205fd5d088ec2837b145ca80ca113c43a1601939ae08b0cbd5a1f94` (6) |
| `obsRefines_separates_doNothing_from_finRefines` | companion `do-nothing-fin-refines-all`; result `obs-refines-separates-do-nothing` | `propext` | `b0a91cd3a080fa89e9142162387964fb240981e4dbfa861c6294db2aa96c19d4` | `049ca5357dde38091ae74431264c0b8cd3dd82d68baa95807982a8538d6249ed` (21) |
| `finRefines_cannot_preserve_property_rejecting_doNothing` | result `fin-refines-no-progress-preservation` | `propext` | `da5add4633a30d9fd728234d3b545962f37083bb59dab27fa439ad769258573f` | `cbe5f57ab484fa818163febd4958a8f56472121476e0678fef61d3c0418447e5` (7) |
| `finRefines_impossibility_tight_prefixClosed` | counterexample `fin-refines-no-progress-preservation`/`hClosed` | (none) | `0ef5d617008edc11b1909e13b5fa01ec845bda782ffe374a1b3dfe46be16b09e` | `cbe5f57ab484fa818163febd4958a8f56472121476e0678fef61d3c0418447e5` (7) |
| `finRefines_impossibility_tight_nonempty` | counterexample `fin-refines-no-progress-preservation`/`hNonempty` | (none) | `2af4d5829f645428499dd27d0531c566f82c816b929a9f09d3ef0899a25ab31f` | `cbe5f57ab484fa818163febd4958a8f56472121476e0678fef61d3c0418447e5` (7) |
| `finRefines_impossibility_tight_spec` | counterexample `fin-refines-no-progress-preservation`/`hSpec` | `propext` | `a240b4bf20817deb968d0cdae94e614e2b5c9b7de8041caa26fdac287b8c0d1c` | `cbe5f57ab484fa818163febd4958a8f56472121476e0678fef61d3c0418447e5` (7) |
| `finRefines_impossibility_tight_reject` | counterexample `fin-refines-no-progress-preservation`/`hReject` | `propext` | `6c90f327bb25246cb5dba85aa8cf0f5e26a12bb9bd708d2eada7d202241d8dfd` | `cbe5f57ab484fa818163febd4958a8f56472121476e0678fef61d3c0418447e5` (7) |
| `finRefines_cannot_preserve_nonvacuity` | non-vacuity `fin-refines-no-progress-preservation` | `propext` | `cacd3e499fd9597363a9a2c05c912023f63fdd929bcc03b6e63db41c6d64938b` | `13e6813919bec478bab77ad2f34b7fec6f25cb1d3e72dc2cc5b326c30ca3106a` (7) |
| `obsRefinesPreserves_emitsEvent_rejects_doNothing` | positive control `fin-refines-no-progress-preservation` | (none) | `2e97a8a0e114e0b5a0f50382be315d3cd90d185c03ff57851855ad68ba5b6203` | `e29617576d3f898cd2d4c8386d44c20378ea27dc776f257ac0a642b5156ff4a4` (18) |
| `finPrefixes_eq_fails_every_nontrivial_liveness` | companion `fin-refines-no-progress-preservation`; companion `fin-trace-refines-fails-nontrivial-liveness` | `Quot.sound`, `propext` | `5845f09ba3ef025cb3d573ef44fd505c7f5484945fa8b86e63048a91abd85036` | `1e754fab6a2080b8ff51bb01070b4323cb4d49bb5e0dc1d10d321cf71682eb14` (10) |
| `linearTime_never_meets_impossibility_hyps` | companion `fin-refines-no-progress-preservation` | (none) | `5dd22e3fff0ae05269c8b0fddfe635c5c7d0db9db251f7afd0df9664096eba8e` | `3e7338b0657d797e6e99e9fc42acd89e6637fe7f576c6c5ad45af652568096f6` (5) |
| `linearTime_pred_accepts_doNothing_of_accepts_healthy` | companion `fin-refines-no-progress-preservation` | (none) | `45214699726c9c1b13e668a4e791804dafbe4382930491221ce8d990c61e436c` | `3e7338b0657d797e6e99e9fc42acd89e6637fe7f576c6c5ad45af652568096f6` (5) |
| `obsRefines_fails_possibility_canEmit` | companion `fin-refines-no-progress-preservation`; companion `obs-refines-separates-do-nothing` | (none) | `a6cf2bd83a119186beaf4ba1b3d4746e50f14447b3887b0e395535b319a03f2f` | `bb7e0eccd26461a6834ae88776a1b3a3791347e4ea5d382cbf322e6b658f9b49` (15) |
| `eventuallyTrue_tight_finPrefixes_safety` | counterexample `fin-trace-refines-preserves-safety`/`hSafe` | `propext` | `60eb011f0d882c026e8e66c476a94c8ccb2c72891b15411fca06d837e9683d18` | `e8760b7ff184c13fb2a89ab4e451f4688beaa2b845919bd10ed2778bc4859a9b` (10) |
| `finPrefixes_safety_tight_refines` | counterexample `fin-trace-refines-preserves-safety`/`hRef` | `Classical.choice`, `Quot.sound`, `propext` | `b500385263a8672a5a7de1eb0760c9bd630fd766f457ae1bf910a6e01e4aee42` | `d9b8784159e1f014ebb6b5276a5cdbbd81fd1ab361047fd549e01c1e0da6f011` (9) |
| `finPrefixes_safety_tight_satisfies` | counterexample `fin-trace-refines-preserves-safety`/`hSpec` | `Classical.choice`, `Quot.sound`, `propext` | `6f0ff92204f41d8393c056c13d79918e61a36b4f3ff266fb6640f560128ad857` | `6233cd73942e29f7b1e6cec0c66c4452bd1b244049f9392d2ff4692ba7923316` (12) |
| `finPrefixes_preserves_safety_nonvacuity` | non-vacuity `fin-trace-refines-preserves-safety` | `Classical.choice`, `Quot.sound`, `propext` | `e97967206e7ce7b38c0ca91b5cff222fd0e3d027e2b5367c069bc195637e2692` | `df6c4c57de1b7a7f2273eb39c814e0224b200acde169e1ec0ddee0ddf49bce22` (12) |
| `finPrefixes_refines_fails_every_nontrivial_liveness` | companion `fin-trace-refines-preserves-safety`; result `fin-trace-refines-fails-nontrivial-liveness` | (none) | `c5217de4866b116640666f8774ba9ad544267a9574b05614c54ab82cbd771848` | `f9730dc24f29cbb4e6330cb2a4fc188133f4c9c89007304aa09f6f33bb158002` (10) |
| `finPrefixes_refines_fails_of_not_isSafety` | companion `fin-trace-refines-preserves-safety`; companion `fin-trace-refines-fails-nontrivial-liveness` | `Classical.choice`, `Quot.sound`, `propext` | `7a1c71b26af4a5ed3805f0a1e9e2c97a7602b426f05c05a0f5ef6b744f56ae8b` | `dc80d579718b208c43c5fad0c2bff4698e3965581f9cbc01bd3b332910dac1bb` (11) |
| `streamRefines_closure_of_finPrefixes_refines` | companion `fin-trace-refines-preserves-safety` | `propext` | `c0e05af6dd6dc694a83b3bf8672ce6635c77dad987ae8e0797a9b72111e0eed6` | `268d557afd4257b292e151a86dbed190eb070eabcf7c2926fd33134b9ca3effa` (10) |
| `alwaysFalse_tight_finPrefixes_liveness` | counterexample `fin-trace-refines-fails-nontrivial-liveness`/`hLive` | `propext` | `27ba25f96d8ade6efd0bf5c08d8bde87883ce8ca23a9d0e4282902f54820cdc8` | `369233d5fc7b9a504f7fdaf04c04e53edc666e73435ae2ce4a64f87482c11422` (11) |
| `univ_tight_finPrefixes_liveness` | counterexample `fin-trace-refines-fails-nontrivial-liveness`/`hNotP` | `propext` | `7a2b515fa7ee101778a337292c748145d83359e31af9d43d793a4164668fa318` | `a70075d67c32a5453dc33bd9a9ee93e0a32523c67d7512b5b9fdf0b9eb1ca094` (12) |
| `finPrefixes_fails_liveness_nonvacuity` | non-vacuity `fin-trace-refines-fails-nontrivial-liveness` | `propext` | `0cd798a270a43847723ef4f8a9fba304b738e58982f00a19d0d9bad1ffa82782` | `ae9b42563de23be02121b18c8c90b20eb32004eee629d749b54c49ba61ee5b68` (6) |
| `streamRefines_rejects_constFalse_for_eventuallyTrue` | positive control `fin-trace-refines-fails-nontrivial-liveness` | `propext` | `6a10c401e1ef709b845843d45d6c4bbee81d4782d4b7977c5a2677b8157a467d` | `79e09d12361518be96231955bcff6905bb2f34b3ba5f5e47dbc11b14c2871c9e` (22) |
| `obsEmpty_tight_implNE` | counterexample `obs-refines-separates-do-nothing`/`hImplNE` | (none) | `d572829a318dc5e22a919d35e3818c5037fc1194b0db89a32d1f728f1dbb4823` | `e4ad625003d57002449677eff18a2b90afe98d2cde14acfc3144abd96f40f46b` (22) |
| `obsSpecEmpty_tight_specNE` | counterexample `obs-refines-separates-do-nothing`/`hSpecNE` | `Quot.sound`, `propext` | `2e83ce533aad0bbd15f4dfebee4add9495e7a4d1f043a8c72590c3e3214ade33` | `d7b14e3280a0d71f7323bb417748fa9eae582f593e6324c46d6020c59824b561` (22) |
| `obsEmitTrue_tight_doNothing` | counterexample `obs-refines-separates-do-nothing`/`hDoNothing` | (none) | `38b6ea57fa0ef835e169088d2dc1cc507a21d3d24598b927153d7ce17371bb11` | `6043efc2cfae13c8cedf1fde59c6087d18155f306f593f6134b4cf7919c7f8f7` (21) |
| `obsAllowDiverge_tight_progress` | counterexample `obs-refines-separates-do-nothing`/`hProgress` | `Quot.sound`, `propext` | `8f5228496635bf0fdef126426574fbd2b2bae28b299e09ce8e8b9cda0503920a` | `38178d733b6607a873aefe10ba9b3f9c11723535587945e338cbb46354166865` (19) |
| `obsRefines_separates_doNothing_nonvacuity` | non-vacuity `obs-refines-separates-do-nothing` | `Quot.sound`, `propext` | `99f9f4268b96e89f824091391d7d48d3e8484411ce1ae11f8c306da7e16299ee` | `f2121ae70a0fd966bdca1fdc44ad572b8cf02a03b446431cff443ca1c85d54ab` (22) |
| `divergeAfterTrue_separates_sameTrace_terminates` | companion `obs-refines-separates-do-nothing`; companion `obs-refines-rejects-new-divergence` | `Quot.sound`, `propext` | `292baa4fcf63d1381c64b94eed8dd8f02e556ba359cc8b4803b741f2e3c8b36b` | `b62cbe6e39a385928e624ae4abcd8582a39975ae34f7fa5674633df40fe8f491` (17) |
| `finRefines_obsFinPrefixes_of_doNothing` | companion `obs-refines-separates-do-nothing` | (none) | `46eae9fbbeba52f62cb43fce44f093c5fea21876a6f2d6b9ab2958c049be922f` | `3895d2a9a9b7107848b71604969dfa10144a4b33ae95d70a657680f01e9f83a6` (17) |
| `mixedSilentAndEmit_not_obsRefines_without_doNothing` | companion `obs-refines-separates-do-nothing` | `propext` | `8d9395b49549e9b7ed43c1af7297b147acd752c9d58f8335a1f29c29b4302ba6` | `a327b51d596602e1a56f8ebded20493f27da00bdc2525be56abad0782d99541d` (20) |
| `not_obsRefines_of_silent_behavior` | companion `obs-refines-separates-do-nothing` | (none) | `0c4e3fb9eb788176dadfbfbd56ce3e49b29a7d897abb369b4afa40d8a7d1d997` | `4041f467a29c09481a5d8e26cc1e7bd792846d229db9756eb75257e70181d39a` (13) |
| `obsRefines_implies_finRefines` | companion `obs-refines-separates-do-nothing` | (none) | `3173c8847c5916b00f38f035953897ff367ec9dbbc566d27e602e68d947ba083` | `e896b9584958ce24c14a50f018e822cd5bec2353ced5cec663c89f011f5672ba` (16) |
| `obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges` | companion `obs-refines-separates-do-nothing`; result `obs-refines-rejects-new-divergence` | `propext` | `cc89ae166c01b29c9e7c9ed99487bc6fcbf7b4370fe5148396a35716daa5a427` | `e896b9584958ce24c14a50f018e822cd5bec2353ced5cec663c89f011f5672ba` (16) |
| `obsSeparatesDiverges_tight_prefix` | counterexample `obs-refines-rejects-new-divergence`/`hPrefix` | `propext` | `b3fe6fe8ecc712baf7fba7cf2f96fce8ce044f7b11bb17d921b81c411d097127` | `b60ab0cbab04cd58c41fc350e2027667bc5398bf96bd2da6552b97a54f9e74c4` (17) |
| `obsSeparatesDiverges_tight_notDiv` | counterexample `obs-refines-rejects-new-divergence`/`hNotDiv` | `propext` | `6d2f8a35e577ba68989c8bb38fdb193925000a7e87ecd1f6e59769d7af332f09` | `cdbbff8d452047628b1adb11b671a5a8d9d7c4eca9166e733a35aa9dfe7749ad` (17) |
| `obsSeparatesDiverges_sameTrace_nonvacuity` | non-vacuity `obs-refines-rejects-new-divergence` | `propext` | `344af828df2544344361624e1620027675f4ef804130016fbcef6435f972668c` | `1539def1a1be2e2a7361a42cb9c5f8bae81f41fa346ef010667b3dbaa585658f` (15) |
| `obsRefines_rejects_divergence_of_noDivergence` | companion `obs-refines-rejects-new-divergence` | (none) | `df8026378287bd7c1adcf420d73bb0eb3496f5226781682c1a0f54483fc8be75` | `11ba2a8e97653b3ee87b7a12274c5d98b31a64c8de8e92fa227793986aa36075` (13) |
| `closure_propInter_eq_iff_isSafety_and_machineClosed` | result `closure-inter-eq-iff-safety-and-machine-closed` | `Classical.choice`, `Quot.sound`, `propext` | `8913c624cb83b5f931ca66950f094b049ee3c41cb13a46cad19856445d9f4f32` | `171954d8d3f01c5d88a1f90dff15cef26fcf419bb3401f8dd05d4e38bbac428e` (8) |
| `closure_propInter_eq_iff_nonvacuity` | non-vacuity `closure-inter-eq-iff-safety-and-machine-closed` | `propext` | `4c611cd44c84a581d364b96b344ec445391e9de2703db5fdab171aae1f947a38` | `0d3a00f75ed4bdd76c2d82ce560b22fcc32a9635f95adbe494a6cdd35841e34d` (10) |
| `eventuallyTrue_tight_machineClosed_iff` | companion `closure-inter-eq-iff-safety-and-machine-closed` | `propext` | `7f4f55e3259342a936e6f1814ee6589bc02187978867d52f10d41547de27c67d` | `2812bde78e9efa34245709a85f601b5c0ef925d916345af236e49d5761a6e7f2` (9) |
| `machineClosed_iff_closure_propInter_eq_of_isSafety` | companion `closure-inter-eq-iff-safety-and-machine-closed` | `Classical.choice`, `Quot.sound`, `propext` | `ef8db63276d4f49d8688169aeff98f0fee404e4d62850533db42ea8864c73202` | `171954d8d3f01c5d88a1f90dff15cef26fcf419bb3401f8dd05d4e38bbac428e` (8) |
| `machineClosed_without_liveness_witness` | companion `closure-inter-eq-iff-safety-and-machine-closed` | `Classical.choice`, `Quot.sound`, `propext` | `a8c04b35aacf035f4f6128ce39698a95996208a6edf7fc65f43333965aff2e2f` | `9bd966f37f125596f827ba2814d0a042b18b97480f8a827d61ca352640200b59` (8) |
| `alpernSchneider_is_machineClosed` | result `alpern-schneider-machine-closed` | `Quot.sound`, `propext` | `acbb2a84da7035adc8569207a7fa4871e8ed864bb25cfff790369015310f506b` | `1b55c43d07c78ae25da75db454337a5ff459c460dab97d21ec9a86b30e3ad9dd` (7) |
| `alpernSchneider_is_machineClosed_nonvacuity` | non-vacuity `alpern-schneider-machine-closed` | `propext` | `a349977d7ac646c146b9ad4886244d7b5551d81ffcd14b23ae13e34ceb38663f` | `dfdfb241b55d18570e7ff1d1ee2cc4c68009509725c1ec0623e04dc75459da26` (7) |
| `nonMachineClosed_consistent_spec_counterexample` | companion `alpern-schneider-machine-closed`; result `non-machine-closed-consistent-spec`; non-vacuity `non-machine-closed-consistent-spec` | `Classical.choice`, `Quot.sound`, `propext` | `e39b6d1552fc778a1d019e7f3154382d8a847abd9fd69206f756bac13e550ff9` | `728054ebe48812b2b15f6b0806cd1c7ffc8f5b2ffddc480683b34638fa436a32` (12) |
| `closure_propInter_startsFalseStaysFalse_eventuallyTrue_eq_startsTrue` | companion `non-machine-closed-consistent-spec` | `Classical.choice`, `Quot.sound`, `propext` | `42b762e2b7ded7577f2de3b8d176cd1ede2fbd5526cba3597097c52eb55f7446` | `372adfe3083f632620026fbefc923ab49af033ae2280d003e95ed02cc280ceb0` (9) |
| `startsTrue_eventuallyFalse_machineClosed` | companion `non-machine-closed-consistent-spec` | `propext` | `8fd42666afede11b7da0a2c92bbba9fd40fcf44ec5eeb22b88d1a64a8222b846` | `db9cf7967d75c7d9e582b22b6aaf39ebbd1af6d35ae7022d7b7b14be75d97d2e` (6) |

### Primary sources

Bibliographic records with a DOI were checked against Crossref metadata (title, authors, venue, volume, issue, pages) on 2026-11-20:

- Bowen Alpern and Fred B. Schneider, "Defining Liveness", *Information Processing Letters* 21(4):181–185, 1985. DOI 10.1016/0020-0190(85)90056-0.
- Bowen Alpern and Fred B. Schneider, "Recognizing safety and liveness", *Distributed Computing* 2(3):117–126, 1987. DOI 10.1007/BF01782772.
- Bowen Alpern, Alan J. Demers, and Fred B. Schneider, "Safety without stuttering", *Information Processing Letters* 23(4):177–180, 1986. DOI 10.1016/0020-0190(86)90132-8.
- "Basic concepts", in M. Paul and H. J. Siegert (eds.), *Distributed Systems: Methods and Tools for Specification*, LNCS 190, pp. 7–43, Springer, 1985. DOI 10.1007/3-540-15216-4_12. The publisher's record lists no chapter authors; DBLP attributes the chapter to Mack W. Alford, Leslie Lamport, and Geoff P. Mullery, and Alpern and Schneider (1985) cite it as "L. Lamport, Basic concepts". This report therefore writes "Lamport (in Alford, Lamport, and Mullery, 1985)".
- Leslie Lamport, "Proving the Correctness of Multiprocess Programs", *IEEE Transactions on Software Engineering* SE-3(2):125–143, 1977. DOI 10.1109/TSE.1977.229904.
- Martín Abadi and Leslie Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991. DOI 10.1016/0304-3975(91)90224-P.
- Martín Abadi, Bowen Alpern, Krzysztof R. Apt, Nissim Francez, Shmuel Katz, Leslie Lamport, and Fred B. Schneider, "Preserving liveness: Comments on 'Safety and liveness from a methodological point of view'", *Information Processing Letters* 40(3):141–142, 1991. DOI 10.1016/0020-0190(91)90168-H.
- Frank Dederichs and Rainer Weber, "Safety and liveness from a methodological point of view", *Information Processing Letters* 36(1):25–30, 1990. DOI 10.1016/0020-0190(90)90181-V.
- Krzysztof R. Apt, Nissim Francez, and Shmuel Katz, "Appraising fairness in languages for distributed programming", *Distributed Computing* 2(4):226–241, 1988. DOI 10.1007/BF01872848.
- Thomas A. Henzinger, "Sooner is safer than later", *Information Processing Letters* 43(3):135–141, 1992. DOI 10.1016/0020-0190(92)90005-G.
- Martin Rem, "A Personal Perspective of the Alpern-Schneider Characterization of Safety and Liveness", in *Beauty Is Our Business*, Springer, 1990, pp. 365–372. DOI 10.1007/978-1-4612-4476-9_44.
- Panagiotis Manolios and Richard Trefler, "A lattice-theoretic characterization of safety and liveness", PODC 2003, pp. 325–333. DOI 10.1145/872035.872083.
- Stephen D. Brookes, C. A. R. Hoare, and A. W. Roscoe, "A Theory of Communicating Sequential Processes", *Journal of the ACM* 31(3):560–599, 1984. DOI 10.1145/828.833.
- Stephen D. Brookes and A. W. Roscoe, "An improved failures model for communicating processes", Seminar on Concurrency, LNCS 197, pp. 281–305, 1985. DOI 10.1007/3-540-15670-4_14.
- Xavier Leroy, "A Formally Verified Compiler Back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009. DOI 10.1007/s10817-009-9155-4.
- Xavier Leroy and Hervé Grall, "Coinductive big-step operational semantics", *Information and Computation* 207(2):284–304, 2009. DOI 10.1016/j.ic.2007.12.004.
- Daniel Patterson and Amal Ahmed, "The next 700 compiler correctness theorems (functional pearl)", *Proc. ACM Program. Lang.* 3(ICFP), 2019. DOI 10.1145/3341689.
- Li-yao Xia, Yannick Zakowski, Paul He, Chung-Kil Hur, Gregory Malecha, Benjamin C. Pierce, and Steve Zdancewic, "Interaction trees: representing recursive and impure programs in Coq", *Proc. ACM Program. Lang.* 4(POPL), 2020. DOI 10.1145/3371119.

Locators checked against the source text on 2026-11-20:

- Christel Baier and Joost-Pieter Katoen, *Principles of Model Checking*, MIT Press, 2008, ISBN 978-0-262-02649-9, Chapter 3: §3.2.4 "Trace Equivalence and Linear-Time Properties" contains Theorem 3.15 (Trace Inclusion and LT Properties); §3.3.2 "Safety Properties" contains Definition 3.26 (Prefix and Closure) and Lemma 3.27 (P is a safety property iff closure(P) = P); §3.3.3 "Trace Equivalence and Safety Properties" contains Theorem 3.28 (Finite Trace Inclusion and Safety Properties); §3.4.1 contains Definition 3.33 (Liveness Property: pref(P) = (2^AP)*); §3.4.2 "Safety vs. Liveness Properties" contains Lemma 3.35 (the only property that is both safety and liveness is (2^AP)^ω), Theorem 3.37 (Decomposition Theorem), and Lemma 3.38 (Sharpest Decomposition). §3.6 is the chapter summary.
- Isabelle Archive of Formal Proofs, development mirror `isabelle-prover/mirror-afp-devel` at commit `523cdc72b5ae4a91c9ab8e1025d4a30b40472720` (committed 2026-11-18): `thys/HOL-CSP/CSP_Refinements.thy` lines 163-166 state `leD_STOP`, `leT_STOP`, and `leDT_STOP` (`P ⊑ STOP` for every `P` in the `D`, `T`, and `DT` orders); `thys/HOL-CSP/CSP_Assertions.thy` lines 128-129 state `deadlock_free_mono_FD` (`deadlock_free P ⟹ P ⊑_FD Q ⟹ deadlock_free Q`); `thys/Topology/LList_Topology.thy` contains `itrace_top.infsafety_closed_iff` (line 422), `infliveness_empty` (line 441, `infliveness {} P ⟹ False`), and `itrace_top.alpern_schneider` (line 483, with assumption `A ≠ {}`); `thys/Lazy-Lists-II/LList2.thy` lines 1194-1198 define `infsafety` and `infliveness`; `thys/ConcurrentHOL/ex/Safety_Closure.thy` (theory `Safety_Closure`) states `tls.live.inf_safety_eq_top` at lines 257-259 (`tls.live ⊓ tls.safety.closed = {⊤}`), defines `tls.Safe P = tls.safety.cl P` (lines 329-330) and `tls.Live P = P ⊔ -tls.safety.cl P` (lines 332-333), and proves `tls.decomp` (`P = tls.Safe P ⊓ tls.Live P`, lines 335-337).
- CompCert, `common/Behaviors.v` (repository `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`, committed 2026-11-06), lines 41-45: `Inductive program_behavior` has constructors `Terminates : trace -> int -> program_behavior`, `Diverges : trace -> program_behavior`, `Reacts : traceinf -> program_behavior`, and `Goes_wrong : trace -> program_behavior`.
- Xavier Leroy, "A Formally Verified Compiler Back-end" (2009), checked against the arXiv version arXiv:0902.2137v3: §3.4 "Traces" defines behaviors `B ::= converges(t, n) | diverges(T) | goeswrong(t)`, with finite traces `t` and a coinductive finite-or-infinite trace `T`; it defines no constructor named `Reacts` and no type named `program_behavior`.

Cited by their published records but not re-checked against the source text for this report: C. A. R. Hoare, *Communicating Sequential Processes* (1985); A. W. Roscoe, *The Theory and Practice of Concurrency* (1997); Nancy A. Lynch, *Distributed Algorithms* (1996); Leslie Lamport, *Specifying Systems* (2002); Ekkart Kindler, "Safety and Liveness Properties: A Survey", *Bulletin of the EATCS* 53 (1994); the Archive of Formal Proofs entry TLA (Grov and Merz, 2011). Every prior-art entry in a card describes where the cited source treats the result; it is not a claim that the source uses this package's exact definitions.

Observation date: all evidence above (build, axiom audit, hashes, toolchain identity, and source checks) was acquired on 2026-11-20.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. No network
access is needed after the toolchain is installed.

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects
`sorry`/`admit`/`native_decide`/`axiom` in the sources, runs a generated Lean audit program that computes the axioms of every
library declaration with `collectAxioms`, and recomputes for every name referenced by `results.json` (and every name in
`audit/statements.json`) the statement hash and closure hash defined under **Evidence**, comparing them with
`audit/statements.json`. It prints `REVALIDATED` and exits 0 only if all checks pass. Its source states exactly what is
hashed (the `closure` function and the `type_repr`/`closure` fields of its audit program).

Manual alternative using only `lake`:

```sh
cd lean
lake build                              # builds library Toy; must report no errors and no warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every card-referenced declaration
```

`lean/RevalidationAudit.lean` lies outside the `Toy` library target, imports `Toy`, and contains one `#print axioms` line per
declaration referenced by `results.json`; every line must report only a subset of `propext`, `Classical.choice`,
`Quot.sound`. A passing run establishes only that these statements are kernel-checked under the pinned toolchain with the
recorded hashes; it says nothing about how well the toy definitions model a given real system (see **Applicability**).

To check one statement without the scripts, open `lean/Toy/SafetyLiveness/<File>.lean` and compare the theorem header with
the statement quoted under **Findings**; the statement hash changes if the header or any definition it depends on changes.
