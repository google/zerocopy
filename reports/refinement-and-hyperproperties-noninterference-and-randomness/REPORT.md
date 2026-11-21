# Refinement and Hyperproperties: Noninterference and Randomness

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

In an extensional single-trace-type model (`System Trace := Trace → Prop`), unconditional trace-inclusion refinement (`Refines S' S`, written `S' ⊑ S`) preserves, across all trace-inclusion transformations (including ones that delete arbitrary behaviors), **exactly** the subset-closed hyperproperties (`subsetClosed_iff_preservedByAllRefiningCompilers`, dualized at a fixed system pair by `refines_iff_preserves_all_subsetClosed`). This class includes lifted trace properties (`k = 1`), universal `k`-trace hyperproperties (`UniversalKHyperprop`), and single-step observational determinism (`ObsDet`, `k = 2`), at the specification cost that `ObsDet` forbids every low-observable nondeterminism (`obsDet_at_most_one_output`). By contrast, single-step generalized noninterference (`GNI`) fails under trace inclusion even when both systems are input-total and the refinement is deterministic (`gni_not_preserved_by_inputTotal_refinement`), and both possibilistic output surjectivity (`RangesOverAll`) and probabilistic min-entropy (`HasMinEntropyAtLeast`) collapse to zero diversity when a randomness source is modeled as internal system choice or abstracted to its support (`fullRange_const_refinement_not_rangesOverAll_of_pos`, `uniform_support_refined_by_const_loses_minEntropy_of_pos`). Moreover, equal supports fail to preserve min-entropy (`same_support_different_minEntropy`) and min-entropy is not a `Hyperprop` of the support (`minEntropy_not_a_hyperprop_of_support`); consequently (derived), no reflexive relation on possibilistic trace sets — including trace equivalence — preserves it.

Three preservation statements in this package — `TraceEquiv` (mutual trace inclusion), `SameDist` (equality of probability distributions, an equivalence relation), and input-total refinement of a deterministic source (`inputTotal_refinement_of_deterministic_eq`, which forces `S' = S`) — are equalities and admit **no proper refinement**. Within the single-step I/O model, filtering a system by a predicate on `(lowIn, lowOut)` (`lowViewRestrict S P`) yields a proper trace-inclusion refinement discipline that always preserves `GNI` (`gni_preserved_by_lowViewRestrict`), is exact among input-total `GNI` refinements (`inputTotal_gni_refinement_is_lowViewRestrict`), and is incomplete for partial refinements (for example, the secret-filtered `highFalseFullSystem`, `secretFiltered_refinement_preserves_gni_not_lowViewRestrict`). For choice-indexed presentations `SpecOf f`, requiring secret-dependent choice indices on the XOR presentation `out = xor highIn c` (`secretIndepDeterminize_fails_gni_on_xorPresentation`) is a property of the **presentation** `f`, not of the trace set `SpecOf f` or of the resulting implementation (`specOf_xor_eq_specOf_constLow`, `xor_gni_determinization_is_constant`, `same_secure_refinement_two_presentations`).

One-sentence summary of the 16 kernel-checked results (consult **Boundaries** first for scope limits, non-claims, and escape hatches):

1. **`subset-closed-iff-refinement-preserved` (`Toy.Hyper.subsetClosed_iff_preservedByAllRefiningCompilers`):** Over any trace type `Trace`, a hyperproperty `H` is subset-closed if and only if every semantic whole-program refining compiler `C` satisfying `C S ⊑ S` for all `S` — including transformations that delete arbitrary behaviors — preserves `H`.
2. **`refines-iff-preserves-all-subset-closed` (`Toy.Hyper.refines_iff_preserves_all_subsetClosed`):** Over any trace type `Trace`, system `S'` trace-refines `S` (`S' ⊑ S`) if and only if every subset-closed hyperproperty satisfied by `S` is also satisfied by `S'`.
3. **`trace-property-lift-subset-closed` (`Toy.Hyper.liftTraceProp_subsetClosed`):** For any trace property `P : Trace → Prop`, its hyperproperty lifting `LiftTraceProp P` (requiring every trace of `S` to satisfy `P`) is subset-closed (instance `k = 1` of `universalKHyperprop_subsetClosed`).
4. **`universal-k-hyperprop-subset-closed` (`Toy.Hyper.universalKHyperprop_subsetClosed`):** For any arity `k : Nat` and `k`-ary trace relation `Rel : (Fin k → Trace) → Prop`, the universal `k`-trace hyperproperty `UniversalKHyperprop k Rel` is subset-closed.
5. **`obs-det-preserved-by-refinement` (`Toy.Hyper.obsDet_preserved_by_refinement`):** For single-step `(lowIn, highIn, lowOut)` systems `S` and `S'`, if `S'` refines `S` (`Refines S' S`) and `S` is observationally deterministic (`ObsDet S`), then `S'` is observationally deterministic (`ObsDet S'`).
6. **`gni-refinement-paradox-input-total` (`Toy.Hyper.gni_not_preserved_by_inputTotal_refinement`):** Generalized noninterference is not preserved by trace-inclusion refinement even when both systems are input-total and the refinement is deterministic (`leakHighSystem` refines `fullIOSystem` on `IOTrace Unit Bool Bool` while violating `GNI`).
7. **`gni-preserved-by-low-view-restrict` (`Toy.Hyper.gni_preserved_by_lowViewRestrict`):** For any single-step system `S` satisfying `GNI` and any public-view predicate `P : L → O → Prop`, the trace-inclusion refinement `lowViewRestrict S P` also satisfies `GNI` (giving a sufficient class that is exact among input-total refinements, though partial refinements outside it — for example, the secret-filtered `highFalseFullSystem` — can also preserve `GNI`).
8. **`full-range-const-refinement-not-ranges-over-all` (`Toy.Hyper.fullRange_const_refinement_not_rangesOverAll_of_pos`):** For every `k > 0` and chosen output `v : Fin (2 ^ k)`, `FullRangeSystem k` satisfies `RangesOverAll (2 ^ k)` while its nonempty constant-output trace-inclusion refinement `ConstSystem k v` fails `RangesOverAll (2 ^ k)` when randomness is modeled as internal system choice.
9. **`uniform-support-const-refinement-loses-min-entropy` (`Toy.Hyper.uniform_support_refined_by_const_loses_minEntropy_of_pos`):** For every `k > 0`, `uniformDist k` over `Fin (2 ^ k)` has exact integer min-entropy `k`, whereas `constDist k` refines its support (`Refines (support (constDist k)) (support (uniformDist k))`), collapses to exact integer min-entropy `0`, and fails min-entropy `k`.
10. **`same-dist-preserves-min-entropy` (`Toy.Hyper.sameDist_preserves_minEntropy`):** For valid finite discrete distributions `d, d' : FinDist n` (using `d.valid` in the raw-table core `proportionalWeights_preserves_minEntropy_of_valid_source`), if `SameDist d' d` (equal probability distributions) and `HasMinEntropyAtLeast d k`, then `HasMinEntropyAtLeast d' k`.
11. **`xor-presentation-secret-indep-choice-fails-gni` (`Toy.Hyper.secretIndepDeterminize_fails_gni_on_xorPresentation`):** On the XOR choice presentation `xorSpecFn (_ h c => xor h c)` (whose trace set `SpecOf xorSpecFn` equals `fullIOSystem` and satisfies `GNI` and `InputTotal`), every secret-independent choice function `g : Unit → Bool` produces a deterministic input-total refinement violating `GNI`, even though the exact same trace set presented as `constLowSpecFn` admits a secret-independent `GNI` choice.
12. **`gni-and-det-iff-obs-det-and-rectangular-domain` (`Toy.Hyper.gni_and_deterministic_iff_obsDet_and_rectangularDomain`):** For any (possibly partial) single-step system `S`, `GNI S ∧ Deterministic S` holds if and only if `ObsDet S ∧ RectangularDomain S` holds (equivalently, under `Deterministic S`, `GNI S ↔ ObsDet S ∧ RectangularDomain S`).
13. **`gni-iff-obs-det-of-deterministic-input-total` (`Toy.Hyper.gni_iff_obsDet_of_deterministic_inputTotal`):** For any single-step system `S` that is both functionally deterministic (`Deterministic S`) and input-total (`InputTotal S`, or more weakly `AcceptanceIgnoresHigh S`), `GNI S` holds if and only if `ObsDet S` holds.
14. **`gni-of-fn-iff-secret-independent` (`Toy.Hyper.gni_ofFn_iff_secretIndependent`):** For any total single-step function `g : L → H → O`, its trace graph `ofFn g` satisfies `GNI` if and only if `g` ignores its secret argument (`SecretIndependent g`).
15. **`exists-input-total-gni-refinement-iff-exists-choice` (`Toy.Hyper.exists_inputTotal_gni_refinement_iff_exists_choice`):** For any choice presentation `f : L → H → C → O`, `SpecOf f` admits an input-total `GNI` refinement (deterministic or not) if and only if there exists a choice function `r : L → H → C` making the resolved output `fun l h => f l h (r l h)` secret-independent.
16. **`gni-input-total-spec-admits-det-gni-refinement` (`Toy.Hyper.gni_inputTotal_spec_admits_det_gni_refinement`):** For any choice presentation `f : L → H → C → O`, if `SpecOf f` satisfies `GNI` and `InputTotal` (`Nonempty (L → H → C)`), then there exists a choice function `r : L → H → C` such that `determinize f r` satisfies `GNI` (alongside `Refines`, `Deterministic`, and `InputTotal`).

See **Boundaries** for all non-claims, excluded stronger readings, and escape hatches before applying any result to a compiler, specification, or verification architecture.

## Applicability

### Model Fidelity and Subject Relationships

This package is a **self-contained toy formalization** (`namespace Toy.Hyper`, Lake library `ToyHyper` under `lean/`) rather than a mechanization over production compiler IR or language definitions. Of the subjects recorded in `REPORT.json`:

- **Toolchain subject (`leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`):** Directly executes and kernel-checks every definition, theorem, non-vacuity witness, tightness counterexample, positive control, and boundary lemma in `lean/ToyHyper/`. The Lake project declares zero external `[[require]]` dependencies (core Lean and `Std` only; **no Mathlib**), and every declaration uses at most the standard Lean axioms `{propext, Classical.choice, Quot.sound}`.
- **Literature and prior mechanization subjects (24 directly inspected entries):** Provide the mathematical definitions restated in `Toy.Hyper` (tier `T0`), the informal security/refinement concepts made precise in single-step form (tier `T1`), and the contrasting multi-step, contextual, constant-time, or probabilistic frameworks referenced in non-claims. Only artifacts whose technical content (full text, technical report, abstract/introduction, publisher overview/TOC, Coq source, or Archive of Formal Proofs entry page) was directly inspected are listed in `REPORT.json` `subjects`; an additional 11 historical references verified only through bibliographic metadata and attributions in inspected papers are recorded in **Evidence** prose and omitted from `REPORT.json`. None of the external Coq or Isabelle/HOL developments is imported as code; relationships are semantic comparisons documented per finding and in **Evidence**.

### Intended Modeling Scope and Known Fidelity Gaps

1. **Extensional trace sets, shared trace type, and unconditional trace inclusion (`ToyHyper.Core`):** A system is modeled as `System Trace := Trace → Prop`, a trace property as `TraceProp Trace := Trace → Prop`, a hyperproperty as `Hyperprop Trace := System Trace → Prop`, and refinement as `Refines S' S := ∀ t, S' t → S t` (`S' ⊑ S`).
   - *Shared-trace-type gap:* Source and target share one type `Trace`; cross-language trace relations between distinct source and target trace spaces (Abate et al., ESOP 2020 / TOPLAS 2021) and contextual linking against adversarial target contexts (`RSCHP` in Abate et al., CSF 2019) are not modeled.
   - *Unconditional-inclusion gap:* Real compiler correctness theorems typically guarantee trace inclusion only for source programs free of undefined behavior or under environmental assumptions; in this model, behaviors permitted when a side condition fails must already be represented inside the source trace set `S`.
   - *Arbitrary-deletion gap:* `RefiningCompiler C := ∀ S, Refines (C S) S` ranges over all subset-producing functions on `System Trace`, including non-computable maps and maps that erase all traces (`intersectCompiler`). Compilers additionally constrained to preserve input totality or liveness satisfy a narrower contract and preserve strictly more properties.
2. **Single-step information-flow traces and occurring-secret quantification (`ToyHyper.Noninterference`):** Security traces have type `IOTrace L H O := { lowIn : L, highIn : H, lowOut : O }` — a single public input, a single secret input, and a single public output, with **no high outputs**, **no multi-step interaction or scheduling**, **no infinite traces or finite-prefix Vietoris safety**, and **no timing, cache, or microarchitectural channels**.
   - *Occurring-secret quantification:* `ObsDet`, `GNI`, and `RectangularDomain` quantify over traces `t₁, t₂` satisfying `S t₁` and `S t₂`, and therefore only over secrets that actually occur in `S`. Consequently, rejecting a secret outright is never by itself a violation of `GNI` or `RectangularDomain` (**derived** from the definitions, not a package theorem: if `S` satisfies either predicate, so does its restriction `fun t => S t ∧ A t.highIn` for any `A : H → Prop`, because every trace the definition requires to exist carries the secret `t₁.highIn` of a trace that is already accepted). Proved instances accepting only `highIn = false`: `echoLowHighFalseSystem` satisfies both `GNI` and `RectangularDomain` (`Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`), and `highFalseFullSystem` satisfies `GNI` (`Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict`; **derived**: it also satisfies `RectangularDomain`, as does every system that accepts at most one secret value, since then `t₁.highIn = t₂.highIn` and `t₂` itself is the required trace). Rejecting some secrets does not, however, make a system satisfy either predicate: when the secret type has three or more values, a system can reject one secret outright and still leak, or jointly filter `(lowIn, highIn)`, among the secrets it still accepts (**derived**, not package theorems: on `IOTrace Unit Nat Nat`, `fun t => t.highIn < 2 ∧ t.lowOut = t.highIn` rejects every secret `≥ 2` and violates `GNI` at `t₁ = ⟨(), 0, 0⟩`, `t₂ = ⟨(), 1, 1⟩`, since no accepted trace has `highIn = 0` and `lowOut = 1`; on `IOTrace Bool Nat Bool`, `fun t => t.highIn < 2 ∧ (t.lowIn = true ↔ t.highIn = 1) ∧ t.lowOut = false` rejects secret `2` and violates `RectangularDomain` at `t₁ = ⟨false, 0, false⟩`, `t₂ = ⟨true, 1, false⟩`, since no trace with `lowIn = true` and `highIn = 0` is accepted). Neither predicate is termination- or acceptance-sensitive in the secret unless combined with `AcceptanceIgnoresHigh` or `InputTotal`.
   - *Single-step collapse of possibilistic taxonomy:* Because traces have one step and no high outputs, `GNI S` reduces to `∀ t₁ t₂, S t₁ → S t₂ → S ⟨t₂.lowIn, t₁.highIn, t₂.lowOut⟩` (`gni_iff_low_view_compatible_with_every_secret`). Distinctions among generalized noninterference, nondeducibility, noninference, and separability that arise in multi-step event systems (McLean 1994) do not appear here, nor does the multi-step CSP gap between McCullough's generalized noninterference and classical noninterference on deterministic state machines proved in Noce (AFP 2014).
3. **Terminology for determinization and choice presentations (`ToyHyper.Determinization`):** Throughout this package, **determinization** means **resolving nondeterminism** by fixing one output per input (`determinize f r := ofFn (fun l h => f l h (r l h))`, shrinking the trace set), also called a scheduler, strategy, or Skolem/uniformization function — **not** the automata-theoretic subset construction (which preserves the language/trace set). A choice presentation `f : L → H → C → O` induces trace set `SpecOf f`, and distinct presentations (`xorSpecFn` vs. `constLowSpecFn`) can induce the exact same trace set while behaving differently under secret-independent choice functions `g : L → C`.
4. **Finite `Nat`-weighted distributions and randomness modeling (`ToyHyper.Randomness`):** Finite discrete probability distributions over `Fin n` are modeled by `FinDist n := { weight : Fin n → Nat, valid : 0 < sumFin weight }`, representing outcome probabilities `weight x / sumFin weight` without real numbers (`FinDist 0` is uninhabited). Min-entropy `H_∞(d) ≥ k` is formalized in exact `Nat` arithmetic as `HasMinEntropyAtLeast d k := maxWeight d * 2 ^ k ≤ totalWeight d` (with raw-table counterpart `RawMinEnt w k := maxFin w * 2 ^ k ≤ sumFin w`). Here **"exact integer min-entropy `k`"** means `HasMinEntropyAtLeast d k ∧ ¬ HasMinEntropyAtLeast d (k + 1)` (for `uniformDist k` and `constDist k`, the real-valued Rényi min-entropy equals `k` and `0` respectively). `SameDist d' d` is cross-multiplied proportionality `∀ x, d'.weight x * totalWeight d = d.weight x * totalWeight d'`, which is an **equivalence relation** on `FinDist n`, not a refinement order.
   - *Randomness modeling gap:* The collapse counterexamples (`fullRange_const_refinement_not_rangesOverAll_of_pos` and `uniform_support_refined_by_const_loses_minEntropy_of_pos`) apply **only** when randomness is modeled as internal demonic choice of the system or when a probabilistic semantics is coarsened to its possibilistic support `support d` before taking trace inclusion. They do not apply when random bits are modeled as external environment inputs under an input-total contract or when compiler correctness preserves probability distributions.

## Findings

### Core Definitions and Proved Examples

Every core definition in `ToyHyper` is paired with kernel-checked positive and negative example theorems confirming that it admits intended instances and rejects unintended ones.

`Basis: source + execution (Lean kernel check)`

#### Module `ToyHyper.Core` (`lean/ToyHyper/Core.lean`)

```lean
abbrev System (Trace : Type u) : Type u := Trace → Prop
abbrev TraceProp (Trace : Type u) : Type u := Trace → Prop
abbrev Hyperprop (Trace : Type u) : Type u := System Trace → Prop

def Refines {Trace : Type u} (S' S : System Trace) : Prop :=
  ∀ t, S' t → S t                                -- scoped notation: S' ⊑ S

def RefiningCompiler {Trace : Type u} (C : System Trace → System Trace) : Prop :=
  ∀ S, Refines (C S) S

def SubsetClosed {Trace : Type u} (H : Hyperprop Trace) : Prop :=
  ∀ S S', (∀ t, S' t → S t) → H S → H S'

def PreservedByAllRefiningCompilers {Trace : Type u} (H : Hyperprop Trace) : Prop :=
  ∀ C : System Trace → System Trace, RefiningCompiler C → ∀ S, H S → H (C S)

def LiftTraceProp {Trace : Type u} (P : TraceProp Trace) : Hyperprop Trace :=
  fun S => ∀ t, S t → P t

def UniversalKHyperprop {Trace : Type u} (k : Nat)
    (Rel : (Fin k → Trace) → Prop) : Hyperprop Trace :=
  fun S => ∀ ts : Fin k → Trace, (∀ i : Fin k, S (ts i)) → Rel ts

def TraceEquiv {Trace : Type u} (S' S : System Trace) : Prop :=
  Refines S' S ∧ Refines S S'
```

| Definition | What It Captures | Positive Example (Proved) | Negative Example (Proved) |
| :--- | :--- | :--- | :--- |
| `Refines S' S` | Whole-program trace-inclusion refinement over a shared trace type. | `Toy.Hyper.refines_pos_example` (`constFalseBoolSystem ⊑ fullBoolSystem`) | `Toy.Hyper.refines_neg_example` (`¬ (fullBoolSystem ⊑ constFalseBoolSystem)`) |
| `RefiningCompiler C` | Semantic whole-program transformation shrinking every trace set (including arbitrary trace deletion). | `Toy.Hyper.refiningCompiler_pos_example` (`intersectCompiler S₀`) | `Toy.Hyper.refiningCompiler_neg_example` (`¬ RefiningCompiler constFullBoolCompiler`) |
| `SubsetClosed H` | Downward closure of hyperproperty `H` under trace-set inclusion. | `Toy.Hyper.subsetClosed_pos_example` (`LiftTraceProp (· = false)`) | `Toy.Hyper.subsetClosed_neg_example` (`¬ SubsetClosed (@NonEmptySystem Bool)`) |
| `PreservedByAllRefiningCompilers H` | Invariance of `H` across all semantic refining compilers `C`. | `Toy.Hyper.preservedByAllRefiningCompilers_pos_example` | `Toy.Hyper.preservedByAllRefiningCompilers_neg_example` |
| `LiftTraceProp P` | Standard lifting `[P]` requiring every trace of `S` to satisfy single-trace predicate `P`. | `Toy.Hyper.liftTraceProp_pos_example` | `Toy.Hyper.liftTraceProp_neg_example` |
| `UniversalKHyperprop k Rel` | Universal `k`-trace relational property `∀ t₁ … tₖ ∈ S, Rel t₁ … tₖ` over complete traces. | `Toy.Hyper.universalKHyperprop_pos_example` (`k = 2` equality on `constFalseBoolSystem`) | `Toy.Hyper.universalKHyperprop_neg_example` (`k = 2` equality on `fullBoolSystem`) |
| `TraceEquiv S' S` | Mutual trace inclusion (extensional equality of trace sets). | `Toy.Hyper.traceEquiv_pos_example` | `Toy.Hyper.traceEquiv_neg_example` |

#### Module `ToyHyper.Noninterference` (`lean/ToyHyper/Noninterference.lean`)

```lean
structure IOTrace (LowIn : Type u) (HighIn : Type v) (LowOut : Type w) where
  lowIn : LowIn
  highIn : HighIn
  lowOut : LowOut

def ofFn {L : Type u} {H : Type v} {O : Type w} (impl : L → H → O) :
    System (IOTrace L H O) :=
  fun t => t.lowOut = impl t.lowIn t.highIn

def ObsDet {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ → t₁.lowIn = t₂.lowIn → t₁.lowOut = t₂.lowOut

def GNI {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ →
    ∃ t₃, S t₃ ∧ t₃.highIn = t₁.highIn ∧ t₃.lowIn = t₂.lowIn ∧ t₃.lowOut = t₂.lowOut

def Deterministic {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ → t₁.lowIn = t₂.lowIn → t₁.highIn = t₂.highIn → t₁.lowOut = t₂.lowOut

def InputTotal {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ l h, ∃ o, S ⟨l, h, o⟩

def RectangularDomain {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ → ∃ o, S ⟨t₂.lowIn, t₁.highIn, o⟩

def AcceptanceIgnoresHigh {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) : Prop :=
  ∀ l h h', (∃ o, S ⟨l, h, o⟩) → ∃ o, S ⟨l, h', o⟩

def SecretIndependent {L : Type u} {H : Type v} {O : Type w} (f : L → H → O) : Prop :=
  ∀ l h₁ h₂, f l h₁ = f l h₂

def lowViewRestrict {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) (P : L → O → Prop) : System (IOTrace L H O) :=
  fun t => S t ∧ P t.lowIn t.lowOut
```

| Definition | What It Captures | Positive Example (Proved) | Negative Example (Proved) |
| :--- | :--- | :--- | :--- |
| `ofFn impl` | Total deterministic system graph induced by pure function `impl : L → H → O`. | `Toy.Hyper.ofFn_pos_example` | `Toy.Hyper.ofFn_neg_example` |
| `ObsDet S` | Single-step observational determinism: equal `lowIn` forces equal `lowOut` across all traces of `S`. | `Toy.Hyper.obsDet_pos_example` (`echoLowSystem`) | `Toy.Hyper.obsDet_neg_example` (`leakHighSystem`) |
| `GNI S` | Single-step generalized noninterference (McLean 1994 / Clarkson & Schneider 2010 Eq. (2.5)) over occurring traces of `S`. | `Toy.Hyper.gni_pos_example` (`fullIOSystem`) | `Toy.Hyper.gni_neg_example` (`leakHighSystem`) |
| `Deterministic S` | Functional determinism: `(lowIn, highIn)` uniquely determines `lowOut` within `S`. | `Toy.Hyper.deterministic_pos_example` (`leakHighSystem`) | `Toy.Hyper.deterministic_neg_example` (`fullIOSystem`) |
| `InputTotal S` | Every `(lowIn, highIn)` input pair has at least one output trace in `S`. | `Toy.Hyper.inputTotal_pos_example` (`leakHighSystem`) | `Toy.Hyper.inputTotal_neg_example` (`emptyIOSystem`) |
| `RectangularDomain S` | Accepted `(lowIn, highIn)` pairs form a Cartesian product (`rectangularDomain_iff_product`); excludes joint `(lowIn, highIn)` filtering but permits secret-only filtering. | `Toy.Hyper.rectangularDomain_pos_example` (`echoLowHighFalseSystem`, partial) | `Toy.Hyper.rectangularDomain_neg_example` (`diagonalPartialSystem`) |
| `AcceptanceIgnoresHigh S` | Secret-independent input acceptance: if `(l, h)` is accepted, `(l, h')` is accepted for every `h'`. | `Toy.Hyper.acceptanceIgnoresHigh_pos_example` (`echoLowOnlyLowFalseSystem`, partial) | `Toy.Hyper.acceptanceIgnoresHigh_neg_example` (`echoLowHighFalseSystem`) |
| `SecretIndependent f` | Pure function `f : L → H → O` produces identical outputs for all secrets `h₁, h₂`. | `Toy.Hyper.secretIndependent_pos_example` | `Toy.Hyper.secretIndependent_neg_example` |
| `lowViewRestrict S P` | Trace-inclusion refinement filtering `S` by a predicate `P` on `(lowIn, lowOut)`. | `Toy.Hyper.lowViewRestrict_pos_example` | `Toy.Hyper.lowViewRestrict_neg_example` |

#### Module `ToyHyper.Randomness` (`lean/ToyHyper/Randomness.lean`)

```lean
def sumFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, w => w 0 + sumFin (fun i => w i.succ)

def maxFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, w => Nat.max (w 0) (maxFin (fun i => w i.succ))

def ValidWeights {n : Nat} (w : Fin n → Nat) : Prop := 0 < sumFin w

def ProportionalWeights {n : Nat} (w' w : Fin n → Nat) : Prop :=
  ∀ x : Fin n, w' x * sumFin w = w x * sumFin w'

def RawMinEnt {n : Nat} (w : Fin n → Nat) (k : Nat) : Prop :=
  maxFin w * 2 ^ k ≤ sumFin w

structure FinDist (n : Nat) where
  weight : Fin n → Nat
  valid : ValidWeights weight

def totalWeight {n : Nat} (d : FinDist n) : Nat := sumFin d.weight
def maxWeight {n : Nat} (d : FinDist n) : Nat := maxFin d.weight
def support {n : Nat} (d : FinDist n) : System (Fin n) := fun x => 0 < d.weight x
def FullRangeSystem (k : Nat) : System (Fin (2 ^ k)) := fun _ => True
def ConstSystem (k : Nat) (v : Fin (2 ^ k)) : System (Fin (2 ^ k)) := fun x => x = v
def RangesOverAll (n : Nat) : Hyperprop (Fin n) := fun S => ∀ x : Fin n, S x
def HasMinEntropyAtLeast {n : Nat} (d : FinDist n) (k : Nat) : Prop :=
  maxWeight d * 2 ^ k ≤ totalWeight d
def SameDist {n : Nat} (d' d : FinDist n) : Prop :=
  ProportionalWeights d'.weight d.weight
```

| Definition | What It Captures | Positive Example (Proved) | Negative Example (Proved) |
| :--- | :--- | :--- | :--- |
| `ValidWeights w` | Positive total unnormalized weight (`0 < sumFin w`) ensuring well-defined finite probabilities. | `Toy.Hyper.validWeights_pos_example` | `Toy.Hyper.validWeights_neg_example` |
| `ProportionalWeights w' w` | Cross-multiplied proportionality on raw weight tables `Fin n → Nat`. | `Toy.Hyper.proportionalWeights_pos_example` | `Toy.Hyper.proportionalWeights_neg_example` |
| `RawMinEnt w k` | Unbundled exact-arithmetic min-entropy inequality `maxFin w * 2 ^ k ≤ sumFin w`. | `Toy.Hyper.rawMinEnt_pos_example` | `Toy.Hyper.rawMinEnt_neg_example` |
| `support d` | Possibilistic trace set of outcomes with strictly positive weight in `d : FinDist n`. | `Toy.Hyper.support_pos_example` | `Toy.Hyper.support_neg_example` |
| `RangesOverAll n` | Possibilistic output surjectivity onto `Fin n` (`∀ x, S x`). | `Toy.Hyper.rangesOverAll_pos_example` | `Toy.Hyper.rangesOverAll_neg_example` |
| `HasMinEntropyAtLeast d k` | Rényi min-entropy lower bound `H_∞(d) ≥ k` (`max_x Pr[d = x] ≤ 2^(-k)`) in exact `Nat` arithmetic. | `Toy.Hyper.hasMinEntropyAtLeast_pos_example` | `Toy.Hyper.hasMinEntropyAtLeast_neg_example` |
| `SameDist d' d` | Equality of probability distributions over `FinDist n` (an equivalence relation invariant under weight scaling). | `Toy.Hyper.sameDist_pos_example` (`scaledUniformDist 1` vs. `uniformDist 1`) | `Toy.Hyper.sameDist_neg_example` (`constDist 1` vs. `uniformDist 1`) |

#### Module `ToyHyper.Determinization` (`lean/ToyHyper/Determinization.lean`)

```lean
def SpecOf {L : Type u} {H : Type v} {C : Type w} {O : Type z}
    (f : L → H → C → O) : System (IOTrace L H O) :=
  fun t => ∃ c : C, t.lowOut = f t.lowIn t.highIn c

def determinize {L : Type u} {H : Type v} {C : Type w} {O : Type z}
    (f : L → H → C → O) (r : L → H → C) : System (IOTrace L H O) :=
  ofFn (fun l h => f l h (r l h))

def secretIndepDeterminize {L : Type u} {H : Type v} {C : Type w} {O : Type z}
    (f : L → H → C → O) (g : L → C) : System (IOTrace L H O) :=
  determinize f (fun l _ => g l)
```

| Definition | What It Captures | Positive Example (Proved) | Negative Example (Proved) |
| :--- | :--- | :--- | :--- |
| `SpecOf f` | Nondeterministic trace-set specification generated by choice-indexed presentation `f : L → H → C → O`. | `Toy.Hyper.specOf_pos_example` (`xorSpecFn`) | `Toy.Hyper.specOf_neg_example` (`leakSpecFn`) |
| `determinize f r` | Resolution of choice parameter `c` via a (possibly secret-dependent) strategy `r : L → H → C`. | `Toy.Hyper.determinize_pos_example` | `Toy.Hyper.determinize_neg_example` |
| `secretIndepDeterminize f g` | Resolution of choice parameter `c` via a public-only choice function `g : L → C`. | `Toy.Hyper.secretIndepDeterminize_pos_example` | `Toy.Hyper.secretIndepDeterminize_neg_example` |

#### Concrete Witness Systems, Presentations, and Distributions

Every concrete system, compiler, hyperproperty, choice presentation, and finite distribution referenced in the result cards, hypothesis ledgers, and non-claims is defined below. Rows for systems, compilers, hyperproperties, and choice-presentation functions quote the definition from `lean/ToyHyper/` verbatim (line breaks joined). Distribution rows quote the `def` signature and the `weight` field verbatim but omit the `valid` field (the proof that the total weight is strictly positive, `ValidWeights`); the `constDist` row quotes its full definition. The parenthetical notes after the distribution entries (totals, maxima, weight lists, point-mass descriptions) are annotations, not Lean text:

| Witness (`Toy.Hyper.*`) | Module | Lean Definition |
| :--- | :--- | :--- |
| `constFalseBoolSystem` | `Core` | `def constFalseBoolSystem : System Bool := fun b => b = false` |
| `fullBoolSystem` | `Core` | `def fullBoolSystem : System Bool := fun _ => True` |
| `intersectCompiler` | `Core` | `def intersectCompiler {Trace : Type u} (S₀ : System Trace) : System Trace → System Trace := fun S t => S t ∧ S₀ t` |
| `constFullBoolCompiler` | `Core` | `def constFullBoolCompiler : System Bool → System Bool := fun _ => fullBoolSystem` |
| `NonEmptySystem` | `Core` | `def NonEmptySystem {Trace : Type u} : Hyperprop Trace := fun S => ∃ t, S t` |
| `BoundedNatSystem` | `Core` | `def BoundedNatSystem : Hyperprop Nat := fun S => ∃ N : Nat, ∀ n : Nat, S n → n < N` |
| `echoLowSystem` | `Noninterference` | `def echoLowSystem : System (IOTrace Bool Bool Bool) := ofFn (fun l _ => l)` |
| `echoLowHighFalseSystem` | `Noninterference` | `def echoLowHighFalseSystem : System (IOTrace Bool Bool Bool) := fun t => t.lowOut = t.lowIn ∧ t.highIn = false` |
| `echoLowOnlyLowFalseSystem` | `Noninterference` | `def echoLowOnlyLowFalseSystem : System (IOTrace Bool Bool Bool) := fun t => t.lowIn = false ∧ t.lowOut = false` |
| `fullIOSystem` | `Noninterference` | `def fullIOSystem : System (IOTrace Unit Bool Bool) := fun _ => True` |
| `leakHighSystem` | `Noninterference` | `def leakHighSystem : System (IOTrace Unit Bool Bool) := ofFn (fun _ h => h)` |
| `constFalseIOSystem` | `Noninterference` | `def constFalseIOSystem : System (IOTrace Unit Bool Bool) := ofFn (fun _ _ => false)` |
| `emptyIOSystem` | `Noninterference` | `def emptyIOSystem : System (IOTrace Unit Bool Bool) := fun _ => False` |
| `diagonalPartialSystem` | `Noninterference` | `def diagonalPartialSystem : System (IOTrace Bool Bool Bool) := fun t => t.lowIn = t.highIn ∧ t.lowOut = false` |
| `highFalseFullSystem` | `Noninterference` | `def highFalseFullSystem : System (IOTrace Unit Bool Bool) := fun t => t.highIn = false` |
| `uniformDist` | `Randomness` | `def uniformDist (k : Nat) : FinDist (2 ^ k)` with `weight := fun _ => 1` (total `2 ^ k`, max `1`) |
| `scaledUniformDist` | `Randomness` | `def scaledUniformDist (k : Nat) : FinDist (2 ^ k)` with `weight := fun _ => 2` (total `2 ^ k * 2`, max `2`) |
| `pointDist` | `Randomness` | `def pointDist {n : Nat} (v : Fin n) : FinDist n` with `weight := fun x => if x = v then 1 else 0` (total `1`, max `1`) |
| `constDist` | `Randomness` | `def constDist (k : Nat) : FinDist (2 ^ k) := pointDist ⟨0, two_pow_pos k⟩` (point mass `1` at `0`, `0` elsewhere) |
| `skewedFullSupportDist` | `Randomness` | `def skewedFullSupportDist : FinDist (2 ^ 1)` with `weight := fun i => if i.val = 0 then 3 else 1` (weights `(3, 1)`) |
| `dist211` | `Randomness` | `def dist211 : FinDist 3` with `weight := fun i => if i.val = 0 then 2 else 1` (weights `(2, 1, 1)`) |
| `dist110` | `Randomness` | `def dist110 : FinDist 3` with `weight := fun i => if i.val = 2 then 0 else 1` (weights `(1, 1, 0)`) |
| `xorSpecFn` | `Determinization` | `def xorSpecFn : Unit → Bool → Bool → Bool := fun _ h c => xor h c` |
| `leakSpecFn` | `Determinization` | `def leakSpecFn : Unit → Bool → Unit → Bool := fun _ h _ => h` |
| `constLowSpecFn` | `Determinization` | `def constLowSpecFn : Unit → Bool → Bool → Bool := fun _ _ c => c` |
| `falseOrHighFn` | `Determinization` | `def falseOrHighFn : Unit → Bool → Bool → Bool := fun _ h c => c && h` |
| `singleFalseTraceSystem` | `Determinization` | `def singleFalseTraceSystem : System (IOTrace Unit Bool Bool) := fun t => t = ⟨(), false, false⟩` |
| `emptyChoiceSpecFn` | `Determinization` | `def emptyChoiceSpecFn : Unit → Bool → Empty → Bool := fun _ _ c => c.elim` |

---

### Result Cards

#### 1. `subset-closed-iff-refinement-preserved` (`Toy.Hyper.subsetClosed_iff_preservedByAllRefiningCompilers`)

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation in compiler-quantified form; Clarkson and Schneider 2010 Section 2.6 characterizes subset-closure via satisfaction/refinement agreement law (2.8), while Abate et al. 2019 prove and mechanize in Coq the dual compiler-fixed criterion `RSCHP ↔ RSCHC`) | **Depth:** `definitional`
- **Plain claim:** For any trace type `Trace` and hyperproperty `H` over `System Trace`, `H` is subset-closed if and only if every semantic whole-program refining compiler (`C : System Trace → System Trace` satisfying `C S ⊑ S` for all `S`, including transformations that delete arbitrary behaviors) preserves `H`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Core.lean:218-220
  theorem subsetClosed_iff_preservedByAllRefiningCompilers
      {Trace : Type u} (H : Hyperprop Trace) :
      SubsetClosed H ↔ PreservedByAllRefiningCompilers H
  -- Unfolded:
  -- (∀ S S' : Trace → Prop, (∀ t, S' t → S t) → H S → H S') ↔
  -- (∀ C : (Trace → Prop) → (Trace → Prop),
  --   (∀ S t, C S t → S t) → ∀ S, H S → H (C S))
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `Trace : Type u` and `H : Hyperprop Trace`).
- **Non-vacuity witness:** `Toy.Hyper.subsetClosed_char_nonvacuity` — on `Trace = Bool`, `LiftTraceProp (fun b => b = false)` is subset-closed, accepts `constFalseBoolSystem`, and rejects `fullBoolSystem`, while `NonEmptySystem` is not subset-closed.
- **Key non-claims (full list in Boundaries):** The reverse direction instantiates `C := intersectCompiler S'` (`C S = S ∩ S'`), which may delete arbitrary traces (including all traces) and need not be computable (`propext` + `funext`); compilers additionally required to preserve input totality preserve strictly more properties (derived: `InputTotal` itself is not subset-closed because `emptyIOSystem ⊑ fullIOSystem` with `InputTotal fullIOSystem` and `¬ InputTotal emptyIOSystem` by `Toy.Hyper.inputTotal_neg_example`, yet `InputTotal` is tautologically preserved by input-totality-preserving compilers; and on a deterministic input-total source they preserve *every* hyperproperty via `Toy.Hyper.inputTotal_refinement_of_deterministic_eq`).
- **Prior art:** Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 2.6; CSF 2008 `10.1109/CSF.2008.7`); Abate et al., IEEE CSF 2019 (`10.1109/CSF.2019.00025`, `arXiv:1807.04603v6` Section 3.2 and Appendix C.2.2 Theorem C.18, Coq `Properties.v`: `SSC_iff`, `Criteria.v`: `RSCHC_RSCHP`); Abate et al., ESOP 2020 / *ACM TOPLAS* 2021 (`10.1007/978-3-030-44914-8_1`, `10.1145/3460860`); related Isabelle/HOL hyperproperty logics (not subset-closure under refinement): Rabe, Lammich, and Popescu, AFP 2014 (`HyperCTL`); Dardinier and Müller, AFP 2023 / PLDI 2024 (`10.1145/3656437`).
- **Design question:** Which security properties automatically survive a compiler proved correct purely via trace-inclusion refinement?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.subsetClosed_iff_preservedByAllRefiningCompilers` and `Toy.Hyper.subsetClosed_char_nonvacuity`.
- `Basis: derived (modeling bridge)` — Applies to whole-program compilation over a shared trace model only insofar as the compiler correctness theorem places no restriction on which source traces may be eliminated; if the compiler must preserve termination/totality per input or links against target contexts, the quantification over `RefiningCompiler` is strictly broader than the real compiler class.

#### 2. `refines-iff-preserves-all-subset-closed` (`Toy.Hyper.refines_iff_preserves_all_subsetClosed`)

- **Kind:** `characterization` | **Tier:** `T0` (whole-program, context-free counterpart of `RSCHP ↔ RSCHC` in Abate et al., CSF 2019) | **Depth:** `definitional`
- **Plain claim:** For any trace type `Trace` and systems `S'`, `S : System Trace`, `S'` refines `S` (`Refines S' S`) if and only if every subset-closed hyperproperty satisfied by `S` is also satisfied by `S'`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Core.lean:247-249
  theorem refines_iff_preserves_all_subsetClosed
      {Trace : Type u} (S' S : System Trace) :
      Refines S' S ↔ ∀ H : Hyperprop Trace, SubsetClosed H → H S → H S'
  -- Unfolded:
  -- (∀ t, S' t → S t) ↔
  -- (∀ H : (Trace → Prop) → Prop,
  --   (∀ A B, (∀ t, B t → A t) → H A → H B) → H S → H S')
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `Trace`, `S'`, and `S`; the reverse direction instantiates `H := fun X => Refines X S`).
- **Non-vacuity witness:** `Toy.Hyper.refines_iff_preserves_all_subsetClosed_nonvacuity` — on `Bool`, `(constFalseBoolSystem, fullBoolSystem)` satisfies both sides, while `(fullBoolSystem, constFalseBoolSystem)` refutes both sides via `LiftTraceProp (fun b => b = false)`.
- **Key non-claims (full list in Boundaries):** Characterizes preservation of the *entire class* of subset-closed hyperproperties at a single whole-program pair `(S', S)`; does not characterize preservation of any individual non-subset-closed hyperproperty (such as `GNI`) and does not model contextual linking or cross-language trace relations.
- **Prior art:** Abate et al., IEEE CSF 2019 (`10.1109/CSF.2019.00025`, `arXiv:1807.04603v6` Section 3.2 and Appendix C.2.2 Theorem C.18); Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 2.6).
- **Design question:** What semantic correctness relation between compiled and source trace sets is both necessary and sufficient to preserve every subset-closed hyperproperty?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.refines_iff_preserves_all_subsetClosed` and `Toy.Hyper.refines_iff_preserves_all_subsetClosed_nonvacuity`.
- `Basis: derived (modeling bridge)` — Shows that in a single-language whole-program semantics, preserving all subset-closed hyperproperties requires nothing stronger (and permits nothing weaker) than ordinary trace inclusion `S' ⊑ S`, provided source undefined-behavior exclusions are already baked into `S`.

#### 3. `trace-property-lift-subset-closed` (`Toy.Hyper.liftTraceProp_subsetClosed`)

- **Kind:** `theorem` | **Tier:** `T0` (standard lifting lemma from Clarkson and Schneider 2010 Section 2.6; mechanized in Coq in Abate et al. 2019 `Properties.v`) | **Depth:** `definitional`
- **Plain claim:** For any trace type `Trace` and trace property `P : Trace → Prop`, its hyperproperty lifting `LiftTraceProp P` (requiring every trace of `S` to satisfy `P`) is subset-closed (corollary of `universalKHyperprop_subsetClosed` at `k = 1` via `liftTraceProp_iff_universal1Hyperprop`).
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Core.lean:274-276
  theorem liftTraceProp_subsetClosed
      {Trace : Type u} (P : TraceProp Trace) :
      SubsetClosed (LiftTraceProp P)
  -- Unfolded:
  -- ∀ S S' : Trace → Prop, (∀ t, S' t → S t) → (∀ t, S t → P t) → (∀ t, S' t → P t)
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `Trace` and `P`).
- **Non-vacuity witness:** `Toy.Hyper.liftTraceProp_subsetClosed_nonvacuity` — on `Bool`, `LiftTraceProp (fun b => b = false)` accepts `constFalseBoolSystem` and rejects `fullBoolSystem`.
- **Key non-claims (full list in Boundaries):** Special case `k = 1` of `universalKHyperprop_subsetClosed` (`Toy.Hyper.liftTraceProp_iff_universal1Hyperprop`); not every subset-closed hyperproperty is a lifted single-trace property (`ObsDet` over `IOTrace Unit Unit Bool` is a 2-trace counterexample, `Toy.Hyper.obsDet_not_liftTraceProp`).
- **Prior art:** Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 2.6); Abate et al., IEEE CSF 2019 (`10.1109/CSF.2019.00025`, Section 3.2, Coq `Properties.v`: `lifting`, `Union_Lift_SSC`).
- **Design question:** Which security properties automatically survive a compiler proved correct purely via trace-inclusion refinement?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.liftTraceProp_subsetClosed`, `Toy.Hyper.liftTraceProp_subsetClosed_nonvacuity`, `Toy.Hyper.liftTraceProp_iff_universal1Hyperprop`, and `Toy.Hyper.obsDet_not_liftTraceProp`.
- `Basis: derived (modeling bridge)` — Any single-execution safety or trace-invariant requirement expressible as `∀ t ∈ S, P t` over shared observable traces transfers from `S` to `S'` under `S' ⊑ S`; multi-execution confidentiality and liveness properties cannot be written in this form.

#### 4. `universal-k-hyperprop-subset-closed` (`Toy.Hyper.universalKHyperprop_subsetClosed`)

- **Kind:** `theorem` | **Tier:** `T0` (subset-closure of universal `k`-trace hyperproperties; Clarkson and Schneider 2010, Mastroeni and Pasqua 2018, Coq `k = 2` mechanization in Abate et al. 2019) | **Depth:** `definitional`
- **Plain claim:** For any trace type `Trace`, arity `k : Nat`, and `k`-ary trace relation `Rel : (Fin k → Trace) → Prop`, the universal `k`-trace hyperproperty `UniversalKHyperprop k Rel` is subset-closed.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Core.lean:288-290
  theorem universalKHyperprop_subsetClosed
      {Trace : Type u} (k : Nat) (Rel : (Fin k → Trace) → Prop) :
      SubsetClosed (UniversalKHyperprop k Rel)
  -- Unfolded:
  -- ∀ S S' : Trace → Prop, (∀ t, S' t → S t) →
  --   (∀ ts : Fin k → Trace, (∀ i, S (ts i)) → Rel ts) →
  --   (∀ ts : Fin k → Trace, (∀ i, S' (ts i)) → Rel ts)
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `Trace`, `k`, and `Rel`).
- **Non-vacuity witness:** `Toy.Hyper.universalKHyperprop_subsetClosed_nonvacuity` — on `Bool`, `UniversalKHyperprop 2 (fun ts => ts 0 = ts 1)` accepts `constFalseBoolSystem` and rejects `fullBoolSystem`.
- **Key non-claims (full list in Boundaries):** Not every subset-closed hyperproperty has the form `UniversalKHyperprop k Rel` for a finite `k`: over `Nat`, `BoundedNatSystem` (`∃ N, ∀ n, S n → n < N`) is subset-closed yet equals no `UniversalKHyperprop k Rel` (`Toy.Hyper.boundedNatSystem_subsetClosed_not_universalKHyperprop`). Does not formalize topological finite-prefix `k`-hypersafety over infinite traces or `∀∃` policies such as `GNI`.
- **Prior art:** Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 3 Theorem 1 `SHP ⊂ SSC` and Section 4); Terauchi and Aiken, SAS 2005 (`10.1007/11547662_24`, 2-safety); Mastroeni and Pasqua, SAS 2018 (`10.1007/978-3-319-99725-4_17`); Abate et al., IEEE CSF 2019 (`10.1109/CSF.2019.00025`, Coq `Properties.v`: `twoSC_SSC`); Barthe, D'Argenio, and Rezk, CSFW 2004 / *MSCS* 2011 (`10.1109/CSFW.2004.1310735`, legacy IEEE CS DOI `10.1109/CSFW.2004.17`; journal `10.1017/S0960129511000193`, background on self-composition).
- **Design question:** Which security properties automatically survive a compiler proved correct purely via trace-inclusion refinement?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.universalKHyperprop_subsetClosed`, `Toy.Hyper.universalKHyperprop_subsetClosed_nonvacuity`, and `Toy.Hyper.boundedNatSystem_subsetClosed_not_universalKHyperprop`.
- `Basis: derived (modeling bridge)` — Any `k`-safety-style policy stated purely by universal quantification over `k` complete traces of the same trace type (such as deterministic noninterference or constant-time equality when cycle/leakage observations are explicitly part of `Trace`) survives trace-inclusion compilation; if timing or cache observations are absent from `Trace`, `UniversalKHyperprop` over I/O traces will not protect them.

#### 5. `obs-det-preserved-by-refinement` (`Toy.Hyper.obsDet_preserved_by_refinement`)

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation of refinement preservation for observational determinism; Clarkson and Schneider 2010 Section 2.6, Roscoe 1995 Section 8.1, Zdancewic and Myers 2003) | **Depth:** `definitional`
- **Plain claim:** For any trace types `L`, `H`, `O` and systems `S`, `S'` over `IOTrace L H O`, if `S'` refines `S` (`Refines S' S`) and `S` is observationally deterministic (`ObsDet S`), then `S'` is observationally deterministic (`ObsDet S'`) (corollary of `universalKHyperprop_subsetClosed` at `k = 2` via `obsDet_iff_universal2Hyperprop`).
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Noninterference.lean:492-496
  theorem obsDet_preserved_by_refinement
      {L : Type u} {H : Type v} {O : Type w}
      {S S' : System (IOTrace L H O)}
      (hRef : Refines S' S) (hOD : ObsDet S) :
      ObsDet S'
  -- Unfolded:
  -- (∀ t, S' t → S t) →
  -- (∀ t₁ t₂, S t₁ → S t₂ → t₁.lowIn = t₂.lowIn → t₁.lowOut = t₂.lowOut) →
  -- (∀ t₁ t₂, S' t₁ → S' t₂ → t₁.lowIn = t₂.lowIn → t₁.lowOut = t₂.lowOut)
  ```
- **Hypothesis ledger:**
  - `hRef : Refines S' S` — requires every trace of `S'` to lie in `S` so `ObsDet S` constrains all trace pairs of `S'`. Tightness: `tight: counterexample Toy.Hyper.obsDet_refinement_counterexample_no_refines` (`ObsDet constFalseIOSystem ∧ ¬ Refines leakHighSystem constFalseIOSystem ∧ ¬ ObsDet leakHighSystem`).
  - `hOD : ObsDet S` — requires the source system to satisfy observational determinism. Tightness: `tight: counterexample Toy.Hyper.obsDet_refinement_counterexample_no_obsDet` (`Refines leakHighSystem fullIOSystem ∧ ¬ ObsDet fullIOSystem ∧ ¬ ObsDet leakHighSystem`).
- **Non-vacuity witness:** `Toy.Hyper.obsDet_refinement_nonvacuity` — `echoLowHighFalseSystem` strictly refines `echoLowSystem`, and `echoLowSystem` satisfies `ObsDet`.
- **Key non-claims (full list in Boundaries):** `ObsDet` forbids **every** low-observable nondeterminism, including secret-independent random outputs (`Toy.Hyper.obsDet_at_most_one_output`), and does **not** prevent termination/acceptance leaks (`echoLowHighFalseSystem` accepts only `highIn = false` yet satisfies `ObsDet`).
- **Prior art:** Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 2.6); Roscoe, IEEE S&P 1995 (`10.1109/SECPRI.1995.398927`, Section 8.1); McLean, *JCS* 1992 (`10.3233/JCS-1992-1103`); Zdancewic and Myers, CSFW 2003 (`10.1109/CSFW.2003.1212703`); Murray et al., IEEE S&P 2013 (`10.1109/SP.2013.35`) and Costanzo, Shao, and Gu, PLDI 2016 (`10.1145/2908080.2908100`, documenting the specification cost of eliminating user-visible nondeterminism); Barthe et al., *PACMPL* (POPL) 2020 (`10.1145/3371075`, cited in non-claims for constant-time compilation).
- **Design question:** Which security properties automatically survive a compiler proved correct purely via trace-inclusion refinement, and at what cost to allowed nondeterminism?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.obsDet_preserved_by_refinement`, `Toy.Hyper.obsDet_refinement_nonvacuity`, `Toy.Hyper.obsDet_refinement_counterexample_no_refines`, `Toy.Hyper.obsDet_refinement_counterexample_no_obsDet`, `Toy.Hyper.obsDet_iff_universal2Hyperprop`, and `Toy.Hyper.obsDet_at_most_one_output`.
- `Basis: derived (modeling bridge)` — Adopting `ObsDet` at the specification boundary buys automatic preservation across trace-inclusion passes only by banishing all public output nondeterminism from specifications (matching the engineering trade-off reported in seL4 and CertiKOS) and still requires separate totality/termination and side-channel obligations (in particular, `ObsDet` implies `GNI` only when the target also maintains a rectangular acceptance domain such as `InputTotal` or `AcceptanceIgnoresHigh`; see Cards 12–13).

#### 6. `gni-refinement-paradox-input-total` (`Toy.Hyper.gni_not_preserved_by_inputTotal_refinement`)

- **Kind:** `counterexample` | **Tier:** `T0` (re-derivation of the refinement paradox for generalized noninterference; Clarkson and Schneider 2010 Sections 1 & 3, Zdancewic and Myers 2003, McLean 1994, Jacob 1988/1989) | **Depth:** `shallow`
- **Plain claim:** Generalized noninterference is not preserved by trace-inclusion refinement even when both systems are input-total and the refinement is deterministic: on `IOTrace Unit Bool Bool`, `fullIOSystem` satisfies `GNI` and `InputTotal`, `leakHighSystem` refines `fullIOSystem` and satisfies `InputTotal` and `Deterministic`, yet `leakHighSystem` violates `GNI`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Noninterference.lean:548-554
  theorem gni_not_preserved_by_inputTotal_refinement :
      GNI fullIOSystem ∧
      InputTotal fullIOSystem ∧
      Refines leakHighSystem fullIOSystem ∧
      InputTotal leakHighSystem ∧
      Deterministic leakHighSystem ∧
      ¬ GNI leakHighSystem
  -- Where:
  --   fullIOSystem   : System (IOTrace Unit Bool Bool) := fun _ => True
  --   leakHighSystem : System (IOTrace Unit Bool Bool) := fun t => t.lowOut = t.highIn
  -- Immediate corollary: Toy.Hyper.gni_not_subsetClosed : ¬ SubsetClosed (@GNI Unit Bool Bool)
  ```
- **Hypothesis ledger:** None (concrete witnessed counterexample).
- **Non-vacuity witness:** `Toy.Hyper.gni_not_preserved_by_inputTotal_refinement` (directly exhibits the concrete witness pair `(fullIOSystem, leakHighSystem)`).
- **Positive control:** `Toy.Hyper.gni_preserved_by_lowViewRestrict` and `Toy.Hyper.lowViewRestrict_proper_gni_control_instance` — restricting any `GNI` system by a predicate `P : L → O → Prop` on `(lowIn, lowOut)` preserves `GNI`; on `fullIOSystem`, `P _ o := (o = false)` produces `constFalseIOSystem`, a **proper**, input-total, deterministic refinement satisfying `GNI`. (By contrast, requiring `Deterministic S` on the source in `Toy.Hyper.gni_preserved_by_inputTotal_refinement_of_deterministic` is degenerate: `Toy.Hyper.inputTotal_refinement_of_deterministic_eq` proves `S' = S`, admitting no proper refinement.)
- **Key non-claims (full list in Boundaries):** Does **not** say every proper refinement of a `GNI` system violates `GNI`; does not treat secret-filtered acceptance as a leak (`Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`); does not formalize multi-step simulation refinements (Mantel 2001; Alur, Černý, and Zdancewic 2006; Attiya and Enea 2019).
- **Prior art:** Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Sections 1–3); Zdancewic and Myers, CSFW 2003 (`10.1109/CSFW.2003.1212703`); McCullough, IEEE S&P 1987 & 1988 (`10.1109/SP.1987.10009`, `10.1109/SECPRI.1988.8110`); Jacob, IEEE S&P 1988 & 1989 (`10.1109/SECPRI.1988.8094`, `10.1109/SECPRI.1989.36298`); Graham-Cumming and Sanders, CSFW 1991 (`10.1109/CSFW.1991.151567`); McLean, IEEE S&P 1994 / *TSE* 1996 (`10.1109/RISP.1994.296590`, `10.1109/32.481534`); Mantel, IEEE S&P 2001 (`10.1109/SECPRI.2001.924289`); Alur, Černý, and Zdancewic, ICALP 2006 (`10.1007/11787006_10`); Attiya and Enea, DISC 2019 (`10.4230/LIPIcs.DISC.2019.2`); Murray et al., IEEE S&P 2013 (`10.1109/SP.2013.35`) and Costanzo, Shao, and Gu, PLDI 2016 (`10.1145/2908080.2908100`).
- **Design question:** Does trace-inclusion refinement preserve possibilistic noninterference (`GNI`), and what stronger condition restores preservation?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_not_preserved_by_inputTotal_refinement`, `Toy.Hyper.gni_not_subsetClosed`, `Toy.Hyper.gni_preserved_by_lowViewRestrict`, `Toy.Hyper.lowViewRestrict_proper_gni_control_instance`, and `Toy.Hyper.inputTotal_refinement_of_deterministic_eq`.
- `Basis: derived (modeling bridge)` — Whenever an input-total `GNI` specification permits at least two distinct public outputs (`o₁ ≠ o₂`) for some public input `l` across at least two distinct secrets (`h₁ ≠ h₂`), an unannotated trace-inclusion compiler correctness theorem allows an input-total deterministic refinement to select `o₁` on `(l, h₁)` and `o₂` on `(l, h₂)` (correlating its public output with secret state, as `leakHighSystem` does), violating `GNI` even though both source and target terminate on every input. (Both premises are needed: with at most one secret value — e.g., `H = Unit` — every single-step system vacuously satisfies `GNI`.)

#### 7. `gni-preserved-by-low-view-restrict` (`Toy.Hyper.gni_preserved_by_lowViewRestrict`)

- **Kind:** `theorem` | **Tier:** `T1` (elementary consequence of the single-step definitions; no consulted source states it in this form) | **Depth:** `definitional`
- **Plain claim:** For any trace types `L`, `H`, `O`, system `S` over `IOTrace L H O`, and public-view predicate `P : L → O → Prop`, if `S` satisfies `GNI` then its trace-inclusion refinement `lowViewRestrict S P` (retaining traces `t` of `S` with `P t.lowIn t.lowOut`) also satisfies `GNI`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Noninterference.lean:572-576
  theorem gni_preserved_by_lowViewRestrict
      {L : Type u} {H : Type v} {O : Type w}
      {S : System (IOTrace L H O)} (P : L → O → Prop)
      (hGNI : GNI S) :
      GNI (lowViewRestrict S P)
  -- Unfolded:
  -- GNI S → GNI (fun t => S t ∧ P t.lowIn t.lowOut)
  ```
- **Hypothesis ledger:**
  - `hGNI : GNI S` — requires the source system `S` to satisfy `GNI` so any low view retained by `P` remains compatible with every occurring secret. Tightness: `tight: counterexample Toy.Hyper.gni_lowViewRestrict_counterexample_no_gni` (`¬ GNI leakHighSystem ∧ ¬ GNI (lowViewRestrict leakHighSystem (fun _ _ => True))`).
  - `P : L → O → Prop` — exposes the arbitrary predicate on `(lowIn, lowOut)` selecting retained traces. Tightness: `harmless`.
- **Non-vacuity witness:** `Toy.Hyper.lowViewRestrict_proper_gni_control_instance` — on `fullIOSystem` (`GNI`), `lowViewRestrict fullIOSystem (fun _ o => o = false)` equals `constFalseIOSystem`, a proper, input-total, deterministic `GNI` refinement.
- **Key non-claims (full list in Boundaries):** Gives a **sufficient class**, not a full characterization of all `GNI`-preserving refinements: among **input-total** refinements the class is exact (`Toy.Hyper.inputTotal_gni_refinement_is_lowViewRestrict`), whereas partial refinements outside it can also preserve `GNI` (`highFalseFullSystem` restricts `fullIOSystem` to `highIn = false`, preserves `GNI`, and equals `lowViewRestrict fullIOSystem P` for no `P`, `Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict`). Membership is a property of the **trace set**, not of how a choice was resolved (`determinize xorSpecFn (fun _ h => h)` consults `highIn` via its choice index yet lies in the class, `Toy.Hyper.same_secure_refinement_two_presentations`, `Toy.Hyper.lowViewRestrict_full_eq_constFalse`), and `lowViewRestrict` does not automatically preserve `InputTotal` (`Toy.Hyper.lowViewRestrict_need_not_preserve_inputTotal`).
- **Prior art:** Elementary consequence of the single-step definitions (tier `T1`: no consulted source states it in this form); related multi-step secrecy-preserving refinement frameworks (not formalized here): Mantel, IEEE S&P 2001 (`10.1109/SECPRI.2001.924289`); Alur, Černý, and Zdancewic, ICALP 2006 (`10.1007/11787006_10`); Attiya and Enea, DISC 2019 (`10.4230/LIPIcs.DISC.2019.2`).
- **Design question:** Which stronger (non-identity) refinement disciplines preserve generalized noninterference, and at what cost to the compilers they admit?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_preserved_by_lowViewRestrict`, `Toy.Hyper.lowViewRestrict_proper_gni_control_instance`, `Toy.Hyper.gni_lowViewRestrict_counterexample_no_gni`, `Toy.Hyper.lowViewRestrict_need_not_preserve_inputTotal`, `Toy.Hyper.inputTotal_gni_refinement_is_lowViewRestrict`, and `Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict`.
- `Basis: derived (modeling bridge)` — In a single-step setting without internal persistent state or probabilistic sampling, any input-total refinement that preserves `GNI` acts extensionally on the trace set as a filter `P` on `(lowIn, lowOut)` (requiring additionally `∀ l h, ∃ o, S ⟨l, h, o⟩ ∧ P l o` to keep input totality).

#### 8. `full-range-const-refinement-not-ranges-over-all` (`Toy.Hyper.fullRange_const_refinement_not_rangesOverAll_of_pos`) — *Reference Point*

- **Kind:** `counterexample` | **Tier:** `T0` (elementary possibilistic hyperliveness failure under subset refinement; Roscoe 1995 Section 8.1, Clarkson and Schneider 2010) | **Depth:** `definitional`
- **Plain claim:** For any `k > 0` and any chosen constant value `v : Fin (2^k)`, `FullRangeSystem k` ranges over all `2^k` values, yet the nonempty constant-output system `ConstSystem k v` is a trace-inclusion refinement of `FullRangeSystem k` that fails `RangesOverAll (2^k)`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Randomness.lean:491-496
  theorem fullRange_const_refinement_not_rangesOverAll_of_pos
      (k : Nat) (hk : 0 < k) (v : Fin (2 ^ k)) :
      RangesOverAll (2 ^ k) (FullRangeSystem k) ∧
      Refines (ConstSystem k v) (FullRangeSystem k) ∧
      (∃ x, ConstSystem k v x) ∧
      ¬ RangesOverAll (2 ^ k) (ConstSystem k v)
  -- Unfolded:
  -- (∀ x : Fin (2 ^ k), True) ∧ (∀ x, x = v → True) ∧ (∃ x, x = v) ∧
  -- ¬ (∀ x : Fin (2 ^ k), x = v)
  ```
- **Hypothesis ledger:**
  - `hk : 0 < k` — ensures `2 ^ k ≥ 2` so a single constant `v` omits at least one element of `Fin (2 ^ k)`. Tightness: `tight: counterexample Toy.Hyper.fullRange_const_refinement_counterexample_k_zero` (at `k = 0`, `¬ (0 < 0)` and `RangesOverAll (2 ^ 0) (ConstSystem 0 0)` holds on the singleton `Fin 1`, refuting the fourth conjunct; negated full conjunction proved in `Toy.Hyper.fullRange_const_refinement_not_conclusion_at_zero`).
  - `v : Fin (2 ^ k)` — exposes the arbitrary constant output chosen by the refinement (`Fin (2 ^ k)` is always inhabited by `two_pow_pos k`). Tightness: `harmless`.
- **Non-vacuity witness:** `Toy.Hyper.fullRange_const_refinement_nonvacuity` — at `k = 1`, `v = 0 : Fin 2`, proves `0 < 1` together with all four conjuncts of the conclusion.
- **Positive control:** `Toy.Hyper.rangesOverAll_preserved_by_traceEquiv` — mutual trace inclusion (`TraceEquiv S' S`, extensional equality of trace sets, admitting **no proper refinement**) preserves `RangesOverAll n`.
- **Key non-claims (full list in Boundaries):** Applies **only** when randomness is modeled as internal demonic system choice; `RangesOverAll` is output surjectivity, not cryptographic or probabilistic unpredictability.
- **Prior art:** Roscoe, IEEE S&P 1995 (`10.1109/SECPRI.1995.398927`, Section 8.1); Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Sections 2.6 and 7.2.4); Golab, Higham, and Woelfel, STOC 2011 (`10.1145/1993636.1993687`).
- **Design question (reference point):** Does trace-inclusion refinement preserve unpredictability of outputs drawn from a randomness source when that source is modeled as internal nondeterminism?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.fullRange_const_refinement_not_rangesOverAll_of_pos`, `Toy.Hyper.fullRange_const_refinement_nonvacuity`, `Toy.Hyper.fullRange_const_refinement_counterexample_k_zero`, `Toy.Hyper.fullRange_const_refinement_not_conclusion_at_zero`, and `Toy.Hyper.rangesOverAll_preserved_by_traceEquiv`.
- `Basis: derived (modeling bridge)` — The trace-set abstraction `FullRangeSystem k` models a source semantics that specifies a `k`-bit random draw merely as internal demonic nondeterminism ("may emit any `x : Fin (2 ^ k)`"). Under that modeling choice, trace inclusion permits replacing the draw by a constant `v`; if random draws are modeled instead as external environment inputs under an input-total contract or as fixed probability distributions, trace inclusion does **not** license constant replacement.

#### 9. `uniform-support-const-refinement-loses-min-entropy` (`Toy.Hyper.uniform_support_refined_by_const_loses_minEntropy_of_pos`)

- **Kind:** `counterexample` | **Tier:** `T0` (comparison of uniform and point-mass Rényi min-entropy under support inclusion; Smith 2009, Roscoe 1995 Section 8.1, Clarkson and Schneider 2010 Section 7.2.4) | **Depth:** `shallow`
- **Plain claim:** For every `k > 0`, `uniformDist k` over `Fin (2^k)` has exact integer min-entropy `k` (at least `k` and not `k + 1`), while `constDist k` satisfies support trace inclusion (`Refines (support (constDist k)) (support (uniformDist k))`), has exact integer min-entropy `0` (at least `0` and not `1`), and fails min-entropy `k`.
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Randomness.lean:570-577
  theorem uniform_support_refined_by_const_loses_minEntropy_of_pos
      (k : Nat) (hk : 0 < k) :
      HasMinEntropyAtLeast (uniformDist k) k ∧
      ¬ HasMinEntropyAtLeast (uniformDist k) (k + 1) ∧
      Refines (support (constDist k)) (support (uniformDist k)) ∧
      HasMinEntropyAtLeast (constDist k) 0 ∧
      ¬ HasMinEntropyAtLeast (constDist k) 1 ∧
      ¬ HasMinEntropyAtLeast (constDist k) k
  -- Where:
  --   HasMinEntropyAtLeast d m := maxFin d.weight * 2 ^ m ≤ sumFin d.weight
  --   support d x              := 0 < d.weight x
  ```
- **Hypothesis ledger:**
  - `hk : 0 < k` — ensures `k ≥ 1` so collapsing min-entropy to `0` violates the source bound `k`. Tightness: `tight: counterexample Toy.Hyper.uniform_support_const_refinement_counterexample_k_zero` (at `k = 0`, `¬ (0 < 0)` and `HasMinEntropyAtLeast (constDist 0) 0` holds, refuting the sixth conjunct; negated full conjunction proved in `Toy.Hyper.uniform_support_const_refinement_not_conclusion_at_zero`).
- **Non-vacuity witness:** `Toy.Hyper.uniform_support_const_refinement_nonvacuity` — at `k = 1`, proves `0 < 1` together with exact min-entropy `1` for `uniformDist 1`, support refinement, exact min-entropy `0` for `constDist 1`, and `¬ HasMinEntropyAtLeast (constDist 1) 1`.
- **Positive control:** `Toy.Hyper.scaledUniform_preserves_minEntropy` — for every `k`, `scaledUniformDist k` (weight `2` on every outcome) satisfies `SameDist (scaledUniformDist k) (uniformDist k)` and retains `HasMinEntropyAtLeast (scaledUniformDist k) k`. (`SameDist` is an equivalence relation and admits no change in outcome probabilities.)
- **Key non-claims (full list in Boundaries):** Depends on modeling randomness as internal choice or abstracting distributions to their possibilistic supports before refinement. Even **equal supports** (`TraceEquiv`) fail to preserve min-entropy (`skewedFullSupportDist` with weights `(3, 1)` vs. `uniformDist 1` with weights `(1, 1)`, `Toy.Hyper.same_support_different_minEntropy`), and min-entropy is not a `Hyperprop` of the support (`Toy.Hyper.minEntropy_not_a_hyperprop_of_support`); consequently (**derived**: because `support skewedFullSupportDist = support (uniformDist 1)` by `same_support_different_minEntropy`, any reflexive relation `R` on possibilistic trace sets relates `support skewedFullSupportDist` to `support (uniformDist 1)`), **no reflexive relation** between possibilistic trace sets (including trace equivalence) preserves min-entropy (the empty relation preserves it only vacuously). Does not rule out proper probabilistic relations that do not increase `max_x Pr[d = x]` (`Toy.Hyper.minEntropy_kept_without_sameDist`).
- **Prior art:** Smith, FoSSaCS 2009 (`10.1007/978-3-642-00596-1_21`, Rényi min-entropy for one-try guessing; does not treat refinement); Roscoe, IEEE S&P 1995 (`10.1109/SECPRI.1995.398927`, Section 8.1); Clarkson and Schneider, *JCS* 2010 (`10.3233/JCS-2009-0393`, Section 7.2.4); McIver and Morgan, *Abstraction, Refinement and Proof for Probabilistic Systems*, Springer 2005 (`10.1007/b138392`, Part I Ch. 1 pp. 3–36 and Part II Ch. 5 pp. 129–164, publisher overview and table of contents inspected); Golab, Higham, and Woelfel, STOC 2011 (`10.1145/1993636.1993687`); Attiya and Enea, DISC 2019 (`10.4230/LIPIcs.DISC.2019.2`).
- **Design question:** Does support-level trace-inclusion refinement preserve min-entropy of a randomness source, and can any reflexive relation on possibilistic trace sets preserve it?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.uniform_support_refined_by_const_loses_minEntropy_of_pos`, `Toy.Hyper.uniform_support_const_refinement_nonvacuity`, `Toy.Hyper.uniform_support_const_refinement_counterexample_k_zero`, `Toy.Hyper.uniform_support_const_refinement_not_conclusion_at_zero`, `Toy.Hyper.scaledUniform_preserves_minEntropy`, `Toy.Hyper.same_support_different_minEntropy`, and `Toy.Hyper.minEntropy_not_a_hyperprop_of_support`.
- `Basis: derived (modeling bridge)` — Support-level trace inclusion `Refines (support d') (support d)` models a specification or compiler-correctness theorem that forgets probability weights and checks only that every possible target outcome had nonzero source probability; any verification architecture that needs quantitative min-entropy guarantees must preserve quantitative bounds (such as `max_x Pr[d = x] ≤ 2^(-k)` or distribution-aware simulation) rather than coarsening to possibilistic trace sets.

#### 10. `same-dist-preserves-min-entropy` (`Toy.Hyper.sameDist_preserves_minEntropy`) — *Reference Point*

- **Kind:** `theorem` | **Tier:** `T0` (well-definedness / rescaling invariance of min-entropy on unnormalized weight tables) | **Depth:** `shallow`
- **Plain claim:** For any valid finite discrete distributions `d`, `d' : FinDist n` and bound `k : Nat`, if `d'` and `d` represent the same probability distribution (`SameDist d' d`) and `d` has min-entropy at least `k` (`HasMinEntropyAtLeast d k`), then `d'` has min-entropy at least `k` (well-definedness of the min-entropy bound under weight rescaling, derived from `proportionalWeights_preserves_minEntropy_of_valid_source`).
- **Lean statement (compact and unfolded, with hashed raw-table core `Toy.Hyper.proportionalWeights_preserves_minEntropy_of_valid_source`):**
  ```lean
  -- lean/ToyHyper/Randomness.lean:723-726
  theorem sameDist_preserves_minEntropy {n k : Nat} {d d' : FinDist n}
      (hSame : SameDist d' d)
      (hEnt : HasMinEntropyAtLeast d k) :
      HasMinEntropyAtLeast d' k

  -- lean/ToyHyper/Randomness.lean:668-673
  -- Unbundled raw-table core (hashed in audit/statements.json):
  theorem proportionalWeights_preserves_minEntropy_of_valid_source
      {n k : Nat} {w' w : Fin n → Nat}
      (hValid : ValidWeights w)
      (hProp : ProportionalWeights w' w)
      (hEnt : RawMinEnt w k) :
      RawMinEnt w' k
  -- Unfolded:
  -- 0 < sumFin w →
  -- (∀ x : Fin n, w' x * sumFin w = w x * sumFin w') →
  -- maxFin w * 2 ^ k ≤ sumFin w →
  -- maxFin w' * 2 ^ k ≤ sumFin w'

  -- Two-sided corollary via `sameDist_symm`:
  -- Toy.Hyper.sameDist_minEntropy_iff : SameDist d' d → (HasMinEntropyAtLeast d k ↔ HasMinEntropyAtLeast d' k)
  ```
- **Hypothesis ledger:**
  - `hSame : SameDist d' d` — requires `d'` and `d` to have proportional weight tables (identical probability distributions); cannot be dropped for arbitrary distributions, though sufficient rather than necessary (`Toy.Hyper.minEntropy_kept_without_sameDist`). Tightness: `tight: counterexample Toy.Hyper.sameDist_minEntropy_counterexample_no_sameDist` (`Refines (support (constDist 1)) (support (uniformDist 1)) ∧ HasMinEntropyAtLeast (uniformDist 1) 1 ∧ ¬ SameDist (constDist 1) (uniformDist 1) ∧ ¬ HasMinEntropyAtLeast (constDist 1) 1`).
  - `hEnt : HasMinEntropyAtLeast d k` — requires source distribution `d` to satisfy bound `k`. Tightness: `tight: counterexample Toy.Hyper.sameDist_minEntropy_counterexample_no_ent` (`SameDist (constDist 1) (constDist 1) ∧ ¬ HasMinEntropyAtLeast (constDist 1) 1`).
  - `d.valid` (`ValidWeights d.weight`, bundled in `FinDist`) — requires positive total weight on the source table `w`; in `proportionalWeights_preserves_minEntropy_of_valid_source`, dropping `ValidWeights w` lets source `(0, 0)` relate to valid target `(1, 0)` (`constDist 1`) while failing `RawMinEnt` at `k = 1`. Tightness: `tight: counterexample Toy.Hyper.proportionalWeights_minEntropy_counterexample_source_not_valid`.
  - `d'.valid` (`ValidWeights d'.weight`, bundled in `FinDist`) — bundled so `d'` denotes a valid probability distribution (and used in the reverse direction of `sameDist_minEntropy_iff`), but **unused** in the forward direction (`Toy.Hyper.rawMinEnt_zero_target` shows an all-zero target table satisfies `RawMinEnt` for every `k`). Tightness: `harmless`.
- **Non-vacuity witness:** `Toy.Hyper.sameDist_preserves_minEntropy_nonvacuity` — `scaledUniformDist 1` (weights `(2, 2)`) and `uniformDist 1` (weights `(1, 1)`) satisfy `SameDist` and `HasMinEntropyAtLeast` at `k = 1`.
- **Key non-claims (full list in Boundaries):** `SameDist` is an equivalence relation, not a refinement order (admits no resolution of nondeterministic choice), is **sufficient but not necessary** (`dist110` with weights `(1, 1, 0)` inside `dist211` with weights `(2, 1, 1)` keeps min-entropy `1` without `SameDist`, `Toy.Hyper.minEntropy_kept_without_sameDist`), and establishes representation well-definedness of `HasMinEntropyAtLeast` under weight rescaling rather than a compiler-correctness discipline.
- **Prior art:** Smith, FoSSaCS 2009 (`10.1007/978-3-642-00596-1_21`); McIver and Morgan, Springer 2005 (`10.1007/b138392`, Part I Ch. 1 and Part II Ch. 5); Attiya and Enea, DISC 2019 (`10.4230/LIPIcs.DISC.2019.2`).
- **Design question (reference point):** Is min-entropy preserved by equal-distribution equivalence (`SameDist`), and what is the cost of requiring exact distribution equality?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.sameDist_preserves_minEntropy`, `Toy.Hyper.proportionalWeights_preserves_minEntropy_of_valid_source`, `Toy.Hyper.sameDist_minEntropy_iff`, `Toy.Hyper.sameDist_preserves_minEntropy_nonvacuity`, `Toy.Hyper.sameDist_minEntropy_counterexample_no_sameDist`, `Toy.Hyper.sameDist_minEntropy_counterexample_no_ent`, `Toy.Hyper.proportionalWeights_minEntropy_counterexample_source_not_valid`, `Toy.Hyper.rawMinEnt_zero_target`, and `Toy.Hyper.minEntropy_kept_without_sameDist`.
- `Basis: derived (modeling bridge)` — Confirms that cross-multiplied `Nat` weight tables represent rational probability distributions faithfully with respect to `2^(-k)` min-entropy bounds; requiring exact distribution equality between source and compiled programs preserves min-entropy trivially only by forbidding any change in outcome probabilities.

#### 11. `xor-presentation-secret-indep-choice-fails-gni` (`Toy.Hyper.secretIndepDeterminize_fails_gni_on_xorPresentation`)

- **Kind:** `counterexample` | **Tier:** `T1` (finite-type analysis of secret-independent vs. secret-dependent choice indices on the XOR presentation `out = xor highIn c` contrasted with `out = c` on the identical trace set) | **Depth:** `shallow`
- **Plain claim:** On the XOR choice presentation `xorSpecFn (_ h c => xor h c)` (whose trace set `SpecOf xorSpecFn` equals `fullIOSystem`), `SpecOf xorSpecFn` satisfies `GNI` and `InputTotal`, yet every secret-independent choice function `g : Unit → Bool` yields a deterministic, input-total refinement violating `GNI` (equivalently, corollary `xorPresentation_gni_choice_not_secretIndependent` proves every `GNI`-preserving choice index `r` on `xorSpecFn` fails `SecretIndependent r`).
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:266-273
  theorem secretIndepDeterminize_fails_gni_on_xorPresentation :
      GNI (SpecOf xorSpecFn) ∧
      InputTotal (SpecOf xorSpecFn) ∧
      (∀ g : Unit → Bool,
        Refines (secretIndepDeterminize xorSpecFn g) (SpecOf xorSpecFn) ∧
        Deterministic (secretIndepDeterminize xorSpecFn g) ∧
        InputTotal (secretIndepDeterminize xorSpecFn g) ∧
        ¬ GNI (secretIndepDeterminize xorSpecFn g))
  -- lean/ToyHyper/Determinization.lean:300-303
  -- Where xorSpecFn : Unit → Bool → Bool → Bool := fun _ h c => xor h c.
  -- Equivalent corollary on arbitrary choice indices r : Unit → Bool → Bool:
  theorem xorPresentation_gni_choice_not_secretIndependent
      (r : Unit → Bool → Bool)
      (hGNI : GNI (determinize xorSpecFn r)) :
      ¬ SecretIndependent r
  ```
- **Hypothesis ledger:** None on `secretIndepDeterminize_fails_gni_on_xorPresentation` (unconditionally proved by exhausting `g : Unit → Bool`). On corollary `xorPresentation_gni_choice_not_secretIndependent`, hypothesis `hGNI` is `tight` (`Toy.Hyper.xorPresentation_gni_choice_counterexample_no_gni`: `r _ _ = false` fails `GNI` and satisfies `SecretIndependent`) with non-vacuity witness `Toy.Hyper.xorPresentation_gni_choice_nonvacuity` (`r _ h = h`).
- **Non-vacuity witness:** `Toy.Hyper.secretIndepDeterminize_fails_gni_on_xorPresentation` (directly proved; corollary witness `Toy.Hyper.xorPresentation_gni_choice_nonvacuity`).
- **Positive controls:**
  - `Toy.Hyper.constLowPresentation_admits_secretIndep_gni_choice` — presenting the **exact same trace set** (`SpecOf constLowSpecFn = SpecOf xorSpecFn = fullIOSystem`, `Toy.Hyper.specOf_xor_eq_specOf_constLow`) as `constLowSpecFn (_ _ c => c)` admits secret-independent choice `r _ _ = false`, yielding `constFalseIOSystem` (`GNI`).
  - `Toy.Hyper.xorPresentation_admits_secretDependent_gni_choice` — on `xorSpecFn` itself, secret-dependent choice index `r _ h = h` yields a deterministic, input-total `GNI` refinement equal to `constFalseIOSystem` (`Toy.Hyper.same_secure_refinement_two_presentations`).
- **Key non-claims (full list in Boundaries):** Does **not** say a secure implementation must read the secret! Every `GNI` determinization of `xorSpecFn` produces a constant system `ofFn (fun _ _ => b)` that ignores `highIn` (`Toy.Hyper.xor_gni_determinization_is_constant`; **derived**: by `determinize_gni_iff_resolvedOutput_secretIndependent`, `xor false (r () false) = xor true (r () true)` holds on `Bool` iff `r () true = !(r () false)`, so the exhaustive `GNI` choice functions are `r _ h = h` and `r _ h = !h`, yielding `lowOut = false` and `lowOut = true`); secret-dependence of `r` is strictly an artifact of the presentation `xorSpecFn` (`Toy.Hyper.secret_dependence_is_presentation_dependent`). Does not contradict scheduler noninterference theorems (Popescu, Hölzl, and Nipkow, CALCO 2013).
- **Prior art:** Morgan, "The Shadow Knows: Refinement of Ignorance in Sequential Programs", Technical Report UNSW-CSE-TR-0522 (30 Nov 2005) and MPC 2006 (`10.1007/11783596_21`; journal version under the title "The Shadow Knows: Refinement and security in sequential programs", *Science of Computer Programming* 2009 `10.1016/j.scico.2007.09.003`; Sections 1 and 7 "The Encryption Lemma" verified in UNSW-CSE-TR-0522); Popescu, Hölzl, and Nipkow, CALCO 2013 (`10.1007/978-3-642-40206-7_18`, contrasting positive scheduler result).
- **Design question:** Can fixing a nondeterministic choice variable independently of the secret always preserve `GNI` for a given choice presentation `f`, and does failure reflect a property of the trace set or of the presentation?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.secretIndepDeterminize_fails_gni_on_xorPresentation`, `Toy.Hyper.xorPresentation_gni_choice_not_secretIndependent`, `Toy.Hyper.xorPresentation_gni_choice_nonvacuity`, `Toy.Hyper.xorPresentation_gni_choice_counterexample_no_gni`, `Toy.Hyper.constLowPresentation_admits_secretIndep_gni_choice`, `Toy.Hyper.xorPresentation_admits_secretDependent_gni_choice`, `Toy.Hyper.specOf_xor_eq_specOf_constLow`, `Toy.Hyper.xor_gni_determinization_is_constant`, `Toy.Hyper.same_secure_refinement_two_presentations`, and `Toy.Hyper.secret_dependence_is_presentation_dependent`.
- `Basis: derived (modeling bridge)` — If a specification syntax exposes an internal choice variable `c` algebraically coupled with secret data (such as a one-time-pad mask in `out = h ⊕ c`), a compiler pass that deterministically fixes `c` without reading `h` destroys secrecy (turning a mask into a fixed constant so `out` leaks `h` or `¬h`), whereas either genuine uniform random sampling of `c` (outside the possibilistic model) or re-parameterizing the specification around public output `out = c` avoids the trap without making the compiled code read `h`.

#### 12. `gni-and-det-iff-obs-det-and-rectangular-domain` (`Toy.Hyper.gni_and_deterministic_iff_obsDet_and_rectangularDomain`)

- **Kind:** `characterization` | **Tier:** `T1` (elementary consequence of the single-step definitions; no consulted source states this exact equivalence with `RectangularDomain` in this form) | **Depth:** `shallow`
- **Plain claim:** For any trace types `L`, `H`, `O` and any (possibly partial) system `S` over `IOTrace L H O`, `S` satisfies both `GNI` and `Deterministic` if and only if `S` satisfies both `ObsDet` and `RectangularDomain` (with equivalent conditional corollary `gni_iff_obsDet_and_rectangularDomain_of_deterministic` and minimal directional lemmas `gni_imp_rectangularDomain`, `obsDet_of_gni_of_deterministic`, `gni_of_obsDet_of_rectangularDomain`).
- **Lean statement (compact and unfolded, with hashed conditional corollary `Toy.Hyper.gni_iff_obsDet_and_rectangularDomain_of_deterministic`):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:386-389
  theorem gni_and_deterministic_iff_obsDet_and_rectangularDomain
      {L : Type u} {H : Type v} {O : Type w}
      (S : System (IOTrace L H O)) :
      GNI S ∧ Deterministic S ↔ ObsDet S ∧ RectangularDomain S

  -- lean/ToyHyper/Determinization.lean:395-399
  -- Equivalent conditional corollary (hashed in audit/statements.json):
  theorem gni_iff_obsDet_and_rectangularDomain_of_deterministic
      {L : Type u} {H : Type v} {O : Type w}
      {S : System (IOTrace L H O)}
      (hDet : Deterministic S) :
      GNI S ↔ ObsDet S ∧ RectangularDomain S
  -- Minimal directional lemmas:
  --   gni_imp_rectangularDomain          : GNI S → RectangularDomain S
  --   obsDet_of_gni_of_deterministic     : Deterministic S → GNI S → ObsDet S
  --   gni_of_obsDet_of_rectangularDomain : ObsDet S → RectangularDomain S → GNI S
  --   obsDet_imp_deterministic           : ObsDet S → Deterministic S
  ```
- **Hypothesis ledger:** None on `gni_and_deterministic_iff_obsDet_and_rectangularDomain`. On conditional corollary `gni_iff_obsDet_and_rectangularDomain_of_deterministic`, hypothesis `hDet : Deterministic S` is proved `tight` by `Toy.Hyper.gni_obsDet_rectangularDomain_counterexample_no_det` (`¬ Deterministic fullIOSystem ∧ GNI fullIOSystem ∧ ¬ (ObsDet fullIOSystem ∧ RectangularDomain fullIOSystem)`).
- **Non-vacuity witness:** `Toy.Hyper.gni_obsDet_rectangularDomain_nonvacuity` — on genuinely **partial** deterministic systems (`¬ InputTotal`), `echoLowHighFalseSystem` satisfies both sides, while `diagonalPartialSystem` is deterministic and refutes both sides.
- **Key non-claims (full list in Boundaries):** Neither `GNI` nor `RectangularDomain` forbids secret-only acceptance filtering (`echoLowHighFalseSystem` accepts iff `highIn = false` and satisfies both sides, `Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`). Specific to single-step traces with no high outputs; in multi-step CSP, McCullough's GNI is strictly weaker than classical noninterference even on deterministic state machines (Noce, AFP 2014, theorems `c_secure_implies_g_secure` and `not_g_secure_implies_c_secure`; Evidence item 21).
- **Prior art:** Elementary consequence of the single-step definitions (`T1`); Goguen and Meseguer, IEEE S&P 1982 (`10.1109/SP.1982.10014`); McCullough, IEEE S&P 1987 (`10.1109/SP.1987.10009`) and McLean, IEEE S&P 1990 (`10.1109/RISP.1990.63849`); Roscoe, Woodcock, and Wulf, ESORICS 1994 / *JCS* 1996 (`10.1007/3-540-58618-0_55`, `10.3233/JCS-1996-4103`); Noce, AFP 2014 (`Noninterference_CSP`).
- **Design question:** How do generalized noninterference and observational determinism relate on deterministic implementations, including partial ones?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_and_deterministic_iff_obsDet_and_rectangularDomain`, `Toy.Hyper.gni_iff_obsDet_and_rectangularDomain_of_deterministic`, `Toy.Hyper.gni_obsDet_rectangularDomain_nonvacuity`, `Toy.Hyper.gni_obsDet_rectangularDomain_counterexample_no_det`, `Toy.Hyper.rectangularDomain_iff_product`, and `Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`.
- `Basis: derived (modeling bridge)` — On partial single-step deterministic semantics (for example, partial functions modeling nontermination or input preconditions), `ObsDet` alone misses joint `(lowIn, highIn)` domain couplings such as `lowIn = highIn` (`diagonalPartialSystem`); `GNI` adds `RectangularDomain` (product-set acceptance), which still permits pure `highIn`-dependent nontermination unless `AcceptanceIgnoresHigh` or `InputTotal` is enforced separately.

#### 13. `gni-iff-obs-det-of-deterministic-input-total` (`Toy.Hyper.gni_iff_obsDet_of_deterministic_inputTotal`)

- **Kind:** `characterization` | **Tier:** `T1` (elementary consequence of the single-step definitions; no consulted source states this exact equivalence in this form) | **Depth:** `shallow`
- **Plain claim:** For any trace types `L`, `H`, `O` and any deterministic, input-total single-step system `S` over `IOTrace L H O` (`Deterministic S` and `InputTotal S`), generalized noninterference (`GNI S`) holds if and only if observational determinism (`ObsDet S`) holds (corollary of `gni_and_deterministic_iff_obsDet_and_rectangularDomain`).
- **Lean statement (compact and unfolded, with hashed weaker-domain corollary `Toy.Hyper.gni_iff_obsDet_of_deterministic_acceptanceIgnoresHigh`):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:470-474
  theorem gni_iff_obsDet_of_deterministic_inputTotal
      {L : Type u} {H : Type v} {O : Type w}
      {S : System (IOTrace L H O)}
      (hDet : Deterministic S) (hTot : InputTotal S) :
      GNI S ↔ ObsDet S

  -- lean/ToyHyper/Determinization.lean:459-463
  -- Weaker-domain corollary under secret-independent acceptance (hashed in audit/statements.json):
  theorem gni_iff_obsDet_of_deterministic_acceptanceIgnoresHigh
      {L : Type u} {H : Type v} {O : Type w}
      {S : System (IOTrace L H O)}
      (hDet : Deterministic S) (hA : AcceptanceIgnoresHigh S) :
      GNI S ↔ ObsDet S
  ```
- **Hypothesis ledger:**
  - `hDet : Deterministic S` — required for `GNI S → ObsDet S`; nondeterministic input-total systems can satisfy `GNI` without `ObsDet`. Tightness: `tight: counterexample Toy.Hyper.gni_obsDet_total_counterexample_no_det` (`InputTotal fullIOSystem ∧ ¬ Deterministic fullIOSystem ∧ GNI fullIOSystem ∧ ¬ ObsDet fullIOSystem`).
  - `hTot : InputTotal S` — ensures `RectangularDomain S` so `ObsDet S → GNI S` holds (weakens to `AcceptanceIgnoresHigh S` or `RectangularDomain S`, but cannot be dropped). Tightness: `tight: counterexample Toy.Hyper.gni_obsDet_total_counterexample_no_inputTotal` (`Deterministic diagonalPartialSystem ∧ ¬ InputTotal diagonalPartialSystem ∧ ObsDet diagonalPartialSystem ∧ ¬ GNI diagonalPartialSystem`).
- **Non-vacuity witness:** `Toy.Hyper.gni_obsDet_total_nonvacuity` — `echoLowSystem` is deterministic and input-total with both `GNI` and `ObsDet` true, while `leakHighSystem` is deterministic and input-total with both false.
- **Key non-claims (full list in Boundaries):** `InputTotal` is sufficient rather than minimal (`AcceptanceIgnoresHigh` and `RectangularDomain` also suffice); `Deterministic S` is unused in the reverse direction `ObsDet S → GNI S` (`obsDet_imp_deterministic`); does not extend to multi-step CSP state machines (Noce, AFP 2014).
- **Prior art:** Elementary consequence of the single-step definitions (`T1`); Goguen and Meseguer, IEEE S&P 1982 (`10.1109/SP.1982.10014`); Roscoe, Woodcock, and Wulf, ESORICS 1994 / *JCS* 1996 (`10.1007/3-540-58618-0_55`, `10.3233/JCS-1996-4103`); Zdancewic and Myers, CSFW 2003 (`10.1109/CSFW.2003.1212703`); Noce, AFP 2014 (`Noninterference_CSP`).
- **Design question:** When a compiler resolves nondeterminism into a total deterministic single-step implementation, do `GNI` and observational determinism coincide?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_iff_obsDet_of_deterministic_inputTotal`, `Toy.Hyper.gni_iff_obsDet_of_deterministic_acceptanceIgnoresHigh`, `Toy.Hyper.gni_obsDet_total_nonvacuity`, `Toy.Hyper.gni_obsDet_total_counterexample_no_det`, and `Toy.Hyper.gni_obsDet_total_counterexample_no_inputTotal`.
- `Basis: derived (modeling bridge)` — Once compilation produces a total, deterministic single-step target program, `GNI` collapses to `ObsDet`; the refinement paradox arises solely at the nondeterministic specification-to-implementation transition, not from any divergence between `GNI` and `ObsDet` on the final total deterministic artifact.

#### 14. `gni-of-fn-iff-secret-independent` (`Toy.Hyper.gni_ofFn_iff_secretIndependent`)

- **Kind:** `characterization` | **Tier:** `T1` (elementary consequence of single-step `GNI` on total function graphs) | **Depth:** `definitional`
- **Plain claim:** For any total single-step function `g : L → H → O`, its trace graph `ofFn g` satisfies `GNI` if and only if `g` is independent of the secret input `h` (`SecretIndependent g`) (corollary of `gni_iff_obsDet_of_deterministic_inputTotal`; instantiating `g := fun l h => f l h (r l h)` yields `determinize_gni_iff_resolvedOutput_secretIndependent`).
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:553-556
  theorem gni_ofFn_iff_secretIndependent
      {L : Type u} {H : Type v} {O : Type w}
      (g : L → H → O) :
      GNI (ofFn g) ↔ SecretIndependent g
  -- Unfolded:
  -- GNI (fun t => t.lowOut = g t.lowIn t.highIn) ↔ (∀ l h₁ h₂, g l h₁ = g l h₂)
  -- Instantiated corollaries in ToyHyper.Determinization:
  --   determinize_gni_iff_resolvedOutput_secretIndependent :
  --     GNI (determinize f r) ↔ SecretIndependent (fun l h => f l h (r l h))
  --   secretIndepDeterminize_gni_iff_resolvedOutput_secretIndependent :
  --     GNI (secretIndepDeterminize f g) ↔ SecretIndependent (fun l h => f l h (g l))
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `L`, `H`, `O`, and `g`; holds vacuously when `H` is empty).
- **Non-vacuity witness:** `Toy.Hyper.gni_ofFn_iff_secretIndependent_nonvacuity` — `fun (l : Bool) (_ : Bool) => l` satisfies both sides, while `fun (_ : Unit) (h : Bool) => h` refutes both sides.
- **Key non-claims (full list in Boundaries):** Constrains the **composite output** `fun l h => f l h (r l h)`, **not** the choice index `r` (`SecretIndependent (fun l h => f l h (r l h))` does not imply `SecretIndependent r`); applies to single-step total pure functions, not stateful interactive systems.
- **Prior art:** Elementary consequence of single-step `GNI` on function graphs (`T1`); background on choice strategies: Coenen et al., CAV 2019 (`10.1007/978-3-030-25540-4_7`); Finkbeiner et al., CAV 2018 (`10.1007/978-3-319-96145-3_16`).
- **Design question:** Under what exact condition does a total function (and in particular a choice-function resolution `determinize f r`) satisfy single-step `GNI`?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_ofFn_iff_secretIndependent`, `Toy.Hyper.gni_ofFn_iff_secretIndependent_nonvacuity`, `Toy.Hyper.determinize_gni_iff_resolvedOutput_secretIndependent`, and `Toy.Hyper.secretIndepDeterminize_gni_iff_resolvedOutput_secretIndependent`.
- `Basis: derived (modeling bridge)` — For pure total Rust/Lean functions without side channels, single-step `GNI` of the I/O graph is literally relational 2-safety `∀ l h₁ h₂, g l h₁ = g l h₂`.

#### 15. `exists-input-total-gni-refinement-iff-exists-choice` (`Toy.Hyper.exists_inputTotal_gni_refinement_iff_exists_choice`)

- **Kind:** `characterization` | **Tier:** `T1` (folklore Skolem/uniformization equivalence made precise in a single-step choice-presentation model) | **Depth:** `shallow`
- **Plain claim:** For any choice presentation `f : L → H → C → O`, `SpecOf f` admits an input-total refinement `S'` satisfying `GNI` (deterministic or not — determinism adds nothing, see `exists_inputTotal_gni_refinement_iff_det`) if and only if there exists a choice function `r : L → H → C` making the resolved output `(fun l h => f l h (r l h))` independent of `highIn` (equivalently, for nonempty `H`, a public-only function `g : L → O` whose graph lies inside `SpecOf f` for every secret).
- **Lean statement (compact and unfolded, with hashed deterministic corollary `Toy.Hyper.exists_det_inputTotal_gni_refinement_iff`):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:603-608
  theorem exists_inputTotal_gni_refinement_iff_exists_choice
      {L : Type u} {H : Type v} {C : Type w} {O : Type z}
      (f : L → H → C → O) :
      (∃ S' : System (IOTrace L H O),
        Refines S' (SpecOf f) ∧ InputTotal S' ∧ GNI S') ↔
      (∃ r : L → H → C, SecretIndependent (fun l h => f l h (r l h)))

  -- lean/ToyHyper/Determinization.lean:631-636
  -- Deterministic corollary (hashed in audit/statements.json):
  theorem exists_det_inputTotal_gni_refinement_iff
      {L : Type u} {H : Type v} {C : Type w} {O : Type z}
      (f : L → H → C → O) :
      (∃ S' : System (IOTrace L H O),
        Refines S' (SpecOf f) ∧ Deterministic S' ∧ InputTotal S' ∧ GNI S') ↔
      (∃ r : L → H → C, SecretIndependent (fun l h => f l h (r l h)))
  -- Presentation-free and choice-free companions:
  --   exists_choice_iff_common_output :
  --     (∃ r, SecretIndependent (fun l h => f l h (r l h))) ↔ ∀ l (_ : H), ∃ o, ∀ h, ∃ c, f l h c = o
  --   exists_choice_iff_exists_low_function [Nonempty H] :
  --     (∃ r, SecretIndependent (fun l h => f l h (r l h))) ↔ ∃ g : L → O, ∀ l h, SpecOf f ⟨l, h, g l⟩
  ```
- **Hypothesis ledger:** None (unconditionally quantified over `L`, `H`, `C`, `O`, and `f`). Inside the left-hand existential, `InputTotal S'` is essential (`Toy.Hyper.partial_det_gni_refinement_exists_without_choice`), whereas `Deterministic S'` is redundant (`Toy.Hyper.exists_inputTotal_gni_refinement_iff_det`).
- **Non-vacuity witness:** `Toy.Hyper.exists_inputTotal_gni_refinement_nonvacuity` — `xorSpecFn` satisfies both sides (via `determinize xorSpecFn (fun _ h => h)` and `r _ h = h`), while `leakSpecFn` refutes both sides.
- **Key non-claims (full list in Boundaries):** Pure existence theorem (uses `Classical.choice` in general, not constructive compilation); for `[Nonempty H]`, the condition is presentation-free on `SpecOf f` (`exists_choice_iff_exists_low_function`, where `[Nonempty H]` is necessary by `Toy.Hyper.emptyHigh_no_low_function_edge_case`); does not require `SpecOf f` itself to satisfy `GNI` (`Toy.Hyper.nonGNI_spec_with_secure_determinization`); does not extend to multi-step reactive causality without lookahead/prophecy constraints.
- **Prior art:** Finkbeiner et al., CAV 2018 (`10.1007/978-3-319-96145-3_16`); Coenen et al., CAV 2019 (`10.1007/978-3-030-25540-4_7`); Alur, Černý, and Zdancewic, ICALP 2006 (`10.1007/11787006_10`); Morgan, "The Shadow Knows: Refinement of Ignorance in Sequential Programs", UNSW-CSE-TR-0522 (2005) / MPC 2006 (`10.1007/11783596_21`; journal version "The Shadow Knows: Refinement and security in sequential programs", *SCP* 2009 `10.1016/j.scico.2007.09.003`); Popescu, Bauereiss, and Lammich, AFP 2014 / ITP 2021 (`10.4230/LIPIcs.ITP.2021.3`).
- **Design question:** When does a choice-indexed specification `SpecOf f` admit a secure (`GNI`) input-total refinement, and how does the choice-function condition relate to the underlying trace set?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.exists_inputTotal_gni_refinement_iff_exists_choice`, `Toy.Hyper.exists_det_inputTotal_gni_refinement_iff`, `Toy.Hyper.exists_inputTotal_gni_refinement_iff_det`, `Toy.Hyper.exists_choice_iff_common_output`, `Toy.Hyper.exists_choice_iff_exists_low_function`, `Toy.Hyper.emptyHigh_no_low_function_edge_case`, `Toy.Hyper.exists_inputTotal_gni_refinement_nonvacuity`, `Toy.Hyper.partial_det_gni_refinement_exists_without_choice`, and `Toy.Hyper.nonGNI_spec_with_secure_determinization`.
- `Basis: derived (modeling bridge)` — Tells specification authors that, for nonempty `H`, a single-step relational spec `SpecOf f` is securely implementable by a total program iff every public input `l` admits at least one output `o` permitted across **all** secrets `h` (`∩_h {f l h c | c} ≠ ∅`), and when that holds, resolving nondeterminism down to a deterministic function `g : L → O` never sacrifices implementability (when `H` is empty, the theorem holds vacuously via `Toy.Hyper.exists_choice_iff_common_output` even when `O` is empty and no `g : L → O` exists, `Toy.Hyper.emptyHigh_no_low_function_edge_case`).

#### 16. `gni-input-total-spec-admits-det-gni-refinement` (`Toy.Hyper.gni_inputTotal_spec_admits_det_gni_refinement`)

- **Kind:** `theorem` | **Tier:** `T1` (instance `S' := SpecOf f` of the forward direction of `exists_inputTotal_gni_refinement_iff_exists_choice`) | **Depth:** `shallow`
- **Plain claim:** For any choice presentation `f : L → H → C → O`, if `SpecOf f` satisfies `GNI` and `InputTotal` (the latter is independent of `f` and equivalent to `Nonempty (L → H → C)`), then there exists a choice function `r : L → H → C` such that `determinize f r` satisfies `GNI` (and automatically satisfies `Refines`, `Deterministic`, and `InputTotal`; corollary of `exists_inputTotal_gni_refinement_iff_exists_choice` at `S' := SpecOf f`).
- **Lean statement (compact and unfolded):**
  ```lean
  -- lean/ToyHyper/Determinization.lean:811-816
  theorem gni_inputTotal_spec_admits_det_gni_refinement
      {L : Type u} {H : Type v} {C : Type w} {O : Type z}
      (f : L → H → C → O)
      (hGNI : GNI (SpecOf f))
      (hTot : InputTotal (SpecOf f)) :
      ∃ r : L → H → C, GNI (determinize f r)
  -- Companion unconditional properties for every r:
  --   determinize_refines_specOf f r : Refines (determinize f r) (SpecOf f)
  --   determinize_deterministic f r  : Deterministic (determinize f r)
  --   determinize_inputTotal f r     : InputTotal (determinize f r)
  -- Domain equivalence: InputTotal (SpecOf f) ↔ Nonempty (L → H → C) (`inputTotal_specOf_iff_nonempty_choiceFn`).
  ```
- **Hypothesis ledger:**
  - `hGNI : GNI (SpecOf f)` — ensures that for each `lowIn`, an output achievable at a reference secret `h₀` is achievable at every secret `h`. Tightness: `tight: counterexample Toy.Hyper.gni_inputTotal_spec_counterexample_no_gni` (`InputTotal (SpecOf leakSpecFn) ∧ ¬ GNI (SpecOf leakSpecFn) ∧ ¬ ∃ r, GNI (determinize leakSpecFn r)`).
  - `hTot : InputTotal (SpecOf f)` — equivalent to `Nonempty (L → H → C)` (`Toy.Hyper.inputTotal_specOf_iff_nonempty_choiceFn`), ruling out empty choice types `C` on nonempty `L, H` where `SpecOf f` is empty (so `GNI` holds vacuously) while no `r : L → H → C` exists. Tightness: `tight: counterexample Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal` (`GNI (SpecOf emptyChoiceSpecFn) ∧ ¬ InputTotal (SpecOf emptyChoiceSpecFn) ∧ ¬ ∃ r, GNI (determinize emptyChoiceSpecFn r)`).
- **Non-vacuity witness:** `Toy.Hyper.gni_inputTotal_spec_admits_nonvacuity` — `xorSpecFn` satisfies both `GNI (SpecOf xorSpecFn)` and `InputTotal (SpecOf xorSpecFn)`.
- **Key non-claims (full list in Boundaries):** Existence of *one* secure determinization does **not** make trace inclusion safe (`leakHighSystem` also refines `SpecOf xorSpecFn` and breaks `GNI`); requires `InputTotal (SpecOf f)` (`Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal`); uses `Classical.choice` (`r` need not be computable or operationally related to `f`); `GNI (SpecOf f)` is sufficient given `InputTotal`, not necessary (`Toy.Hyper.nonGNI_spec_with_secure_determinization`).
- **Prior art:** Finkbeiner et al., CAV 2018 (`10.1007/978-3-319-96145-3_16`); Coenen et al., CAV 2019 (`10.1007/978-3-030-25540-4_7`); Mantel, IEEE S&P 2001 (`10.1109/SECPRI.2001.924289`).
- **Design question:** Does every input-total single-step `GNI` choice presentation admit a deterministic `GNI` refinement, and why does existence of one secure refinement fail to make trace inclusion sufficient?
- `Basis: execution (Lean kernel check)` — `Toy.Hyper.gni_inputTotal_spec_admits_det_gni_refinement`, `Toy.Hyper.gni_inputTotal_spec_admits_nonvacuity`, `Toy.Hyper.gni_inputTotal_spec_counterexample_no_gni`, `Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal`, and `Toy.Hyper.inputTotal_specOf_iff_nonempty_choiceFn`.
- `Basis: derived (modeling bridge)` — Shows that single-step `GNI` specifications `SpecOf f` that are **input-total** (`InputTotal (SpecOf f)`, equivalently `Nonempty (L → H → C)`) are never dead ends for total deterministic implementation. Without `InputTotal (SpecOf f)`, a `GNI` specification can have no total deterministic realization (`Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal` for the empty choice space; likewise, a nonempty partial `GNI` system such as `echoLowHighFalseSystem` admits no `InputTotal` refinement at all, since every trace it permits has `highIn = false`). At the same time, existence of one secure determinization pinpoints why compiler correctness still requires an explicit target `ObsDet` / `GNI` obligation or a restricted refinement relation rather than bare trace inclusion.

## Boundaries

### Attractive Stronger Readings Ruled Out (`known not to apply`)

1. **"A compiler that preserves input totality (or never deletes all traces) preserves *only* subset-closed hyperproperties." — `known not to apply`.** The reverse direction of `subsetClosed_iff_preservedByAllRefiningCompilers` relies on `intersectCompiler S'` (`C S = S ∩ S'`), which may delete arbitrary traces including every trace for a given input. Refinements constrained to preserve `InputTotal` preserve non-subset-closed properties (**derived**: `InputTotal` itself is not subset-closed because `emptyIOSystem ⊑ fullIOSystem` with `InputTotal fullIOSystem` and `¬ InputTotal emptyIOSystem` by `Toy.Hyper.inputTotal_neg_example`, yet `InputTotal` is tautologically preserved by input-totality-preserving compilers), and when the source system `S` is both `Deterministic` and `InputTotal`, every input-totality-preserving refinement satisfies `InputTotal S'` and hence `S' = S` (`Toy.Hyper.inputTotal_refinement_of_deterministic_eq`), preserving **every** hyperproperty.
2. **"Every subset-closed hyperproperty is a lifted trace property or a finite-arity `UniversalKHyperprop k Rel`." — `known not to apply`.** `ObsDet` is subset-closed (`k = 2`) and equals `LiftTraceProp P` for no `P` on `IOTrace Unit Unit Bool` (`Toy.Hyper.obsDet_not_liftTraceProp`). Over `Nat`, `BoundedNatSystem` is subset-closed and equals `UniversalKHyperprop k Rel` for no `k : Nat` and `Rel` (`Toy.Hyper.boundedNatSystem_subsetClosed_not_universalKHyperprop`).
3. **"`ObsDet` permits public coin-flip outputs as long as the coins ignore the secret, or prevents secret-dependent nontermination." — `known not to apply`.** `ObsDet` requires at most one `lowOut` per `lowIn` (`Toy.Hyper.obsDet_at_most_one_output`), ruling out any low-visible randomness modeled as trace nondeterminism. Conversely, `ObsDet`, `GNI`, and `RectangularDomain` quantify only over occurring traces in `S` and hold on `echoLowHighFalseSystem` (`highIn = false` only, `Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`), so none of them detects secret-dependent nontermination/rejection without `AcceptanceIgnoresHigh` or `InputTotal`.
4. **"`lowViewRestrict` characterizes all `GNI`-preserving refinements, preserves `InputTotal`, or forbids choice functions that consult `highIn`." — `known not to apply`.** `lowViewRestrict S P` is **exact among input-total `GNI` refinements** (`Toy.Hyper.inputTotal_gni_refinement_is_lowViewRestrict`), but **incomplete for partial refinements** (`highFalseFullSystem` refines `fullIOSystem` by `highIn = false`, preserves `GNI`, and equals `lowViewRestrict fullIOSystem P` for no `P`, `Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict`). It need not preserve `InputTotal` (`Toy.Hyper.lowViewRestrict_need_not_preserve_inputTotal`). Moreover, membership in `lowViewRestrict S P` is a property of the **trace set**, not of how a choice was resolved: `determinize xorSpecFn (fun _ h => h)` consults `highIn` in its choice index yet equals `constFalseIOSystem = lowViewRestrict fullIOSystem (fun _ o => o = false)` (`Toy.Hyper.same_secure_refinement_two_presentations`, `Toy.Hyper.lowViewRestrict_full_eq_constFalse`).
5. **"A trace-refining compiler may replace calls to an external or hardware RNG with a constant, or trace equivalence of supports preserves min-entropy." — `known not to apply`.** Cards 8 and 9 apply **only** when the randomness source is modeled as internal demonic choice of the system (or after forgetting probabilities via `support d`). If random values are environment inputs under an input-total contract or if correctness is stated over distributions, trace inclusion does not allow replacing the RNG with a constant (Roscoe 1995, Section 8.1). Conversely, once probabilities are forgotten via `support d`, equal supports (`TraceEquiv`) fail to preserve min-entropy (`Toy.Hyper.same_support_different_minEntropy`) and min-entropy is not a `Hyperprop` of `support d` (`Toy.Hyper.minEntropy_not_a_hyperprop_of_support`); consequently (**derived**: since `support skewedFullSupportDist = support (uniformDist 1)`, any reflexive relation relates the two supports to each other), **no reflexive relation** on possibilistic trace sets — not even `TraceEquiv` — preserves min-entropy (only a non-reflexive relation such as the empty relation preserves it vacuously). And `SameDist` is an equivalence relation that is **sufficient, not necessary**, to keep a min-entropy bound (`Toy.Hyper.minEntropy_kept_without_sameDist`).
6. **"On the XOR specification, a secure implementation must read the secret, or secret-dependence belongs to the trace set `SpecOf f`." — `known not to apply`.** `SpecOf xorSpecFn` and `SpecOf constLowSpecFn` are the **exact same trace set** `fullIOSystem` (`Toy.Hyper.specOf_xor_eq_specOf_constLow`). Every `GNI`-satisfying determinization of `xorSpecFn` is a constant system `ofFn (fun _ _ => b)` whose observable behavior ignores `highIn` (`Toy.Hyper.xor_gni_determinization_is_constant`), and `constLowSpecFn` produces that identical system via secret-independent choice `r _ _ = false` (`Toy.Hyper.same_secure_refinement_two_presentations`, `Toy.Hyper.secret_dependence_is_presentation_dependent`).
7. **"Single-step equivalences (`GNI ↔ ObsDet` on total deterministic systems, choice-function realizability without causality) carry over unchanged to multi-step reactive or CSP processes." — `known not to apply`.** In multi-step CSP, Pasquale Noce's Isabelle/HOL mechanization (`Noninterference_CSP`, AFP 2014) proves McCullough's generalized noninterference strictly weaker than classical noninterference even for processes representing deterministic state machines (the implication is theorem `c_secure_implies_g_secure` and the strictness is an explicit deterministic counterexample, theorem `not_g_secure_implies_c_secure`, both in `GeneralizedNoninterference.thy`; see Evidence item 21); in multi-step reactive synthesis, choice strategies cannot depend on future secrets that have not yet arrived.

### Per-Result Non-Claims

- **Card 1 (`subset-closed-iff-refinement-preserved`):**
  - Quantifies over transformations that may delete arbitrary behaviors, including all of them (`intersectCompiler`); does not characterize refinements that must preserve input totality (`Toy.Hyper.inputTotal_refinement_of_deterministic_eq`).
  - Characterizes which hyperproperties survive all refinements, not which relations preserve a given class (for the dual, see Card 2 `Toy.Hyper.refines_iff_preserves_all_subsetClosed`).
  - Does not formalize distinct source/target languages, cross-language trace relations (Abate et al., ESOP 2020 / TOPLAS 2021), syntactic compilers, or contextual linking (`RSCHP` in Abate et al., CSF 2019).
  - Does not restrict `C` to computable functions; the reverse direction uses `intersectCompiler S'` with `propext` and `funext`.
  - Does not claim non-subset-closed hyperproperties fail under every specific compiler — only that they are not preserved across *all* trace-inclusion refinements.
- **Card 2 (`refines-iff-preserves-all-subset-closed`):**
  - Whole-program, shared-trace-type statement; does not model linking with adversarial contexts or cross-language trace relations.
  - Characterizes preservation of the entire class of subset-closed hyperproperties, not preservation of any single non-subset-closed property.
- **Card 3 (`trace-property-lift-subset-closed`):**
  - Corollary `k = 1` of `universalKHyperprop_subsetClosed` (`Toy.Hyper.liftTraceProp_iff_universal1Hyperprop`), not an independent preservation mechanism.
  - Does not claim every subset-closed hyperproperty is a lifted trace property (`Toy.Hyper.obsDet_not_liftTraceProp`).
  - Applies only to single-trace predicates, not multi-trace relational policies.
- **Card 4 (`universal-k-hyperprop-subset-closed`):**
  - Does not claim every subset-closed hyperproperty has the form `UniversalKHyperprop k Rel` (`Toy.Hyper.boundedNatSystem_subsetClosed_not_universalKHyperprop`).
  - Does not formalize finite-prefix Vietoris-topology safety over infinite traces (Clarkson and Schneider 2010).
  - Does not apply to `∀∃` hyperproperties such as `GNI` or hyperliveness.
- **Card 5 (`obs-det-preserved-by-refinement`):**
  - Corollary `k = 2` of `universalKHyperprop_subsetClosed` (`Toy.Hyper.obsDet_iff_universal2Hyperprop`).
  - Forbids **all** low-observable nondeterminism (`Toy.Hyper.obsDet_at_most_one_output`), offering no way to keep both secrecy and public output unpredictability under trace inclusion, and reflects the specification cost reported by Murray et al. (2013) and Costanzo et al. (2016).
  - Does not detect acceptance or termination covert channels: `ObsDet` can hold on systems that reject some secrets (`echoLowHighFalseSystem`, `Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`), and it holds trivially on the empty system (**derived**: secret-filtered partial systems do **not** automatically satisfy `ObsDet`: `highFalseFullSystem` accepts only `highIn = false` yet permits both `lowOut = false` and `lowOut = true`, violating `ObsDet`).
  - Does not model microarchitectural timing/cache/speculative channels (see Barthe et al., POPL 2020) or concurrent stuttering traces (Zdancewic and Myers, CSFW 2003).
- **Card 6 (`gni-refinement-paradox-input-total`):**
  - Deterministic-source input-total refinement (`Toy.Hyper.gni_preserved_by_inputTotal_refinement_of_deterministic`) is trivial equality `S' = S` (`Toy.Hyper.inputTotal_refinement_of_deterministic_eq`), not a proper refinement class.
  - Does not claim every proper refinement of a `GNI` system breaks `GNI` (`constFalseIOSystem` via `Toy.Hyper.lowViewRestrict_proper_gni_control_instance` preserves `GNI`).
  - `GNI` quantifies over occurring secrets only (`Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`) and collapses multi-step possibilistic distinctions (`Toy.Hyper.gni_iff_low_view_compatible_with_every_secret`).
  - Does not formalize multi-step simulation refinements (Mantel 2001; Alur, Černý, and Zdancewic 2006; Attiya and Enea 2019) or quantitative/probabilistic noninterference, and its witness pair coincides with `SpecOf xorSpecFn` and `secretIndepDeterminize xorSpecFn (fun _ => false)` (`Toy.Hyper.specOf_xor_eq_full`, `Toy.Hyper.leakHigh_eq_secretIndep_xor`).
- **Card 7 (`gni-preserved-by-low-view-restrict`):**
  - Does not automatically preserve `InputTotal` (`Toy.Hyper.lowViewRestrict_need_not_preserve_inputTotal`; keeping `InputTotal` requires `∀ l h, ∃ o, S ⟨l, h, o⟩ ∧ P l o`).
  - Does not formalize multi-step secrecy-preserving simulation relations or stateful/probabilistic choice resolution.
  - Gives a sufficient class, not a general characterization: exact among input-total `GNI` refinements (`Toy.Hyper.inputTotal_gni_refinement_is_lowViewRestrict`), incomplete for partial refinements (`Toy.Hyper.highFalseFullSystem`, `Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict`), and defined extensionally on the trace set rather than on how a presentation's choice variable was resolved (`Toy.Hyper.same_secure_refinement_two_presentations`, `Toy.Hyper.lowViewRestrict_full_eq_constFalse`).
- **Card 8 (`full-range-const-refinement-not-ranges-over-all`):**
  - Depends on modeling randomness as internal demonic choice rather than external input or a probability distribution.
  - `RangesOverAll` is bare output surjectivity, not cryptographic or statistical unpredictability.
  - Positive control `rangesOverAll_preserved_by_traceEquiv` uses `TraceEquiv` (extensional trace-set equality, admitting no proper refinement).
  - Models reachable outputs only, without probability weights or entropy.
- **Card 9 (`uniform-support-const-refinement-loses-min-entropy`):**
  - Depends on modeling randomness as internal system choice or abstracting distributions to `support d` before taking trace inclusion.
  - Equal supports also fail to preserve min-entropy (`Toy.Hyper.same_support_different_minEntropy`) and min-entropy is not a `Hyperprop` of `support d` (`Toy.Hyper.minEntropy_not_a_hyperprop_of_support`); **derived**: because `support skewedFullSupportDist = support (uniformDist 1)`, **no reflexive relation** on possibilistic trace sets preserves min-entropy (the empty relation preserves it only vacuously).
  - "Exact integer min-entropy `k`" means `HasMinEntropyAtLeast d k ∧ ¬ HasMinEntropyAtLeast d (k + 1)`.
  - Positive control `scaledUniform_preserves_minEntropy` uses `SameDist` (distribution equality, admitting no probability changes), while proper probabilistic refinements that do not increase the maximum outcome probability also preserve min-entropy (`Toy.Hyper.minEntropy_kept_without_sameDist`).
  - Finite `Nat`-weighted distributions over `Fin (2 ^ k)`; continuous distributions and computational pseudorandomness are not modeled, and the result neither establishes nor refutes the corresponding claims about them.
- **Card 10 (`same-dist-preserves-min-entropy`):**
  - `SameDist` is an equivalence relation (`sameDist_refl`, `sameDist_symm`, `sameDist_trans`), not a refinement order, and transfers bounds both ways (`Toy.Hyper.sameDist_minEntropy_iff`).
  - Sufficient, not necessary (`Toy.Hyper.minEntropy_kept_without_sameDist`).
  - Establishes weight-rescaling invariance of `HasMinEntropyAtLeast`, not a compiler-correctness theorem.
  - Only `d.valid` (source positivity) is used in the forward direction; `d'.valid` is unused (`Toy.Hyper.rawMinEnt_zero_target`).
  - Conditional min-entropy given attacker observations is not modeled.
- **Card 11 (`xor-presentation-secret-indep-choice-fails-gni`):**
  - Failure of secret-independent determinization belongs to the presentation `xorSpecFn`, not to the trace set `SpecOf xorSpecFn = SpecOf constLowSpecFn = fullIOSystem` (`Toy.Hyper.specOf_xor_eq_specOf_constLow`, `Toy.Hyper.secret_dependence_is_presentation_dependent`).
  - Does **not** mean a secure implementation reads `highIn`: every `GNI` determinization of `xorSpecFn` is a constant system `ofFn (fun _ _ => b)` (`Toy.Hyper.xor_gni_determinization_is_constant`, with `r _ h = h` yielding `constFalseIOSystem` in `Toy.Hyper.same_secure_refinement_two_presentations`; **derived**: by `determinize_gni_iff_resolvedOutput_secretIndependent`, `xor false (r () false) = xor true (r () true)` holds on `Bool` iff `r () true = !(r () false)`, so the exhaustive `GNI` choice functions are `r _ h = h` and `r _ h = !h`, producing `lowOut = false` and `lowOut = true`).
  - Adds no new failing target trace set beyond `lowOut = highIn` (`leakHighSystem`, `Toy.Hyper.leakHigh_eq_secretIndep_xor`) and `lowOut = !highIn`, does not contradict multi-threaded scheduler noninterference (Popescu, Hölzl, and Nipkow, CALCO 2013), and proves nothing beyond `Unit` / `Bool` without Card 14 and Card 15.
- **Card 12 (`gni-and-det-iff-obs-det-and-rectangular-domain`):**
  - Does not claim `GNI S ↔ ObsDet S` without `RectangularDomain S`, and neither `GNI` nor `RectangularDomain` rules out secret-only acceptance filtering (`Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance`).
  - Specific to single-step traces with one public output (contrast Noce, AFP 2014).
  - `Deterministic S` is used only in `GNI S → ObsDet S` (`Toy.Hyper.gni_obsDet_rectangularDomain_counterexample_no_det`), not in `GNI S → RectangularDomain S` or `ObsDet S → RectangularDomain S → GNI S`.
- **Card 13 (`gni-iff-obs-det-of-deterministic-input-total`):**
  - Corollary of Card 12 via `inputTotal_imp_rectangularDomain`; `InputTotal` weakens to `AcceptanceIgnoresHigh` (`Toy.Hyper.gni_iff_obsDet_of_deterministic_acceptanceIgnoresHigh`) or `RectangularDomain`.
  - `Deterministic S` is not needed for `ObsDet S → GNI S`.
  - Specific to single-step traces (contrast Noce, AFP 2014).
- **Card 14 (`gni-of-fn-iff-secret-independent`):**
  - Corollary of Card 13 + `obsDet_ofFn_iff_secretIndependent`.
  - `determinize_gni_iff_resolvedOutput_secretIndependent` constrains `fun l h => f l h (r l h)` only, **not** `SecretIndependent r`.
  - Stated for single-step total pure functions; it neither establishes nor refutes the corresponding claims about stateful multi-step interactive systems.
- **Card 15 (`exists-input-total-gni-refinement-iff-exists-choice`):**
  - Under `[Nonempty H]`, equivalent to `∃ g : L → O, ∀ l h, SpecOf f ⟨l, h, g l⟩` (`Toy.Hyper.exists_choice_iff_exists_low_function`; `[Nonempty H]` is necessary by `Toy.Hyper.emptyHigh_no_low_function_edge_case`).
  - `Deterministic S'` adds nothing (`Toy.Hyper.exists_inputTotal_gni_refinement_iff_det`), whereas `InputTotal S'` cannot be dropped (`Toy.Hyper.partial_det_gni_refinement_exists_without_choice`).
  - Existence-only (`Classical.choice`); does not imply a trace-refining compiler chooses `S'`, does not make `r` secret-independent or computable, does not require `GNI (SpecOf f)` (`Toy.Hyper.nonGNI_spec_with_secure_determinization`), and does not extend to multi-step reactive causality without lookahead restrictions.
- **Card 16 (`gni-input-total-spec-admits-det-gni-refinement`):**
  - Instance `S' := SpecOf f` of Card 15; `Refines`, `Deterministic`, and `InputTotal` of `determinize f r` hold for *every* `r`.
  - Uses `Classical.choice`; the witness `determinize f r` need not resemble `f` operationally (constant on `xorSpecFn`) and `r` need not be secret-independent or computable.
  - Existence of one secure determinization does **not** make arbitrary trace-inclusion refinements secure (`Toy.Hyper.gni_not_preserved_by_inputTotal_refinement`), `GNI (SpecOf f)` is not necessary for a secure determinization to exist (`Toy.Hyper.nonGNI_spec_with_secure_determinization`), and `InputTotal (SpecOf f)` cannot be dropped (`Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal`; **derived**: a nonempty partial `GNI` system such as `echoLowHighFalseSystem` rejects `highIn = true` and therefore admits no `InputTotal` refinement at all).

### Escape Hatches for Counterexample Results

- **Defeating the `GNI` refinement paradox (Card 6 `gni-refinement-paradox-input-total`):**
  1. Require `ObsDet` of the specification **and** `InputTotal` (or `AcceptanceIgnoresHigh` / `RectangularDomain`) of the refinement: `ObsDet` is preserved by trace inclusion (Card 5, `Toy.Hyper.obsDet_preserved_by_refinement`), and together with a rectangular acceptance domain it implies `GNI` (`Toy.Hyper.gni_of_obsDet_of_rectangularDomain`, Cards 12–13). `ObsDet` alone does **not** imply `GNI` (`diagonalPartialSystem` satisfies `ObsDet` and violates `GNI`, `Toy.Hyper.gni_obsDet_total_counterexample_no_inputTotal`; **derived**: a partial trace-inclusion refinement of an `ObsDet`, `GNI`, input-total specification — for example `diagonalPartialSystem` refining `ofFn (fun _ _ => false)` — keeps `ObsDet` by Card 5 yet breaks `GNI` by dropping inputs jointly in `(lowIn, highIn)`). Cost: all low-visible nondeterminism is forbidden (`Toy.Hyper.obsDet_at_most_one_output`);
  2. Restrict trace-inclusion refinements to public-view filters `lowViewRestrict S P` (Card 7, exact among input-total `GNI` refinements); or
  3. Replace bare trace inclusion with a simulation-based secrecy-preserving refinement relation (Mantel 2001; Alur, Černý, and Zdancewic 2006; Attiya and Enea 2019 — not formalized here).
- **Defeating randomness and min-entropy collapse (Cards 8 & 9):**
  1. Model random coins as external inputs supplied by the environment under an input-total refinement contract rather than internal system choice;
  2. Keep probability distributions in the semantics and require a distribution-level refinement under which `max_x Pr[d' = x] ≤ max_x Pr[d = x]` (or `SameDist` as an equality special case, Card 10), rather than projecting to `support d`; or
  3. Degenerate case `k = 0` (`Fin 1`), where `0 = k` so no positive entropy exists to lose (`fullRange_const_refinement_counterexample_k_zero`, `uniform_support_const_refinement_counterexample_k_zero`).
- **Defeating secret-independent choice failure on `xorSpecFn` (Card 11):**
  1. Re-present the identical trace set `fullIOSystem` as `out = c` (`constLowSpecFn`), where constant choice `r _ _ = false` is secret-independent and satisfies `GNI` (`Toy.Hyper.constLowPresentation_admits_secretIndep_gni_choice`);
  2. Sample `c` uniformly at random rather than deterministically fixing `c` (moving from possibilistic `SpecOf` to a probabilistic model); or
  3. Select the target system directly on the trace set via `lowViewRestrict` (`Toy.Hyper.lowViewRestrict_proper_gni_control_instance`) or allow the Skolem witness `r` to cancel `highIn` (`Toy.Hyper.xorPresentation_admits_secretDependent_gni_choice`).

### Tightness Status, Disproved/Withdrawn Statements, and Unexamined Scope

- **Hypotheses with `unknown` tightness:** **None.** Every explicit or bundled hypothesis across all 16 cards is either proved `tight` with a kernel-checked Lean counterexample (`hRef` and `hOD` on Card 5; `hGNI` on Card 7; `hk` on Cards 8 and 9; `hSame`, `hEnt`, and `d.valid` on Card 10; `hDet` and `hTot` on Card 13; `hGNI` and `hTot` on Card 16; plus corollary hypotheses `hGNI` on Card 11 and `hDet` on Card 12) or proved `harmless` (`P` on Card 7, `v` on Card 8, and `d'.valid` in the forward direction of Card 10 via `Toy.Hyper.rawMinEnt_zero_target`).
- **Disproved or withdrawn statements:** **None.** No statement in this package was disproved or withdrawn; all 16 main statements are kernel-proved under the standard Lean axioms (`0` withdrawn, `0` disproved).
- **Unexamined or unsupported cases (`not examined` / `unsupported`):**
  - `not examined`: Cross-language trace relations (`τ_S ~ τ_T`), contextual robust hyperproperty preservation (`RSCHP`), multi-step labeled transition systems / CSP trace interleavings, infinite-trace topological hypersafety, sub-probability / demonic-probabilistic `pGCL` refinement orders, conditional min-entropy given public observations, and microarchitectural timing/cache leakage models.
  - `unsupported`: Real-valued or measure-theoretic probability spaces and computational adversary bounds (the Lake project uses core Lean 4 + `Std` only, with no Mathlib).

## Evidence

### Lean Kernel Audit Summary

- **Toolchain:** `leanprover/lean4:v4.34.1` (GitHub repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).
- **Project:** `lean/lakefile.toml` (`name = "toy_hyper"`, single `[[lean_lib]]` target `ToyHyper`, zero `[[require]]` dependencies; modules `ToyHyper.Core`, `ToyHyper.Noninterference`, `ToyHyper.Randomness`, `ToyHyper.Determinization`).
- **Observation / audit date:** `2026-11-20`.
- **Declaration sweep (`audit/axioms.json`):** `319` non-internal declarations in `ToyHyper.*` audited via `Lean.collectAxioms`; `0` banned tokens (`sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `Lean.ofReduceBool`, `Lean.ofReduceNat`); every declaration uses a subset of `{"propext", "Classical.choice", "Quot.sound"}`.
- **Statement and closure hashes (`audit/statements.json`):** `50` card-referenced declarations hashed via `audit/verify_audit.py` under `leanprover/lean4:v4.34.1`:
  - `statement_sha256`: SHA-256 of UTF-8 `toString (repr ci.type)`.
  - `closure_sha256` and `closure_size`: starting from `ci.type.getUsedConstants`, perform a transitive DFS restricted to constants `c` whose defining module has a `[[lean_lib]]` root from `lean/lakefile.toml` (`ToyHyper`) as prefix; for each visited constant `c` with `ConstantInfo` `cc`, traverse `cc.type.getUsedConstants`, plus `v.getUsedConstants` whenever `cc.value? (allowOpaque := true) = some v` and `!cc.isTheorem`, plus `iv.ctors` whenever `cc` is `.inductInfo iv`. Format each constant `c` in the closure as `c.toString ++ " : " ++ toString (repr cc.type)`, appending `" := " ++ toString (repr v)` whenever `!cc.isTheorem` and `cc.value? (allowOpaque := true) = some v` (theorem proof values are omitted). Sort these lines lexicographically, join with `"\n"`, UTF-8 encode, and take SHA-256 (`closure_sha256`), with `closure_size` equal to the number of constants in the closure.

#### Hashed Card Declarations (`audit/statements.json` and `audit/axioms.json`)

| Declaration | Card Role | Axioms (`Lean.collectAxioms`) | Closure Size | `statement_sha256` | `closure_sha256` |
| :--- | :--- | :--- | ---: | :--- | :--- |
| `Toy.Hyper.constLowPresentation_admits_secretIndep_gni_choice` | #11 `xor-presentation-secret-indep-choice-fails-gni` (positive control) | `Quot.sound`, `propext` | 14 | `67ba66a3524818be73036a7ee3dc08316b7e5a6e001bd37ae42c9bf58d072cf9` | `fe64ad22c833208ef8846836a27b42579bfe34678167ca1731fdece84afabb7b` |
| `Toy.Hyper.exists_det_inputTotal_gni_refinement_iff` | #15 `exists-input-total-gni-refinement-iff-exists-choice` (corollary/core) | `Classical.choice`, `Quot.sound`, `propext` | 12 | `932a4b3963d7917fa4e183635174b98b716a986858564c092c47c372f3e2a0e1` | `756c2c14ace2a614f62001eedb0003099e687a52b9b4ee657629ebcf183dadea` |
| `Toy.Hyper.exists_inputTotal_gni_refinement_iff_exists_choice` | #15 `exists-input-total-gni-refinement-iff-exists-choice` (main) | `Classical.choice`, `Quot.sound`, `propext` | 11 | `006dabc4f174eb090d64d26c5099826022af27bf8dafc1823e2bc365caf69876` | `d8fb5c9a82493b953a2f1f9e5bfe7fafb599effa0c80818aea2648c467c174f3` |
| `Toy.Hyper.exists_inputTotal_gni_refinement_nonvacuity` | #15 `exists-input-total-gni-refinement-iff-exists-choice` (non-vacuity) | `(none)` | 14 | `2d93d5e7958c611596a04ee4f6424d7aa9d76bfbec5b390d006a552f2c68a35b` | `26e87699fe4e87ba1ddd5234fe8da753e389307c555fd7863b190def2be6a392` |
| `Toy.Hyper.fullRange_const_refinement_counterexample_k_zero` | #8 `full-range-const-refinement-not-ranges-over-all` (`hk` counterexample) | `Quot.sound`, `propext` | 4 | `a2726c74190ab7215b7b35e80e5bb69fda24813513920d6f7cd6e1a19758de27` | `070936e97f255655b3eb396c0d7601f07e8e354ae8542280702337741def1bef` |
| `Toy.Hyper.fullRange_const_refinement_nonvacuity` | #8 `full-range-const-refinement-not-ranges-over-all` (non-vacuity) | `Quot.sound`, `propext` | 6 | `4fa223f9c6d4a1d0179cea620f70a58a5c3240baa782481f9012d4c55088c701` | `6083d78768c9d5ec44d08f3843e12cab96cea0f6355cfaeff80ec87ed5b1e942` |
| `Toy.Hyper.fullRange_const_refinement_not_rangesOverAll_of_pos` | #8 `full-range-const-refinement-not-ranges-over-all` (main) | `Quot.sound`, `propext` | 6 | `d097e4a0e62f99a21b2f066fca0fa8e45b64d39413a7113c927d85b0ce14d936` | `6083d78768c9d5ec44d08f3843e12cab96cea0f6355cfaeff80ec87ed5b1e942` |
| `Toy.Hyper.gni_and_deterministic_iff_obsDet_and_rectangularDomain` | #12 `gni-and-det-iff-obs-det-and-rectangular-domain` (main) | `(none)` | 10 | `3621e82d783a58baabf9d72ce8dd8ca9cdd52bff6a28fe103fee4badad01ada1` | `711f7842648fdfc615bb000e06a108016498025f6ad5e6f124f2589e76ba509a` |
| `Toy.Hyper.gni_iff_obsDet_and_rectangularDomain_of_deterministic` | #12 `gni-and-det-iff-obs-det-and-rectangular-domain` (corollary/core) | `(none)` | 10 | `084f50a3015540471bc35e4ed5a3e994063771cacdd50e7238eeb2440daf7ebb` | `711f7842648fdfc615bb000e06a108016498025f6ad5e6f124f2589e76ba509a` |
| `Toy.Hyper.gni_iff_obsDet_of_deterministic_acceptanceIgnoresHigh` | #13 `gni-iff-obs-det-of-deterministic-input-total` (corollary/core) | `(none)` | 10 | `2aad362b299efe6256bccd3c2a5a7f476b2ffa83125093785ad508062ac996e7` | `06f47efbab41dc807679086faaa4b71fd1f7a8fa125327a467fb4142a9a83e39` |
| `Toy.Hyper.gni_iff_obsDet_of_deterministic_inputTotal` | #13 `gni-iff-obs-det-of-deterministic-input-total` (main) | `(none)` | 10 | `2a8d6ae28902f6b27ffaa175bc8af4694230f149740cf37c6a6b767bd38e7888` | `77089f6ea02c53819fd4942a85249f77b12ad4b2115c144164fa50c6e24daa28` |
| `Toy.Hyper.gni_inputTotal_spec_admits_det_gni_refinement` | #16 `gni-input-total-spec-admits-det-gni-refinement` (main) | `Classical.choice`, `Quot.sound`, `propext` | 11 | `4759523c0ff6947fee50567f02c167cb8fd7ecdbc31cd0a56f8bbf6d52c3aae0` | `ee91bf443d60accc3fbf4cb9893b359177ac2add1bb23026d39da2fb91fd396b` |
| `Toy.Hyper.gni_inputTotal_spec_admits_nonvacuity` | #16 `gni-input-total-spec-admits-det-gni-refinement` (non-vacuity) | `propext` | 10 | `415fec0bfa95ec87023e5b3033a2b9932684aa001da43489e0fcaae2b2a6d8ee` | `62e7294af8a4ecae2dba51eaf658dc9f25deaef8bcf42e9f1d3b066b91f5f66c` |
| `Toy.Hyper.gni_inputTotal_spec_counterexample_no_gni` | #16 `gni-input-total-spec-admits-det-gni-refinement` (`hGNI` counterexample) | `(none)` | 12 | `53a94622ebb3a1ae4f4ee0fb86e75a389f2b2a6b6da2557371ba3e036e8a1536` | `b6168ec45bf08146dfbe5fc8023f81525ab57fc65a46a52ecfb4f9bbfbcc3a2d` |
| `Toy.Hyper.gni_inputTotal_spec_counterexample_no_inputTotal` | #16 `gni-input-total-spec-admits-det-gni-refinement` (`hTot` counterexample) | `(none)` | 12 | `0f84fbfd1757ca36a11e817fbfd421060a6e635101d847ce9823c2e3431e853d` | `1cfc09f39c224d7df467f6a55143c3b2d148f1d92d65f31b0a180073055ccbe1` |
| `Toy.Hyper.gni_lowViewRestrict_counterexample_no_gni` | #7 `gni-preserved-by-low-view-restrict` (`hGNI` counterexample) | `(none)` | 10 | `47d7157a3728e27abb0238ca92f6eb618c151ad47c5698946910e3d4cdf320c4` | `93da49ba993fddf5aef1b8ddf905e7f4fd94f20696233c1a8311725d70629636` |
| `Toy.Hyper.gni_not_preserved_by_inputTotal_refinement` | #6 `gni-refinement-paradox-input-total` (main); #6 `gni-refinement-paradox-input-total` (non-vacuity) | `(none)` | 13 | `bdf0829634dbf26007e4e96bc821b6b2955ae232e876419f22f056f7d464fae1` | `0553ddbada20444708f2e366340d047c885b025cf2506a57827b3ed604836bc4` |
| `Toy.Hyper.gni_obsDet_rectangularDomain_nonvacuity` | #12 `gni-and-det-iff-obs-det-and-rectangular-domain` (non-vacuity) | `(none)` | 13 | `391cb46bd63a805f82eaaa92551dde754079e082d4c9172640466829bb8f6ad0` | `6e8d9069513d260f385f5a246e9d6084e7fb961f7cc3b4bf22c4d7004a104cd4` |
| `Toy.Hyper.gni_obsDet_total_counterexample_no_det` | #13 `gni-iff-obs-det-of-deterministic-input-total` (`hDet` counterexample) | `(none)` | 11 | `2e7375f26a2f2cec04ca2dfcb369767c5391273d510f7aaae1c6ff65d7fc9519` | `6fc626022dc9c7e6e3cd4ac816cda7ebf41f714ac6056eefb6d824b8c5e8eb4f` |
| `Toy.Hyper.gni_obsDet_total_counterexample_no_inputTotal` | #13 `gni-iff-obs-det-of-deterministic-input-total` (`hTot` counterexample) | `(none)` | 11 | `27571fda973fca47c8826e5af724edeac6d570c2269c7b4ee5a3b1fd70ff9ea9` | `d713581e7a214e1025af5ec3182378a2578ad073a40c1c7e1b53e32de483ae9d` |
| `Toy.Hyper.gni_obsDet_total_nonvacuity` | #13 `gni-iff-obs-det-of-deterministic-input-total` (non-vacuity) | `(none)` | 14 | `386114c2dd864fa62a69f86d6f4085fc5245cbba100c757109e010376cc730ae` | `3fd177bd725d49e8ebd43b31e2d18d6617465226c6ce157fb34cacb9da17ea23` |
| `Toy.Hyper.gni_ofFn_iff_secretIndependent` | #14 `gni-of-fn-iff-secret-independent` (main) | `(none)` | 9 | `e931f5dc4be82d08514239a40f5341cd9377a7437911d04d835db359ddc6f2e6` | `28036b29857c47adb24729f8e2cebf1d49a896fbeffc27c23c0c95d2657a15c8` |
| `Toy.Hyper.gni_ofFn_iff_secretIndependent_nonvacuity` | #14 `gni-of-fn-iff-secret-independent` (non-vacuity) | `(none)` | 9 | `936578ed093f0f5a91cfdec3110d24634326b471ea51821cd5e72de2b94095f2` | `28036b29857c47adb24729f8e2cebf1d49a896fbeffc27c23c0c95d2657a15c8` |
| `Toy.Hyper.gni_preserved_by_lowViewRestrict` | #6 `gni-refinement-paradox-input-total` (positive control); #7 `gni-preserved-by-low-view-restrict` (main) | `(none)` | 8 | `f29133ee3092b2cee474d4e018077e2aacbe46998810aa099c85119457f4c6ca` | `745a910060f3ee07e0f373be3f51b6927226063dcbc79036705fdcbd42fae8f8` |
| `Toy.Hyper.liftTraceProp_subsetClosed` | #3 `trace-property-lift-subset-closed` (main) | `(none)` | 5 | `423b54606635796b67610ecf1e91150941bc53a6ecd31a000a3dfa5a08bce5c6` | `4dc94c2265dc7de311e1266b7f17707c37edcfe9af755fbfd4d914b9f80fb5ba` |
| `Toy.Hyper.liftTraceProp_subsetClosed_nonvacuity` | #3 `trace-property-lift-subset-closed` (non-vacuity) | `(none)` | 6 | `a93d5d05e4af1a5988068f63455cf67de691a05884ad871fc09335ef5f978452` | `fac9a9e46c66ed5b3e275dc9aa02cb88bd5181cb6ebe62890144ef928d19e407` |
| `Toy.Hyper.lowViewRestrict_proper_gni_control_instance` | #6 `gni-refinement-paradox-input-total` (positive control); #7 `gni-preserved-by-low-view-restrict` (non-vacuity) | `Quot.sound`, `propext` | 14 | `bdbbeabbb7baa44f3e783bb924d5c2fd7edb43c812dd2b9995c3a54115128efb` | `9c7e26ae7174231a13f72a4f0119d9c864c6927ee69a08726bda75d40affe076` |
| `Toy.Hyper.obsDet_preserved_by_refinement` | #5 `obs-det-preserved-by-refinement` (main) | `(none)` | 7 | `7cc1111ca953d843d0ee7d5915be38bbe7aadfd34bb72cb3812ec0aa49973cdc` | `8cb7d78247826a45dad10b01491e63271850c340aa9c8f95e46519b3002e83d7` |
| `Toy.Hyper.obsDet_refinement_counterexample_no_obsDet` | #5 `obs-det-preserved-by-refinement` (`hOD` counterexample) | `(none)` | 11 | `311229e3d1b58fe8b81f54b4dcad77e7aac79d58e07416e355935a3c6ffce739` | `302e6e13729878100d048798907c572762cb0de751b3c7da362020e6fc426981` |
| `Toy.Hyper.obsDet_refinement_counterexample_no_refines` | #5 `obs-det-preserved-by-refinement` (`hRef` counterexample) | `(none)` | 11 | `d79159d5e10e44995d8329dee01fd50b44cd68c19158012193c67946f1e3adef` | `e4d25606708c2e4155f4690a130643435bb3240347765f8a884ffdb948287a7c` |
| `Toy.Hyper.obsDet_refinement_nonvacuity` | #5 `obs-det-preserved-by-refinement` (non-vacuity) | `(none)` | 11 | `70af8c9a5397957b6dfc196f12cfbe678faa694c119714a1457eb2de57a467fa` | `c94a1cdfab33c08c88b9e22a6d1088be979d6f410c26a7af7f812de88c66bf8b` |
| `Toy.Hyper.proportionalWeights_minEntropy_counterexample_source_not_valid` | #10 `same-dist-preserves-min-entropy` (`d.valid (ValidWeights d.weight, bundled in FinDist)` counterexample) | `Quot.sound`, `propext` | 15 | `0561f3f0ef0d931701d86f3aa6d58238e186498fe26b47f57f9560f2a8149631` | `91f9a236257b0454733c3e5d4aa420771e4804a4b0b11d414f37d630c650a179` |
| `Toy.Hyper.proportionalWeights_preserves_minEntropy_of_valid_source` | #10 `same-dist-preserves-min-entropy` (corollary/core) | `Quot.sound`, `propext` | 8 | `0cb66901849eb75720e1532fbb2abda831b500730a53d8c9b4484eb3746a0190` | `0c35fb46b1972ba41417f45a6b8b262945a2222fbd443b84749913be43eea37e` |
| `Toy.Hyper.rangesOverAll_preserved_by_traceEquiv` | #8 `full-range-const-refinement-not-ranges-over-all` (positive control) | `(none)` | 5 | `a86116be46b9603320ae0a95ba00bec8b568a00a4cc377b3e7fc08112ac18fd1` | `c539ed301a71167802cb4f5e1d3a0ebb1fd722ea068ae7e79414db7f77e03e5b` |
| `Toy.Hyper.refines_iff_preserves_all_subsetClosed` | #2 `refines-iff-preserves-all-subset-closed` (main) | `(none)` | 4 | `30bae60cb4004578732113d9c3d38725b8e7fe457934faca7d82b1b35c28d9e4` | `a2fa57a16db1c49438899b3aaae0f04393895d5eb85b37e105af1cbf391ae29e` |
| `Toy.Hyper.refines_iff_preserves_all_subsetClosed_nonvacuity` | #2 `refines-iff-preserves-all-subset-closed` (non-vacuity) | `(none)` | 6 | `0c5730d5f6d4b0f10bc01842afb1bac1140fe01b6743aaa6835b6e08fc546616` | `35e9441071591e6cd60c3ac73ae6d98cbc4c93b7b77f0548ccadc15229fc02e0` |
| `Toy.Hyper.sameDist_minEntropy_counterexample_no_ent` | #10 `same-dist-preserves-min-entropy` (`hEnt` counterexample) | `Quot.sound`, `propext` | 18 | `2aa5e2080678c23f346f764a7f4d343b0c21c415bb568c001a17c33b2dbee195` | `8d3b3ff52ee115d78a7b20880aae1eca350dde95254d6a5909c87d0fcb97f64f` |
| `Toy.Hyper.sameDist_minEntropy_counterexample_no_sameDist` | #10 `same-dist-preserves-min-entropy` (`hSame` counterexample) | `Quot.sound`, `propext` | 23 | `97a4ff48f3bd3295d5bb75a0d501fe61d920a566ce6e2e8a308a956a944b7c96` | `2d1aab9491a607f316f4a6c9acd2b9ecbe6bc97cc649cb0869e5d7cc0e93baea` |
| `Toy.Hyper.sameDist_preserves_minEntropy` | #10 `same-dist-preserves-min-entropy` (main) | `Quot.sound`, `propext` | 14 | `e438fbbf250ad85c3fa371481d5066d93bd1125e6271528609ad012596c2b8d8` | `adf44386bbd00ac1b804b95f82699e198041bd0c1a51a88d23cc8eb67fa62ce2` |
| `Toy.Hyper.sameDist_preserves_minEntropy_nonvacuity` | #10 `same-dist-preserves-min-entropy` (non-vacuity) | `Quot.sound`, `propext` | 18 | `b1d139fdbaba59109c0069f61cbcb77b116e68095f0911820bb888b6ca78ee11` | `552078dffc8750a672a7327d60bbd2a4139048e33da261850b38eb837b0c1e0e` |
| `Toy.Hyper.scaledUniform_preserves_minEntropy` | #9 `uniform-support-const-refinement-loses-min-entropy` (positive control) | `Quot.sound`, `propext` | 18 | `16ad30d25c0d3263c135f5ecd43d2ae86e4fefcf333f742bd94357a32a43d7c2` | `552078dffc8750a672a7327d60bbd2a4139048e33da261850b38eb837b0c1e0e` |
| `Toy.Hyper.secretIndepDeterminize_fails_gni_on_xorPresentation` | #11 `xor-presentation-secret-indep-choice-fails-gni` (main); #11 `xor-presentation-secret-indep-choice-fails-gni` (non-vacuity) | `propext` | 15 | `aa287543cab23ec2221f8fabdb4c0a3c44633ae2e1b86aebe547ed378cb4f88f` | `993e24724a27cfae824ac3281964a3cdc197b48f616504f3e558716e0b76c1d4` |
| `Toy.Hyper.subsetClosed_char_nonvacuity` | #1 `subset-closed-iff-refinement-preserved` (non-vacuity) | `(none)` | 8 | `44f84db0ef043647a56660ebff552816fe4d3b018d8cdd26d154f8ec025bf11b` | `db5e7381a78714afa152a0b5053b58ae7cd6ceb8ab141cc0695aa1f3c20605c2` |
| `Toy.Hyper.subsetClosed_iff_preservedByAllRefiningCompilers` | #1 `subset-closed-iff-refinement-preserved` (main) | `Quot.sound`, `propext` | 6 | `3725dcb3e88f5949fb2207b5be3b9f873e1d23a90b1cf59c089f6afc345cb2ee` | `ea75d328a3dbb9dc19b22b67457cda0cf7a75809e23722a0d3ec87e61f723b82` |
| `Toy.Hyper.uniform_support_const_refinement_counterexample_k_zero` | #9 `uniform-support-const-refinement-loses-min-entropy` (`hk` counterexample) | `Quot.sound`, `propext` | 16 | `b149403bc56974ee13411cf66ef78471baa70d5de04a4f2f9288829d67a30afd` | `7160e24e87d1281633158469b0b0f171b9bcbfb93cb685825154a6a39048012a` |
| `Toy.Hyper.uniform_support_const_refinement_nonvacuity` | #9 `uniform-support-const-refinement-loses-min-entropy` (non-vacuity) | `Quot.sound`, `propext` | 21 | `432c53158e9872fe62755d5b868723c572e5abc5dad4f79762f576d0cdb16f1c` | `c2abe66843b6930fed73fe426fb00e8705436fb9ff935dfe02df94d879723340` |
| `Toy.Hyper.uniform_support_refined_by_const_loses_minEntropy_of_pos` | #9 `uniform-support-const-refinement-loses-min-entropy` (main) | `Quot.sound`, `propext` | 21 | `a8343c279bbfdbdfb2aa0471c687a559bcacb7e0e124b98de3150bd4fbdb030e` | `c2abe66843b6930fed73fe426fb00e8705436fb9ff935dfe02df94d879723340` |
| `Toy.Hyper.universalKHyperprop_subsetClosed` | #4 `universal-k-hyperprop-subset-closed` (main) | `(none)` | 4 | `5aa9856708c0937e3575f9d65a6dd0283a05261559819865ad86dd1a1e9cd1b5` | `f582e79b9e4f07bec4310ba71b688e4705cab04107bd9fad1f939cf019b3aa2a` |
| `Toy.Hyper.universalKHyperprop_subsetClosed_nonvacuity` | #4 `universal-k-hyperprop-subset-closed` (non-vacuity) | `Quot.sound`, `propext` | 5 | `34a1eadfedc907c0d82bd9b0667d689a628910f1dfa57bf4d5a1f7a842c4b63a` | `44ed32c51f763ecde6e4082cd48645cc17d78de6b9a08fb9a08f165d2584ddbe` |
| `Toy.Hyper.xorPresentation_admits_secretDependent_gni_choice` | #11 `xor-presentation-secret-indep-choice-fails-gni` (positive control) | `(none)` | 14 | `0146e46875548f2e26c58ae70af425b9fc984c07f614eea4888498a70cf0e3a5` | `32c9c2cb2b59b33242c0c40c3f77ad6a1f369e57c0747646757632eb6f42b437` |

#### Supporting Structural and Boundary Theorems (`audit/axioms.json`)

| Declaration | Role | Axioms (`Lean.collectAxioms`) |
| :--- | :--- | :--- |
| `Toy.Hyper.liftTraceProp_iff_universal1Hyperprop` | Card 3 equivalence with `k = 1` universal hyperproperty | `propext` |
| `Toy.Hyper.obsDet_not_liftTraceProp` | Card 3 boundary: `ObsDet` is not a lifted single-trace property | `(none)` |
| `Toy.Hyper.boundedNatSystem_subsetClosed_not_universalKHyperprop` | Card 4 boundary: subset-closed hyperproperty outside `UniversalKHyperprop k Rel` for every `k` | `Quot.sound`, `propext` |
| `Toy.Hyper.traceEquiv_preserves_hyperprop` | Cards 6 & 8 structural lemma: `TraceEquiv` forces extensional trace-set equality | `Quot.sound`, `propext` |
| `Toy.Hyper.gni_iff_low_view_compatible_with_every_secret` | Cards 6, 7, 15 structural characterization of single-step `GNI` | `(none)` |
| `Toy.Hyper.obsDet_at_most_one_output` | Card 5 boundary: `ObsDet` allows at most one public output per public input | `(none)` |
| `Toy.Hyper.obsDet_iff_universal2Hyperprop` | Card 5 equivalence with `k = 2` universal hyperproperty | `propext` |
| `Toy.Hyper.inputTotal_refinement_of_deterministic_eq` | Cards 1 & 6 boundary: input-total refinement of a deterministic system is `S' = S` | `Quot.sound`, `propext` |
| `Toy.Hyper.gni_preserved_by_inputTotal_refinement_of_deterministic` | Card 6 degenerate control (`S' = S` when source is deterministic) | `Quot.sound`, `propext` |
| `Toy.Hyper.gni_not_subsetClosed` | Card 6 corollary: `GNI` is not subset-closed | `(none)` |
| `Toy.Hyper.lowViewRestrict_refines` | Card 7 structural lemma: `lowViewRestrict S P` refines `S` | `(none)` |
| `Toy.Hyper.lowViewRestrict_full_eq_constFalse` | Cards 6 & 7 structural equality `lowViewRestrict fullIOSystem (fun _ o => o = false) = constFalseIOSystem` | `Quot.sound`, `propext` |
| `Toy.Hyper.lowViewRestrict_need_not_preserve_inputTotal` | Card 7 boundary: `lowViewRestrict` need not preserve `InputTotal` | `(none)` |
| `Toy.Hyper.secretFiltered_refinement_preserves_gni_not_lowViewRestrict` | Card 7 boundary: partial secret-filtered refinement keeps `GNI` outside `lowViewRestrict` | `(none)` |
| `Toy.Hyper.inputTotal_gni_refinement_is_lowViewRestrict` | Card 7 boundary: `lowViewRestrict` is exact among input-total `GNI` refinements | `Quot.sound`, `propext` |
| `Toy.Hyper.fullRange_const_refinement_not_conclusion_at_zero` | Card 8 negated full conclusion at `k = 0` | `Quot.sound`, `propext` |
| `Toy.Hyper.uniform_support_const_refinement_not_conclusion_at_zero` | Card 9 negated full conclusion at `k = 0` | `Quot.sound`, `propext` |
| `Toy.Hyper.same_support_different_minEntropy` | Card 9 boundary: equal supports (`TraceEquiv`) fail to preserve min-entropy | `Quot.sound`, `propext` |
| `Toy.Hyper.minEntropy_not_a_hyperprop_of_support` | Card 9 boundary: min-entropy is not a `Hyperprop` of `support d` | `Quot.sound`, `propext` |
| `Toy.Hyper.rawMinEnt_zero_target` | Card 10 harmlessness witness: all-zero target table satisfies `RawMinEnt` | `Quot.sound`, `propext` |
| `Toy.Hyper.sameDist_minEntropy_iff` | Card 10 two-sided invariance corollary via `sameDist_symm` | `Quot.sound`, `propext` |
| `Toy.Hyper.minEntropy_kept_without_sameDist` | Card 10 boundary: `SameDist` is sufficient, not necessary, to preserve min-entropy | `propext` |
| `Toy.Hyper.proportionalWeights_without_valid_fails` | Card 10 boundary: `ProportionalWeights` fails transitivity without `ValidWeights` | `Quot.sound`, `propext` |
| `Toy.Hyper.specOf_xor_eq_specOf_constLow` | Card 11 boundary: `xorSpecFn` and `constLowSpecFn` denote the exact same trace set | `Quot.sound`, `propext` |
| `Toy.Hyper.leakHigh_eq_secretIndep_xor` | Cards 6 & 11 link: `leakHighSystem = secretIndepDeterminize xorSpecFn (fun _ => false)` | `Quot.sound`, `propext` |
| `Toy.Hyper.xor_gni_determinization_is_constant` | Cards 11, 15, 16 boundary: every `GNI` determinization of `xorSpecFn` is a constant system | `Quot.sound`, `propext` |
| `Toy.Hyper.same_secure_refinement_two_presentations` | Cards 7 & 11 boundary: secret-dependent choice on `xorSpecFn` equals secret-independent choice on `constLowSpecFn` | `Quot.sound`, `propext` |
| `Toy.Hyper.xorPresentation_gni_choice_not_secretIndependent` | Card 11 named corollary: every `GNI` choice index on `xorSpecFn` fails `SecretIndependent` | `Quot.sound`, `propext` |
| `Toy.Hyper.xorPresentation_gni_choice_nonvacuity` | Card 11 corollary non-vacuity witness (`r _ h = h`) | `(none)` |
| `Toy.Hyper.xorPresentation_gni_choice_counterexample_no_gni` | Card 11 corollary `hGNI` tightness counterexample (`r _ _ = false`) | `propext` |
| `Toy.Hyper.secret_dependence_is_presentation_dependent` | Card 11 summary boundary theorem: choice secret-dependence belongs to `f`, not `SpecOf f` | `Quot.sound`, `propext` |
| `Toy.Hyper.obsDet_imp_deterministic` | Cards 12 & 13 directional lemma: `ObsDet S -> Deterministic S` | `(none)` |
| `Toy.Hyper.gni_imp_rectangularDomain` | Card 12 minimal directional lemma: `GNI S -> RectangularDomain S` | `(none)` |
| `Toy.Hyper.obsDet_of_gni_of_deterministic` | Card 12 minimal directional lemma: `Deterministic S -> GNI S -> ObsDet S` | `(none)` |
| `Toy.Hyper.gni_of_obsDet_of_rectangularDomain` | Card 12 minimal directional lemma: `ObsDet S -> RectangularDomain S -> GNI S` | `(none)` |
| `Toy.Hyper.rectangularDomain_iff_product` | Card 12 product-set characterization of `RectangularDomain` | `(none)` |
| `Toy.Hyper.gni_and_rectangularDomain_allow_secret_filtered_acceptance` | Cards 5, 6, 12 boundary: `echoLowHighFalseSystem` satisfies `GNI`, `ObsDet`, and `RectangularDomain` | `(none)` |
| `Toy.Hyper.gni_obsDet_rectangularDomain_counterexample_no_det` | Card 12 tightness witness for `Deterministic S` in conditional corollary | `(none)` |
| `Toy.Hyper.acceptanceIgnoresHigh_not_imp_inputTotal` | Card 13 strictness: `AcceptanceIgnoresHigh` is strictly weaker than `InputTotal` | `(none)` |
| `Toy.Hyper.determinize_gni_iff_resolvedOutput_secretIndependent` | Card 14 choice-presentation corollary for `determinize f r` | `(none)` |
| `Toy.Hyper.secretIndepDeterminize_gni_iff_resolvedOutput_secretIndependent` | Card 14 choice-presentation corollary for `secretIndepDeterminize f g` | `(none)` |
| `Toy.Hyper.exists_inputTotal_gni_refinement_iff_det` | Card 15 corollary: determinism adds nothing for input-total `GNI` refinements | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Hyper.exists_choice_iff_common_output` | Card 15 choice-free common-output characterization | `Classical.choice`, `Quot.sound`, `propext` |
| `Toy.Hyper.exists_choice_iff_exists_low_function` | Card 15 presentation-free trace-set characterization under `[Nonempty H]` | `Classical.choice` |
| `Toy.Hyper.emptyHigh_no_low_function_edge_case` | Card 15 edge case showing `[Nonempty H]` is necessary | `(none)` |
| `Toy.Hyper.partial_det_gni_refinement_exists_without_choice` | Card 15 boundary: `InputTotal S'` cannot be dropped from the left-hand existential | `(none)` |
| `Toy.Hyper.nonGNI_spec_with_secure_determinization` | Cards 15 & 16 boundary: `GNI (SpecOf f)` is not necessary for a `GNI` determinization to exist | `propext` |
| `Toy.Hyper.inputTotal_specOf_iff_nonempty_choiceFn` | Card 16 structural lemma: `InputTotal (SpecOf f) <-> Nonempty (L -> H -> C)` | `Classical.choice` |

### Primary Literature and Prior Mechanization Records

Every citation in `REPORT.json`, `results.json`, and **Findings** was checked against DBLP/Crossref bibliographic metadata (`2026-11-20`), with exact inspection depth recorded so primary observations remain distinct from secondary attributions. In accordance with subject-identity discipline, only the 24 literature and prior-mechanization artifacts whose technical content was directly inspected are recorded in `REPORT.json` `subjects` (alongside the Lean 4 toolchain subject, 25 subjects total); the 11 historical works inspected only via bibliographic metadata and attributions in other inspected papers are listed separately below and omitted from `REPORT.json`.

#### Directly Inspected Literature and Prior Mechanization Subjects (`REPORT.json`, 24 entries)

1. **Clarkson and Schneider (2010 / 2008):** Michael R. Clarkson and Fred B. Schneider, "Hyperproperties", *Journal of Computer Security* 18(6):1157–1210, 2010, DOI `10.3233/JCS-2009-0393`, DBLP `journals/jcs/ClarksonS10` (conference precursor: IEEE CSF 2008, pp. 51–65, DOI `10.1109/CSF.2008.7`, DBLP `conf/csfw/ClarksonS08`). *Inspected:* full text of the 2010 journal article (Sections 1, 2, 2.6, 3, 4, 7.2.4) and DBLP record of CSF 2008.
2. **Abate et al. (CSF 2019):** Carmine Abate, Roberto Blanco, Deepak Garg, Cătălin Hrițcu, Marco Patrignani, and Jérémy Thibault, "Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation", IEEE CSF 2019, pp. 256–271, DOI `10.1109/CSF.2019.00025`, DBLP `conf/csfw/AbateB0HPT19`; extended preprint `arXiv:1807.04603v6`; Coq repository `https://github.com/secure-compilation/exploring-robust-property-preservation` at commit `c68187cbaba763d88cbb3509df4ca9cf49cc6338`. *Inspected:* full text of `arXiv:1807.04603v6` (Section 3.2, Appendix C.2.2 Theorem C.18) and `Properties.v` (`SSC`, `SSC_iff`, `lifting`, `Union_Lift_SSC`, `twoSC_SSC`, `twoSC_H2Safe`); `Criteria.v` (`RSCHC_RSCHP`) confirmed at the cited commit.
3. **Abate et al. (ESOP 2020 / TOPLAS 2021):** Carmine Abate, Roberto Blanco, Ștefan Ciobâcă, Adrien Durier, Deepak Garg, Cătălin Hrițcu, Marco Patrignani, Éric Tanter, and Jérémy Thibault, "Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020, LNCS 12075, pp. 1–28, DOI `10.1007/978-3-030-44914-8_1`, DBLP `conf/esop/AbateBCD0HPTT20`; extended journal version *ACM TOPLAS* 43(4):14:1–14:48, 2021, DOI `10.1145/3460860`, DBLP `journals/toplas/AbateBCDGHPTT21`. *Inspected:* abstract (`arXiv:1907.05320`) and DBLP records.
4. **McLean (IEEE S&P 1990):** John McLean, "Security Models and Information Flow", IEEE S&P 1990, pp. 180–189, DOI `10.1109/RISP.1990.63849`, DBLP `conf/sp/McLean90`. *Inspected:* full text.
5. **McLean (IEEE S&P 1994 / TSE 1996):** John McLean, "A general theory of composition for trace sets closed under selective interleaving functions", IEEE S&P 1994, pp. 79–93, DOI `10.1109/RISP.1994.296590`, DBLP `conf/sp/McLean94`; journal version "A General Theory of Composition for a Class of 'Possibilistic' Properties", *IEEE Trans. Software Eng.* 22(1):53–67, 1996, DOI `10.1109/32.481534`, DBLP `journals/tse/McLean96`. *Inspected:* full text of the 1994 conference paper and DBLP record of the 1996 journal paper.
6. **Roscoe, Woodcock, and Wulf (ESORICS 1994 / JCS 1996):** A. W. Roscoe, Jim Woodcock, and Lars Wulf, "Non-Interference Through Determinism", ESORICS 1994, LNCS 875, pp. 33–53, DOI `10.1007/3-540-58618-0_55`, DBLP `conf/esorics/RoscoeWW94`; journal version *Journal of Computer Security* 4(1):27–54, 1996, DOI `10.3233/JCS-1996-4103`, DBLP `journals/jcs/RoscoeWW96`. *Inspected:* publisher abstract and DBLP records.
7. **Roscoe (IEEE S&P 1995):** A. W. Roscoe, "CSP and determinism in security modelling", IEEE S&P 1995, pp. 114–127, DOI `10.1109/SECPRI.1995.398927`, DBLP `conf/sp/Roscoe95`. *Inspected:* full text (abstract and Section 8.1).
8. **Zdancewic and Myers (CSFW 2003):** Steve Zdancewic and Andrew C. Myers, "Observational Determinism for Concurrent Program Security", IEEE CSFW 2003, pp. 29–43, DOI `10.1109/CSFW.2003.1212703`, DBLP `conf/csfw/ZdancewicM03`. *Inspected:* full text.
9. **McIver and Morgan (Springer 2005):** Annabelle McIver and Carroll Morgan, *Abstraction, Refinement and Proof for Probabilistic Systems*, Monographs in Computer Science, Springer, 2005, DOI `10.1007/b138392`, DBLP `series/mcs/McIverM05`. *Inspected:* DBLP record, publisher overview, and chapter table of contents (Part I Ch. 1 pp. 3–36; Part II Ch. 5 pp. 129–164; chapter prose not inspected).
10. **Alur, Černý, and Zdancewic (ICALP 2006):** Rajeev Alur, Pavol Černý, and Steve Zdancewic, "Preserving Secrecy Under Refinement", ICALP 2006 (2), LNCS 4052, pp. 107–118, DOI `10.1007/11787006_10`, DBLP `conf/icalp/AlurCZ06`. *Inspected:* abstract and introduction.
11. **Morgan (TR 2005 / MPC 2006 / SCP 2009):** Carroll Morgan, "The Shadow Knows: Refinement of Ignorance in Sequential Programs", Technical Report `UNSW-CSE-TR-0522` (November 30, 2005), School of Computer Science and Engineering, UNSW; conference version under the same title in MPC 2006, LNCS 4014, pp. 359–378, DOI `10.1007/11783596_21`, DBLP `conf/mpc/Morgan06`; extended journal version titled "The Shadow Knows: Refinement and security in sequential programs", *Science of Computer Programming* 74(8):629–653, 2009, DOI `10.1016/j.scico.2007.09.003`, DBLP `journals/scp/Morgan09`. *Inspected:* full text of `UNSW-CSE-TR-0522` (Sections 1 and 7, "The Encryption Lemma") and DBLP records of MPC 2006 and SCP 2009 (journal prose not directly inspected).
12. **Smith (FoSSaCS 2009):** Geoffrey Smith, "On the Foundations of Quantitative Information Flow", FoSSaCS 2009, LNCS 5504, pp. 288–302, DOI `10.1007/978-3-642-00596-1_21`, DBLP `conf/fossacs/Smith09`. *Inspected:* publisher abstract and DBLP record.
13. **Golab, Higham, and Woelfel (STOC 2011):** Wojciech M. Golab, Lisa Higham, and Philipp Woelfel, "Linearizable implementations do not suffice for randomized distributed computation", STOC 2011, pp. 373–382, DOI `10.1145/1993636.1993687`, DBLP `conf/stoc/GolabHW11`. *Inspected:* abstract (`arXiv:1103.4690`) and DBLP record.
14. **Murray et al. (IEEE S&P 2013):** Toby C. Murray, Daniel Matichuk, Matthew Brassil, Peter Gammie, Timothy Bourke, Sean Seefried, Corey Lewis, Xin Gao, and Gerwin Klein, "seL4: From General Purpose to a Proof of Information Flow Enforcement", IEEE S&P 2013, pp. 415–429, DOI `10.1109/SP.2013.35`, DBLP `conf/sp/MurrayMBGBSLGK13`. *Inspected:* full text.
15. **Popescu, Hölzl, and Nipkow (CALCO 2013):** Andrei Popescu, Johannes Hölzl, and Tobias Nipkow, "Noninterfering Schedulers — When Possibilistic Noninterference Implies Probabilistic Noninterference", CALCO 2013, LNCS 8089, pp. 236–252, DOI `10.1007/978-3-642-40206-7_18`, DBLP `conf/calco/0001HN13`. *Inspected:* publisher abstract and DBLP record.
16. **Costanzo, Shao, and Gu (PLDI 2016):** David Costanzo, Zhong Shao, and Ronghui Gu, "End-to-end verification of information-flow security for C and assembly programs", PLDI 2016, pp. 648–664, DOI `10.1145/2908080.2908100`, DBLP `conf/pldi/CostanzoSG16`. *Inspected:* full text.
17. **Finkbeiner et al. (CAV 2018):** Bernd Finkbeiner, Christopher Hahn, Philip Lukert, Marvin Stenger, and Leander Tentrup, "Synthesizing Reactive Systems from Hyperproperties", CAV 2018 (1), LNCS 10981, pp. 289–306, DOI `10.1007/978-3-319-96145-3_16`, DBLP `conf/cav/FinkbeinerHLST18`. *Inspected:* abstract (`arXiv:1905.13511`) and DBLP record.
18. **Coenen et al. (CAV 2019):** Norine Coenen, Bernd Finkbeiner, César Sánchez, and Leander Tentrup, "Verifying Hyperliveness", CAV 2019 (1), LNCS 11561, pp. 121–139, DOI `10.1007/978-3-030-25540-4_7`, DBLP `conf/cav/CoenenFST19`. *Inspected:* abstract (`arXiv:2005.07425`) and DBLP record.
19. **Attiya and Enea (DISC 2019):** Hagit Attiya and Constantin Enea, "Putting Strong Linearizability in Context: Preserving Hyperproperties in Programs that Use Concurrent Objects", DISC 2019, LIPIcs 146, pp. 2:1–2:17, DOI `10.4230/LIPIcs.DISC.2019.2`, DBLP `conf/wdag/AttiyaE19`. *Inspected:* abstract (`arXiv:1905.12063`) and DBLP record.
20. **Barthe et al. (POPL 2020):** Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David Pichardie, and Alix Trieu, "Formal verification of a constant-time preserving C compiler", *Proc. ACM Program. Lang.* 4(POPL):7:1–7:30, 2020, DOI `10.1145/3371075`, DBLP `journals/pacmpl/BartheBGHLPT20`. *Inspected:* abstract (IACR ePrint `2019/926`) and DBLP record.
21. **Archive of Formal Proofs — `Noninterference_CSP`:** Pasquale Noce, "Noninterference Security in Communicating Sequential Processes", *Archive of Formal Proofs*, May 23, 2014, entry URL `https://www.isa-afp.org/entries/Noninterference_CSP.html`, `Isabelle2026` release archive `https://www.isa-afp.org/release/afp-Noninterference_CSP-2026-10-26.tar.gz` (observed `2026-11-20`). *Inspected:* AFP entry page (abstract, session outline, and release listing), whose abstract says only that generalized noninterference is "weaker"; and the theory source `thys/Noninterference_CSP/GeneralizedNoninterference.thy` (section "CSP noninterference vs. generalized noninterference") at revision `2e7a917337578454a9525c4a3e182cc3e6eb0b4f` of the `isabelle-prover/mirror-afp-devel` GitHub mirror of the AFP development repository, the most recent commit touching that file (file SHA-256 `72ff118128a5f40e08817d012123fa77cc23893bdadaa0eba7ea4315ff315ad9`, observed `2026-11-20`). That file proves theorem `c_secure_implies_g_secure` (classical noninterference of a deterministic state machine implies generalized noninterference of the corresponding process) and, via lemmas `g_secure_counterexample` and `not_c_secure_counterexample`, theorems `not_g_secure_implies_c_secure` and `not_g_secure_implies_secure`: a two-state deterministic machine (states `Even`/`Odd`; the high action `Any` toggles the state, the low action `Count` outputs it) is generalized-noninterference secure but neither classical- nor CSP-noninterference secure. These establish the strictness cited in Boundaries item 7 and Card 12. The `.tar.gz` release archive was not downloaded, so its copy of the file was not compared with the mirror.
22. **Archive of Formal Proofs — `HyperCTL`:** Markus N. Rabe, Peter Lammich, and Andrei Popescu, "A shallow embedding of HyperCTL*", *Archive of Formal Proofs*, April 16, 2014, entry URL `https://www.isa-afp.org/entries/HyperCTL.html`, `Isabelle2026` release archive `https://www.isa-afp.org/release/afp-HyperCTL-2026-10-26.tar.gz` (observed `2026-11-20`). *Inspected:* AFP entry page (abstract, session outline, and release listing); full `.thy` archive not downloaded.
23. **Archive of Formal Proofs — `Bounded_Deducibility_Security`:** Andrei Popescu, Peter Lammich, and Thomas Bauereiss, "Bounded-Deducibility Security", *Archive of Formal Proofs*, April 22, 2014 (revised August 12, 2021), entry URL `https://www.isa-afp.org/entries/Bounded_Deducibility_Security.html`, `Isabelle2026` release archive `https://www.isa-afp.org/release/afp-Bounded_Deducibility_Security-2026-10-26.tar.gz` (observed `2026-11-20`); companion paper ITP 2021, LIPIcs 193, pp. 3:1–3:20, DOI `10.4230/LIPIcs.ITP.2021.3`, DBLP `conf/itp/0001BL21`. *Inspected:* AFP entry page (abstract, history, session outline, release listing) and DBLP record; full `.thy` archive not downloaded.
24. **Archive of Formal Proofs — `HyperHoareLogic`:** Thibault Dardinier, "Formalization of Hyper Hoare Logic: A Logic to (Dis-)Prove Program Hyperproperties", *Archive of Formal Proofs*, April 3, 2023 (revised April 12, 2024), entry URL `https://www.isa-afp.org/entries/HyperHoareLogic.html`, `Isabelle2026` release archive `https://www.isa-afp.org/release/afp-HyperHoareLogic-2026-10-26.tar.gz` (observed `2026-11-20`); companion paper Thibault Dardinier and Peter Müller, *Proc. ACM Program. Lang.* 8(PLDI):1485–1509, 2024, DOI `10.1145/3656437`, DBLP `journals/pacmpl/DardinierM24`. *Inspected:* AFP entry page (abstract, history, session outline, release listing) and DBLP record; full `.thy` archive not downloaded.

*AFP identity note:* AFP entry pages (`https://www.isa-afp.org/entries/<Entry>.html`) are mutable web pages that track the latest Isabelle release; `REPORT.json` pairs each entry URL with the dated `Isabelle2026` release archive (`afp-<Entry>-2026-10-26.tar.gz`) observed on `2026-11-20`, noting that only the entry pages (abstract, history, session listing, and release coordinates) were directly inspected rather than the unpacked Isabelle theory files.

#### Secondary / Metadata-Only Bibliographic References (omitted from `REPORT.json` `subjects`, 11 entries)

The following works are cited in **Findings** and **Boundaries** for historical attribution or context; only their bibliographic metadata (DBLP/Crossref) and attributions inside the inspected papers above were examined:

1. **Terauchi and Aiken (SAS 2005):** Tachio Terauchi and Alex Aiken, "Secure Information Flow as a Safety Problem", SAS 2005, LNCS 3672, pp. 352–367, DOI `10.1007/11547662_24`, DBLP `conf/sas/TerauchiA05`. *Inspected:* DBLP record and attribution in Clarkson and Schneider (2010, Section 4).
2. **Mastroeni and Pasqua (SAS 2018):** Isabella Mastroeni and Michele Pasqua, "Verifying Bounded Subset-Closed Hyperproperties", SAS 2018, LNCS 11002, pp. 263–283, DOI `10.1007/978-3-319-99725-4_17`, DBLP `conf/sas/MastroeniP18`. *Inspected:* DBLP record and attribution in `Properties.v` of Abate et al. (CSF 2019).
3. **Barthe, D'Argenio, and Rezk (CSFW 2004 / MSCS 2011):** Gilles Barthe, Pedro R. D'Argenio, and Tamara Rezk, "Secure Information Flow by Self-Composition", IEEE CSFW 2004, pp. 100–114, Crossref/IEEE Xplore DOI `10.1109/CSFW.2004.1310735` (legacy IEEE Computer Society DOI `10.1109/CSFW.2004.17`), DBLP `conf/csfw/BartheDR04`; journal version *Math. Struct. Comput. Sci.* 21(6):1207–1252, 2011, DOI `10.1017/S0960129511000193`, DBLP `journals/mscs/BartheDR11`. *Inspected:* Crossref/DBLP records and attribution in Clarkson and Schneider (2010, Section 4).
4. **Goguen and Meseguer (IEEE S&P 1982):** Joseph A. Goguen and José Meseguer, "Security Policies and Security Models", IEEE S&P 1982, pp. 11–20, DOI `10.1109/SP.1982.10014`, DBLP `conf/sp/GoguenM82a`. *Inspected:* DBLP record and characterization in McLean (1990, 1994) and Zdancewic and Myers (2003).
5. **McCullough (IEEE S&P 1987):** Daryl McCullough, "Specifications for Multi-Level Security and a Hook-Up Property", IEEE S&P 1987, pp. 161–166, DOI `10.1109/SP.1987.10009`, DBLP `conf/sp/McCullough87`. *Inspected:* DBLP record and attributions in McLean (1990, 1994 fn. 2) and Clarkson and Schneider (2010).
6. **McCullough (IEEE S&P 1988):** Daryl McCullough, "Noninterference and the composability of security properties", IEEE S&P 1988, pp. 177–186, DOI `10.1109/SECPRI.1988.8110`, DBLP `conf/sp/McCullough88`. *Inspected:* DBLP record and attributions in McLean (1990, 1994 fn. 2) and Clarkson and Schneider (2010).
7. **Jacob (IEEE S&P 1988):** Jeremy Jacob, "Security specifications", IEEE S&P 1988, pp. 14–23, DOI `10.1109/SECPRI.1988.8094`, DBLP `conf/sp/Jacob88`. *Inspected:* DBLP record and attribution in Morgan (`UNSW-CSE-TR-0522`, ref. [13]).
8. **Jacob (IEEE S&P 1989):** Jeremy Jacob, "On the Derivation of Secure Components", IEEE S&P 1989, pp. 242–247, DOI `10.1109/SECPRI.1989.36298`, DBLP `conf/sp/Jacob89`. *Inspected:* DBLP record and attribution in McLean (1994 fn. 2).
9. **Graham-Cumming and Sanders (CSFW 1991):** John Graham-Cumming and Jeff W. Sanders, "On the Refinement of Non-Interference", IEEE CSFW 1991, pp. 35–42, DOI `10.1109/CSFW.1991.151567`, DBLP `conf/csfw/Graham-CummingS91`. *Inspected:* DBLP record and attribution in McLean (1994 fn. 2).
10. **McLean (JCS 1992):** John McLean, "Proving Noninterference and Functional Correctness Using Traces", *Journal of Computer Security* 1(1):37–58, 1992, DOI `10.3233/JCS-1992-1103`, DBLP `journals/jcs/McLean92`. *Inspected:* DBLP record and attributions in Zdancewic and Myers (2003) and Clarkson and Schneider (2010).
11. **Mantel (IEEE S&P 2001):** Heiko Mantel, "Preserving Information Flow Properties under Refinement", IEEE S&P 2001, pp. 78–91, DOI `10.1109/SECPRI.2001.924289`, DBLP `conf/sp/Mantel01`. *Inspected:* DBLP record and attribution in Clarkson and Schneider (2010 fn. 12).

## Revalidation

**Primary command.** From the package directory run:

```bash
python3 support/revalidate.py .
```

It requires `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`, and it never modifies the package: the Lean project is first copied to a temporary directory. It runs `lake build`, rejects `sorry`, `admit`, `native_decide`, and `axiom` declarations in the Lean sources, checks that every package declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`, and recomputes the statement and closure SHA-256 hashes of every name referenced by `results.json` or recorded in `audit/statements.json`; its docstring describes exactly what is hashed. Expected final line: `REVALIDATED`.

**Independent equivalent check.** To rebuild the Lean mechanization from a clean state, verify that every declaration compiles without `sorry` and uses only `{propext, Classical.choice, Quot.sound}` under `leanprover/lean4:v4.34.1`, and recompute all `audit/axioms.json` and `audit/statements.json` SHA-256 hashes, run the following commands from the package root directory:

```bash
# 1. Clean kernel build and standalone axiom sweep in a scratch copy
WORKDIR="$(mktemp -d)"
cp -R lean "$WORKDIR/lean"
(
  cd "$WORKDIR/lean"
  lake build

  cat > AuditCheck.lean <<'EOF'
import Lean
import ToyHyper
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`ToyHyper).isPrefixOf m && !n.isInternal then
        count := count + 1
        if ci matches .axiomInfo _ | .opaqueInfo _ then
          throwError s!"forbidden axiom/opaque declaration: {n}"
        let axs ← collectAxioms n
        for a in axs do
          if !allowed.contains a then
            throwError s!"disallowed axiom {a} in {n}"
  IO.println s!"Audited {count} declarations: all axiom checks passed."
EOF
  lake env lean AuditCheck.lean
)
rm -rf "$WORKDIR"

# 2. Recompute and verify audit/axioms.json and audit/statements.json (SHA-256)
python3 audit/verify_audit.py .
```

Expected output:
- From step 1 (`AuditCheck.lean`): `Audited 319 declarations: all axiom checks passed.`
- From step 2 (`audit/verify_audit.py`): `Verified 319 declarations against audit/axioms.json and 50 statement/closure SHA-256 hashes against audit/statements.json: OK.`

### Scope of Revalidation Checks

- **What passing `lake build`, `AuditCheck.lean`, and `audit/verify_audit.py` establishes:** All 16 main theorems, their corollaries, non-vacuity witnesses, tightness counterexamples, positive controls, and boundary lemmas type-check in the Lean 4 kernel with zero `sorryAx` or `Lean.ofReduceBool` dependencies; every package declaration's exact axiom set matches `audit/axioms.json`; and all 50 card-referenced declarations match `audit/statements.json` on `statement_sha256`, `closure_sha256`, and `closure_size` (catching any silent change to a statement or to any non-theorem definition in its transitive package closure).
- **When statement hashes change (toolchain upgrade):** `statement_sha256` and `closure_sha256` in `audit/statements.json` serialize Lean's internal `Expr` representation under `leanprover/lean4:v4.34.1`. Moving `lean-toolchain` to a newer Lean release may alter `repr ci.type` even when source text is unchanged; after any toolchain bump, diff `lean/ToyHyper/*.lean` directly to confirm zero semantic edits before regenerating `audit/statements.json`.
- **When extending to a richer model:** Any move from single-step `(lowIn, highIn, lowOut)` traces or `FinDist n` to multi-step interactive traces, cross-language trace relations, or sub-probability/demonic-probabilistic refinement invalidates the modeling bridges on Cards 6–16 and requires re-proving or refuting the corresponding characterizations in the richer semantics rather than extrapolating from `Toy.Hyper`.
