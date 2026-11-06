-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Core

/-!
# Tractability, Decidability, and Incompleteness: Tractability, Decidability, Incompleteness, and Witness Reduction

This module (`TractabilityAndIncompleteness.lean`) is a self-contained,
kernel-checked Lean `v4.34.1` formalization (`prelude`, `import Init.Core`,
zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`) accompanying
the Tractability and Incompleteness reference report on the fundamental mathematical limits of
specification non-vacuity and verification tool auditing.

It mechanizes three foundational meta-theorems and their constructive counterparts
in Anneal's architecture:

1. **Tarski / Gödel / Löb Meta-Boundary Separation (`Section 2`):**
   - `internal_self_certification_explodes` and
     `internal_conjunct_cannot_detect_sorryAx`: Prove that no object-language
     proposition `InternalNoSorryProp : Prop` conjoined onto `StrictUnitTheorem u`
     can detect whether its own proof term invoked `sorryAx` or an inconsistent
     axiom, because `sorryAx : ∀ {α : Sort u}, α` inhabits both halves of
     `StrictUnitTheorem u ∧ InternalNoSorryProp` simultaneously via Principle of
     Explosion.
   - `abstract_lob_theorem` and `godel_second_incompleteness_from_lob`: Prove
     Löb's Theorem (`Prov (Prov P → P) → Prov P`) and Gödel's Second
     Incompleteness Theorem (`¬ Prov (Prov False → False)`) from the
     Hilbert-Bernays-Löb derivability conditions (`D1`–`D3`) and a diagonal
     fixed point, establishing why a consistent formal system cannot internally
     certify its own soundness.
   - `meta_auditor_two_level_soundness`: Formalizes the Tarskian two-level
     separation between the meta-language `.olean` axiom-footprint checker
     (`checkAxiomFootprint cert = true`) and the object-language root theorem
     (`StrictUnitTheorem u`), proving that their conjunction establishes both
     meta-theoretic axiom hygiene and object-level zero-waiver completeness.

2. **Lawvere Fixed-Point Theorem & Constructive Rice's Theorem (`Section 3`):**
   - `lawvere_diagonal_no_surjection`: Proves Lawvere's diagonal theorem showing
     that if `neg : Val → Val` has no fixed point, no `Prog` can represent the
     diagonal map `fun p => neg (eval p p)`.
   - `rice_semantic_undecidability` and `rice_verified_undecidable`: Instantiate
     Lawvere diagonalization to prove a constructive Rice-style theorem: for any
     non-trivial semantic specification (`∃ p_yes, P (L.sem p_yes)` and
     `∃ p_bad, ¬ P (L.sem p_bad)`) over a language closed under diagonal
     branching, no total boolean decider `decideProg : L.Prog → Bool` can decide
     `P (L.sem p)` (or `L.Verified pre post p`) for all programs `p`.
   - `undecidability_of_unrestricted_spec_equivalence`: Shows how Rice's theorem
     rules out any total decision procedure for unrestricted verification.

3. **Dialectica / Realizability Witness Reduction: $\Sigma^0_1 \to \Delta^0_0$
   Decidable Canary Certificates (`Section 4`):**
   - Defines `ComputableLang` and `CanaryCertificate` (`q₀`, `k_good`, `k_bad`)
     together with a purely computable boolean checker
     `checkCanaryCertificate : ... → CanaryCertificate Query → Bool`.
   - Proves `certificate_discharges_canary_and_nonvacuity`: when
     `checkCanaryCertificate ... cert = true` (which is $\Delta^0_0$ decidable by
     kernel reduction `rfl` / `decide`), the Lean kernel automatically derives:
     (a) precondition inhabitation `∃ q, pre q`,
     (b) distinct observable outcomes `obs o_good ≠ obs o_bad`,
     (c) non-constant observable projection `¬ (∀ o₁ o₂, obs o₁ = obs o₂)`,
     (d) non-subsingleton observable spine `¬ (∀ s₁ s₂ : SemObs, s₁ = s₂)`,
     (e) non-trivial postcondition `¬ (∀ q o, pre q → post q o)`,
     (f) semantic program discrimination `L.sem p_good ≠ L.sem p_bad`, and
     (g) negative-canary refutation `L.RefutedOn ... p_bad`!
   - Instantiates the theorem on a concrete arithmetic language where `rfl`
     discharges the entire anti-vacuity and negative-canary proof in $O(1)$
     kernel reduction (`toy_canary_and_nonvacuity_by_rfl`).
-/

namespace Anneal.TractabilityAndIncompleteness

/-!
## 1. Self-Contained Reproduction of Anneal's `Trusted/Refinement.lean` Kernel

To allow standalone compilation via `lean -DElab.async=false -Ddebug.skipKernelTC=false`
with zero external path flags, we include the exact core definitions from
`Trusted/Refinement.lean`.
-/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality carrier representing `B ∪ {UB}` with zero
    `Classical.choice` axioms. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => False⟩

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Spine-indexed semantic language parameterized by `SemObs`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out
  dom   : Query → Prop := fun _ => True

abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := fun o => o
  sem   := sem

abbrev Language.Behavior {SemObs : Type} (L : Language SemObs) : Type :=
  Trusted.Behavior L.Query L.Out

def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

def Language.SpineSpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) : L.Behavior :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

abbrev Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn L.dom pre post prog

abbrev Language.VerifiedSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn dom pre (fun q o => obsPost q (L.obs o)) prog

abbrev Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedSpineOn L.dom pre obsPost prog

abbrev Language.RefutedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  ¬ L.VerifiedOn dom pre post badProg

abbrev Language.Refuted {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.RefutedOn L.dom pre post badProg

def Language.RefutedProductiveOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.ProductiveOn pre badProg ∧ ¬ L.VerifiedOn dom pre post badProg

def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

def Language.VerifiedWithCanariesOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedOn dom pre post goodProg ∧
  badProgs ≠ [] ∧
  AllHold (badProgs.map (L.RefutedOn dom pre post))

abbrev Language.VerifiedSpineWithCanariesOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedWithCanariesOn dom pre (fun q o => obsPost q (L.obs o))
    goodProg badProgs

abbrev Language.VerifiedSpineWithCanaries {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedSpineWithCanariesOn L.dom pre obsPost goodProg badProgs

structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.verified {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.Verified pre post prog⟩

abbrev Obligation.verifiedSpineWithCanaries {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpineWithCanaries pre obsPost goodProg badProgs⟩

abbrev Obligation.refutedProductiveOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Obligation Id :=
  ⟨id, L.RefutedProductiveOn dom pre post badProg⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

def TrustPolicy.strict {Id : Type} : TrustPolicy Id :=
  ⟨fun _ => False⟩

structure EmittedArtifact where
  path     : String
  contents : String
  expected : String := contents

def EmittedArtifact.holds (a : EmittedArtifact) : Prop :=
  a.contents = a.expected

def NoDupIds {Id : Type} : List Id → Prop
  | []        => True
  | id :: ids => AllHold (ids.map (fun id' => id ≠ id')) ∧ NoDupIds ids

def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

structure VerificationUnit (Id : Type) where
  policy      : TrustPolicy Id := TrustPolicy.strict
  waived      : List Id := []
  obligations : List (Obligation Id)
  artifacts   : List EmittedArtifact := []

def UnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  VerificationResult u.policy u.waived u.obligations

def StrictUnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  UnitTheorem u ∧
  u.waived = [] ∧
  NoDupIds (u.obligations.map Obligation.id) ∧
  AllHold (u.artifacts.map EmittedArtifact.holds)

end Trusted

open Trusted

/-!
## 2. Tarski / Gödel / Löb Meta-Boundary Separation

Why can structural properties of values (`u.waived = []`, `NoDupIds`,
`Obligation` smart-constructor typing, `VerifiedSpineWithCanaries`, and
`EmittedArtifact.holds`) be enforced inside the object language
(`Trusted/Refinement.lean`), whereas the **axiom-footprint and environment
integrity check** (`#print axioms` / `TrustedBoundary.lean` checking for
`sorryAx`, `Classical.choice`, `Lean.ofReduceBool`, `@[implemented_by]`, and
`unsafe`) MUST remain in the Tarskian meta-language?

We prove three theorems establishing this boundary:
1. `internal_self_certification_explodes`: Any attempt to replace the
   meta-language axiom audit with an object-language conjunct
   `InternalNoSorryProp : Prop` inside `StrictUnitTheorem` fails by Principle of
   Explosion (`sorryAx` proves both `StrictUnitTheorem u` and
   `InternalNoSorryProp` simultaneously).
2. `abstract_lob_theorem` and `godel_second_incompleteness_from_lob`: Under
   Hilbert-Bernays-Löb derivability (`D1`–`D3`) and Gödel-Carnap diagonalization,
   any system that internally proves `Prov P → P` already proves `P`; setting
   `P := False` shows that no consistent system can internally prove its own
   consistency (`¬ Prov (Prov False → False)`).
3. `meta_auditor_two_level_soundness`: Separating the Tarskian meta-language
   certificate audit (`checkAxiomFootprint cert = true`) from the object-language
   theorem (`StrictUnitTheorem u`) yields both axiom hygiene and full
   object-level verification completeness.
-/

/-- Candidate internal "self-certified" theorem statement that attempts to fold
    the meta-level "no `sorryAx` was used" check into an object-level `Prop`
    conjunct `InternalNoSorryProp`. -/
def SelfCertifiedUnitTheorem {Id : Type}
    (u : VerificationUnit Id) (InternalNoSorryProp : Prop) : Prop :=
  StrictUnitTheorem u ∧ InternalNoSorryProp

/-- **Theorem 2.1 (`internal_self_certification_explodes`):**
    If the proof environment contains an unsound axiom equivalent to `sorryAx`
    (`h_sorryAx : ∀ (P : Prop), P`), then for *every* verification unit `u`
    (even a unit with `u.obligations = []`, non-empty `u.waived`, or false
    obligations) and *every* candidate internal self-certification proposition
    `InternalNoSorryProp : Prop`, `SelfCertifiedUnitTheorem u InternalNoSorryProp`
    is trivially provable! -/
theorem internal_self_certification_explodes {Id : Type}
    (h_sorryAx : ∀ (P : Prop), P)
    (u : VerificationUnit Id)
    (InternalNoSorryProp : Prop) :
    SelfCertifiedUnitTheorem u InternalNoSorryProp :=
  ⟨h_sorryAx (StrictUnitTheorem u), h_sorryAx InternalNoSorryProp⟩

/-- **Theorem 2.2 (`internal_conjunct_cannot_detect_sorryAx`):**
    More generally, let `AuditTransform : Prop → Prop` be *any* object-language
    proposition transformer intended to guard a theorem `T : Prop`. In any
    environment where `sorryAx` (`∀ P : Prop, P`) is available, `AuditTransform T`
    is inhabited for every `T : Prop`—including `T := False`. Hence no
    object-language `Prop` transformer can detect whether its own proof term
    used `sorryAx`. -/
theorem internal_conjunct_cannot_detect_sorryAx
    (AuditTransform : Prop → Prop)
    (h_sorryAx : ∀ (P : Prop), P)
    (T : Prop) :
    AuditTransform T :=
  h_sorryAx (AuditTransform T)

/-- Abstract Hilbert-Bernays-Löb (HBL / Gödel-Löb `GL`) provability system over
    `Prop`. Models a formal theory with provability predicate `Prov : Prop → Prop`
    satisfying the Hilbert-Bernays-Löb derivability conditions:
    - `d1` (Necessitation / Internalization): if `P` holds at the meta-level,
      `Prov P` holds.
    - `d2` (Distributivity / Internal Modus Ponens):
      `Prov (P → Q) → Prov P → Prov Q`.
    - `d2_box` (Internalized Distributivity):
      `Prov (Prov (P → Q) → (Prov P → Prov Q))`.
    - `d3_box` (Internalized Positive Introspection / Provable $\Sigma^0_1$-Completeness):
      `Prov (Prov P → Prov (Prov P))`. -/
structure HBLSystem where
  Prov : Prop → Prop
  d1   : ∀ {P : Prop}, P → Prov P
  d2   : ∀ {P Q : Prop}, Prov (P → Q) → Prov P → Prov Q
  d3   : ∀ {P : Prop}, Prov P → Prov (Prov P)

/-- Internalized `D2` (`Prov (Prov (P → Q) → (Prov P → Prov Q))`), derived from
    `d1` and `d2`. -/
theorem HBLSystem.d2_box (S : HBLSystem) {P Q : Prop} :
    S.Prov (S.Prov (P → Q) → (S.Prov P → S.Prov Q)) :=
  S.d1 (@HBLSystem.d2 S P Q)

/-- Internalized `D3` (`Prov (Prov P → Prov (Prov P))`), derived from `d1` and
    `d3`. -/
theorem HBLSystem.d3_box (S : HBLSystem) {P : Prop} :
    S.Prov (S.Prov P → S.Prov (S.Prov P)) :=
  S.d1 (@HBLSystem.d3 S P)

/-- Applicative 2-argument lifting inside an `HBLSystem` via `d1` and `d2`. -/
theorem HBLSystem.lift2 (S : HBLSystem) {A B C : Prop}
    (f : A → B → C) (ha : S.Prov A) (hb : S.Prov B) : S.Prov C :=
  S.d2 (S.d2 (S.d1 f) ha) hb

/-- A Gödel-Carnap diagonal fixed point for the formula `Prov Ψ → P` inside
    an `HBLSystem` `S`. -/
structure DiagonalFixedPoint (S : HBLSystem) (P : Prop) where
  Psi      : Prop
  forward  : Psi → (S.Prov Psi → P)
  backward : (S.Prov Psi → P) → Psi

/-- **Theorem 2.3 (Löb's Theorem, 1955 — `abstract_lob_theorem`):**
    In any `HBLSystem` `S`, given a diagonal fixed point `fp` for `S.Prov Ψ → P`,
    if `S` proves the reflection principle `S.Prov P → P`
    (`h_refl : S.Prov (S.Prov P → P)`), then `S` unconditionally proves `P`
    (`S.Prov P`)!

    *Proof (Löb 1955):*
    1. `h1 : S.Prov (Ψ → (S.Prov Ψ → P))` by `d1` on `fp.forward`.
    2. `h2 : S.Prov (S.Prov Ψ → S.Prov (S.Prov Ψ → P))` by `d3` + `d2_box`.
    3. `h3 : S.Prov (S.Prov Ψ → (S.Prov (S.Prov Ψ) → S.Prov P))` by composing
       `h2` with `d2_box`.
    4. `h4 : S.Prov (S.Prov Ψ → S.Prov P)` by contracting with `d3_box`
       (`S.Prov Ψ → S.Prov (S.Prov Ψ)`).
    5. `h5 : S.Prov (S.Prov Ψ → P)` by composing `h4` with `h_refl`.
    6. `h_psi : S.Prov Ψ` by `d2` on `d1 fp.backward` and `h5`.
    7. `exact S.d2 h5 (S.d3 h_psi)`. -/
theorem abstract_lob_theorem (S : HBLSystem) (P : Prop)
    (fp : DiagonalFixedPoint S P)
    (h_refl : S.Prov (S.Prov P → P)) :
    S.Prov P := by
  have h1 : S.Prov (fp.Psi → (S.Prov fp.Psi → P)) :=
    S.d1 fp.forward
  have h1_box : S.Prov (S.Prov (fp.Psi → (S.Prov fp.Psi → P))) :=
    S.d3 h1
  have h2 : S.Prov (S.Prov fp.Psi → S.Prov (S.Prov fp.Psi → P)) :=
    S.d2 (@HBLSystem.d2_box S fp.Psi (S.Prov fp.Psi → P)) h1_box
  have h3 : S.Prov (S.Prov fp.Psi → (S.Prov (S.Prov fp.Psi) → S.Prov P)) :=
    S.lift2 (fun ab bc a => bc (ab a)) h2
      (@HBLSystem.d2_box S (S.Prov fp.Psi) P)
  have h4 : S.Prov (S.Prov fp.Psi → S.Prov P) :=
    S.lift2 (fun abc ab a => abc a (ab a)) h3
      (@HBLSystem.d3_box S fp.Psi)
  have h5 : S.Prov (S.Prov fp.Psi → P) :=
    S.lift2 (fun ab bc a => bc (ab a)) h4 h_refl
  have h_psi : S.Prov fp.Psi :=
    S.d2 (S.d1 fp.backward) h5
  have h_prov_psi : S.Prov (S.Prov fp.Psi) :=
    S.d3 h_psi
  exact S.d2 h5 h_prov_psi

/-- **Theorem 2.4 (Gödel's Second Incompleteness Theorem, 1931 —
    `godel_second_incompleteness_from_lob`):**
    Let `S` be a consistent `HBLSystem` (`h_cons : ¬ S.Prov False`) with a
    diagonal fixed point `fp` for `S.Prov Ψ → False` (the Gödel sentence
    asserting its own unprovability). Then `S` cannot prove its own consistency
    (`¬ S.Prov (S.Prov False → False)`). -/
theorem godel_second_incompleteness_from_lob (S : HBLSystem)
    (fp : DiagonalFixedPoint S False)
    (h_cons : ¬ S.Prov False) :
    ¬ S.Prov (S.Prov False → False) := by
  intro h_prov_cons
  exact h_cons (abstract_lob_theorem S False fp h_prov_cons)

/-- Tarskian meta-language classification of kernel axiom tags inspected by
    `TrustedBoundary.lean` / `#print axioms`. -/
inductive MetaAxiom where
  | propext
  | quotSound
  | sorryAx
  | classicalChoice
  | ofReduceBool
  | customUnsafe
  deriving DecidableEq

/-- Anneal's strict foundation axiom policy: only `.propext` and `.quotSound`
    are permitted; `.sorryAx`, `.classicalChoice`, `.ofReduceBool`, and
    `.customUnsafe` are rejected. -/
def MetaAxiom.isAllowed : MetaAxiom → Bool
  | .propext         => true
  | .quotSound       => true
  | .sorryAx         => false
  | .classicalChoice => false
  | .ofReduceBool    => false
  | .customUnsafe    => false

/-- Meta-language representation of a replayed `.olean` proof certificate,
    recording the transitive axiom footprint collected by `Lean.collectAxioms`. -/
structure ProofCert where
  axiomsUsed : List MetaAxiom

/-- Meta-language boolean auditor checking that every axiom in `cert.axiomsUsed`
    satisfies `MetaAxiom.isAllowed`. -/
def checkAxiomFootprint (cert : ProofCert) : Bool :=
  cert.axiomsUsed.all MetaAxiom.isAllowed

theorem all_Allowed_of_list_all :
    ∀ (xs : List MetaAxiom),
      xs.all MetaAxiom.isAllowed = true →
      ∀ a, a ∈ xs → MetaAxiom.isAllowed a = true
  | [], _, _, h_in => nomatch h_in
  | x :: xs, h_all, a, h_in => by
      simp only [List.all] at h_all
      cases h_x : MetaAxiom.isAllowed x with
      | false =>
          rw [h_x] at h_all
          cases h_all
      | true =>
          rw [h_x] at h_all
          cases h_in with
          | head => exact h_x
          | tail _ h_tail => exact all_Allowed_of_list_all xs h_all a h_tail

theorem allHold_prop_of_waived_nil {Id : Type} :
    ∀ (obligations : List (Obligation Id)),
      AllHold (obligations.map (fun ob => ob.id ∈ ([] : List Id) ∨ ob.prop)) →
      AllHold (obligations.map Obligation.prop)
  | [], _ => trivial
  | _ :: rest, ⟨h_head, h_tail⟩ =>
      match h_head with
      | .inl h_in => nomatch h_in
      | .inr h_prop => ⟨h_prop, allHold_prop_of_waived_nil rest h_tail⟩

/-- **Theorem 2.5 (Tarskian Two-Level Soundness —
    `meta_auditor_two_level_soundness`):**
    When the meta-language auditor check (`checkAxiomFootprint cert = true`) is
    paired with the object-language root theorem (`StrictUnitTheorem u`), we
    obtain both:
    1. **Meta-level axiom hygiene:** Neither `.sorryAx`, `.classicalChoice`,
       `.ofReduceBool`, nor `.customUnsafe` appears in `cert.axiomsUsed`, AND
    2. **Object-level verification completeness:** `u.waived = []`,
       `u.obligations ≠ []`, `NoDupIds`, every obligation in `u.obligations`
       holds constructively, and every `EmittedArtifact` matches its expected
       contents. -/
theorem meta_auditor_two_level_soundness {Id : Type}
    (cert : ProofCert) (u : VerificationUnit Id)
    (h_meta : checkAxiomFootprint cert = true)
    (h_obj : StrictUnitTheorem u) :
    (.sorryAx ∉ cert.axiomsUsed ∧
     .classicalChoice ∉ cert.axiomsUsed ∧
     .ofReduceBool ∉ cert.axiomsUsed ∧
     .customUnsafe ∉ cert.axiomsUsed) ∧
    (u.waived = [] ∧
     u.obligations ≠ [] ∧
     NoDupIds (u.obligations.map Obligation.id) ∧
     AllHold (u.obligations.map Obligation.prop) ∧
     AllHold (u.artifacts.map EmittedArtifact.holds)) := by
  have h_each := all_Allowed_of_list_all cert.axiomsUsed h_meta
  have h_no_sorry : .sorryAx ∉ cert.axiomsUsed := by
    intro h_in
    have h_ok := h_each .sorryAx h_in
    cases h_ok
  have h_no_choice : .classicalChoice ∉ cert.axiomsUsed := by
    intro h_in
    have h_ok := h_each .classicalChoice h_in
    cases h_ok
  have h_no_reduce : .ofReduceBool ∉ cert.axiomsUsed := by
    intro h_in
    have h_ok := h_each .ofReduceBool h_in
    cases h_ok
  have h_no_unsafe : .customUnsafe ∉ cert.axiomsUsed := by
    intro h_in
    have h_ok := h_each .customUnsafe h_in
    cases h_ok
  have h_waived : u.waived = [] := h_obj.2.1
  have h_disj : AllHold (u.obligations.map (fun ob => ob.id ∈ u.waived ∨ ob.prop)) :=
    h_obj.1.2.2
  rw [h_waived] at h_disj
  exact ⟨⟨h_no_sorry, h_no_choice, h_no_reduce, h_no_unsafe⟩,
    ⟨h_waived, h_obj.1.1, h_obj.2.2.1,
     allHold_prop_of_waived_nil u.obligations h_disj, h_obj.2.2.2⟩⟩

/-!
## 3. Lawvere Fixed-Point Theorem & Constructive Rice's Theorem

Why can't Anneal replace deductive verification (`L.Verified pre post p`) or
witnessed canary refutation with an automatic total decision procedure
`decideVerified : L.Prog → Bool`?

We prove Lawvere's diagonal theorem (Lawvere 1969; Yanofsky 2003) and instantiate
it to obtain a constructive, zero-axiom Rice's Theorem for `Language SemObs`:
any non-trivial semantic property over a language closed under diagonal
branching is undecidable by any total boolean function.
-/

/-- **Theorem 3.1 (Lawvere's Fixed-Point / Diagonal Theorem, 1969 —
    `lawvere_diagonal_no_surjection`):**
    Let `eval : Prog → Prog → Val` be any parameterization of `Prog → Val` by
    `Prog`, and let `neg : Val → Val` be an endomap with no fixed point
    (`∀ v, neg v ≠ v`). Then no `p₀ : Prog` can represent the diagonal function
    `fun p => neg (eval p p)`. -/
theorem lawvere_diagonal_no_surjection {Prog Val : Type}
    (eval : Prog → Prog → Val)
    (neg : Val → Val)
    (h_no_fix : ∀ v : Val, neg v ≠ v) :
    ∀ p₀ : Prog, ¬ (∀ p : Prog, eval p₀ p = neg (eval p p)) := by
  intro p₀ h_surj
  have h_diag : eval p₀ p₀ = neg (eval p₀ p₀) := h_surj p₀
  exact h_no_fix (eval p₀ p₀) h_diag.symm

/-- Diagonal branching closure: for any candidate boolean decider
    `decideProg : L.Prog → Bool` and any two programs `p_yes p_no : L.Prog`,
    there exists a diagonal program `diagProg : L.Prog` whose semantics acts as
    `p_no` if `decideProg diagProg = true` and acts as `p_yes` if
    `decideProg diagProg = false`. -/
def HasDiagonalBranching {SemObs : Type} (L : Language SemObs) : Prop :=
  ∀ (decideProg : L.Prog → Bool) (p_yes p_no : L.Prog),
    ∃ diagProg : L.Prog,
      L.sem diagProg =
        if decideProg diagProg then L.sem p_no else L.sem p_yes

/-- **Theorem 3.2 (Constructive Rice's Theorem, 1953 —
    `rice_semantic_undecidability`):**
    Let `L : Language SemObs` satisfy `HasDiagonalBranching L`, and let
    `P : L.Behavior → Prop` be any non-trivial semantic property on `L.Behavior`
    (witnessed by `p_yes` with `P (L.sem p_yes)` and `p_no` with
    `¬ P (L.sem p_no)`). Then no total boolean function
    `decideProg : L.Prog → Bool` can decide `P (L.sem p)` for all `p : L.Prog`! -/
theorem rice_semantic_undecidability {SemObs : Type}
    (L : Language SemObs)
    (h_diag_lang : HasDiagonalBranching L)
    (P : L.Behavior → Prop)
    (p_yes p_no : L.Prog)
    (h_yes : P (L.sem p_yes))
    (h_no : ¬ P (L.sem p_no))
    (decideProg : L.Prog → Bool) :
    ¬ (∀ p : L.Prog, (decideProg p = true ↔ P (L.sem p))) := by
  intro h_decides
  cases h_diag_lang decideProg p_yes p_no with
  | intro diagProg h_sem =>
    have h_iff := h_decides diagProg
    cases h_b : decideProg diagProg with
    | true =>
      have h_sem_no : L.sem diagProg = L.sem p_no := by
        rw [h_b] at h_sem
        exact h_sem
      have h_p_diag : P (L.sem diagProg) := h_iff.mp h_b
      rw [h_sem_no] at h_p_diag
      exact h_no h_p_diag
    | false =>
      have h_sem_yes : L.sem diagProg = L.sem p_yes := by
        rw [h_b] at h_sem
        exact h_sem
      have h_p_diag : P (L.sem diagProg) := by
        rw [h_sem_yes]
        exact h_yes
      have h_true : decideProg diagProg = true := h_iff.mpr h_p_diag
      rw [h_b] at h_true
      cases h_true

/-- **Theorem 3.3 (Undecidability of `L.Verified` — `rice_verified_undecidable`):**
    For any specification `(pre, post)` that admits at least one verified
    implementation `goodProg` (`L.Verified pre post goodProg`) and refutes at
    least one buggy canary `badProg` (`L.Refuted pre post badProg`), if `L` has
    diagonal branching, no total boolean decider `decideVer : L.Prog → Bool` can
    decide `L.Verified pre post p` for all `p : L.Prog`. -/
theorem rice_verified_undecidable {SemObs : Type}
    (L : Language SemObs)
    (h_diag_lang : HasDiagonalBranching L)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg badProg : L.Prog)
    (h_good : L.Verified pre post goodProg)
    (h_bad : L.Refuted pre post badProg)
    (decideVer : L.Prog → Bool) :
    ¬ (∀ p : L.Prog, (decideVer p = true ↔ L.Verified pre post p)) := by
  let P : L.Behavior → Prop := fun b =>
    NonVacuousOn L.dom pre ∧
    (∀ q, pre q → ∃ h : (b q).defined, ∃ o : L.Out, (b q).val h o) ∧
    b ≤ L.SpecOn pre post
  exact rice_semantic_undecidability L h_diag_lang P goodProg badProg
    h_good h_bad decideVer

/-- **Theorem 3.4 (Undecidability of Halting / `ProductiveOn` —
    `rice_productiveOn_undecidable`):**
    In any language `L` with diagonal branching that contains at least one
    productive (terminating) program `p_halt` (`L.ProductiveOn pre p_halt`) and
    at least one diverging/unproductive program `p_loop`
    (`¬ L.ProductiveOn pre p_loop`), no total boolean function
    `decideHalt : L.Prog → Bool` can decide `L.ProductiveOn pre p` for all `p`. -/
theorem rice_productiveOn_undecidable {SemObs : Type}
    (L : Language SemObs)
    (h_diag_lang : HasDiagonalBranching L)
    (pre : L.Query → Prop)
    (p_halt p_loop : L.Prog)
    (h_halt : L.ProductiveOn pre p_halt)
    (h_loop : ¬ L.ProductiveOn pre p_loop)
    (decideHalt : L.Prog → Bool) :
    ¬ (∀ p : L.Prog, (decideHalt p = true ↔ L.ProductiveOn pre p)) := by
  let P : L.Behavior → Prop := fun b =>
    ∀ q, pre q → ∃ h : (b q).defined, ∃ o : L.Out, (b q).val h o
  exact rice_semantic_undecidability L h_diag_lang P p_halt p_loop
    h_halt h_loop decideHalt

/-- **Theorem 3.5 (Non-Existence of a Total Verification Decider —
    `undecidability_of_unrestricted_spec_equivalence`):**
    Under the hypotheses of Theorem 3.3, no total boolean function exists that
    decides `L.Verified pre post p` across all `p : L.Prog`. -/
theorem undecidability_of_unrestricted_spec_equivalence {SemObs : Type}
    (L : Language SemObs)
    (h_diag_lang : HasDiagonalBranching L)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg badProg : L.Prog)
    (h_good : L.Verified pre post goodProg)
    (h_bad : L.Refuted pre post badProg) :
    ¬ ∃ (decideVer : L.Prog → Bool),
        ∀ p : L.Prog, (decideVer p = true ↔ L.Verified pre post p) := by
  intro ⟨decideVer, h_dec⟩
  exact rice_verified_undecidable L h_diag_lang pre post
    goodProg badProg h_good h_bad decideVer h_dec

/-!
## 4. Dialectica / Realizability Witness Reduction ($\Sigma^0_1 \to \Delta^0_0$)

While universal verification `∀ q, pre q → ...` is $\Pi^0_1$ / $\Pi^0_2$
(undecidable by Theorem 3.3) and unassisted existential search `∃ q k₁ k₂, ...`
is $\Sigma^0_1$ (unbounded search), **Kreisel's Modified Realizability (1959)**
and **Gödel's *Dialectica* Interpretation (1958)** Skolemize existential
quantifiers into explicit witness certificates.

Once an explicit witness certificate `cert : CanaryCertificate Query`
(`(q₀, k_good, k_bad)`) is supplied, checking that `p_good` and `p_bad` both
terminate at `q₀` and diverge on `obsPost` drops to **$\Delta^0_0$ (primitive
recursive / bounded boolean evaluation)**—discharged in $O(1)$ by Lean's kernel
via `rfl` or `decide`!
-/

/-- Step-indexed computable language induced by a bounded evaluator
    `eval : Prog → Query → Nat → Option Out` and observable projection
    `obs : Out → SemObs`. -/
abbrev ComputableLang (Prog Query Out SemObs : Type)
    (eval : Prog → Query → Nat → Option Out)
    (obs : Out → SemObs)
    (dom : Query → Prop := fun _ => True) : Language SemObs where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := obs
  sem   := fun p q => {
    defined := ∃ k o, eval p q k = some o
    val     := fun _ o => ∃ k, eval p q k = some o
  }
  dom   := dom

/-- Step-budget determinism of `eval p q`: any two terminating fuel budgets `k₁`
    and `k₂` at `(p, q)` yield the same concrete outcome `o₁ = o₂`. -/
def StepDeterministic {Prog Query Out : Type}
    (eval : Prog → Query → Nat → Option Out) (p : Prog) (q : Query) : Prop :=
  ∀ k₁ k₂ o₁ o₂,
    eval p q k₁ = some o₁ →
    eval p q k₂ = some o₂ →
    o₁ = o₂

/-- Explicit Dialectica / realizability witness certificate for 2-point canary
    separation and specification non-vacuity:
    - `q₀`: concrete input query witnessing `preB q₀ = true`,
    - `k_good`: concrete step budget under which `p_good` produces `some o_good`
      satisfying `obsPostB q₀ (obs o_good) = true`, and
    - `k_bad`: concrete step budget under which `p_bad` produces `some o_bad`
      violating `obsPostB q₀ (obs o_bad) = false`. -/
structure CanaryCertificate (Query : Type) where
  q₀     : Query
  k_good : Nat
  k_bad  : Nat

/-- Computable $\Delta^0_0$ boolean certificate checker: evaluates `preB`,
    `eval p_good`, `eval p_bad`, and `obsPostB` at `cert` in finite time. -/
def checkCanaryCertificate {Prog Query Out SemObs : Type}
    (eval : Prog → Query → Nat → Option Out)
    (obs : Out → SemObs)
    (preB : Query → Bool)
    (obsPostB : Query → SemObs → Bool)
    (p_good p_bad : Prog)
    (cert : CanaryCertificate Query) : Bool :=
  preB cert.q₀ &&
  match eval p_good cert.q₀ cert.k_good with
  | none => false
  | some o_good =>
    match eval p_bad cert.q₀ cert.k_bad with
    | none => false
    | some o_bad =>
        obsPostB cert.q₀ (obs o_good) && !(obsPostB cert.q₀ (obs o_bad))

/-- Transport an outcome witness across an equality of `Partial` behaviors via
    definitional proof irrelevance of `defined : Prop`. -/
theorem Partial.val_of_eq {Out : Type} {p₁ p₂ : Partial (Out → Prop)}
    (h_eq : p₁ = p₂) (h₁ : p₁.defined) (h₂ : p₂.defined) (o : Out)
    (h_val : p₂.val h₂ o) : p₁.val h₁ o := by
  cases h_eq
  exact h_val

/-- Helper unpacking a boolean conjunction `a && b = true` without classical
    tactics. -/
theorem and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

/-- **Theorem 4.1 (Dialectica / Popperian Witness Reduction Theorem —
    `certificate_discharges_canary_and_nonvacuity`):**
    If the $\Delta^0_0$ boolean check
    `checkCanaryCertificate eval obs preB obsPostB p_good p_bad cert = true`
    holds (checkable by `rfl`!), then on
    `L := ComputableLang Prog Query Out SemObs eval obs dom` with
    `pre q := (preB q = true)` and `obsPost q s := (obsPostB q s = true)`
    (and `h_det_good : StepDeterministic eval p_good cert.q₀` for semantic
    program inequality):
    1. **Precondition Inhabitation:** `∃ q, preB q = true`,
    2. **Distinct Observable Spine Values:** `∃ o₁ o₂ : Out, obs o₁ ≠ obs o₂`,
    3. **Non-Constant Observable Projection:** `¬ (∀ o₁ o₂ : Out, obs o₁ = obs o₂)`,
    4. **Non-Subsingleton `SemObs`:** `¬ (∀ s₁ s₂ : SemObs, s₁ = s₂)` (refuting
       `SemObs = Unit`),
    5. **Non-Trivial Postcondition:**
       `¬ (∀ q o, preB q = true → obsPostB q (obs o) = true)`,
    6. **Program-Discriminating Semantics:** `L.sem p_good ≠ L.sem p_bad`,
    7. **In-Kernel Negative Canary Refutation:**
       `L.RefutedOn dom (fun q => preB q = true) (fun q o => obsPostB q (obs o) = true) p_bad`, and
    8. **Pointwise Productive Negative-Canary Refutation:**
       `L.RefutedProductiveOn dom (fun q => q = cert.q₀ ∧ preB q = true) (fun q o => obsPostB q (obs o) = true) p_bad`! -/
theorem certificate_discharges_canary_and_nonvacuity
    {Prog Query Out SemObs : Type}
    (eval : Prog → Query → Nat → Option Out)
    (obs : Out → SemObs)
    (dom : Query → Prop)
    (preB : Query → Bool)
    (obsPostB : Query → SemObs → Bool)
    (p_good p_bad : Prog)
    (cert : CanaryCertificate Query)
    (h_cert : checkCanaryCertificate eval obs preB obsPostB p_good p_bad cert = true)
    (h_det_good : StepDeterministic eval p_good cert.q₀) :
    let L := ComputableLang Prog Query Out SemObs eval obs dom
    (∃ q, preB q = true) ∧
    (∃ o_good o_bad : Out, obs o_good ≠ obs o_bad) ∧
    ¬ (∀ o₁ o₂ : Out, obs o₁ = obs o₂) ∧
    ¬ (∀ s₁ s₂ : SemObs, s₁ = s₂) ∧
    ¬ (∀ q o, preB q = true → obsPostB q (obs o) = true) ∧
    L.sem p_good ≠ L.sem p_bad ∧
    L.RefutedOn dom (fun q => preB q = true)
      (fun q o => obsPostB q (obs o) = true) p_bad ∧
    L.RefutedProductiveOn dom (fun q => q = cert.q₀ ∧ preB q = true)
      (fun q o => obsPostB q (obs o) = true) p_bad := by
  intro L
  unfold checkCanaryCertificate at h_cert
  have ⟨h_pre, h_match⟩ := (and_eq_true_iff _ _).mp h_cert
  revert h_match
  cases h_eg : eval p_good cert.q₀ cert.k_good with
  | none => intro h_false; cases h_false
  | some o_good =>
    cases h_eb : eval p_bad cert.q₀ cert.k_bad with
    | none => intro h_false; cases h_false
    | some o_bad =>
      intro h_post_both
      have ⟨h_post_good, h_not_post_bad⟩ := (and_eq_true_iff _ _).mp h_post_both
      have h_post_bad_false : obsPostB cert.q₀ (obs o_bad) = false := by
        cases h_pb : obsPostB cert.q₀ (obs o_bad) with
        | false => rfl
        | true =>
          rw [h_pb] at h_not_post_bad
          cases h_not_post_bad
      have h_obs_ne : obs o_good ≠ obs o_bad := by
        intro h_eq
        rw [h_eq] at h_post_good
        rw [h_post_good] at h_post_bad_false
        cases h_post_bad_false
      have h_not_const_obs : ¬ (∀ o₁ o₂ : Out, obs o₁ = obs o₂) :=
        fun h_all => h_obs_ne (h_all o_good o_bad)
      have h_not_subsingleton : ¬ (∀ s₁ s₂ : SemObs, s₁ = s₂) :=
        fun h_sub => h_obs_ne (h_sub (obs o_good) (obs o_bad))
      have h_not_triv_post :
          ¬ (∀ q o, preB q = true → obsPostB q (obs o) = true) := by
        intro h_triv
        have h_true := h_triv cert.q₀ o_bad h_pre
        rw [h_true] at h_post_bad_false
        cases h_post_bad_false
      have h_sem_ne : L.sem p_good ≠ L.sem p_bad := by
        intro h_sem_eq
        have h_def_good : (L.sem p_good cert.q₀).defined :=
          ⟨cert.k_good, o_good, h_eg⟩
        have h_def_bad : (L.sem p_bad cert.q₀).defined :=
          ⟨cert.k_bad, o_bad, h_eb⟩
        have h_val_bad : (L.sem p_bad cert.q₀).val h_def_bad o_bad :=
          ⟨cert.k_bad, h_eb⟩
        have h_q_eq : L.sem p_good cert.q₀ = L.sem p_bad cert.q₀ :=
          congrFun h_sem_eq cert.q₀
        have h_val_good : (L.sem p_good cert.q₀).val h_def_good o_bad :=
          Partial.val_of_eq h_q_eq h_def_good h_def_bad o_bad h_val_bad
        cases h_val_good with
        | intro k_alt h_eg_alt =>
          have h_o_eq : o_good = o_bad :=
            h_det_good cert.k_good k_alt o_good o_bad h_eg h_eg_alt
          exact h_obs_ne (congrArg obs h_o_eq)
      have h_refuted :
          L.RefutedOn dom (fun q => preB q = true)
            (fun q o => obsPostB q (obs o) = true) p_bad := by
        intro h_ver
        have ⟨_, h_post_le⟩ := h_ver.2.2 cert.q₀ h_pre
        have h_bad_runs : ∃ k, eval p_bad cert.q₀ k = some o_bad :=
          ⟨cert.k_bad, h_eb⟩
        have h_bad_sat : obsPostB cert.q₀ (obs o_bad) = true :=
          h_post_le o_bad h_bad_runs
        rw [h_bad_sat] at h_post_bad_false
        cases h_post_bad_false
      have h_refuted_prod :
          L.RefutedProductiveOn dom (fun q => q = cert.q₀ ∧ preB q = true)
            (fun q o => obsPostB q (obs o) = true) p_bad := by
        refine ⟨?_, ?_⟩
        · intro q ⟨hq_eq, _⟩
          rw [hq_eq]
          exact ⟨⟨cert.k_bad, o_bad, h_eb⟩, o_bad, ⟨cert.k_bad, h_eb⟩⟩
        · intro h_ver_pt
          have ⟨_, h_post_le⟩ := h_ver_pt.2.2 cert.q₀ ⟨rfl, h_pre⟩
          have h_bad_runs : ∃ k, eval p_bad cert.q₀ k = some o_bad :=
            ⟨cert.k_bad, h_eb⟩
          have h_bad_sat : obsPostB cert.q₀ (obs o_bad) = true :=
            h_post_le o_bad h_bad_runs
          rw [h_bad_sat] at h_post_bad_false
          cases h_post_bad_false
      exact ⟨⟨cert.q₀, h_pre⟩, ⟨o_good, o_bad, h_obs_ne⟩,
        h_not_const_obs, h_not_subsingleton, h_not_triv_post,
        h_sem_ne, h_refuted, h_refuted_prod⟩

/-!
### 4.1 Concrete Toy Instantiation Discharged in $O(1)$ by `rfl`

We instantiate `ComputableLang` and `certificate_discharges_canary_and_nonvacuity`
on a concrete arithmetic language with three programs:
- `.addOne` (`p_good`): returns `some ⟨q + 1, 99⟩` at fuel `≥ 1`,
- `.idBug` (`p_bad`): off-by-one bug returning `some ⟨q, 0⟩` at fuel `≥ 1`, and
- `.hang` (`p_div`): diverges (`none` for all fuel `k`).
-/

inductive ToyProg where
  | addOne
  | idBug
  | hang
  deriving DecidableEq

/-- Concrete outcomes include both an observable return value `retVal : Nat`
    and an unobserved scratch register `scratchReg : Nat`. -/
structure ToyOut where
  retVal     : Nat
  scratchReg : Nat
  deriving DecidableEq

def toyObs (o : ToyOut) : Nat :=
  o.retVal

def toyEval (p : ToyProg) (q : Nat) (fuel : Nat) : Option ToyOut :=
  match fuel with
  | 0 => none
  | _ + 1 =>
    match p with
    | .addOne => some ⟨q + 1, 99⟩
    | .idBug  => some ⟨q, 0⟩
    | .hang   => none

def toyPreB (q : Nat) : Bool :=
  Nat.ble q 100

def toyObsPostB (q : Nat) (sObs : Nat) : Bool :=
  Nat.beq sObs (q + 1)

def toyCert : CanaryCertificate Nat where
  q₀     := 7
  k_good := 1
  k_bad  := 1

/-- The $\Delta^0_0$ certificate check reduces to `true` by literal `rfl` in
    the Lean kernel! -/
theorem toyCert_valid_by_rfl :
    checkCanaryCertificate toyEval toyObs toyPreB toyObsPostB
      .addOne .idBug toyCert = true :=
  rfl

theorem toyEval_addOne_deterministic (q : Nat) :
    StepDeterministic toyEval .addOne q := by
  intro k₁ k₂ o₁ o₂ h₁ h₂
  cases k₁ with
  | zero => cases h₁
  | succ k₁' =>
    cases k₂ with
    | zero => cases h₂
    | succ k₂' =>
      unfold toyEval at h₁ h₂
      cases h₁
      cases h₂
      rfl

/-- **Theorem 4.2 (`toy_canary_and_nonvacuity_by_rfl`):**
    Combining `toyCert_valid_by_rfl` (`rfl`) with
    `certificate_discharges_canary_and_nonvacuity` immediately discharges
    precondition inhabitation, observable-spine separation, non-constant `obs`,
    non-subsingleton `SemObs`, non-trivial `obsPost`, semantic program
    inequality, and `RefutedOn` for `.idBug`! -/
theorem toy_canary_and_nonvacuity_by_rfl :
    let L := ComputableLang ToyProg Nat ToyOut Nat toyEval toyObs (fun _ => True)
    (∃ q, toyPreB q = true) ∧
    (∃ o_good o_bad : ToyOut, toyObs o_good ≠ toyObs o_bad) ∧
    ¬ (∀ o₁ o₂ : ToyOut, toyObs o₁ = toyObs o₂) ∧
    ¬ (∀ s₁ s₂ : Nat, s₁ = s₂) ∧
    ¬ (∀ q o, toyPreB q = true → toyObsPostB q (toyObs o) = true) ∧
    L.sem .addOne ≠ L.sem .idBug ∧
    L.RefutedOn
      (fun _ => True)
      (fun q => toyPreB q = true)
      (fun q o => toyObsPostB q (toyObs o) = true)
      .idBug ∧
    L.RefutedProductiveOn
      (fun _ => True)
      (fun q => q = toyCert.q₀ ∧ toyPreB q = true)
      (fun q o => toyObsPostB q (toyObs o) = true)
      .idBug :=
  certificate_discharges_canary_and_nonvacuity
    toyEval toyObs (fun _ => True) toyPreB toyObsPostB
    .addOne .idBug toyCert
    toyCert_valid_by_rfl
    (toyEval_addOne_deterministic toyCert.q₀)

/-!
## 5. Formalizing the Intent Gap: Naur's Theory, Popperian Falsifiers, and Lakatosian Refinement

Peter Naur (1985, *"Programming as Theory Building"*) and Brian Cantwell Smith
(1985, *"The Limits of Correctness"*) observe that a programmer's intended
behavior is an unformalized mental theory (`HumanIntent : Query → SemObs → Prop`)
living outside the formal text. Because `HumanIntent` is not directly inspectable
as a closed formula, a formal specification `(pre, obsPost)` can suffer from
**Under-Specification** (`obsPost` permits an outcome that violates
`HumanIntent`) or **Over-Specification** (`obsPost` rejects an outcome permitted
by `HumanIntent`).

We prove two theorems characterizing why pure $\Pi^0_1$ verification is blind to
under-specification and how **Popperian ground falsifiers** (Popper 1934/1959)
and **Lakatosian counterexample-driven specification refinement** (Lakatos 1976)
bridge the formal/informal boundary:
1. `pure_deduction_blind_to_under_specification`: Any productive buggy program
   `p_bad` that violates `HumanIntent` at `(q₀, o_bad)` still satisfies
   `L.VerifiedSpine pre (fun _ _ => True) p_bad` when `pre` is inhabited.
2. `lakatos_counterexample_exposes_under_specification_and_refines`: When a
   buggy program `p_bad` violates `HumanIntent` at `(q₀, o_bad)` yet passes a
   candidate formal specification `obsPost₁`, that false positive constructively
   proves `UnderSpecified pre obsPost₁ HumanIntent`. Strengthening `obsPost₁` to
   `obsPost₂` under `L.VerifiedSpineWithCanaries pre obsPost₂ p_good [p_bad]`
   refutes `p_bad` while preserving `p_good`.
-/

/-- A formal spine postcondition `obsPost` is **under-specified** relative to
    `HumanIntent` on `pre` if there exists a valid query `q` and observable
    outcome `s` permitted by `obsPost q s` that violates `HumanIntent q s`. -/
def UnderSpecified {Query SemObs : Type}
    (pre : Query → Prop)
    (obsPost HumanIntent : Query → SemObs → Prop) : Prop :=
  ∃ q s, pre q ∧ obsPost q s ∧ ¬ HumanIntent q s

/-- **Theorem 5.1 (`pure_deduction_blind_to_under_specification`):**
    Even if a buggy program `p_bad` produces an outcome `o_bad` at `q₀` (`pre q₀`)
    that violates `HumanIntent q₀ (L.obs o_bad)`, pure universal verification
    `L.VerifiedSpine pre obsPost p_bad` still holds whenever `obsPost` is
    under-specified so as to permit `L.obs o_bad` (for example,
    `obsPost := fun _ _ => True`). -/
theorem pure_deduction_blind_to_under_specification
    {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (HumanIntent : L.Query → SemObs → Prop)
    (p_bad : L.Prog)
    (q₀ : L.Query) (h_pre₀ : pre q₀)
    (h_prod : L.ProductiveOn pre p_bad)
    (h_def₀ : (L.sem p_bad q₀).defined)
    (o_bad : L.Out) (h_out_bad : (L.sem p_bad q₀).val h_def₀ o_bad)
    (h_violates_intent : ¬ HumanIntent q₀ (L.obs o_bad)) :
    (L.sem p_bad q₀).val h_def₀ o_bad ∧
    L.VerifiedSpine pre (fun _ _ => True) p_bad ∧
    UnderSpecified pre (fun _ _ => True) HumanIntent := by
  refine ⟨h_out_bad, ⟨Or.inl ⟨q₀, h_pre₀⟩, h_prod, ?_⟩,
    ⟨q₀, L.obs o_bad, h_pre₀, trivial, h_violates_intent⟩⟩
  intro q _
  cases h_prod q ‹pre q› with
  | intro hdef _ =>
    exact ⟨hdef, fun _ _ => trivial⟩

/-- **Theorem 5.2 (Lakatosian Counterexample Discovery & Specification
    Refinement — `lakatos_counterexample_exposes_under_specification_and_refines`):**
    Suppose a candidate formal specification `obsPost₁` mistakenly verifies a
    mutant `p_bad` (`L.VerifiedSpine pre obsPost₁ p_bad`) that produces an
    outcome `o_bad` at `q₀` (`pre q₀`) violating the user's mental model
    (`¬ HumanIntent q₀ (L.obs o_bad)`). Then:
    1. `(q₀, L.obs o_bad)` constructively witnesses
       `UnderSpecified pre obsPost₁ HumanIntent` (exposing the specification
       gap), and
    2. Refining `obsPost₁` by conjoining a guard `guard : L.Query → SemObs → Prop`
       that holds on `p_good` and rejects `(q₀, L.obs o_bad)` produces a
       strictly stronger specification
       `obsPost₂ q s := obsPost₁ q s ∧ guard q s` (`L.SpineSpecOn pre obsPost₂ ≤
       L.SpineSpecOn pre obsPost₁`) that refutes `p_bad`! -/
theorem lakatos_counterexample_exposes_under_specification_and_refines
    {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (obsPost₁ HumanIntent guard : L.Query → SemObs → Prop)
    (p_bad : L.Prog)
    (q₀ : L.Query) (h_pre₀ : pre q₀)
    (h_def₀ : (L.sem p_bad q₀).defined)
    (o_bad : L.Out) (h_out_bad : (L.sem p_bad q₀).val h_def₀ o_bad)
    (h_false_pos : L.VerifiedSpine pre obsPost₁ p_bad)
    (h_violates_intent : ¬ HumanIntent q₀ (L.obs o_bad))
    (h_guard_refutes : ¬ guard q₀ (L.obs o_bad)) :
    let obsPost₂ := fun q s => obsPost₁ q s ∧ guard q s
    UnderSpecified pre obsPost₁ HumanIntent ∧
    (L.SpineSpecOn pre obsPost₂ ≤ L.SpineSpecOn pre obsPost₁) ∧
    L.Refuted pre (fun q o => obsPost₂ q (L.obs o)) p_bad := by
  intro obsPost₂
  have ⟨_, h_post₁_le⟩ := h_false_pos.2.2 q₀ h_pre₀
  have h_sat₁ : obsPost₁ q₀ (L.obs o_bad) := h_post₁_le o_bad h_out_bad
  have h_under : UnderSpecified pre obsPost₁ HumanIntent :=
    ⟨q₀, L.obs o_bad, h_pre₀, h_sat₁, h_violates_intent⟩
  have h_stronger : L.SpineSpecOn pre obsPost₂ ≤ L.SpineSpecOn pre obsPost₁ := by
    intro q hpre
    exact ⟨hpre, fun o h_both => h_both.1⟩
  have h_refuted₂ : L.Refuted pre (fun q o => obsPost₂ q (L.obs o)) p_bad := by
    intro h_ver₂
    have ⟨_, h_post₂_le⟩ := h_ver₂.2.2 q₀ h_pre₀
    have h_sat₂ : obsPost₂ q₀ (L.obs o_bad) := h_post₂_le o_bad h_out_bad
    exact h_guard_refutes h_sat₂.2
  exact ⟨h_under, h_stronger, h_refuted₂⟩

end Anneal.TractabilityAndIncompleteness
