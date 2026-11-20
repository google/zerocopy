import ToyHyper.Core

/-!
# Observational Determinism, Low-View Restriction, and the Refinement Paradox

This module models single-step input/output traces `(lowIn, highIn, lowOut)`
(with no high outputs) and formalizes:
- observational determinism (`ObsDet`),
- single-step generalized noninterference (`GNI`, specializing McLean's 1994
  selective-interleaving formulation as restated in Clarkson & Schneider 2010),
- functional determinism (`Deterministic`),
- input totality (`InputTotal`),
- rectangular acceptance domains (`RectangularDomain`),
- secret-independent acceptance (`AcceptanceIgnoresHigh`),
- secret-independent output functions (`SecretIndependent`), and
- low-view restriction (`lowViewRestrict`).

It states preservation of `ObsDet` under trace inclusion, proves the refinement
paradox for `GNI` with an input-total deterministic refinement, proves that
every low-view restriction preserves `GNI` (yielding proper input-total
deterministic refinements), and proves that a deterministic system admits no
proper input-total refinement at all.
-/

namespace Toy.Hyper

universe u v w

/-- A single-step security trace recording a public input `lowIn`, a secret
input `highIn`, and a public output `lowOut` (with no high outputs). -/
structure IOTrace (LowIn : Type u) (HighIn : Type v) (LowOut : Type w) where
  lowIn : LowIn
  highIn : HighIn
  lowOut : LowOut
  deriving DecidableEq, Repr

/-- The total deterministic system induced by a pure function `impl : L → H → O`. -/
def ofFn {L : Type u} {H : Type v} {O : Type w} (impl : L → H → O) :
    System (IOTrace L H O) :=
  fun t => t.lowOut = impl t.lowIn t.highIn

/-- Observational determinism: any two executions with the same public input
produce the same public output, regardless of secret input or internal
nondeterminism. Each public input therefore has at most one public output. -/
def ObsDet {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ → t₁.lowIn = t₂.lowIn → t₁.lowOut = t₂.lowOut

/-- Generalized noninterference (`GNI`), specializing McLean's (1994)
selective-interleaving formulation (restated as Eq. (2.5) in Clarkson &
Schneider 2010) to single-step `(lowIn, highIn, lowOut)` traces with no high
outputs: for any two traces `t₁` and `t₂` of `S`, there exists a trace `t₃` of
`S` combining `t₁.highIn` with `t₂.lowIn` and `t₂.lowOut`. Because `t₁` and
`t₂` range over traces of `S`, this quantifies over occurring secrets only and
is equivalent to `∀ t₁ t₂, S t₁ → S t₂ → S ⟨t₂.lowIn, t₁.highIn, t₂.lowOut⟩`
(see `gni_iff_low_view_compatible_with_every_secret`). -/
def GNI {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ →
    ∃ t₃, S t₃ ∧ t₃.highIn = t₁.highIn ∧ t₃.lowIn = t₂.lowIn ∧ t₃.lowOut = t₂.lowOut

/-- Functional determinism: each `(lowIn, highIn)` pair determines at most one
`lowOut`. -/
def Deterministic {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ →
    t₁.lowIn = t₂.lowIn → t₁.highIn = t₂.highIn → t₁.lowOut = t₂.lowOut

/-- Input totality: every `(lowIn, highIn)` input pair yields at least one
trace in `S`. -/
def InputTotal {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ l h, ∃ o, S ⟨l, h, o⟩

/-- Rectangular acceptance domain: the accepted `(lowIn, highIn)` input pairs
form a product set (rectangle) of the accepted low inputs and the accepted high
inputs. This excludes acceptance that depends jointly on `lowIn` and `highIn`
(such as `diagonalPartialSystem`), but does **not** exclude acceptance that
depends on `highIn` alone (such as `echoLowHighFalseSystem`); neither
`RectangularDomain` nor `GNI` is termination-sensitive in the secret. -/
def RectangularDomain {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ t₁ t₂, S t₁ → S t₂ → ∃ o, S ⟨t₂.lowIn, t₁.highIn, o⟩

/-- Secret-independent acceptance: if `(l, h)` is accepted by `S`, then
`(l, h')` is accepted for every secret `h' : H`. Strictly stronger than
`RectangularDomain` and strictly weaker than `InputTotal`. -/
def AcceptanceIgnoresHigh {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) : Prop :=
  ∀ l h h', (∃ o, S ⟨l, h, o⟩) → ∃ o, S ⟨l, h', o⟩

/-- Secret independence of a function `f : L → H → O`: its output depends only
on the public input `l`, never on the secret input `h`. -/
def SecretIndependent {L : Type u} {H : Type v} {O : Type w}
    (f : L → H → O) : Prop :=
  ∀ l h₁ h₂, f l h₁ = f l h₂

/-- Restricting a system `S` by a predicate `P : L → O → Prop` depending only
on the public (low) view `(lowIn, lowOut)`. This defines a trace-inclusion
refinement that filters traces by `(lowIn, lowOut)` and always preserves `GNI`
(exact among input-total `GNI` refinements by
`inputTotal_gni_refinement_is_lowViewRestrict`, though it need not preserve
`InputTotal` and does not cover secret-filtered partial refinements such as
`highFalseFullSystem`). -/
def lowViewRestrict {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) (P : L → O → Prop) : System (IOTrace L H O) :=
  fun t => S t ∧ P t.lowIn t.lowOut

/-! ## Concrete Systems and Definition Examples -/

/-- A system that outputs its public input and ignores the secret input. -/
def echoLowSystem : System (IOTrace Bool Bool Bool) :=
  ofFn (fun l _ => l)

/-- A strict refinement of `echoLowSystem` that accepts inputs exactly when
`highIn = false`. It is partial (not `InputTotal`), yet satisfies
`Deterministic`, `ObsDet`, `RectangularDomain`, and `GNI`, while failing
`AcceptanceIgnoresHigh`. -/
def echoLowHighFalseSystem : System (IOTrace Bool Bool Bool) :=
  fun t => t.lowOut = t.lowIn ∧ t.highIn = false

/-- A partial deterministic system on `IOTrace Bool Bool Bool` that accepts
inputs exactly when `lowIn = false` (for every `highIn`), outputting `false`.
Separates `AcceptanceIgnoresHigh` from `InputTotal`. -/
def echoLowOnlyLowFalseSystem : System (IOTrace Bool Bool Bool) :=
  fun t => t.lowIn = false ∧ t.lowOut = false

/-- The nondeterministic system on `IOTrace Unit Bool Bool` that allows every
Boolean output for every secret bit. -/
def fullIOSystem : System (IOTrace Unit Bool Bool) :=
  fun _ => True

/-- The deterministic, input-total system on `IOTrace Unit Bool Bool` that
copies the secret bit directly to the public output. -/
def leakHighSystem : System (IOTrace Unit Bool Bool) :=
  ofFn (fun _ h => h)

/-- The constant-false deterministic system on `IOTrace Unit Bool Bool`. -/
def constFalseIOSystem : System (IOTrace Unit Bool Bool) :=
  ofFn (fun _ _ => false)

/-- The empty system on `IOTrace Unit Bool Bool`. -/
def emptyIOSystem : System (IOTrace Unit Bool Bool) :=
  fun _ => False

/-- A partial deterministic system on `IOTrace Bool Bool Bool` that always
outputs `false`, but only accepts inputs where `lowIn = highIn` (acceptance
depends jointly on `lowIn` and `highIn`, violating `RectangularDomain`). -/
def diagonalPartialSystem : System (IOTrace Bool Bool Bool) :=
  fun t => t.lowIn = t.highIn ∧ t.lowOut = false

/-- Positive example for `ofFn`: `(false, true, false)` belongs to `echoLowSystem`. -/
theorem ofFn_pos_example : ofFn (fun (l : Bool) (_ : Bool) => l) ⟨false, true, false⟩ :=
  rfl

/-- Negative example for `ofFn`: `(false, true, true)` does not belong to `echoLowSystem`. -/
theorem ofFn_neg_example : ¬ ofFn (fun (l : Bool) (_ : Bool) => l) ⟨false, true, true⟩ := by
  intro h
  cases h

/-- Positive example for `ObsDet`: `echoLowSystem` is observationally
deterministic. -/
theorem obsDet_pos_example : ObsDet echoLowSystem := by
  intro t₁ t₂ ht₁ ht₂ hLo
  change t₁.lowOut = t₁.lowIn at ht₁
  change t₂.lowOut = t₂.lowIn at ht₂
  rw [ht₁, ht₂, hLo]

/-- Negative example for `ObsDet`: `leakHighSystem` violates observational
determinism. -/
theorem obsDet_neg_example : ¬ ObsDet leakHighSystem := by
  intro hOD
  have h0 : leakHighSystem ⟨(), false, false⟩ := rfl
  have h1 : leakHighSystem ⟨(), true, true⟩ := rfl
  have hEq := hOD ⟨(), false, false⟩ ⟨(), true, true⟩ h0 h1 rfl
  cases hEq

/-- Positive example for `GNI`: `fullIOSystem` satisfies generalized
noninterference. -/
theorem gni_pos_example : GNI fullIOSystem := by
  intro t₁ t₂ _ _
  exact ⟨⟨t₂.lowIn, t₁.highIn, t₂.lowOut⟩, trivial, rfl, rfl, rfl⟩

/-- Negative example for `GNI`: `leakHighSystem` violates generalized
noninterference. -/
theorem gni_neg_example : ¬ GNI leakHighSystem := by
  intro hGNI
  have h0 : leakHighSystem ⟨(), false, false⟩ := rfl
  have h1 : leakHighSystem ⟨(), true, true⟩ := rfl
  rcases hGNI ⟨(), false, false⟩ ⟨(), true, true⟩ h0 h1 with ⟨t₃, hS₃, hHi, _, hOut⟩
  change t₃.lowOut = t₃.highIn at hS₃
  rw [hOut, hHi] at hS₃
  cases hS₃

/-- Positive example for `Deterministic`: `leakHighSystem` is deterministic. -/
theorem deterministic_pos_example : Deterministic leakHighSystem := by
  intro t₁ t₂ ht₁ ht₂ _ hHi
  change t₁.lowOut = t₁.highIn at ht₁
  change t₂.lowOut = t₂.highIn at ht₂
  rw [ht₁, ht₂, hHi]

/-- Negative example for `Deterministic`: `fullIOSystem` is nondeterministic. -/
theorem deterministic_neg_example : ¬ Deterministic fullIOSystem := by
  intro hDet
  have hEq := hDet ⟨(), false, false⟩ ⟨(), false, true⟩ trivial trivial rfl rfl
  cases hEq

/-- Positive example for `InputTotal`: `leakHighSystem` is input-total. -/
theorem inputTotal_pos_example : InputTotal leakHighSystem := by
  intro _ h
  exact ⟨h, rfl⟩

/-- Negative example for `InputTotal`: `emptyIOSystem` is not input-total. -/
theorem inputTotal_neg_example : ¬ InputTotal emptyIOSystem := by
  intro hTot
  rcases hTot () false with ⟨_, hf⟩
  exact hf

/-- Positive example for `RectangularDomain`: `echoLowHighFalseSystem` has a
rectangular acceptance domain (`Bool × {false}`) while failing `InputTotal`,
separating `RectangularDomain` from `InputTotal`. -/
theorem rectangularDomain_pos_example : RectangularDomain echoLowHighFalseSystem := by
  intro t₁ t₂ h₁ _
  exact ⟨t₂.lowIn, rfl, h₁.2⟩

/-- Negative example for `RectangularDomain`: `diagonalPartialSystem` accepts
`(false, false)` and `(true, true)` but rejects `(true, false)`. -/
theorem rectangularDomain_neg_example :
    ¬ RectangularDomain diagonalPartialSystem := by
  intro hDom
  have h0 : diagonalPartialSystem ⟨false, false, false⟩ := ⟨rfl, rfl⟩
  have h1 : diagonalPartialSystem ⟨true, true, false⟩ := ⟨rfl, rfl⟩
  rcases hDom ⟨false, false, false⟩ ⟨true, true, false⟩ h0 h1 with ⟨_, hEq, _⟩
  cases hEq

/-- Positive example for `AcceptanceIgnoresHigh`: `echoLowOnlyLowFalseSystem`
accepts an input iff `lowIn = false` regardless of `highIn` (separating
`AcceptanceIgnoresHigh` from `InputTotal`). -/
theorem acceptanceIgnoresHigh_pos_example :
    AcceptanceIgnoresHigh echoLowOnlyLowFalseSystem := by
  intro l _ _ ⟨_, hLo, _⟩
  exact ⟨false, hLo, rfl⟩

/-- Negative example for `AcceptanceIgnoresHigh`: `echoLowHighFalseSystem`
accepts `(false, false)` but rejects `(false, true)`. -/
theorem acceptanceIgnoresHigh_neg_example :
    ¬ AcceptanceIgnoresHigh echoLowHighFalseSystem := by
  intro hA
  rcases hA false false true ⟨false, rfl, rfl⟩ with ⟨_, _, hBad⟩
  cases hBad

/-- Positive example for `SecretIndependent`: projecting `lowIn` is
secret-independent. -/
theorem secretIndependent_pos_example :
    SecretIndependent (fun (l : Bool) (_ : Bool) => l) := by
  intro _ _ _
  rfl

/-- Negative example for `SecretIndependent`: projecting `highIn` is not
secret-independent. -/
theorem secretIndependent_neg_example :
    ¬ SecretIndependent (fun (_ : Unit) (h : Bool) => h) := by
  intro hSI
  have hEq := hSI () false true
  cases hEq

/-- Positive example for `lowViewRestrict`: restricting `fullIOSystem` to
`lowOut = false` admits `((), true, false)`. -/
theorem lowViewRestrict_pos_example :
    lowViewRestrict fullIOSystem (fun _ o => o = false) ⟨(), true, false⟩ :=
  ⟨trivial, rfl⟩

/-- Negative example for `lowViewRestrict`: restricting `fullIOSystem` to
`lowOut = false` rejects `((), true, true)`. -/
theorem lowViewRestrict_neg_example :
    ¬ lowViewRestrict fullIOSystem (fun _ o => o = false) ⟨(), true, true⟩ := by
  intro ⟨_, h⟩
  cases h

/-! ## Structural and Boundary Lemmas -/

/-- In this single-step trace shape with no high outputs, `GNI` is equivalent
to requiring every occurring low view `(t₂.lowIn, t₂.lowOut)` to be compatible
with every occurring secret `t₁.highIn`. -/
theorem gni_iff_low_view_compatible_with_every_secret
    {L : Type u} {H : Type v} {O : Type w} (S : System (IOTrace L H O)) :
    GNI S ↔ ∀ t₁ t₂, S t₁ → S t₂ → S ⟨t₂.lowIn, t₁.highIn, t₂.lowOut⟩ := by
  constructor
  · intro h t₁ t₂ h₁ h₂
    rcases h t₁ t₂ h₁ h₂ with ⟨t₃, hS, hH, hL, hO⟩
    cases t₃ with
    | mk l hh o =>
      simp only at hH hL hO
      subst hH; subst hL; subst hO
      exact hS
  · intro h t₁ t₂ h₁ h₂
    exact ⟨_, h t₁ t₂ h₁ h₂, rfl, rfl, rfl⟩

/-- `ObsDet` forbids all low-observable nondeterminism: each public input has
at most one public output. -/
theorem obsDet_at_most_one_output
    {L : Type u} {H : Type v} {O : Type w} {S : System (IOTrace L H O)}
    (hOD : ObsDet S) (l : L) (h₁ h₂ : H) (o₁ o₂ : O)
    (h₁S : S ⟨l, h₁, o₁⟩) (h₂S : S ⟨l, h₂, o₂⟩) : o₁ = o₂ :=
  hOD _ _ h₁S h₂S rfl

/-- Derivable implication: every observationally deterministic system is
functionally deterministic. -/
theorem obsDet_imp_deterministic
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hOD : ObsDet S) : Deterministic S := by
  intro t₁ t₂ ht₁ ht₂ hLo _
  exact hOD t₁ t₂ ht₁ ht₂ hLo

/-- Derivable implication: every input-total system has secret-independent
acceptance. -/
theorem inputTotal_imp_acceptanceIgnoresHigh
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hTot : InputTotal S) : AcceptanceIgnoresHigh S := by
  intro l _ h' _
  exact hTot l h'

/-- `AcceptanceIgnoresHigh` is strictly weaker than `InputTotal`. -/
theorem acceptanceIgnoresHigh_not_imp_inputTotal :
    AcceptanceIgnoresHigh echoLowOnlyLowFalseSystem ∧
    ¬ InputTotal echoLowOnlyLowFalseSystem := by
  refine ⟨acceptanceIgnoresHigh_pos_example, ?_⟩
  intro hTot
  rcases hTot true false with ⟨_, hLo, _⟩
  cases hLo

/-- Derivable implication: secret-independent acceptance implies a rectangular
acceptance domain. -/
theorem acceptanceIgnoresHigh_imp_rectangularDomain
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hA : AcceptanceIgnoresHigh S) : RectangularDomain S := by
  intro t₁ t₂ _ h₂
  exact hA t₂.lowIn t₂.highIn t₁.highIn ⟨t₂.lowOut, h₂⟩

/-- Derivable implication: every input-total system has a rectangular
acceptance domain. -/
theorem inputTotal_imp_rectangularDomain
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hTot : InputTotal S) : RectangularDomain S :=
  acceptanceIgnoresHigh_imp_rectangularDomain (inputTotal_imp_acceptanceIgnoresHigh hTot)

/-- Exact product-set (rectangle) characterization of `RectangularDomain`:
accepted `(lowIn, highIn)` pairs form the Cartesian product of the accepted low
inputs and the accepted high inputs. -/
theorem rectangularDomain_iff_product
    {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) :
    RectangularDomain S ↔
      ∀ l h, (∃ t, S t ∧ t.lowIn = l) → (∃ t, S t ∧ t.highIn = h) → ∃ o, S ⟨l, h, o⟩ := by
  constructor
  · rintro hDom l h ⟨t₂, h₂, rfl⟩ ⟨t₁, h₁, rfl⟩
    exact hDom t₁ t₂ h₁ h₂
  · intro hRect t₁ t₂ h₁ h₂
    exact hRect t₂.lowIn t₁.highIn ⟨t₂, h₂, rfl⟩ ⟨t₁, h₁, rfl⟩

/-- Minimal-hypothesis directional lemma: `GNI` implies `RectangularDomain`
without any determinism assumption. -/
theorem gni_imp_rectangularDomain
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hGNI : GNI S) : RectangularDomain S := by
  intro t₁ t₂ h₁ h₂
  rcases hGNI t₁ t₂ h₁ h₂ with ⟨t₃, h₃, hHi, hLo, _⟩
  refine ⟨t₃.lowOut, ?_⟩
  rw [← hHi, ← hLo]
  exact h₃

/-- Minimal-hypothesis directional lemma: `GNI` and `Deterministic` imply
`ObsDet` (no domain condition needed). -/
theorem obsDet_of_gni_of_deterministic
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hDet : Deterministic S) (hGNI : GNI S) : ObsDet S := by
  intro t₁ t₂ h₁ h₂ hLo
  rcases hGNI t₁ t₂ h₁ h₂ with ⟨t₃, h₃, hHi, hLo₃, hOut⟩
  have h13 : t₁.lowOut = t₃.lowOut := hDet t₁ t₃ h₁ h₃ (hLo.trans hLo₃.symm) hHi.symm
  exact h13.trans hOut

/-- Minimal-hypothesis directional lemma: `ObsDet` and `RectangularDomain`
imply `GNI` (no separate `Deterministic` hypothesis needed). -/
theorem gni_of_obsDet_of_rectangularDomain
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)}
    (hOD : ObsDet S) (hDom : RectangularDomain S) : GNI S := by
  intro t₁ t₂ h₁ h₂
  rcases hDom t₁ t₂ h₁ h₂ with ⟨o, ho⟩
  have hEq : o = t₂.lowOut := hOD ⟨t₂.lowIn, t₁.highIn, o⟩ t₂ ho h₂ rfl
  exact ⟨⟨t₂.lowIn, t₁.highIn, o⟩, ho, rfl, rfl, hEq⟩

/-- Boundary theorem: `echoLowHighFalseSystem` accepts an input **iff**
`highIn = false`, yet satisfies `Deterministic`, `ObsDet`, `RectangularDomain`,
and `GNI` while failing `InputTotal` and `AcceptanceIgnoresHigh`. Thus neither
`GNI` nor `RectangularDomain` rules out secret-filtered acceptance domains. -/
theorem gni_and_rectangularDomain_allow_secret_filtered_acceptance :
    Deterministic echoLowHighFalseSystem ∧
    ObsDet echoLowHighFalseSystem ∧
    RectangularDomain echoLowHighFalseSystem ∧
    GNI echoLowHighFalseSystem ∧
    ¬ InputTotal echoLowHighFalseSystem ∧
    ¬ AcceptanceIgnoresHigh echoLowHighFalseSystem ∧
    (∀ l h, (∃ o, echoLowHighFalseSystem ⟨l, h, o⟩) ↔ h = false) := by
  have hOD : ObsDet echoLowHighFalseSystem := by
    intro t₁ t₂ h₁ h₂ hLo
    rw [h₁.1, h₂.1, hLo]
  have hDom : RectangularDomain echoLowHighFalseSystem := rectangularDomain_pos_example
  refine ⟨obsDet_imp_deterministic hOD, hOD, hDom,
    gni_of_obsDet_of_rectangularDomain hOD hDom, ?_, acceptanceIgnoresHigh_neg_example, ?_⟩
  · intro hTot
    rcases hTot false true with ⟨_, _, hBad⟩
    cases hBad
  · intro l h
    exact ⟨fun ⟨_, _, hh⟩ => hh, fun hh => ⟨l, rfl, hh⟩⟩

/-- `ObsDet` is equivalent to a 2-ary universal hyperproperty. -/
theorem obsDet_iff_universal2Hyperprop
    {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) :
    ObsDet S ↔
      UniversalKHyperprop 2
        (fun ts : Fin 2 → IOTrace L H O =>
          (ts 0).lowIn = (ts 1).lowIn → (ts 0).lowOut = (ts 1).lowOut) S := by
  constructor
  · intro hOD ts hts hLo
    exact hOD (ts 0) (ts 1) (hts 0) (hts 1) hLo
  · intro hU t₁ t₂ ht₁ ht₂ hLo
    let ts : Fin 2 → IOTrace L H O := fun i => if i.val = 0 then t₁ else t₂
    have hts : ∀ i : Fin 2, S (ts i) := by
      intro ⟨i, hi⟩
      match i with
      | 0 => exact ht₁
      | 1 => exact ht₂
    exact hU ts hts hLo

/-- `lowViewRestrict S P` is always a trace-inclusion refinement of `S`. -/
theorem lowViewRestrict_refines
    {L : Type u} {H : Type v} {O : Type w}
    (S : System (IOTrace L H O)) (P : L → O → Prop) :
    Refines (lowViewRestrict S P) S :=
  fun _ h => h.1

/-- An input-total refinement of a deterministic system is trace-equivalent to
the source (there are no proper input-total refinements of a deterministic
system). -/
theorem inputTotal_refinement_of_deterministic_is_traceEquiv
    {L : Type u} {H : Type v} {O : Type w}
    {S S' : System (IOTrace L H O)}
    (hDet : Deterministic S) (hRef : Refines S' S) (hTot' : InputTotal S') :
    TraceEquiv S' S := by
  refine ⟨hRef, ?_⟩
  intro ⟨l, h, o'⟩ ht
  rcases hTot' l h with ⟨o, ho⟩
  have hEq : o' = o := hDet ⟨l, h, o'⟩ ⟨l, h, o⟩ ht (hRef _ ho) rfl rfl
  subst hEq
  exact ho

/-- Extensional form: any input-total refinement of a deterministic system is
extensionally equal to the source system itself. -/
theorem inputTotal_refinement_of_deterministic_eq
    {L : Type u} {H : Type v} {O : Type w}
    {S S' : System (IOTrace L H O)}
    (hDet : Deterministic S) (hRef : Refines S' S) (hTot' : InputTotal S') :
    S' = S :=
  funext fun t => propext
    ⟨hRef t, (inputTotal_refinement_of_deterministic_is_traceEquiv hDet hRef hTot').2 t⟩

/-- Consequence of `inputTotal_refinement_of_deterministic_is_traceEquiv`: a
deterministic system has no proper input-total refinement, so every
hyperproperty (in particular `GNI`) is trivially preserved because `S' = S`. -/
theorem gni_preserved_by_inputTotal_refinement_of_deterministic
    {L : Type u} {H : Type v} {O : Type w}
    {S S' : System (IOTrace L H O)}
    (hDet : Deterministic S) (hGNI : GNI S)
    (hRef : Refines S' S) (hTot' : InputTotal S') :
    GNI S' :=
  traceEquiv_preserves_hyperprop GNI
    (inputTotal_refinement_of_deterministic_is_traceEquiv hDet hRef hTot') hGNI

/-! ## Observational Determinism Is Preserved by Refinement -/

/-- Observational determinism is preserved by trace-inclusion refinement
(corollary of `universalKHyperprop_subsetClosed` via
`obsDet_iff_universal2Hyperprop`). -/
theorem obsDet_preserved_by_refinement
    {L : Type u} {H : Type v} {O : Type w}
    {S S' : System (IOTrace L H O)}
    (hRef : Refines S' S) (hOD : ObsDet S) :
    ObsDet S' := by
  intro t₁ t₂ h₁ h₂ hLo
  exact hOD t₁ t₂ (hRef _ h₁) (hRef _ h₂) hLo

/-- Non-vacuity witness for `obsDet_preserved_by_refinement`: a strict
refinement of `echoLowSystem` satisfying both hypotheses. -/
theorem obsDet_refinement_nonvacuity :
    Refines echoLowHighFalseSystem echoLowSystem ∧
    ¬ Refines echoLowSystem echoLowHighFalseSystem ∧
    ObsDet echoLowSystem := by
  refine ⟨?_, ?_, obsDet_pos_example⟩
  · intro _ ht
    exact ht.1
  · intro hRev
    have hBad := hRev ⟨false, true, false⟩ rfl
    cases hBad.2

/-- Tightness counterexample for hypothesis `hRef` of
`obsDet_preserved_by_refinement`: `constFalseIOSystem` satisfies `ObsDet`, but
without `Refines`, `leakHighSystem` violates `ObsDet`. -/
theorem obsDet_refinement_counterexample_no_refines :
    ObsDet constFalseIOSystem ∧
    ¬ Refines leakHighSystem constFalseIOSystem ∧
    ¬ ObsDet leakHighSystem := by
  refine ⟨?_, ?_, obsDet_neg_example⟩
  · intro t₁ t₂ ht₁ ht₂ _
    change t₁.lowOut = false at ht₁
    change t₂.lowOut = false at ht₂
    rw [ht₁, ht₂]
  · intro hRef
    have h1 : constFalseIOSystem ⟨(), true, true⟩ := hRef ⟨(), true, true⟩ rfl
    cases h1

/-- Tightness counterexample for hypothesis `hOD` of
`obsDet_preserved_by_refinement`: `leakHighSystem` strictly refines
`fullIOSystem`, `fullIOSystem` fails `ObsDet`, and `leakHighSystem` fails
`ObsDet`. -/
theorem obsDet_refinement_counterexample_no_obsDet :
    Refines leakHighSystem fullIOSystem ∧
    ¬ ObsDet fullIOSystem ∧
    ¬ ObsDet leakHighSystem := by
  refine ⟨fun _ _ => trivial, ?_, obsDet_neg_example⟩
  intro hOD
  have hEq := hOD ⟨(), false, false⟩ ⟨(), false, true⟩ trivial trivial rfl
  cases hEq

/-! ## Refinement Paradox for `GNI` and Low-View Restriction Preservation -/

/-- Refinement paradox: generalized noninterference is not preserved by
trace-inclusion refinement, even when both source and refinement are
input-total and the refinement is deterministic. On `IOTrace Unit Bool Bool`,
`leakHighSystem` refines `fullIOSystem` while breaking `GNI`. -/
theorem gni_not_preserved_by_inputTotal_refinement :
    GNI fullIOSystem ∧
    InputTotal fullIOSystem ∧
    Refines leakHighSystem fullIOSystem ∧
    InputTotal leakHighSystem ∧
    Deterministic leakHighSystem ∧
    ¬ GNI leakHighSystem := by
  refine ⟨gni_pos_example, ?_, ?_, inputTotal_pos_example, deterministic_pos_example,
    gni_neg_example⟩
  · intro _ _
    exact ⟨false, trivial⟩
  · intro _ _
    trivial

/-- Corollary: `GNI` on `IOTrace Unit Bool Bool` is not subset-closed. -/
theorem gni_not_subsetClosed : ¬ SubsetClosed (@GNI Unit Bool Bool) := by
  intro hSC
  have h := gni_not_preserved_by_inputTotal_refinement
  exact h.2.2.2.2.2 (hSC fullIOSystem leakHighSystem h.2.2.1 h.1)

/-- Non-trivial preservation class for `GNI`: restricting any `GNI` system by a
predicate `P : L → O → Prop` depending only on the public view `(lowIn, lowOut)`
is a trace-inclusion refinement (`lowViewRestrict_refines`) that preserves
`GNI` without requiring source determinism or trace equivalence. -/
theorem gni_preserved_by_lowViewRestrict
    {L : Type u} {H : Type v} {O : Type w}
    {S : System (IOTrace L H O)} (P : L → O → Prop)
    (hGNI : GNI S) :
    GNI (lowViewRestrict S P) := by
  intro t₁ t₂ h₁ h₂
  rcases hGNI t₁ t₂ h₁.1 h₂.1 with ⟨t₃, h₃, hHi, hLo, hOut⟩
  refine ⟨t₃, ⟨h₃, ?_⟩, hHi, hLo, hOut⟩
  rw [hLo, hOut]
  exact h₂.2

/-- Restricting `fullIOSystem` by `lowOut = false` yields `constFalseIOSystem`. -/
theorem lowViewRestrict_full_eq_constFalse :
    lowViewRestrict fullIOSystem (fun _ o => o = false) = constFalseIOSystem := by
  funext t
  apply propext
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Non-vacuity witness for `gni_preserved_by_lowViewRestrict` and non-degenerate
positive control for `gni_not_preserved_by_inputTotal_refinement`: on the
paradox's own source `fullIOSystem`, low-view restriction by `lowOut = false`
yields `constFalseIOSystem`, a **proper**, input-total, deterministic refinement
that preserves `GNI`. -/
theorem lowViewRestrict_proper_gni_control_instance :
    GNI fullIOSystem ∧
    lowViewRestrict fullIOSystem (fun _ o => o = false) = constFalseIOSystem ∧
    Refines constFalseIOSystem fullIOSystem ∧
    ¬ Refines fullIOSystem constFalseIOSystem ∧
    InputTotal constFalseIOSystem ∧
    Deterministic constFalseIOSystem ∧
    GNI constFalseIOSystem := by
  refine ⟨gni_pos_example, lowViewRestrict_full_eq_constFalse, fun _ _ => trivial, ?_,
    fun _ _ => ⟨false, rfl⟩, ?_, ?_⟩
  · intro h
    have hBad : constFalseIOSystem ⟨(), true, true⟩ := h _ trivial
    cases hBad
  · intro t₁ t₂ h₁ h₂ _ _
    change t₁.lowOut = false at h₁
    change t₂.lowOut = false at h₂
    rw [h₁, h₂]
  · rw [← lowViewRestrict_full_eq_constFalse]
    exact gni_preserved_by_lowViewRestrict (fun _ o => o = false) gni_pos_example

/-- Tightness counterexample for `hGNI` in `gni_preserved_by_lowViewRestrict`:
with `P _ _ := True`, `leakHighSystem` violates `GNI` and its low-view
restriction also violates `GNI`. -/
theorem gni_lowViewRestrict_counterexample_no_gni :
    ¬ GNI leakHighSystem ∧
    ¬ GNI (lowViewRestrict leakHighSystem (fun _ _ => True)) := by
  refine ⟨gni_neg_example, ?_⟩
  intro hGNI
  have h0 : lowViewRestrict leakHighSystem (fun _ _ => True) ⟨(), false, false⟩ := ⟨rfl, trivial⟩
  have h1 : lowViewRestrict leakHighSystem (fun _ _ => True) ⟨(), true, true⟩ := ⟨rfl, trivial⟩
  rcases hGNI ⟨(), false, false⟩ ⟨(), true, true⟩ h0 h1 with ⟨t₃, ⟨hS₃, _⟩, hHi, _, hOut⟩
  change t₃.lowOut = t₃.highIn at hS₃
  rw [hOut, hHi] at hS₃
  cases hS₃

/-- Boundary lemma for `lowViewRestrict`: low-view restriction preserves `GNI`
but does not automatically preserve `InputTotal`. -/
theorem lowViewRestrict_need_not_preserve_inputTotal :
    InputTotal fullIOSystem ∧
    GNI (lowViewRestrict fullIOSystem (fun _ _ => False)) ∧
    ¬ InputTotal (lowViewRestrict fullIOSystem (fun _ _ => False)) := by
  refine ⟨fun _ _ => ⟨false, trivial⟩,
    gni_preserved_by_lowViewRestrict (fun _ _ => False) gni_pos_example, ?_⟩
  intro hTot
  rcases hTot () false with ⟨_, _, hf⟩
  exact hf

/-- Partial trace-inclusion refinement of `fullIOSystem` retaining only traces
with `highIn = false`. -/
def highFalseFullSystem : System (IOTrace Unit Bool Bool) :=
  fun t => t.highIn = false

/-- Boundary theorem: restricting `fullIOSystem` to `highIn = false` is a
strict trace-inclusion refinement that preserves `GNI`, yet equals
`lowViewRestrict fullIOSystem P` for no `P`. Thus `lowViewRestrict` gives a
sufficient class of `GNI`-preserving refinements, not a characterization of
partial refinements. -/
theorem secretFiltered_refinement_preserves_gni_not_lowViewRestrict :
    GNI fullIOSystem ∧
    Refines highFalseFullSystem fullIOSystem ∧
    ¬ Refines fullIOSystem highFalseFullSystem ∧
    GNI highFalseFullSystem ∧
    (∀ P : Unit → Bool → Prop, lowViewRestrict fullIOSystem P ≠ highFalseFullSystem) := by
  refine ⟨gni_pos_example, fun _ _ => trivial, ?_, ?_, ?_⟩
  · intro h
    have hBad : highFalseFullSystem ⟨(), true, false⟩ := h _ trivial
    cases hBad
  · intro t₁ t₂ h₁ _
    exact ⟨⟨t₂.lowIn, t₁.highIn, t₂.lowOut⟩, h₁, rfl, rfl, rfl⟩
  · intro P hEq
    have h0 : highFalseFullSystem ⟨(), false, false⟩ := rfl
    rw [← hEq] at h0
    have h1 : lowViewRestrict fullIOSystem P ⟨(), true, false⟩ := ⟨trivial, h0.2⟩
    rw [hEq] at h1
    cases h1

/-- Exactness of `lowViewRestrict` among input-total refinements: every
input-total `GNI` refinement `S'` of any system `S` equals `lowViewRestrict S P`
for some public-view predicate `P`. -/
theorem inputTotal_gni_refinement_is_lowViewRestrict
    {L : Type u} {H : Type v} {O : Type w} {S S' : System (IOTrace L H O)}
    (hRef : Refines S' S) (hTot' : InputTotal S') (hGNI' : GNI S') :
    ∃ P : L → O → Prop, S' = lowViewRestrict S P := by
  have hG := (gni_iff_low_view_compatible_with_every_secret S').1 hGNI'
  refine ⟨fun l o => ∃ h, S' ⟨l, h, o⟩,
    funext fun t => propext ⟨fun ht => ⟨hRef t ht, t.highIn, ht⟩, ?_⟩⟩
  rintro ⟨_, h', ht'⟩
  rcases hTot' t.lowIn t.highIn with ⟨o₁, ho₁⟩
  exact hG ⟨t.lowIn, t.highIn, o₁⟩ ⟨t.lowIn, h', t.lowOut⟩ ho₁ ht'

/-- Boundary theorem: `ObsDet` is a 2-trace subset-closed hyperproperty that
coincides with no lifted single-trace property `LiftTraceProp P` on
`IOTrace Unit Unit Bool`. -/
theorem obsDet_not_liftTraceProp :
    ¬ ∃ P : TraceProp (IOTrace Unit Unit Bool), ∀ S, ObsDet S ↔ LiftTraceProp P S := by
  rintro ⟨P, hP⟩
  have hF : P ⟨(), (), false⟩ :=
    (hP (fun t => t = ⟨(), (), false⟩)).1 (by intro t₁ t₂ h₁ h₂ _; rw [h₁, h₂]) _ rfl
  have hT : P ⟨(), (), true⟩ :=
    (hP (fun t => t = ⟨(), (), true⟩)).1 (by intro t₁ t₂ h₁ h₂ _; rw [h₁, h₂]) _ rfl
  have hOD : ObsDet (fun _ : IOTrace Unit Unit Bool => True) := (hP _).2 (fun t _ => by
    rcases t with ⟨⟨⟩, ⟨⟩, b⟩
    cases b
    · exact hF
    · exact hT)
  have hEq := hOD ⟨(), (), false⟩ ⟨(), (), true⟩ trivial trivial rfl
  cases hEq

end Toy.Hyper
