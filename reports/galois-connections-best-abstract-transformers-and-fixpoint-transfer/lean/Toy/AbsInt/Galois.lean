/-
Toy.AbsInt.Galois
=================

Galois connections between the concrete domain `Pred σ` and an abstract domain
`A` with a bare `≤` relation, and their characterization by the four classical
laws (cards `R1-gc-iff`, `R1-gc-forward`, `R1-gc-backward`), with definition
examples and tightness counterexamples.
-/
import Toy.AbsInt.Domains

namespace Toy.AbsInt

section Defs
variable {σ A : Type} [LE A]

/-- `α` and `γ` form a Galois connection: for every concrete set `x` and every
abstract value `a`, `α x ≤ a` exactly when `x ⊆ γ a`.  This is the isotone form
(an adjunction `α ⊣ γ`), not the antitone form of Ore (1944), and it does not
require a Galois insertion (`α (γ a) = a`).

Over a *reflexive* abstract order it captures that `α x` is a most precise
abstract value soundly describing `x`: `x ⊆ γ (α x)`, and `α x ≤ a` for every `a`
with `x ⊆ γ a`; that value is unique up to `a ≤ b ∧ b ≤ a`, and unique up to `=`
only under antisymmetry.  Without reflexivity the connection can hold although
`α x` does not describe `x` soundly (`nr2_gc`, `nr2_not_extensive`). -/
def GaloisConnection (α : Pred σ → A) (γ : A → Pred σ) : Prop :=
  ∀ x a, α x ≤ a ↔ x ≤ γ a

/-- Extensivity of `γ ∘ α`: abstracting and then concretizing loses no concrete
state (`x ⊆ γ (α x)`), i.e. abstraction is sound. -/
def Extensive (α : Pred σ → A) (γ : A → Pred σ) : Prop := ∀ x, x ≤ γ (α x)

/-- Reductivity of `α ∘ γ`: re-abstracting a concretization is at least as
precise as the original abstract value (`α (γ a) ≤ a`). -/
def Reductive (α : Pred σ → A) (γ : A → Pred σ) : Prop := ∀ a, α (γ a) ≤ a

end Defs

/-! ## Main results -/

section Main
variable {σ A : Type} [LE A]

/-- **Characterization of Galois connections** (card `R1-gc-iff`).  Over a
reflexive and transitive abstract order,
`α`, `γ` form a Galois connection iff `α` and `γ` are monotone, `γ ∘ α` is
extensive and `α ∘ γ` is reductive.  Antisymmetry is not assumed. -/
theorem galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans
    (hrefl : IsRefl A) (htrans : IsTrans A) (α : Pred σ → A) (γ : A → Pred σ) :
    GaloisConnection α γ ↔
      (Monotone α ∧ Monotone γ ∧ Extensive α γ ∧ Reductive α γ) := by
  constructor
  · intro hgc
    have hext : Extensive α γ := fun x => (hgc x (α x)).mp (hrefl (α x))
    have hred : Reductive α γ := fun a => (hgc (γ a) a).mpr (Pred.le_refl (γ a))
    exact ⟨fun _ _ hxy => (hgc _ _).mpr (Pred.le_trans hxy (hext _)),
           fun _ _ hab => (hgc _ _).mp (htrans _ _ _ (hred _) hab), hext, hred⟩
  · rintro ⟨hα, hγ, hext, hred⟩ x a
    exact ⟨fun h => Pred.le_trans (hext x) (hγ _ _ h),
           fun h => htrans _ _ _ (hα _ _ h) (hred a)⟩

/-- **Laws of a Galois connection** (card `R1-gc-forward`, a reference point: the
forward direction of `R1-gc-iff`).  A Galois connection over a reflexive,
transitive abstract order has monotone `α` and `γ`, extensive `γ ∘ α`, and
reductive `α ∘ γ`. -/
theorem monotone_extensive_reductive_of_galoisConnection_of_refl_of_trans
    (hrefl : IsRefl A) (htrans : IsTrans A) {α : Pred σ → A} {γ : A → Pred σ}
    (hgc : GaloisConnection α γ) :
    Monotone α ∧ Monotone γ ∧ Extensive α γ ∧ Reductive α γ :=
  (galoisConnection_iff_monotone_extensive_reductive_of_refl_of_trans hrefl htrans α γ).mp hgc

/-- **Galois connection from the four laws** (card `R1-gc-backward`).  Over a
transitive abstract order (reflexivity not needed),
monotone `α`, monotone `γ`, extensive `γ ∘ α` and reductive `α ∘ γ` give a
Galois connection. -/
theorem galoisConnection_of_monotone_extensive_reductive_of_trans
    (htrans : IsTrans A) {α : Pred σ → A} {γ : A → Pred σ}
    (hα : Monotone α) (hγ : Monotone γ) (hext : Extensive α γ) (hred : Reductive α γ) :
    GaloisConnection α γ :=
  fun x a => ⟨fun h => Pred.le_trans (hext x) (hγ _ _ h), fun h => htrans _ _ _ (hα _ _ h) (hred a)⟩

end Main

/-! ## Fixture instances on the one-state concrete domain -/

theorem unit_le_of_not {x : Pred Unit} (hx : ¬ x ()) (y : Pred Unit) : x ≤ y :=
  fun s hs => by cases s; exact absurd hs hx

theorem not_le_E_of {x : Pred Unit} (hx : x ()) : ¬ x ≤ E := fun h => h () hx

theorem unitAlpha_E {A : Type} (lo hi : A) : unitAlpha lo hi E = lo :=
  unitAlpha_neg lo hi (fun h => h)

theorem unitAlpha_U {A : Type} (lo hi : A) : unitAlpha lo hi U = hi :=
  unitAlpha_pos lo hi trivial

/-- `B2` exact instance on `Pred Unit`: `γ lo = ∅`, `γ hi = {()}`. -/
def b2Gamma : B2 → Pred Unit
  | .lo => E
  | .hi => U

noncomputable def b2Alpha : Pred Unit → B2 := unitAlpha B2.lo B2.hi

theorem b2_gc : GaloisConnection b2Alpha b2Gamma := by
  intro x a
  by_cases hx : x ()
  · rw [show b2Alpha x = B2.hi from unitAlpha_pos _ _ hx]
    cases a
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_le_E_of hx)⟩
    · exact ⟨fun _ => le_U x, fun _ => by decide⟩
  · rw [show b2Alpha x = B2.lo from unitAlpha_neg _ _ hx]
    exact ⟨fun _ => unit_le_of_not hx _, fun _ => by cases a <;> decide⟩

theorem b2Gamma_monotone : Monotone b2Gamma := by
  intro a b hab
  cases a <;> cases b
  · exact Pred.le_refl _
  · exact E_le _
  · exact absurd hab (by decide)
  · exact Pred.le_refl _

/-- `B2` with the order-reversing concretization `γ lo = {()}`, `γ hi = ∅`. -/
def b2GammaRev : B2 → Pred Unit
  | .lo => U
  | .hi => E

theorem b2GammaRev_not_monotone : ¬ Monotone b2GammaRev :=
  fun h => not_U_le_E (h B2.lo B2.hi (by decide))

/-- `NR2` instance: `γ` constantly `∅`, `α ∅ = lo`, `α {()} = hi`. -/
def nr2Gamma : NR2 → Pred Unit := fun _ => E
noncomputable def nr2Alpha : Pred Unit → NR2 := unitAlpha NR2.lo NR2.hi

theorem nr2_gc : GaloisConnection nr2Alpha nr2Gamma := by
  intro x a
  by_cases hx : x ()
  · rw [show nr2Alpha x = NR2.hi from unitAlpha_pos _ _ hx]
    exact ⟨fun h => absurd h (by cases a <;> decide), fun h => absurd h (not_le_E_of hx)⟩
  · rw [show nr2Alpha x = NR2.lo from unitAlpha_neg _ _ hx]
    exact ⟨fun _ => unit_le_of_not hx _, fun _ => by cases a <;> decide⟩

theorem nr2_not_extensive : ¬ Extensive nr2Alpha nr2Gamma :=
  fun h => not_U_le_E (h U)

/-- `NT3` instance: `γ lo = ∅`, `γ mid = γ hi = {()}`; `α ∅ = lo`, `α {()} = mid`. -/
def nt3Gamma : NT3 → Pred Unit
  | .lo => E
  | .mid => U
  | .hi => U
noncomputable def nt3Alpha : Pred Unit → NT3 := unitAlpha NT3.lo NT3.mid

theorem nt3_laws :
    Monotone nt3Alpha ∧ Monotone nt3Gamma ∧ Extensive nt3Alpha nt3Gamma ∧
      Reductive nt3Alpha nt3Gamma := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x ()
    · rw [show nt3Alpha x = NT3.mid from unitAlpha_pos _ _ hx,
          show nt3Alpha y = NT3.mid from unitAlpha_pos _ _ (hxy () hx)]
      decide
    · rw [show nt3Alpha x = NT3.lo from unitAlpha_neg _ _ hx]
      by_cases hy : y ()
      · rw [show nt3Alpha y = NT3.mid from unitAlpha_pos _ _ hy]; decide
      · rw [show nt3Alpha y = NT3.lo from unitAlpha_neg _ _ hy]; decide
  · intro a b hab
    cases a <;> cases b <;>
      first
        | exact absurd hab (by decide)
        | exact Pred.le_refl _
        | exact E_le _
        | exact le_U _
  · intro x
    by_cases hx : x ()
    · rw [show nt3Alpha x = NT3.mid from unitAlpha_pos _ _ hx]; exact le_U x
    · exact unit_le_of_not hx _
  · intro a
    cases a
    · show nt3Alpha E ≤ NT3.lo
      rw [show nt3Alpha E = NT3.lo from unitAlpha_E _ _]; decide
    · show nt3Alpha U ≤ NT3.mid
      rw [show nt3Alpha U = NT3.mid from unitAlpha_U _ _]; decide
    · show nt3Alpha U ≤ NT3.hi
      rw [show nt3Alpha U = NT3.mid from unitAlpha_U _ _]; decide

theorem nt3_not_gc : ¬ GaloisConnection nt3Alpha nt3Gamma := by
  intro h
  have := (h E NT3.hi).mpr (le_U E)
  rw [show nt3Alpha E = NT3.lo from unitAlpha_E _ _] at this
  exact absurd this (by decide)

/-- `NT4` instance: `γ z = γ r = ∅`, `γ p = γ q = {()}`; `α ∅ = z`, `α {()} = p`. -/
def nt4Gamma : NT4 → Pred Unit
  | .z => E
  | .p => U
  | .q => U
  | .r => E
noncomputable def nt4Alpha : Pred Unit → NT4 := unitAlpha NT4.z NT4.p

theorem nt4_gc : GaloisConnection nt4Alpha nt4Gamma := by
  intro x a
  by_cases hx : x ()
  · rw [show nt4Alpha x = NT4.p from unitAlpha_pos _ _ hx]
    cases a
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_le_E_of hx)⟩
    · exact ⟨fun _ => le_U x, fun _ => by decide⟩
    · exact ⟨fun _ => le_U x, fun _ => by decide⟩
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_le_E_of hx)⟩
  · rw [show nt4Alpha x = NT4.z from unitAlpha_neg _ _ hx]
    exact ⟨fun _ => unit_le_of_not hx _, fun _ => by cases a <;> decide⟩

theorem nt4_not_monotone_gamma : ¬ Monotone nt4Gamma :=
  fun h => not_U_le_E (h NT4.q NT4.r (by decide))

/-- `NR3` instance: `γ lo = γ mid = ∅`, `γ hi = {()}`; `α ∅ = lo`, `α {()} = mid`. -/
def nr3Gamma : NR3 → Pred Unit
  | .lo => E
  | .mid => E
  | .hi => U

noncomputable def nr3Alpha : Pred Unit → NR3 := unitAlpha NR3.lo NR3.mid

theorem nr3_gc : GaloisConnection nr3Alpha nr3Gamma := by
  intro x a
  by_cases hx : x ()
  · rw [show nr3Alpha x = NR3.mid from unitAlpha_pos _ _ hx]
    cases a
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_le_E_of hx)⟩
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_le_E_of hx)⟩
    · exact ⟨fun _ => le_U x, fun _ => by decide⟩
  · rw [show nr3Alpha x = NR3.lo from unitAlpha_neg _ _ hx]
    exact ⟨fun _ => unit_le_of_not hx _, fun _ => by cases a <;> decide⟩

/-! ## Definition examples (all proved) -/

/-- Positive example: the exact two-point instance is a Galois connection. -/
theorem galoisConnection_example_pos : GaloisConnection b2Alpha b2Gamma := b2_gc

/-- Negative example: `α` constantly `lo` with `γ` constantly `∅` is not a Galois
connection (it would claim `{()} ⊆ ∅`). -/
theorem galoisConnection_example_neg :
    ¬ GaloisConnection (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) :=
  fun h => not_U_le_E ((h U B2.lo).mp (by decide))

theorem extensive_example_pos : Extensive b2Alpha b2Gamma :=
  fun x => (b2_gc x (b2Alpha x)).mp (B2.isRefl _)

theorem extensive_example_neg : ¬ Extensive (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) :=
  fun h => not_U_le_E (h U)

theorem reductive_example_pos : Reductive b2Alpha b2Gamma :=
  fun a => (b2_gc (b2Gamma a) a).mpr (Pred.le_refl _)

theorem reductive_example_neg : ¬ Reductive (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) :=
  fun h => absurd (h B2.lo) (by decide)

theorem monotone_example_pos : Monotone b2Gamma := b2Gamma_monotone

/-- Negative example: the abstraction that sends `∅` to `hi` and `{()}` to `lo`
is not monotone. -/
theorem monotone_example_neg : ¬ Monotone (unitAlpha B2.hi B2.lo) := by
  intro h
  have := h E U (le_U E)
  rw [unitAlpha_E, unitAlpha_U] at this
  exact absurd this (by decide)

theorem isRefl_example_pos : IsRefl B2 := B2.isRefl
theorem isRefl_example_neg : ¬ IsRefl NR2 := NR2.not_isRefl
theorem isTrans_example_pos : IsTrans B2 := B2.isTrans
theorem isTrans_example_neg : ¬ IsTrans NT3 := NT3.not_isTrans

/-! ## Tightness counterexamples (all proved)

Each states that a concrete instance satisfies every hypothesis of the named
result except one, and that the conclusion fails.  Where cheap, the failing
hypothesis is also shown to fail. -/

/-- `R1-gc-iff` needs reflexivity: over the transitive, non-reflexive `NR2`, the
Galois connection `nr2Alpha`, `nr2Gamma` violates extensivity, so the
equivalence fails. -/
theorem gcIff_tight_refl :
    IsTrans NR2 ∧ ¬ IsRefl NR2 ∧
      ¬ (GaloisConnection nr2Alpha nr2Gamma ↔
          (Monotone nr2Alpha ∧ Monotone nr2Gamma ∧ Extensive nr2Alpha nr2Gamma ∧
            Reductive nr2Alpha nr2Gamma)) :=
  ⟨NR2.isTrans, NR2.not_isRefl, fun h => nr2_not_extensive (h.mp nr2_gc).2.2.1⟩

/-- `R1-gc-iff` needs transitivity: over the reflexive, non-transitive `NT3`, the four
laws hold for `nt3Alpha`, `nt3Gamma` but they do not form a Galois connection. -/
theorem gcIff_tight_trans :
    IsRefl NT3 ∧ ¬ IsTrans NT3 ∧
      ¬ (GaloisConnection nt3Alpha nt3Gamma ↔
          (Monotone nt3Alpha ∧ Monotone nt3Gamma ∧ Extensive nt3Alpha nt3Gamma ∧
            Reductive nt3Alpha nt3Gamma)) :=
  ⟨NT3.isRefl, NT3.not_isTrans, fun h => nt3_not_gc (h.mpr nt3_laws)⟩

/-- `R1-gc-forward` needs reflexivity (same instance as `gcIff_tight_refl`). -/
theorem gcForward_tight_refl :
    IsTrans NR2 ∧ ¬ IsRefl NR2 ∧ GaloisConnection nr2Alpha nr2Gamma ∧
      ¬ (Monotone nr2Alpha ∧ Monotone nr2Gamma ∧ Extensive nr2Alpha nr2Gamma ∧
          Reductive nr2Alpha nr2Gamma) :=
  ⟨NR2.isTrans, NR2.not_isRefl, nr2_gc, fun h => nr2_not_extensive h.2.2.1⟩

/-- `R1-gc-forward` needs transitivity: over the reflexive, non-transitive `NT4`,
`nt4Alpha`, `nt4Gamma` form a Galois connection but `nt4Gamma` is not monotone. -/
theorem gcForward_tight_trans :
    IsRefl NT4 ∧ ¬ IsTrans NT4 ∧ GaloisConnection nt4Alpha nt4Gamma ∧
      ¬ (Monotone nt4Alpha ∧ Monotone nt4Gamma ∧ Extensive nt4Alpha nt4Gamma ∧
          Reductive nt4Alpha nt4Gamma) :=
  ⟨NT4.isRefl, NT4.not_isTrans, nt4_gc, fun h => nt4_not_monotone_gamma h.2.1⟩

/-- `R1-gc-forward` needs the Galois connection itself: over the reflexive,
transitive `B2`, constant `α = lo`, constant `γ = ∅` violate extensivity. -/
theorem gcForward_tight_gc :
    IsRefl B2 ∧ IsTrans B2 ∧
      ¬ GaloisConnection (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) ∧
      ¬ (Monotone (fun _ : Pred Unit => B2.lo) ∧ Monotone (fun _ : B2 => E) ∧
          Extensive (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) ∧
          Reductive (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E)) :=
  ⟨B2.isRefl, B2.isTrans, galoisConnection_example_neg,
    fun h => extensive_example_neg h.2.2.1⟩

/-- `R1-gc-backward` needs transitivity (same instance as `gcIff_tight_trans`). -/
theorem gcBackward_tight_trans :
    Monotone nt3Alpha ∧ Monotone nt3Gamma ∧ Extensive nt3Alpha nt3Gamma ∧
      Reductive nt3Alpha nt3Gamma ∧ ¬ IsTrans NT3 ∧ ¬ GaloisConnection nt3Alpha nt3Gamma :=
  ⟨nt3_laws.1, nt3_laws.2.1, nt3_laws.2.2.1, nt3_laws.2.2.2, NT3.not_isTrans, nt3_not_gc⟩

/-- `R1-gc-backward` needs monotone `α`: on `B2`, `γ` constantly `{()}` with
`α ∅ = hi`, `α {()} = lo`. -/
theorem gcBackward_tight_monoAlpha :
    IsTrans B2 ∧ Monotone (fun _ : B2 => U) ∧
      Extensive (unitAlpha B2.hi B2.lo) (fun _ : B2 => U) ∧
      Reductive (unitAlpha B2.hi B2.lo) (fun _ : B2 => U) ∧
      ¬ Monotone (unitAlpha B2.hi B2.lo) ∧
      ¬ GaloisConnection (unitAlpha B2.hi B2.lo) (fun _ : B2 => U) := by
  refine ⟨B2.isTrans, fun _ _ _ => Pred.le_refl _, fun x => le_U x, ?_, monotone_example_neg, ?_⟩
  · intro a
    show unitAlpha B2.hi B2.lo U ≤ a
    rw [unitAlpha_U]; cases a <;> decide
  · intro h
    have := (h E B2.lo).mpr (le_U E)
    rw [unitAlpha_E] at this
    exact absurd this (by decide)

/-- `R1-gc-backward` needs monotone `γ`: on `B2`, `γ = b2GammaRev` (`γ lo = {()}`,
`γ hi = ∅`) and `α` constantly `lo`. -/
theorem gcBackward_tight_monoGamma :
    IsTrans B2 ∧ Monotone (fun _ : Pred Unit => B2.lo) ∧
      Extensive (fun _ : Pred Unit => B2.lo) b2GammaRev ∧
      Reductive (fun _ : Pred Unit => B2.lo) b2GammaRev ∧
      ¬ Monotone b2GammaRev ∧
      ¬ GaloisConnection (fun _ : Pred Unit => B2.lo) b2GammaRev :=
  ⟨B2.isTrans, fun _ _ _ => B2.isRefl _, fun x => le_U x, fun a => by cases a <;> decide,
    b2GammaRev_not_monotone, fun h => not_U_le_E ((h U B2.hi).mp (by decide))⟩

/-- `R1-gc-backward` needs extensivity: on `B2`, constant `α = lo`, constant `γ = ∅`. -/
theorem gcBackward_tight_extensive :
    IsTrans B2 ∧ Monotone (fun _ : Pred Unit => B2.lo) ∧ Monotone (fun _ : B2 => E) ∧
      Reductive (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) ∧
      ¬ Extensive (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) ∧
      ¬ GaloisConnection (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) :=
  ⟨B2.isTrans, fun _ _ _ => B2.isRefl _, fun _ _ _ => Pred.le_refl _,
    fun a => by cases a <;> decide, extensive_example_neg, galoisConnection_example_neg⟩

/-- `R1-gc-backward` needs reductivity: on `B2`, constant `α = hi`, constant `γ = {()}`. -/
theorem gcBackward_tight_reductive :
    IsTrans B2 ∧ Monotone (fun _ : Pred Unit => B2.hi) ∧ Monotone (fun _ : B2 => U) ∧
      Extensive (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) ∧
      ¬ Reductive (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) ∧
      ¬ GaloisConnection (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) :=
  ⟨B2.isTrans, fun _ _ _ => B2.isRefl _, fun _ _ _ => Pred.le_refl _,
    fun x => le_U x, reductive_example_neg,
    fun h => absurd ((h E B2.lo).mpr (le_U E)) (by decide)⟩

end Toy.AbsInt
