/-
Toy.AbsInt.Sign
===============

The classical sign domain for one integer variable, with its abstraction and
concretization, and a fully proved Galois connection.  Used as the intended
instance (non-vacuity witness) for most results, and for the strict
precision-loss example of composition.
-/
import Toy.AbsInt.Galois

namespace Toy.AbsInt

/-- The sign domain: `bot` (no value), `neg` (`< 0`), `zero` (`= 0`),
`pos` (`> 0`), `top` (any value). -/
inductive Sign | bot | neg | zero | pos | top
  deriving DecidableEq, Repr

def Sign.leb : Sign → Sign → Bool
  | .bot, _ => true
  | _, .top => true
  | .neg, .neg => true
  | .zero, .zero => true
  | .pos, .pos => true
  | _, _ => false

instance : LE Sign := ⟨fun a b => Sign.leb a b = true⟩
instance (a b : Sign) : Decidable (a ≤ b) := inferInstanceAs (Decidable (Sign.leb a b = true))

theorem Sign.isRefl : IsRefl Sign := by intro a; cases a <;> decide
theorem Sign.isTrans : IsTrans Sign := by
  intro a b c; cases a <;> cases b <;> cases c <;> decide
theorem Sign.isAntisymm : IsAntisymm Sign := by
  intro a b; cases a <;> cases b <;> decide

def Sign.rank : Sign → Nat
  | .bot => 0
  | .top => 2
  | _ => 1

theorem Sign.rank_strict : ∀ a b : Sign, StrictLt a b → Sign.rank a < Sign.rank b := by
  intro a b; cases a <;> cases b <;> decide

theorem Sign.heightLE : HeightLE Sign 2 :=
  heightLE_of_rank Sign.rank 2 Sign.rank_strict (by intro a; cases a <;> decide)

theorem Sign.acc : ACC Sign :=
  acc_of_rank Sign.rank 2 Sign.rank_strict (by intro a; cases a <;> decide)

/-- Concretization of the sign domain. -/
def signGamma : Sign → Pred Int
  | .bot => fun _ => False
  | .neg => fun n => n < 0
  | .zero => fun n => n = 0
  | .pos => fun n => 0 < n
  | .top => fun _ => True

/-- Positive example for `Pred` (and `signGamma`): `1` satisfies `signGamma pos`. -/
theorem pred_example_pos : signGamma .pos 1 := by show (0:Int) < 1; omega

/-- Negative example for `Pred` (and `signGamma`): `0` does not satisfy `signGamma pos`. -/
theorem pred_example_neg : ¬ signGamma .pos 0 := by show ¬ (0:Int) < 0; omega

/-- Abstraction of the sign domain: the first of `bot, neg, zero, pos` whose
concretization contains the set, and `top` otherwise. -/
noncomputable def signAlpha (x : Pred Int) : Sign :=
  open Classical in
  if x ≤ signGamma .bot then .bot
  else if x ≤ signGamma .neg then .neg
  else if x ≤ signGamma .zero then .zero
  else if x ≤ signGamma .pos then .pos
  else .top

theorem signGamma_monotone : Monotone signGamma := by
  intro a b hab n hn
  cases a <;> cases b <;> simp_all [signGamma] <;> first | exact absurd hab (by decide) | omega

/-- The sign domain forms a Galois connection with `Pred Int` (proved). -/
theorem signGC : GaloisConnection signAlpha signGamma := by
  intro x a
  have bot_le : ∀ c, x ≤ signGamma .bot → x ≤ signGamma c :=
    fun c h s hs => (h s hs).elim
  have nz : x ≤ signGamma .neg → x ≤ signGamma .zero → x ≤ signGamma .bot := by
    intro h1 h2 s hs
    have e1 : s < 0 := h1 s hs
    have e2 : s = 0 := h2 s hs
    omega
  have np : x ≤ signGamma .neg → x ≤ signGamma .pos → x ≤ signGamma .bot := by
    intro h1 h2 s hs
    have e1 : s < 0 := h1 s hs
    have e2 : 0 < s := h2 s hs
    omega
  have zp : x ≤ signGamma .zero → x ≤ signGamma .pos → x ≤ signGamma .bot := by
    intro h1 h2 s hs
    have e1 : s = 0 := h1 s hs
    have e2 : 0 < s := h2 s hs
    omega
  have top_ : x ≤ signGamma .top := fun _ _ => trivial
  unfold signAlpha
  by_cases h0 : x ≤ signGamma .bot
  · simp only [h0, ite_true]
    exact ⟨fun _ => bot_le a h0, fun _ => by cases a <;> decide⟩
  · by_cases h1 : x ≤ signGamma .neg
    · simp only [h0, h1, ite_true, ite_false]
      cases a
      · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
      · exact ⟨fun _ => h1, fun _ => by decide⟩
      · exact ⟨fun h => absurd h (by decide), fun h => absurd (nz h1 h) h0⟩
      · exact ⟨fun h => absurd h (by decide), fun h => absurd (np h1 h) h0⟩
      · exact ⟨fun _ => top_, fun _ => by decide⟩
    · by_cases h2 : x ≤ signGamma .zero
      · simp only [h0, h1, h2, ite_true, ite_false]
        cases a
        · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
        · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
        · exact ⟨fun _ => h2, fun _ => by decide⟩
        · exact ⟨fun h => absurd h (by decide), fun h => absurd (zp h2 h) h0⟩
        · exact ⟨fun _ => top_, fun _ => by decide⟩
      · by_cases h3 : x ≤ signGamma .pos
        · simp only [h0, h1, h2, h3, ite_true, ite_false]
          cases a
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩
          · exact ⟨fun _ => h3, fun _ => by decide⟩
          · exact ⟨fun _ => top_, fun _ => by decide⟩
        · simp only [h0, h1, h2, h3, ite_false]
          cases a
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩
          · exact ⟨fun h => absurd h (by decide), fun h => absurd h h3⟩
          · exact ⟨fun _ => top_, fun _ => by decide⟩

/-- Evaluation helpers for `signAlpha` (proved). -/
theorem signAlpha_eq_pos {x : Pred Int} (hne : ∃ s, x s) (hpos : ∀ s, x s → 0 < s) :
    signAlpha x = .pos := by
  obtain ⟨s₀, hs₀⟩ := hne
  have p0 := hpos s₀ hs₀
  have h0 : ¬ x ≤ signGamma .bot := fun h => h s₀ hs₀
  have h1 : ¬ x ≤ signGamma .neg := fun h => by have : s₀ < 0 := h s₀ hs₀; omega
  have h2 : ¬ x ≤ signGamma .zero := fun h => by have : s₀ = 0 := h s₀ hs₀; omega
  have h3 : x ≤ signGamma .pos := hpos
  unfold signAlpha
  simp only [h0, h1, h2, h3, ite_true, ite_false]

theorem signAlpha_eq_top {x : Pred Int} (hz : x 0) (hp : ∃ s, x s ∧ 0 < s) :
    signAlpha x = .top := by
  obtain ⟨s₁, hs₁, p1⟩ := hp
  have h0 : ¬ x ≤ signGamma .bot := fun h => h 0 hz
  have h1 : ¬ x ≤ signGamma .neg := fun h => by have : (0:Int) < 0 := h 0 hz; omega
  have h2 : ¬ x ≤ signGamma .zero := fun h => by have : s₁ = 0 := h s₁ hs₁; omega
  have h3 : ¬ x ≤ signGamma .pos := fun h => by have : (0:Int) < 0 := h 0 hz; omega
  unfold signAlpha
  simp only [h0, h1, h2, h3, ite_false]

end Toy.AbsInt
