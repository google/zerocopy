import Toy.WrapNiche.Affine

/-!
# Nested `Option` by adjacent reservation

Each nesting level of `Option` over a payload whose valid field values form the wrapping
interval `I` reserves one value for its `None`. *Adjacent reservation* takes the value just
past either end of `I`: `e + 1` (`Side.high`) or `s - 1` (`Side.low`), both wrapping. The
next level's valid set is `I` together with the reserved value, which is again a wrapping
interval (`extend I side`). `nest R₀ sides` iterates this from the innermost valid interval
`R₀`, one side choice per level.
-/

namespace Toy.WrapNiche

open Imported

/-- Which end of the current valid interval a level reserves. -/
inductive Side
  /-- Reserve `s - 1` (wrapping). -/
  | low
  /-- Reserve `e + 1` (wrapping). -/
  | high
deriving DecidableEq, Repr

/-- The value adjacent to `I` on the given side: `s - 1` or `e + 1` (wrapping). -/
def adjNiche {M : Nat} (I : WrapInterval M) : Side → Fin M
  | .low => wrapSub I.s 1
  | .high => wrapAdd I.e 1

/-- The interval extended by its adjacent value on the given side. -/
def extend {M : Nat} (I : WrapInterval M) : Side → WrapInterval M
  | .low => ⟨wrapSub I.s 1, I.e⟩
  | .high => ⟨I.s, wrapAdd I.e 1⟩

/-- The valid interval after one level per entry of `sides` (innermost level first). -/
def nest {M : Nat} (I : WrapInterval M) : List Side → WrapInterval M
  | [] => I
  | d :: ds => nest (extend I d) ds

/-- At every level `j < sides.length`, the value reserved by adjacent reservation is invalid
for the valid interval of the levels below it (so, by the imported
`nicheLayout_lawful_iff_isNiche`, that level's niche-filled layout is lawful). -/
def LevelsReserveNiches {M : Nat} (R₀ : WrapInterval M) (sides : List Side) : Prop :=
  ∀ j (hj : j < sides.length),
    ¬ (nest R₀ (sides.take j)).Mem (adjNiche (nest R₀ (sides.take j)) sides[j])

instance {M : Nat} (R₀ : WrapInterval M) (sides : List Side) :
    Decidable (LevelsReserveNiches R₀ sides) := by
  unfold LevelsReserveNiches; infer_instance

end Toy.WrapNiche
