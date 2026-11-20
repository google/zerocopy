import ToyFarkas.Checker
import ToyFarkas.Motzkin

/-!
# Farkas completeness over the rationals and its failure over the integers

`farkas_complete_scaled` is the converse of `checkFarkas_sound_scaled`: every system with no
rational solution has a certificate that `checkFarkas` accepts. For systems mixing strict and
non-strict constraints this is Motzkin's transposition theorem, with rational multipliers
cleared to integers by a common denominator. It is proved by integer-scaled Fourier–Motzkin
elimination in `ToyFarkas.Motzkin` (`Toy.Farkas.Motzkin.complete`).

Over the integers the converse is false: `ce_farkas_incomplete_int` gives an integer-infeasible
system for which `checkFarkas` rejects every certificate (proved, from rational soundness).
-/

namespace Toy.Farkas

/-- **Farkas completeness for scaled points.** If no scaled point `(d, p)` with `d > 0`
satisfies `S`, then some certificate is accepted by `checkFarkas`. (Read through the
modeling bridge described in `ToyFarkas.Constraint`, this is completeness for rationally
infeasible finite systems.) The proof homogenizes `S` with a denominator coordinate and runs
Fourier–Motzkin elimination with positive integer pivot weights (`ToyFarkas.Motzkin`). -/
theorem farkas_complete_scaled (S : List Constraint)
    (h : ∀ (d : Int) (p : Nat → Int), 0 < d → ¬ SatScaled S d p) :
    ∃ cert : List Int, checkFarkas S cert = true :=
  Motzkin.complete S h

/-- Non-vacuity of `farkas_complete_scaled`: `sysLeGe` and `sysStrict` have no scaled solution
with `d > 0` (proved from soundness), so they satisfy the hypothesis; certificates exist for both. -/
theorem nv_farkas_complete_scaled :
    (∀ (d : Int) (p : Nat → Int), 0 < d → ¬ SatScaled sysLeGe d p) ∧
    (∀ (d : Int) (p : Nat → Int), 0 < d → ¬ SatScaled sysStrict d p) ∧
    checkFarkas sysLeGe [1, 1] = true ∧ checkFarkas sysStrict [1, 1] = true :=
  ⟨fun d p hd => checkFarkas_sound_scaled _ [1, 1] (by decide) d hd p,
   fun d p hd => checkFarkas_sound_scaled _ [1, 1] (by decide) d hd p,
   by decide, by decide⟩

/-- `{2x₀ ≤ 1, -2x₀ ≤ -1}`, i.e. `x₀ = 1/2`: rationally feasible, integer infeasible. -/
def sysHalf : List Constraint := [⟨[(0, 2)], .le, 1⟩, ⟨[(0, -2)], .le, -1⟩]

/-- **Farkas certificates are incomplete for integer infeasibility.** `{2x₀ ≤ 1, -2x₀ ≤ -1}`
has no integer solution, yet `checkFarkas` rejects every certificate (because the rational
point `x₀ = 1/2` satisfies the system). The positive control (a nearby setting where the
conclusion fails) is `nv_checkCutCert_sound_int`: adding Chvátal–Gomory cuts yields an accepted
certificate for the same system; `sysHalf_refuted_by_case_split` gives a second one. -/
theorem ce_farkas_incomplete_int :
    (∀ x : Nat → Int, ¬ SatInt sysHalf x) ∧ (∀ cert : List Int, checkFarkas sysHalf cert = false) := by
  constructor
  · intro x hx
    have h1 := hx _ (List.mem_cons_self ..)
    have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp [Constraint.HoldsInt, Rel.Sat, SparseVec.eval] at h1 h2
    omega
  · intro cert
    cases hc : checkFarkas sysHalf cert with
    | false => rfl
    | true => exact absurd (by decide : SatScaled sysHalf 2 (pt1 1))
                (checkFarkas_sound_scaled sysHalf cert hc 2 (by decide) (pt1 1))

/-- **The infeasibility hypothesis of `farkas_complete_scaled` is necessary** (canonical form:
the hypothesis fails, witnessed by the scaled point `(1, pt1 1)` with `1 > 0`, and the conclusion
fails). The satisfiable `sysEq` (`x₀ = 1`) has no accepted certificate (by soundness). -/
theorem ce_farkas_complete_feasible_system :
    (0 : Int) < 1 ∧ SatScaled sysEq 1 (pt1 1) ∧ ¬ ∃ cert : List Int, checkFarkas sysEq cert = true := by
  refine ⟨by decide, by decide, fun ⟨cert, hc⟩ => ?_⟩
  exact checkFarkas_sound_scaled sysEq cert hc 1 (by decide) (pt1 1) (by decide)

/-- **Escape hatch (case split).** Over the integers `x₀ ≤ 0 ∨ x₀ ≥ 1`; each branch of `sysHalf`
extended by one side of the split has an accepted Farkas certificate. So a checker that also
admits integer case splits refutes `sysHalf` without cutting planes. -/
theorem sysHalf_refuted_by_case_split :
    (∀ v : Int, v ≤ 0 ∨ -v ≤ -1) ∧
    checkFarkas (sysHalf ++ [⟨[(0, 1)], .le, 0⟩]) [0, 1, 2] = true ∧
    checkFarkas (sysHalf ++ [⟨[(0, -1)], .le, -1⟩]) [1, 0, 2] = true := by
  refine ⟨fun v => by omega, by decide, by decide⟩

end Toy.Farkas
