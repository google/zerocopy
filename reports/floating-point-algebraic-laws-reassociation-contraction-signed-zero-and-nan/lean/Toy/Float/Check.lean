/-
Toy.Float.Check
===============

Flat Boolean checkers over the values of a format, with correctness lemmas.
A bounded claim `∀ x, P x` over a concrete small format is proved by
evaluating, in the kernel (`decide +kernel`), one Boolean check per biased
exponent `E` (`allAtExp`) plus the three special values, and combining them
with `forall_of_allAtExp`. Unlike the nested `Decidable` instances of
`Toy.Float.Enum`, these checkers build no proof terms during evaluation, and
splitting by exponent keeps each kernel evaluation small.
-/
import Toy.Float.Enum

namespace Toy.Float

variable {f : Fmt}

theorem mem_FP_list (x : FP f) : x ∈ FP.list f := by
  unfold FP.list
  cases x with
  | nan => simp
  | inf s => cases s <;> simp
  | fin s E M =>
    simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_finRange]
    refine Or.inr (Or.inr (Or.inr ⟨s, ?_, E, trivial, M, trivial, rfl⟩))
    cases s <;> simp

/-- `(FP.list f).all p` checks `p` at every value of `f`. -/
theorem all_FP_list_iff (p : FP f → Bool) : (FP.list f).all p = true ↔ ∀ x, p x = true := by
  simp only [List.all_eq_true]
  exact ⟨fun h x => h x (mem_FP_list x), fun h x _ => h x⟩

/-- `true` iff `P` holds at every finite value with biased exponent `E`. -/
def allAtExp (f : Fmt) (E : Fin f.expCount) (P : FP f → Bool) : Bool :=
  [false, true].all fun s => (List.finRange f.fracCount).all fun M => P (.fin s E M)

theorem forall_of_allAtExp (P : FP f → Bool)
    (hs : P .nan = true ∧ P (.inf false) = true ∧ P (.inf true) = true)
    (h : ∀ E : Fin f.expCount, allAtExp f E P = true) : ∀ x, P x = true := by
  intro x
  cases x with
  | nan => exact hs.1
  | inf s => cases s; exact hs.2.1; exact hs.2.2
  | fin s E M =>
    have := h E
    unfold allAtExp at this
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      List.all_eq_true, List.mem_finRange, forall_const] at this
    cases s
    · exact this.1 M
    · exact this.2 M

end Toy.Float
