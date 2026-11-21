import Toy.PlaceEval.Erasure

/-!
# Zero-size reads

Supporting lemmas for the degenerate edge `τ.size = 0` of `evalInt_copy_eq_none_iff`: a
zero-byte access is permitted through every pointer, the cells read form the empty list,
and that list decodes to the integer `0` at an integer type, while at an enum type it
decodes to `0` iff `0` is a valid tag.
-/

namespace Toy.PlaceEval

/-- At a type of size `0`, every pointer (including null and dangling pointers) is
dereferenceable for `τ.size` bytes. -/
theorem dereferenceable_of_size_eq_zero (m : Mem) (q : Ptr) (τ : Ty) (h : τ.size = 0) :
    m.dereferenceable q τ.size = true := by
  simp [Mem.dereferenceable, h]

/-- At a type of size `0`, the cells read at any address form the empty list. -/
theorem readCells_of_size_eq_zero (m : Mem) (a : Nat) (τ : Ty) (h : τ.size = 0) :
    m.readCells a τ.size = [] := by
  simp [Mem.readCells, h]

/-- At a type of size `0`, the cells read decode at `τ` to the integer `n` iff `n = 0`
and, if `τ` is an enum type, `0` is one of its valid tags. -/
theorem decode_readCells_of_size_eq_zero_iff (m : Mem) (a : Nat) (τ : Ty) (h : τ.size = 0)
    (n : Nat) :
    τ.decode (m.readCells a τ.size) = some (.int n) ↔
      n = 0 ∧ ∀ s al valid, τ = Ty.enum s al valid → 0 ∈ valid := by
  rw [readCells_of_size_eq_zero m a τ h]
  cases τ with
  | int s al =>
    rw [decode_int_eq_some_iff]
    simp [decodeLE, eq_comm]
  | ptr => simp [Ty.size, ptrSize] at h
  | enum s al valid =>
    rw [decode_enum_eq_some_iff]
    simp only [decodeLE, Option.some.injEq, Ty.enum.injEq]
    constructor
    · rintro ⟨rfl, hv⟩
      exact ⟨rfl, fun _ _ _ ⟨_, _, h3⟩ => h3 ▸ hv⟩
    · rintro ⟨rfl, hv⟩
      exact ⟨rfl, hv s al valid ⟨rfl, rfl, rfl⟩⟩

/-- A zero-size enum read through the null pointer succeeds with `0` when `0` is a valid
tag. -/
theorem load_ex_pos_zero_size_enum :
    mEx.load ⟨none, 0⟩ (.enum 0 1 [0]) = some (.int 0) := by decide

/-- A zero-size enum read through the null pointer fails when `0` is not a valid tag. -/
theorem load_ex_neg_zero_size_enum : mEx.load ⟨none, 0⟩ (.enum 0 1 [1]) = none := by decide

end Toy.PlaceEval
