/-
Toy.Float.Table
===============

The flag table in the `(3,3)` format `F33`, fully proved: for each rewrite,
the exact family of flag sets modulo which it is valid. For a row with flag
set `S`, `∀ T, ValidMod T r ↔ S ⊆ T`: `S` suffices, and for each flag in `S`
the rewrite is invalid modulo *all other flags together*. A rewrite that is
never valid fails modulo all five flags.

Sufficiency of each row is the corresponding conjunct of the general
`flagTable_sufficient`; minimality (invalidity modulo all flags except one)
is checked by kernel evaluation over the inputs of `F33`, or by one witness
per flag for the three-variable rows.
-/
import Toy.Float.Counterexamples
import Toy.Float.Statements

namespace Toy.Float

variable {f : Fmt} {n : Nat}

theorem flags_sub_all (T : Flags) : Flags.Sub T Flags.all :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ### Per-flag witnesses for the three-variable rows -/

theorem rwMulAssoc_not_validMod_allBut_reassoc_F33 :
    ¬ ValidMod (Flags.allBut .reassoc) (rwMulAssoc F33) := by
  intro h
  have := h (env3 (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 7 (-2))) (by decide +kernel)
  revert this; decide +kernel

theorem rwContract_not_validMod_allBut_contract_F33 :
    ¬ ValidMod (Flags.allBut .contract) (rwContract F33) := by
  intro h
  have := h (env3 (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) (by decide +kernel)
  revert this; decide +kernel

theorem rwUncontract_not_validMod_all_F33 : ¬ ValidMod Flags.all (rwUncontract F33) := by
  intro h
  have := h (env3 (dy F33 5 (-4)) (dy F33 7 (-3)) (dy F33 2 0)) (by decide +kernel)
  revert this; decide +kernel

/-! ### Rows -/

theorem rwAddNegZero_validMod_iff_F33 (T : Flags) : ValidMod T (rwAddNegZero F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwAddPosZero_validMod_iff_F33 (T : Flags) : ValidMod T (rwAddPosZero F33) ↔ Flags.Sub fNsz T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.1
    (by intro fl h; cases fl <;> simp [Flags.has, fNsz] at h ⊢ <;> decide +kernel) T

theorem rwMulOne_validMod_iff_F33 (T : Flags) : ValidMod T (rwMulOne F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwMulNegOne_validMod_iff_F33 (T : Flags) : ValidMod T (rwMulNegOne F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwMulTwo_validMod_iff_F33 (T : Flags) : ValidMod T (rwMulTwo F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwSubSelf_validMod_iff_F33 (T : Flags) : ValidMod T (rwSubSelf F33) ↔ Flags.Sub fNnan T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has, fNnan] at h ⊢ <;> decide +kernel) T

theorem rwMulPosZero_validMod_iff_F33 (T : Flags) :
    ValidMod T (rwMulPosZero F33) ↔ Flags.Sub fNnanNsz T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has, fNnanNsz] at h ⊢ <;> decide +kernel) T

theorem rwPosZeroSub_validMod_iff_F33 (T : Flags) : ValidMod T (rwPosZeroSub F33) ↔ Flags.Sub fNsz T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has, fNsz] at h ⊢ <;> decide +kernel) T

theorem rwNegZeroSub_validMod_iff_F33 (T : Flags) : ValidMod T (rwNegZeroSub F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwNegSub_validMod_iff_F33 (T : Flags) : ValidMod T (rwNegSub F33) ↔ Flags.Sub fNsz T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has, fNsz] at h ⊢ <;> decide +kernel) T

theorem rwAddComm_validMod_iff_F33 (T : Flags) : ValidMod T (rwAddComm F33) ↔ Flags.Sub {} T :=
  validMod_iff_sub_of_minimal (flagTable_sufficient F33).2.2.2.2.2.2.2.2.2.2.1
    (by intro fl h; cases fl <;> simp [Flags.has] at h) T

theorem rwAddAssoc_validMod_iff_F33 (T : Flags) : ValidMod T (rwAddAssoc F33) ↔ Flags.Sub fReassoc T :=
  validMod_iff_sub_of_minimal (rwAddAssoc_validMod_reassoc F33)
    (by
      intro fl h
      cases fl <;> simp [Flags.has, fReassoc] at h
      exact add_assoc_not_validMod_allBut_reassoc_F33.2.2.2.2) T

theorem rwMulAssoc_validMod_iff_F33 (T : Flags) : ValidMod T (rwMulAssoc F33) ↔ Flags.Sub fReassoc T :=
  validMod_iff_sub_of_minimal (rwMulAssoc_validMod_reassoc F33)
    (by
      intro fl h
      cases fl <;> simp [Flags.has, fReassoc] at h
      exact rwMulAssoc_not_validMod_allBut_reassoc_F33) T

theorem rwContract_validMod_iff_F33 (T : Flags) :
    ValidMod T (rwContract F33) ↔ Flags.Sub fContract T :=
  validMod_iff_sub_of_minimal (rwContract_validMod_contract F33)
    (by
      intro fl h
      cases fl <;> simp [Flags.has, fContract] at h
      exact rwContract_not_validMod_allBut_contract_F33) T

theorem rwUncontract_never_validMod_F33 (T : Flags) : ¬ ValidMod T (rwUncontract F33) :=
  fun h => rwUncontract_not_validMod_all_F33 (validMod_mono (flags_sub_all T) h)

/-- The flag table in `F33` [bounded: F33]. For every flag set `T`:
`x + (-0) → x`, `x * 1 → x`, `x * (-1) → -x`, `x * 2 → x + x`,
`(-0) - x → -x`, `x + y → y + x` are valid modulo every `T`;
`x + (+0) → x`, `(+0) - x → -x`, `-(x - y) → y - x` are valid modulo `T` iff
`nsz ∈ T`; `x - x → +0` iff `nnan ∈ T`; `x * (+0) → +0` iff
`nnan, nsz ∈ T`; `(x + y) + z → x + (y + z)` and `(x * y) * z → x * (y * z)`
iff `reassoc ∈ T`; `x * y + z → fma x y z` iff `contract ∈ T`; and
`fma x y z → x * y + z` is valid modulo no `T`. -/
theorem flagTable_exact_F33 :
    (∀ T, ValidMod T (rwAddNegZero F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwAddPosZero F33) ↔ Flags.Sub fNsz T) ∧
    (∀ T, ValidMod T (rwMulOne F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwMulNegOne F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwMulTwo F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwSubSelf F33) ↔ Flags.Sub fNnan T) ∧
    (∀ T, ValidMod T (rwMulPosZero F33) ↔ Flags.Sub fNnanNsz T) ∧
    (∀ T, ValidMod T (rwPosZeroSub F33) ↔ Flags.Sub fNsz T) ∧
    (∀ T, ValidMod T (rwNegZeroSub F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwNegSub F33) ↔ Flags.Sub fNsz T) ∧
    (∀ T, ValidMod T (rwAddComm F33) ↔ Flags.Sub {} T) ∧
    (∀ T, ValidMod T (rwAddAssoc F33) ↔ Flags.Sub fReassoc T) ∧
    (∀ T, ValidMod T (rwMulAssoc F33) ↔ Flags.Sub fReassoc T) ∧
    (∀ T, ValidMod T (rwContract F33) ↔ Flags.Sub fContract T) ∧
    (∀ T, ¬ ValidMod T (rwUncontract F33)) :=
  ⟨rwAddNegZero_validMod_iff_F33, rwAddPosZero_validMod_iff_F33, rwMulOne_validMod_iff_F33,
    rwMulNegOne_validMod_iff_F33, rwMulTwo_validMod_iff_F33, rwSubSelf_validMod_iff_F33,
    rwMulPosZero_validMod_iff_F33, rwPosZeroSub_validMod_iff_F33, rwNegZeroSub_validMod_iff_F33,
    rwNegSub_validMod_iff_F33, rwAddComm_validMod_iff_F33, rwAddAssoc_validMod_iff_F33,
    rwMulAssoc_validMod_iff_F33, rwContract_validMod_iff_F33, rwUncontract_never_validMod_F33⟩

/-- Non-vacuity for the table: for each row, an input admissible for its
source expression under all five flags (so every validity claim constrains
some input), at `x = 1`, `y = 2`, `z = 1/4`. -/
theorem flagTable_nonvacuous_F33 :
    Admissible Flags.all (rwAddNegZero F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwAddPosZero F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwMulOne F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwMulNegOne F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwMulTwo F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwSubSelf F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwMulPosZero F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwPosZeroSub F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwNegZeroSub F33).lhs (env1 (one F33)) ∧
    Admissible Flags.all (rwNegSub F33).lhs (env2 (one F33) (dy F33 2 0)) ∧
    Admissible Flags.all (rwAddComm F33).lhs (env2 (one F33) (dy F33 2 0)) ∧
    Admissible Flags.all (rwAddAssoc F33).lhs (env3 (one F33) (dy F33 2 0) (dy F33 1 (-2))) ∧
    Admissible Flags.all (rwMulAssoc F33).lhs (env3 (one F33) (dy F33 2 0) (dy F33 1 (-2))) ∧
    Admissible Flags.all (rwContract F33).lhs (env3 (one F33) (dy F33 2 0) (dy F33 1 (-2))) ∧
    Admissible Flags.all (rwUncontract F33).lhs (env3 (one F33) (dy F33 2 0) (dy F33 1 (-2))) := by
  decide +kernel

/-- Positive control for "`fma x y z → x * y + z` is never valid": the
reverse rewrite (contraction) is valid modulo `contract`, in every format. -/
theorem rwUncontract_positive_control (f : Fmt) : ValidMod fContract (rwContract f) :=
  rwContract_validMod_contract f

end Toy.Float
