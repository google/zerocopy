/-
Toy.FloatTier.Examples
======================

Fully proved positive and negative examples for the definitions of the NaN-set
semantics.
-/
import Toy.FloatTier.Counterexamples

namespace Toy.FloatTier

variable {f : Fmt}

/-! ### `V`, `payload`, `bits` -/

/-- A signaling NaN in `F23` carries payload `1`, never `0`. -/
theorem ex_snan_payload_F23 : (V.snan false ⟨0, by decide⟩ : V F23).payload = 1 := by decide

/-- In formats with precision 2 there are no signaling NaNs (`payCount = 1`, so the
index type `Fin (payCount - 1)` is empty). -/
theorem ex_no_snan_p2 (k : Fin (F32.payCount - 1)) : False := by
  have h : F32.payCount - 1 = 0 := by decide
  exact absurd k.isLt (by omega)

/-- `bits` of the positive preferred quiet NaN: `0x7FC00000` in binary32. -/
theorem ex_bits_prefNaN_binary32 : (V.prefNaN Fbin32 false).bits = 0x7FC00000 := by decide

/-- `bits` distinguishes the sign of a NaN and the quiet bit (binary32:
`0xFFC00000` and the signaling NaN `0x7F800001`). -/
theorem ex_bits_nan_variants_binary32 :
    (V.prefNaN Fbin32 true).bits = 0xFFC00000 ∧
    (V.snan false ⟨0, by decide⟩ : V Fbin32).bits = 0x7F800001 := by decide

/-! ### `NaNChoice` -/

/-- Positive: the preferred NaN with either sign is allowed for any operands. -/
theorem nanChoice_prefNaN (X : Extra f) (x y : V f) (s : Bool) :
    NaNChoice X x y (V.prefNaN f s) := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Positive: unchanged propagation of a signaling NaN operand (with flipped
sign) and quieting propagation of it are both allowed. -/
theorem ex_nanChoice_propagation_F23 :
    NaNChoice noExtra (V.snan false ⟨0, by decide⟩ : V F23) (V.one F23)
      (V.snan true ⟨0, by decide⟩) ∧
    NaNChoice noExtra (V.snan false ⟨0, by decide⟩ : V F23) (V.one F23)
      (V.qnan false ⟨1, by decide⟩) := by decide

/-- Negative: without NaN operands, a signaling NaN, a quiet NaN with nonzero
payload (when there are no extra payloads), and a non-NaN value are all
rejected. -/
theorem ex_nanChoice_rejects_F23 :
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.snan false ⟨0, by decide⟩) ∧
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.qnan false ⟨1, by decide⟩) ∧
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.zero F23 false) := by decide

/-- Positive: an extra payload allowed by `X` may be chosen. -/
theorem ex_nanChoice_extra_F23 :
    NaNChoice (fun _ _ k => k == 1) (V.zero F23 false) (V.inf false) (V.qnan true ⟨1, by decide⟩) := by
  decide

/-! ### `primSet` -/

/-- Positive: `min(+0, -0)` may return either zero; `0 * ∞` may return the
negative preferred NaN. -/
theorem ex_primSet_allows_F23 :
    primSet noExtra .min (V.zero F23 false) (V.zero F23 true) (V.zero F23 true) ∧
    primSet noExtra .min (V.zero F23 false) (V.zero F23 true) (V.zero F23 false) ∧
    primSet noExtra .mul (V.zero F23 false) (V.inf false) (V.prefNaN F23 true) := by decide

/-- Negative: `min(1, NaN)` must return `1` (not a NaN); `+∞ + -∞` must return a
NaN (not `+∞`); `1 * 1` must return `1` (not `-1`). -/
theorem ex_primSet_rejects_F23 :
    ¬ primSet noExtra .min (V.one F23) (V.prefNaN F23 false) (V.prefNaN F23 false) ∧
    ¬ primSet noExtra .add (V.inf false : V F23) (V.inf true) (V.inf false) ∧
    ¬ primSet noExtra .mul (V.one F23) (V.one F23) ((V.one F23).neg) := by decide

/-! ### `TierSound` -/

/-- Positive: the example tiers are sound in `F23` (also an instance of
`tierOf_sound`). Negative: `tierBad` is not. -/
theorem ex_tierSound_F23 :
    TierSound (noExtra (f := F23)) tierCtfe ∧ TierSound (noExtra (f := F23)) tierRunA ∧
    ¬ TierSound (noExtra (f := F23)) tierBad :=
  ⟨tierOf_sound _ _, tierOf_sound _ _, refinesS_iff_tierSound_nonvacuous.2.2⟩

/-! ### `ValEq` -/

/-- Positive: `+0 ≈ -0`, and a positive quiet NaN `≈` a negative signaling NaN.
Negative: `+∞ ≉ -∞`, `+0 ≉ 1.0`, and a NaN `≉` `+∞`. -/
theorem ex_valEq_F23 :
    ValEq (V.zero F23 false) (V.zero F23 true) ∧
    ValEq (V.prefNaN F23 false) (V.snan true ⟨0, by decide⟩) ∧
    ¬ ValEq (V.inf false : V F23) (V.inf true) ∧
    ¬ ValEq (V.zero F23 false) (V.one F23) ∧
    ¬ ValEq (V.prefNaN F23 false) (V.inf false) := by decide

/-! ### `BitSafe`, `MinMaxFree`, `fold` -/

/-- Negative example for `BitSafe`: `toBits (0.0 * +∞)` applies a bit-level
observation to a NaN. -/
theorem ex_bitSafe_rejects (X : Extra f) (ρ : Nat → V f) :
    ¬ (progBitsZeroMulInf f).BitSafe X ρ V.isNaN := by
  rintro ⟨_, h⟩
  have := h (V.prefNaN f false) ((evalS_mulZeroInf X ρ _).2 (nanChoice_prefNaN X _ _ false))
  exact absurd this (by simp [V.prefNaN, V.isNaN])

/-- `MinMaxFree` (positive and negative). -/
theorem ex_minMaxFree :
    (progCopysignNaN f).MinMaxFree = true ∧ (progMinZeroEq f).MinMaxFree = false := ⟨rfl, rfl⟩

/-- `fold` keeps a variable and folds a closed subexpression next to it. -/
theorem ex_fold_keeps_var :
    (FExpr.prim .add (.var 0) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))).fold
        tierCtfe =
      .prim .add (.var 0) (.lit (V.prefNaN f false)) := by
  simp [FExpr.fold, FExpr.closed, FExpr.evalT, tierCtfe_mul_zero_inf]

end Toy.FloatTier
