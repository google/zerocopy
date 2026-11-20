import Toy.MachInt.Defs

/-!
# Positive and negative examples for every core definition, plus helper derivations

Every definition in `Toy.MachInt.Defs` has at least one fully proved positive example
(`ex_*_pos`) and at least one fully proved negative example (`ex_*_neg`). We also prove
small structural derivations used to minimize hypotheses in `Statements.lean`.
-/

namespace Toy.MachInt

/-! ## Examples for width, shift, and range predicates -/

theorem ex_posWidth_pos : PosWidth 8 := by decide
theorem ex_posWidth_neg : ¬ PosWidth 0 := by decide

theorem ex_widthLe_pos : WidthLe 8 32 := by decide
theorem ex_widthLe_neg : ¬ WidthLe 32 8 := by decide

theorem ex_shiftInBounds_pos : ShiftInBounds 8 7 := by decide
theorem ex_shiftInBounds_neg : ¬ ShiftInBounds 8 8 := by decide

theorem ex_sMinVal_pos : sMinVal 8 = -128 := by decide
theorem ex_sMinVal_neg : sMinVal 0 ≠ -1 := by decide

theorem ex_sMaxVal_pos : sMaxVal 8 = 127 := by decide
theorem ex_sMaxVal_neg : sMaxVal 8 ≠ 128 := by decide

theorem ex_inUnsignedRange_pos : InUnsignedRange 8 255 := by decide
theorem ex_inUnsignedRange_neg : ¬ InUnsignedRange 8 256 := by decide

theorem ex_inSignedRange_pos : InSignedRange 8 (-128) := by decide
theorem ex_inSignedRange_neg : ¬ InSignedRange 8 128 := by decide
theorem ex_inSignedRange_zero_width_neg : ¬ InSignedRange 0 (-1) := by decide

/-! ## Helper derivations for ranges and non-zero divisors -/

/-- Any non-zero `BitVec n` witnesses that `n > 0` (`PosWidth n`), since `BitVec 0` is a
    subsingleton whose sole value is `0#0`. -/
theorem posWidth_of_nonZeroDiv {n : Nat} {b : BitVec n} (hb : NonZeroDiv b) : PosWidth n := by
  by_cases h : n = 0
  · subst h
    exfalso
    exact hb (BitVec.eq_nil b)
  · exact Nat.pos_of_ne_zero h

/-- For positive bitwidths (`PosWidth n`), `InSignedRange n z` coincides with the standard
    two's-complement bounds `-(2^(n-1)) ≤ z < 2^(n-1)`. -/
theorem inSignedRange_iff_two_pow_of_posWidth {n : Nat} (hn : PosWidth n) (z : Int) :
    InSignedRange n z ↔
      (-((2 ^ (n - 1) : Nat) : Int) ≤ z ∧ z < ((2 ^ (n - 1) : Nat) : Int)) := by
  have hmin : sMinVal n = -((2 ^ (n - 1) : Nat) : Int) := by
    unfold sMinVal
    rw [BitVec.toInt_intMin_of_pos hn]
    norm_cast
  have hmax : sMaxVal n = ((2 ^ (n - 1) : Nat) : Int) - 1 := by
    unfold sMaxVal
    rw [BitVec.toInt_intMax]
    norm_cast
  unfold InSignedRange
  rw [hmin, hmax]
  omega

/-- If `a < b` (unsigned), then `a + 1` never overflows unsigned arithmetic. -/
theorem noUAddOverflow_one_of_ult {n : Nat} {a b : BitVec n} (h : Ult a b) :
    NoUAddOverflow a 1#n := by
  unfold NoUAddOverflow BitVec.uaddOverflow
  unfold Ult BitVec.ult at h
  simp only [decide_eq_true_eq] at h
  have hn : 0 < n := by
    by_cases h0 : n = 0
    · subst h0
      have ha : a = 0#0 := BitVec.eq_nil a
      have hb : b = 0#0 := BitVec.eq_nil b
      subst ha hb
      simp at h
    · exact Nat.pos_of_ne_zero h0
  have hb : b.toNat < 2 ^ n := b.isLt
  have h1 : (1#n).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hn)
  simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le]
  omega

/-- If `a < b` (unsigned) and `b + c` does not overflow unsigned arithmetic, then `a + c`
    does not overflow unsigned arithmetic either. -/
theorem noUAddOverflow_of_ult_of_noUAddOverflow {n : Nat} {a b c : BitVec n}
    (hlt : Ult a b) (hnoB : NoUAddOverflow b c) : NoUAddOverflow a c := by
  unfold Ult BitVec.ult at hlt
  unfold NoUAddOverflow BitVec.uaddOverflow at hnoB ⊢
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le, ge_iff_le] at hlt hnoB ⊢
  omega

/-- At power-of-two widths `n = 2 ^ m`, modulo reduction `k % (2 ^ m)` coincides with
    Rust `core::num`'s bitmask `k &&& (2 ^ m - 1)`. -/
theorem mod_twoPow_eq_and_mask (m k : Nat) :
    k % (2 ^ m) = k &&& (2 ^ m - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow]

/-- The `= none` results of `checkedSRem` and `checkedSRemEuclid` on `(BitVec.intMin n, -1#n)`
    hold at every width `n` (without `PosWidth n`): at `n = 0`, `-1#0 = 0#0` triggers the
    zero-divisor guard; at `n > 0`, the `(intMin n, -1#n)` guard fires. -/
theorem checkedSRem_intMin_negOne_eq_none_unconditional (n : Nat) :
    checkedSRem (BitVec.intMin n) (-1#n) = none ∧
    checkedSRemEuclid (BitVec.intMin n) (-1#n) = none := by
  simp [checkedSRem, checkedSRemEuclid]

/-! ## Examples for `Outcome` and `Outcome.ofOption` -/

theorem ex_outcome_pos : Outcome.ofOption (some (42#8)) = Outcome.ok (42#8) := rfl
theorem ex_outcome_neg : Outcome.ofOption (none : Option (BitVec 8)) ≠ Outcome.ok (0#8) := by
  decide

/-! ## Examples for `RingExpr`, `evalInt`, `IntRingIdentity`, `evalWrap` -/

/-- The algebraic identity `(x + y) - y = x`. -/
def addSubCancelExpr : RingExpr :=
  .sub (.add (.var 0) (.var 1)) (.var 1)

theorem ex_ringExpr_evalInt_pos :
    evalInt (fun | 0 => 200 | _ => 100) addSubCancelExpr = 200 := rfl

theorem ex_ringExpr_evalInt_neg :
    evalInt (fun | 0 => 200 | _ => 100) addSubCancelExpr ≠ 300 := by decide

theorem ex_intRingIdentity_pos : IntRingIdentity addSubCancelExpr (.var 0) := by
  intro ρ
  simp [addSubCancelExpr, evalInt]

theorem ex_intRingIdentity_neg : ¬ IntRingIdentity (.add (.var 0) (.var 1)) (.var 0) := by
  intro h
  have h1 := h (fun _ => 1)
  simp [evalInt] at h1

theorem ex_evalWrap_pos :
    evalWrap 8 (fun | 0 => 200#8 | _ => 100#8) addSubCancelExpr = 200#8 := by decide

theorem ex_evalWrap_neg :
    evalWrap 8 (fun | 0 => 200#8 | _ => 100#8) (.add (.var 0) (.var 1)) ≠
      BitVec.ofInt 8 200 := by decide

/-! ## Examples for checked primitives and expression evaluators -/

theorem ex_checkedUNeg_pos : checkedUNeg (0#8) = some (0#8) := rfl
theorem ex_checkedUNeg_neg : checkedUNeg (1#8) = none := rfl

theorem ex_checkedUAdd_pos : checkedUAdd (200#8) (55#8) = some (255#8) := by decide
theorem ex_checkedUAdd_neg : checkedUAdd (200#8) (56#8) = none := by decide

theorem ex_checkedUSub_pos : checkedUSub (10#8) (10#8) = some (0#8) := by decide
theorem ex_checkedUSub_neg : checkedUSub (10#8) (11#8) = none := by decide

theorem ex_checkedUMul_pos : checkedUMul (15#8) (17#8) = some (255#8) := by decide
theorem ex_checkedUMul_neg : checkedUMul (16#8) (16#8) = none := by decide

theorem ex_checkedSNeg_pos : checkedSNeg (-127#8) = some (127#8) := by decide
theorem ex_checkedSNeg_neg : checkedSNeg (BitVec.intMin 8) = none := by decide

theorem ex_checkedSAdd_pos : checkedSAdd (100#8) (27#8) = some (127#8) := by decide
theorem ex_checkedSAdd_neg : checkedSAdd (100#8) (28#8) = none := by decide

theorem ex_checkedSSub_pos : checkedSSub (-100#8) (28#8) = some (-128#8) := by decide
theorem ex_checkedSSub_neg : checkedSSub (-100#8) (29#8) = none := by decide

theorem ex_checkedSMul_pos : checkedSMul (-16#8) (8#8) = some (-128#8) := by decide
theorem ex_checkedSMul_neg : checkedSMul (-16#8) (-8#8) = none := by decide

theorem ex_evalCheckedU_pos :
    evalCheckedU 8 (fun | 0 => 200#8 | _ => 55#8) addSubCancelExpr = some (200#8) := by decide
theorem ex_evalCheckedU_neg :
    evalCheckedU 8 (fun | 0 => 200#8 | _ => 100#8) addSubCancelExpr = none := by decide

theorem ex_evalCheckedS_pos :
    evalCheckedS 8 (fun | 0 => 100#8 | _ => 27#8) addSubCancelExpr = some (100#8) := by decide
theorem ex_evalCheckedS_neg :
    evalCheckedS 8 (fun | 0 => 100#8 | _ => 50#8) addSubCancelExpr = none := by decide

theorem ex_evalPlainU_pos :
    evalPlainU 8 (fun | 0 => 200#8 | _ => 55#8) addSubCancelExpr = Outcome.ok (200#8) := by decide
theorem ex_evalPlainU_neg :
    evalPlainU 8 (fun | 0 => 200#8 | _ => 100#8) addSubCancelExpr = Outcome.panic := by decide

theorem ex_evalPlainS_pos :
    evalPlainS 8 (fun | 0 => 100#8 | _ => 27#8) addSubCancelExpr = Outcome.ok (100#8) := by decide
theorem ex_evalPlainS_neg :
    evalPlainS 8 (fun | 0 => 100#8 | _ => 50#8) addSubCancelExpr = Outcome.panic := by decide

theorem ex_subexprsInRange_pos :
    SubexprsInRange (InUnsignedRange 8) (fun | 0 => 200 | _ => 55) addSubCancelExpr := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide

theorem ex_subexprsInRange_neg :
    ¬ SubexprsInRange (InUnsignedRange 8) (fun | 0 => 200 | _ => 100) addSubCancelExpr := by
  intro ⟨⟨_, _, h⟩, _⟩
  exact (by decide : ¬ InUnsignedRange 8 (200 + 100)) h

/-! ## Examples for order and addition-overflow predicates -/

theorem ex_ult_pos : Ult (10#8) (20#8) := by decide
theorem ex_ult_neg : ¬ Ult (255#8) (255#8) := by decide

theorem ex_slt_pos : Slt (-1#8) (0#8) := by decide
theorem ex_slt_neg : ¬ Slt (0#8) (-1#8) := by decide

theorem ex_noUAddOverflow_pos : NoUAddOverflow (200#8) (55#8) := by decide
theorem ex_noUAddOverflow_neg : ¬ NoUAddOverflow (200#8) (56#8) := by decide

theorem ex_noSAddOverflow_pos : NoSAddOverflow (100#8) (27#8) := by decide
theorem ex_noSAddOverflow_neg : ¬ NoSAddOverflow (100#8) (28#8) := by decide

/-! ## Examples for division and remainder -/

theorem ex_nonZeroDiv_pos : NonZeroDiv (1#8) := by decide
theorem ex_nonZeroDiv_neg : ¬ NonZeroDiv (0#8) := by decide

theorem ex_noSDivOverflow_pos : NoSDivOverflow (BitVec.intMin 8 + 1#8) (-1#8) := by decide
theorem ex_noSDivOverflow_neg : ¬ NoSDivOverflow (BitVec.intMin 8) (-1#8) := by decide

theorem ex_checkedUDiv_pos : checkedUDiv (7#8) (2#8) = some (3#8) := by decide
theorem ex_checkedUDiv_neg : checkedUDiv (7#8) (0#8) = none := by decide

theorem ex_checkedURem_pos : checkedURem (7#8) (2#8) = some (1#8) := by decide
theorem ex_checkedURem_neg : checkedURem (7#8) (0#8) = none := by decide

theorem ex_checkedSDiv_pos : checkedSDiv (-7#8) (4#8) = some (-1#8) := by decide
theorem ex_checkedSDiv_neg : checkedSDiv (BitVec.intMin 8) (-1#8) = none := by decide

theorem ex_checkedSRem_pos : checkedSRem (-7#8) (4#8) = some (-3#8) := by decide
theorem ex_checkedSRem_neg : checkedSRem (BitVec.intMin 8) (-1#8) = none := by decide

theorem ex_sdivEuclid_pos : sdivEuclid (-7#8) (4#8) = (-2#8) := by decide
theorem ex_sdivEuclid_neg : sdivEuclid (-7#8) (4#8) ≠ (-1#8) := by decide

theorem ex_sremEuclid_pos : sremEuclid (-7#8) (4#8) = (1#8) := by decide
theorem ex_sremEuclid_neg : sremEuclid (-7#8) (4#8) ≠ (-3#8) := by decide

theorem ex_checkedSDivEuclid_pos : checkedSDivEuclid (-7#8) (4#8) = some (-2#8) := by decide
theorem ex_checkedSDivEuclid_neg : checkedSDivEuclid (BitVec.intMin 8) (-1#8) = none := by decide

theorem ex_checkedSRemEuclid_pos : checkedSRemEuclid (-7#8) (4#8) = some (1#8) := by decide
theorem ex_checkedSRemEuclid_neg : checkedSRemEuclid (BitVec.intMin 8) (-1#8) = none := by decide

/-! ## Examples for shifts -/

theorem ex_wrappingShl_pos : wrappingShl (1#8) 3 = (8#8) := by decide
theorem ex_wrappingShl_neg : wrappingShl (1#8) 8 ≠ (0#8) := by decide

theorem ex_wrappingUShr_pos : wrappingUShr (8#8) 2 = (2#8) := by decide
theorem ex_wrappingUShr_neg : wrappingUShr (8#8) 8 ≠ (0#8) := by decide

theorem ex_wrappingSShr_pos : wrappingSShr (-8#8) 2 = (-2#8) := by decide
theorem ex_wrappingSShr_neg : wrappingSShr (-8#8) 8 ≠ (-1#8) := by decide

theorem ex_checkedShl_pos : checkedShl (1#8) 7 = some (128#8) := by decide
theorem ex_checkedShl_neg : checkedShl (1#8) 8 = none := by decide

theorem ex_checkedUShr_pos : checkedUShr (128#8) 7 = some (1#8) := by decide
theorem ex_checkedUShr_neg : checkedUShr (128#8) 8 = none := by decide

theorem ex_checkedSShr_pos : checkedSShr (-128#8) 7 = some (-1#8) := by decide
theorem ex_checkedSShr_neg : checkedSShr (-128#8) 8 = none := by decide

/-! ## Examples for numeric `as` casts -/

theorem ex_castFromUnsigned_pos : castFromUnsigned 8 (0x1234#16) = (0x34#8) := by decide
theorem ex_castFromUnsigned_neg : castFromUnsigned 8 (0x1234#16) ≠ (0x12#8) := by decide

theorem ex_castFromSigned_pos : castFromSigned 16 (-17#8) = (-17#16) := by decide
theorem ex_castFromSigned_neg : castFromSigned 16 (-17#8) ≠ (239#16) := by decide

theorem ex_reinterpretCast_pos : (reinterpretCast (-1#8)).toNat = 255 := by decide
theorem ex_reinterpretCast_neg : (reinterpretCast (-1#8)).toNat ≠ 1 := by decide

end Toy.MachInt
