import Toy.MachInt.Defs
import Toy.MachInt.Examples
import Toy.MachInt.Statements
import Toy.MachInt.Counterexamples

/-!
# Non-vacuity witnesses and positive controls (`Toy.MachInt`)

Every main result in `Toy.MachInt.Statements` has a fully proved concrete non-vacuity
witness (`nv_*`) showing that all of its hypotheses hold simultaneously on a concrete,
non-degenerate instance. Each impossibility result also has a fully proved positive
control (`pc_*`) showing that restricting or weakening the hypothesis restores the
property.
-/

namespace Toy.MachInt

/-! ## Result 1 non-vacuity witnesses -/

theorem nv_evalWrap_toNat_eq_emod :
    let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
    ((evalWrap 8 env addSubCancelExpr).toNat : Int) =
      (evalInt (fun i => (env i).toNat) addSubCancelExpr) % ((2 ^ 8 : Nat) : Int) := by
  decide

theorem nv_evalWrap_toInt_eq_bmod :
    let env : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 50#8
    (evalWrap 8 env addSubCancelExpr).toInt =
      (evalInt (fun i => (env i).toInt) addSubCancelExpr).bmod (2 ^ 8) := by
  decide

theorem nv_evalWrap_eq_of_intRingIdentity :
    IntRingIdentity addSubCancelExpr (.var 0) ∧
    (let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
     evalWrap 8 env addSubCancelExpr = evalWrap 8 env (.var 0)) :=
  ⟨ex_intRingIdentity_pos, by decide⟩

/-! ## Result 2 non-vacuity witnesses -/

theorem nv_evalCheckedU_sound :
    let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 55#8
    evalCheckedU 8 env addSubCancelExpr = some (200#8) ∧
    ((200#8).toNat : Int) = evalInt (fun i => (env i).toNat) addSubCancelExpr := by
  decide

theorem nv_evalCheckedU_complete :
    let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 55#8
    SubexprsInRange (InUnsignedRange 8) (fun i => (env i).toNat) addSubCancelExpr ∧
    evalCheckedU 8 env addSubCancelExpr = some (evalWrap 8 env addSubCancelExpr) :=
  ⟨ex_subexprsInRange_pos, by decide⟩

theorem nv_evalCheckedU_isSome_iff_subexprsInRange :
    (let envGood : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 55#8
     (evalCheckedU 8 envGood addSubCancelExpr).isSome = true ∧
     SubexprsInRange (InUnsignedRange 8) (fun i => (envGood i).toNat) addSubCancelExpr) ∧
    (let envBad : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
     (evalCheckedU 8 envBad addSubCancelExpr).isSome ≠ true ∧
     ¬ SubexprsInRange (InUnsignedRange 8) (fun i => (envBad i).toNat) addSubCancelExpr) := by
  refine ⟨⟨by decide, ex_subexprsInRange_pos⟩, ⟨by decide, ex_subexprsInRange_neg⟩⟩

theorem nv_evalCheckedS_sound :
    let env : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 27#8
    evalCheckedS 8 env addSubCancelExpr = some (100#8) ∧
    (100#8).toInt = evalInt (fun i => (env i).toInt) addSubCancelExpr := by
  decide

theorem nv_evalCheckedS_complete :
    let env : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 27#8
    SubexprsInRange (InSignedRange 8) (fun i => (env i).toInt) addSubCancelExpr ∧
    evalCheckedS 8 env addSubCancelExpr = some (evalWrap 8 env addSubCancelExpr) := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩ <;> decide

theorem nv_evalCheckedS_isSome_iff_subexprsInRange :
    (let envGood : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 27#8
     (evalCheckedS 8 envGood addSubCancelExpr).isSome = true ∧
     SubexprsInRange (InSignedRange 8) (fun i => (envGood i).toInt) addSubCancelExpr) ∧
    (let envBad : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 50#8
     (evalCheckedS 8 envBad addSubCancelExpr).isSome ≠ true ∧
     ¬ SubexprsInRange (InSignedRange 8) (fun i => (envBad i).toInt) addSubCancelExpr) := by
  refine ⟨⟨by decide, ⟨⟨by decide, by decide, by decide⟩, by decide, by decide⟩⟩,
    ⟨by decide, fun ⟨⟨_, _, h⟩, _⟩ => (by decide : ¬ InSignedRange 8 (100 + 50)) h⟩⟩

/-! ## Result 3 non-vacuity witnesses and positive controls -/

theorem nv_not_ult_allOnes_add_one :
    BitVec.allOnes 8 + 1#8 = 0#8 ∧
    ¬ Ult (BitVec.allOnes 8) (BitVec.allOnes 8 + 1#8) ∧
    Ult (BitVec.allOnes 8 + 1#8) (BitVec.allOnes 8) ∧
    ¬ (∀ x : BitVec 8, Ult x (x + 1#8)) := by
  decide

/-- Exact characterization of `Ult x (x + 1#n)` across all widths `n`. -/
theorem ult_add_one_iff_ne_allOnes {n : Nat} (x : BitVec n) :
    Ult x (x + 1#n) ↔ x ≠ BitVec.allOnes n := by
  constructor
  · intro h hx
    subst hx
    exact (not_ult_allOnes_add_one n).2.1 h
  · intro hx
    have hlt : x.toNat < (BitVec.allOnes n).toNat := by
      have hxlt : x.toNat < 2 ^ n := x.isLt
      have hne : x.toNat ≠ 2 ^ n - 1 := by
        intro heq
        apply hx
        apply BitVec.eq_of_toNat_eq
        rw [heq, BitVec.toNat_allOnes]
      rw [BitVec.toNat_allOnes]
      omega
    have hno : NoUAddOverflow x 1#n := noUAddOverflow_one_of_ult (by
      unfold Ult BitVec.ult
      simp only [decide_eq_true_eq]
      exact hlt)
    have hpos : 0 < n := by
      by_cases h0 : n = 0
      · subst h0; exact False.elim (hx (by exact Subsingleton.elim _ _))
      · exact Nat.pos_of_ne_zero h0
    have h1 : (1#n).toNat = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hpos))]
    unfold Ult BitVec.ult
    simp only [decide_eq_true_eq]
    unfold NoUAddOverflow BitVec.uaddOverflow at hno
    simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le] at hno
    rw [BitVec.toNat_add_of_lt hno, h1]
    omega

/-- Positive control for `not_ult_allOnes_add_one`: when `x < u<n>::MAX` (`Ult x (BitVec.allOnes n)`),
    `Ult x (x + 1#n)` holds for every `n`, and the premise is inhabited at `n = 8, x = 254#8`. -/
theorem pc_ult_add_one_of_lt_uMax :
    (∀ (n : Nat) (x : BitVec n), Ult x (BitVec.allOnes n) → Ult x (x + 1#n)) ∧
    (Ult (254#8) (BitVec.allOnes 8) ∧ Ult (254#8) (254#8 + 1#8)) := by
  constructor
  · intro n x h
    have hno : NoUAddOverflow x 1#n := noUAddOverflow_one_of_ult h
    unfold Ult BitVec.ult at h ⊢
    unfold NoUAddOverflow BitVec.uaddOverflow at hno
    simp only [decide_eq_true_eq] at h ⊢
    simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le] at hno
    have hpos : 0 < n := by
      by_cases h0 : n = 0
      · subst h0; have hx := BitVec.eq_nil x; subst hx; simp at h
      · exact Nat.pos_of_ne_zero h0
    have h1 : (1#n).toNat = 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hpos))]
    rw [BitVec.toNat_add_of_lt hno, h1]
    omega
  · decide

theorem nv_not_slt_intMax_add_one :
    BitVec.intMax 8 + 1#8 = BitVec.intMin 8 ∧
    ¬ Slt (BitVec.intMax 8) (BitVec.intMax 8 + 1#8) ∧
    Slt (BitVec.intMax 8 + 1#8) (BitVec.intMax 8) ∧
    ¬ (∀ x : BitVec 8, Slt x (x + 1#8)) := by
  decide

/-- Positive control for `not_slt_intMax_add_one`: when `x < i<n>::MAX` (`Slt x (BitVec.intMax n)`),
    `Slt x (x + 1#n)` holds for every `n`, and the premise is inhabited at `n = 8, x = 126#8`. -/
theorem pc_slt_add_one_of_lt_sMax :
    (∀ (n : Nat) (x : BitVec n), Slt x (BitVec.intMax n) → Slt x (x + 1#n)) ∧
    (Slt (126#8) (BitVec.intMax 8) ∧ Slt (126#8) (126#8 + 1#8)) := by
  constructor
  · intro n x h
    unfold Slt BitVec.slt at h ⊢
    simp only [decide_eq_true_eq] at h ⊢
    by_cases h0 : n = 0
    · subst h0; have hx := BitVec.eq_nil x; subst hx; simp at h
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      rw [BitVec.toInt_intMax] at h
      have hxlow : -((2 ^ (n - 1) : Nat) : Int) ≤ x.toInt := by
        have := @BitVec.le_toInt n x
        simpa [Int.natCast_pow] using this
      have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
        have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hpos).symm
        calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
          _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
          _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
      have hpow : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
        exact_mod_cast hnat
      by_cases h1n : n = 1
      · subst h1n
        have hlt1 : x.toInt < 0 := by simpa using h
        rcases BitVec.eq_zero_or_eq_one x with rfl | rfl
        · simp at hlt1
        · decide
      · have hgt1 : 1 < n := by omega
        have h1 : (1#n).toInt = 1 := BitVec.toInt_one hgt1
        have h2p : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := (Int.natCast_pow 2 (n - 1)).symm
        rw [h2p] at h
        rw [BitVec.toInt_add, h1, Int.bmod_eq_of_le_mul_two]
        · omega
        · rw [hpow]; omega
        · rw [hpow]; omega
  · decide

/-- Exact characterization of `Slt x (x + 1#n)` across all widths `n`. -/
theorem slt_add_one_iff_ne_intMax {n : Nat} (x : BitVec n) :
    Slt x (x + 1#n) ↔ x ≠ BitVec.intMax n := by
  constructor
  · intro h hx
    subst hx
    exact (not_slt_intMax_add_one n).2.1 h
  · intro hx
    have hlt : Slt x (BitVec.intMax n) := by
      have hpos : 0 < n := by
        by_cases h0 : n = 0
        · subst h0; exact False.elim (hx (by exact Subsingleton.elim _ _))
        · exact Nat.pos_of_ne_zero h0
      have hxlt : x.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
        simpa [Int.natCast_pow] using @BitVec.toInt_lt n x
      have hne : x.toInt ≠ (BitVec.intMax n).toInt := by
        intro heq
        exact hx (BitVec.eq_of_toInt_eq heq)
      unfold Slt BitVec.slt
      simp only [decide_eq_true_eq]
      rw [BitVec.toInt_intMax] at hne ⊢
      have h2p : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := (Int.natCast_pow 2 (n - 1)).symm
      rw [h2p] at hne ⊢
      omega
    exact pc_slt_add_one_of_lt_sMax.1 n x hlt

theorem nv_ult_add_right_of_noUAddOverflow :
    Ult (10#8) (20#8) ∧ NoUAddOverflow (20#8) (5#8) ∧ Ult (10#8 + 5#8) (20#8 + 5#8) := by
  decide

theorem nv_slt_add_right_of_noSAddOverflow :
    Slt (-10#8) (20#8) ∧
    NoSAddOverflow (-10#8) (5#8) ∧
    NoSAddOverflow (20#8) (5#8) ∧
    Slt (-10#8 + 5#8) (20#8 + 5#8) := by
  decide

theorem nv_ult_add_right_iff_uaddOverflow_eq :
    Ult (200#8) (250#8) ∧
    (Ult (200#8 + 100#8) (250#8 + 100#8) ↔
      BitVec.uaddOverflow (200#8) (100#8) = BitVec.uaddOverflow (250#8) (100#8)) := by
  decide

theorem nv_slt_add_right_iff_saddOverflow_eq :
    Slt (100#8) (120#8) ∧
    (Slt (100#8 + 100#8) (120#8 + 100#8) ↔
      BitVec.saddOverflow (100#8) (100#8) = BitVec.saddOverflow (120#8) (100#8)) := by
  decide

/-! ## Result 4 non-vacuity witnesses -/

theorem nv_checkedUDiv_and_checkedURem_eq_nat_div_mod :
    NonZeroDiv (4#8) ∧
    checkedUDiv (7#8) (4#8) = some (1#8) ∧
    checkedURem (7#8) (4#8) = some (3#8) ∧
    (1#8).toNat = (7#8).toNat / (4#8).toNat ∧
    (3#8).toNat = (7#8).toNat % (4#8).toNat := by
  decide

theorem nv_checkedSDiv_eq_some_and_toInt_eq_tdiv :
    NonZeroDiv (4#8) ∧
    NoSDivOverflow (-7#8) (4#8) ∧
    checkedSDiv (-7#8) (4#8) = some (-1#8) ∧
    (-1#8).toInt = (-7#8).toInt.tdiv (4#8).toInt := by
  decide

theorem nv_checkedSRem_eq_some_and_toInt_eq_tmod :
    NonZeroDiv (4#8) ∧
    NoSDivOverflow (-7#8) (4#8) ∧
    checkedSRem (-7#8) (4#8) = some (-3#8) ∧
    (-3#8).toInt = (-7#8).toInt.tmod (4#8).toInt := by
  decide

theorem nv_tdiv_not_inSignedRange_iff_intMin_negOne :
    PosWidth 8 ∧
    ¬ InSignedRange 8 ((BitVec.intMin 8).toInt.tdiv (-1#8).toInt) ∧
    ((BitVec.intMin 8) = BitVec.intMin 8 ∧ (-1#8) = -1#8) := by
  decide

theorem nv_checkedSRem_intMin_negOne_eq_none :
    PosWidth 8 ∧
    NonZeroDiv (-1#8) ∧
    InSignedRange 8 ((BitVec.intMin 8).toInt.tmod (-1#8).toInt) ∧
    checkedSRem (BitVec.intMin 8) (-1#8) = none := by
  decide

theorem nv_checkedSDivEuclid_eq_some_and_toInt_eq_ediv :
    NonZeroDiv (4#8) ∧
    NoSDivOverflow (-7#8) (4#8) ∧
    checkedSDivEuclid (-7#8) (4#8) = some (-2#8) ∧
    (-2#8).toInt = (-7#8).toInt.ediv (4#8).toInt := by
  decide

theorem nv_checkedSRemEuclid_eq_some_and_toInt_eq_emod :
    NonZeroDiv (4#8) ∧
    NoSDivOverflow (-7#8) (4#8) ∧
    checkedSRemEuclid (-7#8) (4#8) = some (1#8) ∧
    (1#8).toInt = (-7#8).toInt.emod (4#8).toInt := by
  decide

/-! ## Result 5 non-vacuity witnesses -/

theorem nv_wrappingShl_eq_mul_twoPow_of_shiftInBounds :
    ShiftInBounds 8 3 ∧
    checkedShl (5#8) 3 = some (wrappingShl (5#8) 3) ∧
    (wrappingShl (5#8) 3).toNat = ((5#8).toNat * 2 ^ 3) % 2 ^ 8 := by
  decide

theorem nv_wrappingUShr_and_wrappingSShr_of_shiftInBounds :
    ShiftInBounds 8 2 ∧
    checkedUShr (9#8) 2 = some (wrappingUShr (9#8) 2) ∧
    (wrappingUShr (9#8) 2).toNat = (9#8).toNat / 2 ^ 2 ∧
    checkedSShr (-7#8) 2 = some (wrappingSShr (-7#8) 2) ∧
    (wrappingSShr (-7#8) 2).toInt = (-7#8).toInt.fdiv ((2 ^ 2 : Nat) : Int) := by
  decide

/-! ## Result 6 non-vacuity witnesses -/

theorem nv_castFromUnsigned_toNat_eq_mod :
    (castFromUnsigned 8 (0x1234#16)).toNat = (0x1234#16).toNat % 2 ^ 8 := by
  decide

theorem nv_castFromUnsigned_widened_toNat_eq_mod :
    WidthLe 8 32 ∧
    (castFromUnsigned 32 (castFromUnsigned 8 (0x12345678#32))).toNat =
      (0x12345678#32).toNat % 2 ^ 8 := by
  decide

theorem nv_cast_u32_to_u8_to_u32_eq_mod_256 :
    (castFromUnsigned 32 (castFromUnsigned 8 (0x12345678#32))).toNat =
      (0x12345678#32).toNat % 256 := by
  decide

theorem nv_castFromSigned_toInt_eq_of_widthLe :
    WidthLe 8 16 ∧
    (castFromSigned 16 (-17#8)).toInt = (-17#8).toInt := by
  decide

theorem nv_reinterpretCast_characterization :
    (reinterpretCast (-17#8)).toNat = 239 ∧
    (reinterpretCast (-17#8)).toInt = -17 := by
  decide

theorem nv_cast_roundTrip_widen_then_narrow_of_widthLe :
    WidthLe 8 16 ∧
    castFromUnsigned 8 (castFromUnsigned 16 (200#8)) = (200#8) ∧
    castFromSigned 8 (castFromSigned 16 (-17#8)) = (-17#8) := by
  decide

end Toy.MachInt
