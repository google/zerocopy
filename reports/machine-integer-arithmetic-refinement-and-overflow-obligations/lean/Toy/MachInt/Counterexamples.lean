import Toy.MachInt.Defs
import Toy.MachInt.Examples
import Toy.MachInt.Statements

/-!
# Counterexamples and canonical hypothesis-tightness witnesses (`Toy.MachInt`)

All theorems in this module are fully proved (zero `sorry`). They provide:
1. Standalone counterexamples required by the domain analysis:
   - Intermediate overflow in `(a + b) - b` (`ce_checked_add_sub_intermediate_overflow`);
   - Signed truncating `/` and `%` vs Lean's default `Int` Euclidean `/` and `%`
     (`ce_sdiv_srem_ne_int_ediv_emod`);
   - Overshifting `wrapping_shl` vs `x * 2^k (mod 2^n)` (`ce_wrappingShl_overshift_ne_mul_twoPow`);
   - Narrowing-then-widening and sign-vs-zero extension cast mismatches
     (`ce_cast_roundTrip_narrow_then_widen`).
2. Canonical per-hypothesis tightness counterexamples showing that every `tight` hypothesis
   in `Statements.lean` cannot be omitted without falsifying the conclusion.
-/

namespace Toy.MachInt

/-! ## Standalone counterexamples -/

/-- Counterexample (Result 2): For `(a + b) - b` with `a = 200u8, b = 100u8` (unsigned)
    and `a = 100i8, b = 50i8` (signed), the final mathematical integer values `200` and `100`
    are in range and wrapping evaluation yields the exact integer answer, yet checked
    evaluation returns `none` and plain overflow-checked evaluation panics because the
    intermediate `a + b` overflows. -/
theorem ce_checked_add_sub_intermediate_overflow :
    let uEnv : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
    let uIntEnv : Nat → Int := fun i => (uEnv i).toNat
    let sEnv : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 50#8
    let sIntEnv : Nat → Int := fun i => (sEnv i).toInt
    InUnsignedRange 8 (evalInt uIntEnv addSubCancelExpr) ∧
    ((evalWrap 8 uEnv addSubCancelExpr).toNat : Int) = evalInt uIntEnv addSubCancelExpr ∧
    evalCheckedU 8 uEnv addSubCancelExpr = none ∧
    evalPlainU 8 uEnv addSubCancelExpr = Outcome.panic ∧
    InSignedRange 8 (evalInt sIntEnv addSubCancelExpr) ∧
    (evalWrap 8 sEnv addSubCancelExpr).toInt = evalInt sIntEnv addSubCancelExpr ∧
    evalCheckedS 8 sEnv addSubCancelExpr = none ∧
    evalPlainS 8 sEnv addSubCancelExpr = Outcome.panic := by
  decide

/-- Counterexample (Result 4): On `(-7 : i8)` divided by `(4 : i8)`, Rust/bitvector
    truncating division `sdiv`/`srem` yields `(-1, -3)` (`Int.tdiv`/`Int.tmod`), directly
    disagreeing with Lean's default `Int` `/` and `%` (`Int.ediv`/`Int.emod`, `-2` and `1`,
    matching `sdivEuclid`/`sremEuclid`). On `(7 : i8)` divided by `(-4 : i8)`, truncating
    `sdiv`/`srem` coincide with `Int.ediv`/`Int.emod` (`-1`, `3`), whereas flooring
    `Int.fdiv`/`BitVec.smod` yield `(-2, -1)`. -/
theorem ce_sdiv_srem_ne_int_ediv_emod :
    ((-7#8).sdiv (4#8)).toInt = -1 ∧
    ((-7#8).srem (4#8)).toInt = -3 ∧
    ((-7 : Int) / (4 : Int)) = -2 ∧
    ((-7 : Int) % (4 : Int)) = 1 ∧
    ((-7#8).sdiv (4#8)).toInt ≠ (-7#8).toInt / (4#8).toInt ∧
    ((-7#8).srem (4#8)).toInt ≠ (-7#8).toInt % (4#8).toInt ∧
    (sdivEuclid (-7#8) (4#8)).toInt = (-7 : Int).ediv 4 ∧
    (sremEuclid (-7#8) (4#8)).toInt = (-7 : Int).emod 4 ∧
    ((7#8).sdiv (-4#8)).toInt = (7#8).toInt / (-4#8).toInt ∧
    ((7#8).srem (-4#8)).toInt = (7#8).toInt % (-4#8).toInt ∧
    ((7#8).sdiv (-4#8)).toInt ≠ (7 : Int).fdiv (-4) ∧
    ((7#8).srem (-4#8)).toInt ≠ ((7#8).smod (-4#8)).toInt := by
  decide

/-- Counterexample (Result 5): When `k ≥ n`, `wrappingShl` masks `k` modulo `n`, so it
    disagrees with `(x.toNat * 2^k) % 2^n` and `(x.toInt * 2^k).bmod (2^n)`:
    `wrappingShl 1#8 8 = 1#8 ≠ 0#8` and `wrappingShl 5#8 9 = 10#8 ≠ 0#8`, while `checkedShl`
    returns `none`. -/
theorem ce_wrappingShl_overshift_ne_mul_twoPow :
    checkedShl (1#8) 8 = none ∧
    (wrappingShl (1#8) 8).toNat ≠ (1 * 2 ^ 8) % 2 ^ 8 ∧
    checkedShl (5#8) 9 = none ∧
    (wrappingShl (5#8) 9).toNat ≠ (5 * 2 ^ 9) % 2 ^ 8 ∧
    (wrappingShl (-1#8) 8).toInt ≠ ((-1 : Int) * ((2 ^ 8 : Nat) : Int)).bmod (2 ^ 8) := by
  decide

/-- Counterexample (Result 5): `ShiftInBounds` (`k < n`) guarantees `checkedShl` returns `some`,
    but does NOT detect bits shifted out: on 8 bits, `checkedShl 128#8 1 = some 0#8` whereas
    unbounded `128 * 2 = 256` overflows `u8` (`checkedUMul 128#8 2#8 = none`), and
    `checkedShl 64#8 1 = some (-128#8)` whereas `64 * 2 = 128` overflows `i8`
    (`checkedSMul 64#8 2#8 = none`). -/
theorem ce_checkedShl_drops_high_bits_without_none :
    ShiftInBounds 8 1 ∧
    checkedShl (128#8) 1 = some (0#8) ∧
    (0#8).toNat ≠ (128#8).toNat * 2 ^ 1 ∧
    checkedUMul (128#8) (2#8) = none ∧
    checkedShl (64#8) 1 = some (-128#8) ∧
    (-128#8).toInt ≠ (64#8).toInt * ((2 ^ 1 : Nat) : Int) ∧
    checkedSMul (64#8) (2#8) = none := by
  decide

/-- Counterexample (Result 5): At non-power-of-two bitwidths such as `n = 3`, `k % n`
    diverges from Rust `core::num`'s `k &&& (n - 1)` bitmask (`4 % 3 = 1 ≠ 0 = 4 &&& 2`). -/
theorem ce_wrappingShl_mod_ne_and_mask_nonPowTwo :
    4 % 3 ≠ 4 &&& (3 - 1) ∧
    wrappingShl (1#3) 4 ≠ (1#3) <<< (4 &&& (3 - 1)) := by
  decide

/-- Counterexample (Result 6): Narrowing then widening loses high bits (`256u16 -> u8 -> u16 = 0 ≠ 256`
    and `128i16 -> i8 -> i16 = -128 ≠ 128`), and casting `(-1i8)` directly to `u16` (`65535`)
    differs from casting via `u8` (`255`). -/
theorem ce_cast_roundTrip_narrow_then_widen :
    castFromUnsigned 16 (castFromUnsigned 8 (256#16)) ≠ (256#16) ∧
    castFromSigned 16 (castFromSigned 8 (128#16)) ≠ (128#16) ∧
    castFromSigned 16 (-1#8) ≠ castFromUnsigned 16 (reinterpretCast (-1#8)) := by
  decide

/-! ## Canonical per-hypothesis tightness counterexamples -/

/-- Tightness for `evalWrap_eq_of_intRingIdentity`: dropping `IntRingIdentity e₁ e₂`
    allows `evalWrap 8 env (.add (.var 0) (.var 1)) ≠ evalWrap 8 env (.var 0)`. -/
theorem ce_evalWrap_eq_drop_intRingIdentity :
    ∃ (n : Nat) (env : Nat → BitVec n) (e₁ e₂ : RingExpr),
      ¬ IntRingIdentity e₁ e₂ ∧
      evalWrap n env e₁ ≠ evalWrap n env e₂ := by
  refine ⟨8, (fun _ => 1#8), .add (.var 0) (.var 1), .var 0, ex_intRingIdentity_neg, ?_⟩
  decide

/-- Non-claim for `evalWrap_eq_of_intRingIdentity`: agreement on wrapping `BitVec n` does not
    imply `IntRingIdentity` (using valid in-range `u8`/`i8` constants: `64 * (4 * x) = 0` on
    `u8`/`i8`, and `128 * (x + x) = 0` on `u8`, both fail over `Int`). -/
theorem ce_evalWrap_eq_not_imp_intRingIdentity :
    (∀ env : Nat → BitVec 8,
      evalWrap 8 env (.mul (.lit 64) (.mul (.lit 4) (.var 0))) = evalWrap 8 env (.lit 0)) ∧
    ¬ IntRingIdentity (.mul (.lit 64) (.mul (.lit 4) (.var 0))) (.lit 0) ∧
    (∀ env : Nat → BitVec 8,
      evalWrap 8 env (.mul (.lit 128) (.add (.var 0) (.var 0))) = evalWrap 8 env (.lit 0)) ∧
    ¬ IntRingIdentity (.mul (.lit 128) (.add (.var 0) (.var 0))) (.lit 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro env
    apply BitVec.eq_of_toNat_eq
    have h64 : (BitVec.ofInt 8 64).toNat = 64 := by decide
    have h4 : (BitVec.ofInt 8 4).toNat = 4 := by decide
    simp only [evalWrap, BitVec.toNat_mul, h64, h4, BitVec.toNat_ofInt]
    omega
  · intro h
    have h1 := h (fun _ => 1)
    simp [evalInt] at h1
  · intro env
    apply BitVec.eq_of_toNat_eq
    have h128 : (BitVec.ofInt 8 128).toNat = 128 := by decide
    simp only [evalWrap, BitVec.toNat_mul, BitVec.toNat_add, h128, BitVec.toNat_ofInt]
    omega
  · intro h
    have h1 := h (fun _ => 1)
    simp [evalInt] at h1

/-- Tightness for `evalCheckedU_sound`: dropping `evalCheckedU n env e = some v` allows
    arbitrary `v` (or wrapping evaluation) to disagree with `evalInt`. -/
theorem ce_evalCheckedU_sound_drop_some :
    let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
    let e : RingExpr := .add (.var 0) (.var 1)
    evalCheckedU 8 env e = none ∧
    ((evalWrap 8 env e).toNat : Int) ≠ evalInt (fun i => (env i).toNat) e := by
  decide

/-- Tightness for `evalCheckedS_sound`: dropping `evalCheckedS n env e = some v` allows
    wrapping evaluation to disagree with `evalInt`. -/
theorem ce_evalCheckedS_sound_drop_some :
    let env : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 50#8
    let e : RingExpr := .add (.var 0) (.var 1)
    evalCheckedS 8 env e = none ∧
    (evalWrap 8 env e).toInt ≠ evalInt (fun i => (env i).toInt) e := by
  decide

/-- Tightness for `evalCheckedU_complete`: dropping `SubexprsInRange (InUnsignedRange n)`
    allows final-result-in-range `(200u8 + 100u8) - 100u8` to return `none`. -/
theorem ce_checkedU_add_sub_intermediate_overflow :
    let env : Nat → BitVec 8 := fun | 0 => 200#8 | _ => 100#8
    let ρ : Nat → Int := fun i => (env i).toNat
    InUnsignedRange 8 (evalInt ρ addSubCancelExpr) ∧
    ¬ SubexprsInRange (InUnsignedRange 8) ρ addSubCancelExpr ∧
    evalCheckedU 8 env addSubCancelExpr ≠ some (evalWrap 8 env addSubCancelExpr) := by
  refine ⟨by decide, ex_subexprsInRange_neg, by decide⟩

/-- Tightness for `evalCheckedS_complete`: dropping `SubexprsInRange (InSignedRange n)`
    allows final-result-in-range `(100i8 + 50i8) - 50i8` to return `none`. -/
theorem ce_checkedS_add_sub_intermediate_overflow :
    let env : Nat → BitVec 8 := fun | 0 => 100#8 | _ => 50#8
    let ρ : Nat → Int := fun i => (env i).toInt
    InSignedRange 8 (evalInt ρ addSubCancelExpr) ∧
    ¬ SubexprsInRange (InSignedRange 8) ρ addSubCancelExpr ∧
    evalCheckedS 8 env addSubCancelExpr ≠ some (evalWrap 8 env addSubCancelExpr) := by
  refine ⟨by decide, ?_, by decide⟩
  intro ⟨⟨_, _, h⟩, _⟩
  exact (by decide : ¬ InSignedRange 8 (100 + 50)) h

/-- Tightness for `ult_add_right_of_noUAddOverflow` (hypothesis `hlt : Ult a b`). -/
theorem ce_ult_add_right_drop_hlt :
    ¬ Ult (10#8) (5#8) ∧
    NoUAddOverflow (5#8) (1#8) ∧
    ¬ Ult (10#8 + 1#8) (5#8 + 1#8) := by
  decide

theorem ce_ult_add_right_drop_noUAddOverflow :
    Ult (1#8) (255#8) ∧
    ¬ NoUAddOverflow (255#8) (1#8) ∧
    ¬ Ult (1#8 + 1#8) (255#8 + 1#8) := by
  decide

theorem ce_slt_add_right_drop_hlt :
    ¬ Slt (10#8) (5#8) ∧
    NoSAddOverflow (10#8) (1#8) ∧
    NoSAddOverflow (5#8) (1#8) ∧
    ¬ Slt (10#8 + 1#8) (5#8 + 1#8) := by
  decide

theorem ce_slt_add_right_drop_noSAddOverflow_left :
    Slt (-128#8) (10#8) ∧
    ¬ NoSAddOverflow (-128#8) (-1#8) ∧
    NoSAddOverflow (10#8) (-1#8) ∧
    ¬ Slt (-128#8 + -1#8) (10#8 + -1#8) := by
  decide

theorem ce_slt_add_right_drop_noSAddOverflow_right :
    Slt (10#8) (127#8) ∧
    NoSAddOverflow (10#8) (1#8) ∧
    ¬ NoSAddOverflow (127#8) (1#8) ∧
    ¬ Slt (10#8 + 1#8) (127#8 + 1#8) := by
  decide

/-- Tightness for `ult_add_right_iff_uaddOverflow_eq` (hypothesis `hlt : Ult a b`):
    when `¬ Ult a b`, equal overflow flags do not entail `Ult (a + c) (b + c)`. -/
theorem ce_ult_add_right_iff_drop_hlt :
    ¬ Ult (10#8) (5#8) ∧
    ¬ (Ult (10#8 + 1#8) (5#8 + 1#8) ↔
        BitVec.uaddOverflow (10#8) (1#8) = BitVec.uaddOverflow (5#8) (1#8)) := by
  decide

/-- Tightness for `slt_add_right_iff_saddOverflow_eq` (hypothesis `hlt : Slt a b`):
    when `¬ Slt a b`, equal overflow flags do not entail `Slt (a + c) (b + c)`. -/
theorem ce_slt_add_right_iff_drop_hlt :
    ¬ Slt (10#8) (5#8) ∧
    ¬ (Slt (10#8 + 1#8) (5#8 + 1#8) ↔
        BitVec.saddOverflow (10#8) (1#8) = BitVec.saddOverflow (5#8) (1#8)) := by
  decide

/-- Non-necessity witness (unsigned): when both `a + c` and `b + c` overflow modulo `2^n`,
    `Ult (a + c) (b + c)` is still preserved (`200u8 < 250u8` and `44u8 < 94u8`). -/
theorem ce_ult_add_right_both_wrap :
    Ult (200#8) (250#8) ∧
    ¬ NoUAddOverflow (200#8) (100#8) ∧
    ¬ NoUAddOverflow (250#8) (100#8) ∧
    Ult (200#8 + 100#8) (250#8 + 100#8) := by
  decide

/-- Non-necessity witness (signed): when both `a + c` and `b + c` wrap in the same
    direction, `Slt (a + c) (b + c)` is still preserved (`100i8 < 120i8` and `-56i8 < -36i8`). -/
theorem ce_slt_add_right_both_wrap :
    Slt (100#8) (120#8) ∧
    ¬ NoSAddOverflow (100#8) (100#8) ∧
    ¬ NoSAddOverflow (120#8) (100#8) ∧
    Slt (100#8 + 100#8) (120#8 + 100#8) := by
  decide

/-- Tightness for `checkedUDiv_and_checkedURem_eq_nat_div_mod`: dropping `NonZeroDiv b`
    yields `checkedUDiv a 0 = none` and `checkedURem a 0 = none`. -/
theorem ce_checkedUDiv_drop_nonZeroDiv :
    ¬ NonZeroDiv (0#8) ∧
    ¬ (∃ q r : BitVec 8,
      checkedUDiv (7#8) (0#8) = some q ∧ checkedURem (7#8) (0#8) = some r ∧
      q.toNat = (7#8).toNat / (0#8).toNat ∧ r.toNat = (7#8).toNat % (0#8).toNat) := by
  decide

/-- Tightness for `checkedSDiv_eq_some_and_toInt_eq_tdiv` (hypothesis `hb : NonZeroDiv b`). -/
theorem ce_checkedSDiv_drop_nonZeroDiv :
    ¬ NonZeroDiv (0#8) ∧
    NoSDivOverflow (7#8) (0#8) ∧
    ¬ (∃ q : BitVec 8, checkedSDiv (7#8) (0#8) = some q ∧ q.toInt = (7#8).toInt.tdiv (0#8).toInt) := by
  decide

/-- Tightness for `checkedSDiv_eq_some_and_toInt_eq_tdiv` (hypothesis `hno : NoSDivOverflow a b`). -/
theorem ce_checkedSDiv_drop_noSDivOverflow :
    NonZeroDiv (-1#8) ∧
    ¬ NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
    ¬ (∃ q : BitVec 8,
      checkedSDiv (BitVec.intMin 8) (-1#8) = some q ∧
      q.toInt = (BitVec.intMin 8).toInt.tdiv (-1#8).toInt) := by
  decide

/-- Tightness for `checkedSRem_eq_some_and_toInt_eq_tmod` (hypothesis `hb : NonZeroDiv b`). -/
theorem ce_checkedSRem_drop_nonZeroDiv :
    ¬ NonZeroDiv (0#8) ∧
    NoSDivOverflow (7#8) (0#8) ∧
    ¬ (∃ r : BitVec 8, checkedSRem (7#8) (0#8) = some r ∧ r.toInt = (7#8).toInt.tmod (0#8).toInt) := by
  decide

/-- Tightness for `checkedSRem_eq_some_and_toInt_eq_tmod` (hypothesis `hno : NoSDivOverflow a b`). -/
theorem ce_checkedSRem_drop_noSDivOverflow :
    NonZeroDiv (-1#8) ∧
    ¬ NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
    ¬ (∃ r : BitVec 8,
      checkedSRem (BitVec.intMin 8) (-1#8) = some r ∧
      r.toInt = (BitVec.intMin 8).toInt.tmod (-1#8).toInt) := by
  decide

/-- Tightness for `tdiv_not_inSignedRange_iff_intMin_negOne` (hypothesis `hn : PosWidth n`):
    at width `0`, `0#0 = BitVec.intMin 0` and `0#0 = -1#0`, yet `InSignedRange 0 (0.tdiv 0)` holds. -/
theorem ce_tdiv_overflow_iff_drop_posWidth :
    ¬ PosWidth 0 ∧
    (0#0 = BitVec.intMin 0 ∧ (0#0) = -1#0) ∧
    InSignedRange 0 ((0#0).toInt.tdiv (0#0).toInt) := by
  decide

/-- Tightness for `checkedSRem_intMin_negOne_eq_none` (hypothesis `hn : PosWidth n`):
    at width `0`, `-1#0 = 0#0` fails `NonZeroDiv (-1#0)`. -/
theorem ce_checkedSRem_intMin_drop_posWidth :
    ¬ PosWidth 0 ∧ ¬ NonZeroDiv (-1#0) := by
  decide

/-- Tightness for `checkedSDivEuclid_eq_some_and_toInt_eq_ediv` (hypothesis `hb : NonZeroDiv b`). -/
theorem ce_checkedSDivEuclid_drop_nonZeroDiv :
    ¬ NonZeroDiv (0#8) ∧
    NoSDivOverflow (7#8) (0#8) ∧
    ¬ (∃ q : BitVec 8,
      checkedSDivEuclid (7#8) (0#8) = some q ∧ q.toInt = (7#8).toInt.ediv (0#8).toInt) := by
  decide

/-- Tightness for `checkedSDivEuclid_eq_some_and_toInt_eq_ediv` (hypothesis `hno : NoSDivOverflow a b`). -/
theorem ce_checkedSDivEuclid_drop_noSDivOverflow :
    NonZeroDiv (-1#8) ∧
    ¬ NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
    ¬ (∃ q : BitVec 8,
      checkedSDivEuclid (BitVec.intMin 8) (-1#8) = some q ∧
      q.toInt = (BitVec.intMin 8).toInt.ediv (-1#8).toInt) := by
  decide

/-- Tightness for `checkedSRemEuclid_eq_some_and_toInt_eq_emod` (hypothesis `hb : NonZeroDiv b`). -/
theorem ce_checkedSRemEuclid_drop_nonZeroDiv :
    ¬ NonZeroDiv (0#8) ∧
    NoSDivOverflow (7#8) (0#8) ∧
    ¬ (∃ r : BitVec 8,
      checkedSRemEuclid (7#8) (0#8) = some r ∧ r.toInt = (7#8).toInt.emod (0#8).toInt) := by
  decide

/-- Tightness for `checkedSRemEuclid_eq_some_and_toInt_eq_emod` (hypothesis `hno : NoSDivOverflow a b`). -/
theorem ce_checkedSRemEuclid_drop_noSDivOverflow :
    NonZeroDiv (-1#8) ∧
    ¬ NoSDivOverflow (BitVec.intMin 8) (-1#8) ∧
    ¬ (∃ r : BitVec 8,
      checkedSRemEuclid (BitVec.intMin 8) (-1#8) = some r ∧
      r.toInt = (BitVec.intMin 8).toInt.emod (-1#8).toInt) := by
  decide

/-- Tightness for `wrappingUShr_and_wrappingSShr_of_shiftInBounds`: when `k ≥ n`, both
    `checkedUShr`/`checkedSShr` return `none` and masked right shifts wrap the count modulo `n`.
    Also records that arithmetic right shift `(-1#8) >> 1 = -1` matches flooring `Int.fdiv`,
    not truncating `Int.tdiv` (`(-1).tdiv 2 = 0`). -/
theorem ce_wrappingShr_overshift :
    ¬ ShiftInBounds 8 8 ∧
    checkedUShr (128#8) 8 = none ∧
    (wrappingUShr (128#8) 8).toNat ≠ (128#8).toNat / 2 ^ 8 ∧
    checkedSShr (-128#8) 8 = none ∧
    (wrappingSShr (-128#8) 8).toInt ≠ (-128#8).toInt.fdiv ((2 ^ 8 : Nat) : Int) := by
  decide

/-- Companion separation for arithmetic right shift: `(-1#8) >> 1 = -1` matches `Int.fdiv (-1) 2`,
    not truncating division `Int.tdiv (-1) 2 = 0`. -/
theorem ce_sshiftRight_ne_sdiv_twoPow :
    (wrappingSShr (-1#8) 1).toInt = (-1 : Int).fdiv 2 ∧
    (wrappingSShr (-1#8) 1).toInt ≠ (-1 : Int).tdiv 2 := by
  decide

/-- Tightness for `castFromUnsigned_widened_toNat_eq_mod` (hypothesis `hle : WidthLe m k`):
    when `k < m` (`m = 16, k = 8`), casting `256#32` via `u16` to `u8` truncates further modulo
    `2^8`, disagreeing with `256 % 2^16`. -/
theorem ce_castFromUnsigned_widened_drop_widthLe :
    ¬ WidthLe 16 8 ∧
    (castFromUnsigned 8 (castFromUnsigned 16 (256#32))).toNat ≠ (256#32).toNat % 2 ^ 16 := by
  decide

/-- Companion witness that narrowing then widening fails to be the identity on unsigned values. -/
theorem ce_castFromUnsigned_narrow_widen_ne_id :
    ¬ WidthLe 16 8 ∧
    (castFromUnsigned 16 (castFromUnsigned 8 (256#16))).toNat ≠ (256#16).toNat := by
  decide

/-- Tightness for `castFromSigned_toInt_eq_of_widthLe` (hypothesis `hle : WidthLe n m`):
    narrowing `128#16` (`128`) to `8` bits produces `-128#8` (`-128 ≠ 128`). -/
theorem ce_castFromSigned_drop_widthLe :
    ¬ WidthLe 16 8 ∧
    (castFromSigned 8 (128#16)).toInt ≠ (128#16).toInt := by
  decide

/-- Tightness for `cast_roundTrip_widen_then_narrow_of_widthLe` (hypothesis `hle : WidthLe n m`). -/
theorem ce_cast_roundTrip_drop_widthLe :
    ¬ WidthLe 16 8 ∧
    castFromUnsigned 16 (castFromUnsigned 8 (256#16)) ≠ (256#16) ∧
    castFromSigned 16 (castFromSigned 8 (128#16)) ≠ (128#16) := by
  decide

end Toy.MachInt
