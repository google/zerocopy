/-
  MirCastKindSaturatingAndStrictProvenanceSoundness.lean

  Kernel-checked Lean v4.34.1 mechanization of rustc MIR `CastKind` lowering,
  two's-complement `IntToInt` (`sext`/`zext`/`trunc`), total saturating
  `FloatToInt` (`@llvm.fptosi.sat` / `@llvm.fptoui.sat`) vs. open-interval
  unchecked `float_to_int_unchecked`, IEEE-754 `IntToFloat` round-to-nearest
  ties-to-even (`roundTiesToEven`), `PtrToPtr` wide-to-thin data-pointer
  projection, and `PointerExposeProvenance` / `PointerWithExposedProvenance`
  vs. Strict Provenance (`addr` / `with_addr` / `without_provenance`).

  Primary-source anchors:
  - rust-lang/rust `compiler/rustc_middle/src/mir/syntax.rs` (`CastKind`)
  - rust-lang/rust `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`cast_immediate`, `codegen_rvalue_operand`, `transmute_scalar`)
  - rust-lang/rust `compiler/rustc_codegen_ssa/src/traits/builder.rs` (`cast_float_to_int`)
  - rust-lang/rust `compiler/rustc_codegen_llvm/src/builder.rs` (`fptosi_sat`, `fptoui_sat`, `intcast`, `sext`, `zext`, `trunc`)
  - rust-lang/rust `compiler/rustc_const_eval/src/interpret/cast.rs` (`cast_from_int_like`, `cast_from_float`, `ptr_to_ptr`, `pointer_expose_provenance_cast`, `pointer_with_exposed_provenance_cast`)
  - rust-lang/rust `src/tools/miri/src/alloc_addresses/mod.rs` (`ProvenanceMode`, `expose_provenance`, `ptr_from_addr_cast`, `alloc_id_from_addr`)
  - rust-lang/rust `library/core/src/ptr/{const_ptr.rs,mod.rs}` (`addr`, `with_addr`, `without_provenance`, `expose_provenance`, `with_exposed_provenance`)
  - llvm/llvm-project `llvm/docs/LangRef.md` (`@llvm.fptoui.sat.*`, `@llvm.fptosi.sat.*`, `trunc`, `zext`, `sext`, `uitofp`, `sitofp`, `ptrtoint`, `ptrtoaddr`, `inttoptr`)

  Lean Purity Contract:
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
    zero `native_decide`, zero `partial def`, zero `._unsafe_rec`, zero `deriving`,
    zero `noncomputable section`; every `def` is explicitly `noncomputable def`.
-/

namespace MirCastKindSoundness

/-! ## Section 1: Constructive Natural, Integer, and Dyadic-Truncation Foundations -/

/-- Structural boolean equality avoiding `BEq` typeclass synthesis. -/
noncomputable def boolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_refl (a : Bool) : boolEq a a = true := by
  cases a <;> rfl

theorem boolEq_eq {a b : Bool} (h : boolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- `2 ^ n > 0` for every natural exponent `n`. -/
theorem pow2_pos (n : Nat) : 0 < 2 ^ n :=
  Nat.pow_pos (Nat.succ_pos 1)

/-- Monotonicity of `2 ^ ·` on `Nat`. -/
theorem pow2_le_pow2 {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos 1) h

/-- Strict monotonicity of `2 ^ ·` on `Nat`. -/
theorem pow2_lt_pow2 {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : a + 1 ≤ b := h
  have h2 : 2 ^ (a + 1) ≤ 2 ^ b := pow2_le_pow2 h1
  have h3 : 2 ^ a < 2 ^ a + 2 ^ a := Nat.lt_add_of_pos_right (pow2_pos a)
  have h4 : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by
    rw [Nat.pow_succ, Nat.mul_two]
  rw [h4] at h2
  exact Nat.lt_of_lt_of_le h3 h2

/-- Divisibility `2 ^ a ∣ 2 ^ b` whenever `a ≤ b`. -/
theorem pow2_dvd_pow2 {a b : Nat} (h : a ≤ b) : 2 ^ a ∣ 2 ^ b := by
  have hk : ∃ k, b = a + k := ⟨b - a, (Nat.add_sub_of_le h).symm⟩
  cases hk with
  | intro k hk =>
    subst hk
    rw [Nat.pow_add]
    exact Nat.dvd_mul_right (2 ^ a) (2 ^ k)

/-- `2 ^ n = 2 * 2 ^ (n - 1)` for `0 < n`. -/
theorem pow2_eq_two_mul_pred {n : Nat} (h : 0 < n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  cases n with
  | zero => cases h
  | succ m =>
    rw [Nat.succ_sub_one, Nat.pow_succ, Nat.mul_comm]

/-- `2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n` for `0 < n`. -/
theorem pow2_pred_add_self {n : Nat} (h : 0 < n) : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
  rw [← Nat.two_mul, ← pow2_eq_two_mul_pred h]

/-- If `a < b` then `2 ^ a ≤ 2 ^ (b - 1)`. -/
theorem pow2_le_pow2_pred {a b : Nat} (h : a < b) : 2 ^ a ≤ 2 ^ (b - 1) := by
  cases b with
  | zero => cases h
  | succ m =>
    rw [Nat.succ_sub_one]
    exact pow2_le_pow2 (Nat.le_of_lt_succ h)

/-- Constructive truncation toward zero of `num / 2 ^ s` (`Round::TowardZero`). -/
noncomputable def truncDivPow2 (num : Int) (s : Nat) : Int :=
  match num with
  | .ofNat m => Int.ofNat (m / 2 ^ s)
  | .negSucc m => Int.neg (Int.ofNat ((m + 1) / 2 ^ s))

theorem truncDivPow2_zero_exp (num : Int) : truncDivPow2 num 0 = num := by
  cases num with
  | ofNat m =>
    change Int.ofNat (m / 2 ^ 0) = Int.ofNat m
    rw [Nat.pow_zero, Nat.div_one]
  | negSucc m =>
    change Int.neg (Int.ofNat ((m + 1) / 2 ^ 0)) = Int.negSucc m
    rw [Nat.pow_zero, Nat.div_one]
    rfl

theorem truncDivPow2_nonneg {m s : Nat} : 0 ≤ truncDivPow2 (Int.ofNat m) s := by
  unfold truncDivPow2
  exact Int.natCast_nonneg (m / 2 ^ s)

theorem truncDivPow2_nonpos_negSucc {m s : Nat} : truncDivPow2 (Int.negSucc m) s ≤ 0 := by
  change Int.neg (Int.ofNat ((m + 1) / 2 ^ s)) ≤ 0
  cases hq : (m + 1) / 2 ^ s with
  | zero => exact Int.le_refl 0
  | succ q =>
    have hneg : Int.neg (Int.ofNat (Nat.succ q)) = Int.negSucc q := rfl
    rw [hneg]
    exact Int.le_of_lt (Int.negSucc_lt_zero q)

/-- Exact characterization of `truncDivPow2 (.ofNat m) s`:
    `q * 2^s ≤ m < (q + 1) * 2^s`. -/
theorem nat_div_pow2_bounds (m s : Nat) :
    (m / 2 ^ s) * 2 ^ s ≤ m ∧ m < ((m / 2 ^ s) + 1) * 2 ^ s := by
  have hd : 0 < 2 ^ s := pow2_pos s
  have heq : 2 ^ s * (m / 2 ^ s) + m % 2 ^ s = m := Nat.div_add_mod m (2 ^ s)
  have hle : (m / 2 ^ s) * 2 ^ s ≤ m := by
    rw [Nat.mul_comm]
    exact Nat.le.intro heq
  have hmod : m % 2 ^ s < 2 ^ s := Nat.mod_lt m hd
  have hlt : m < ((m / 2 ^ s) + 1) * 2 ^ s := by
    have hstep : 2 ^ s * (m / 2 ^ s) + m % 2 ^ s < 2 ^ s * (m / 2 ^ s) + 2 ^ s :=
      Nat.add_lt_add_left hmod (2 ^ s * (m / 2 ^ s))
    rw [heq] at hstep
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (m / 2 ^ s) (2 ^ s)]
    exact hstep
  exact ⟨hle, hlt⟩

/-- Monotonicity of `truncDivPow2` with respect to `num₁ ≤ num₂`. -/
theorem truncDivPow2_mono {a b : Int} {s : Nat} (h : a ≤ b) :
    truncDivPow2 a s ≤ truncDivPow2 b s := by
  cases a with
  | ofNat ma =>
    cases b with
    | ofNat mb =>
      unfold truncDivPow2
      have hm : ma ≤ mb := Int.ofNat_le.mp h
      exact Int.ofNat_le.mpr (Nat.div_le_div_right hm)
    | negSucc mb =>
      have hbad : Int.ofNat ma < 0 := Int.lt_of_le_of_lt h (Int.negSucc_lt_zero mb)
      exact absurd hbad (Int.not_lt_of_ge (Int.natCast_nonneg ma))
  | negSucc ma =>
    cases b with
    | ofNat mb =>
      exact Int.le_trans truncDivPow2_nonpos_negSucc truncDivPow2_nonneg
    | negSucc mb =>
      unfold truncDivPow2
      have hsub : Int.negSucc ma ≤ Int.negSucc mb := h
      have hle : mb + 1 ≤ ma + 1 := by
        have hneg : Int.ofNat (mb + 1) ≤ Int.ofNat (ma + 1) := Int.neg_le_neg_iff.mp hsub
        exact Int.ofNat_le.mp hneg
      have hdiv : (mb + 1) / 2 ^ s ≤ (ma + 1) / 2 ^ s := Nat.div_le_div_right hle
      exact Int.neg_le_neg (Int.ofNat_le.mpr hdiv)

/-- Exact integer-comparison equivalence for non-negative `num`:
    `k ≤ truncDivPow2 (.ofNat m) s ↔ k * 2^s ≤ m`. -/
theorem int_le_truncDivPow2_ofNat_iff {k : Int} {m s : Nat} (hk : 0 ≤ k) :
    k ≤ truncDivPow2 (Int.ofNat m) s ↔ k * Int.ofNat (2 ^ s) ≤ Int.ofNat m := by
  cases k with
  | negSucc n => exact absurd hk (Int.not_le_of_gt (Int.negSucc_lt_zero n))
  | ofNat kn =>
    unfold truncDivPow2
    have hdiv : kn ≤ m / 2 ^ s ↔ kn * 2 ^ s ≤ m := by
      constructor
      · intro hkn
        have hm1 : kn * 2 ^ s ≤ (m / 2 ^ s) * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hkn
        exact Nat.le_trans hm1 (nat_div_pow2_bounds m s).1
      · intro hmul
        exact (Nat.le_div_iff_mul_le (pow2_pos s)).mpr hmul
    constructor
    · intro h
      have hkn : kn ≤ m / 2 ^ s := Int.ofNat_le.mp h
      change Int.ofNat (kn * 2 ^ s) ≤ Int.ofNat m
      exact Int.ofNat_le.mpr (hdiv.mp hkn)
    · intro h
      change Int.ofNat (kn * 2 ^ s) ≤ Int.ofNat m at h
      have hmul : kn * 2 ^ s ≤ m := Int.ofNat_le.mp h
      exact Int.ofNat_le.mpr (hdiv.mpr hmul)

/-- Scaling invariance: `(num * 2^k) / 2^(s + k)` truncated equals `num / 2^s` truncated. -/
theorem truncDivPow2_scale (num : Int) (s k : Nat) :
    truncDivPow2 (num * Int.ofNat (2 ^ k)) (s + k) = truncDivPow2 num s := by
  have hkpos : 0 < 2 ^ k := pow2_pos k
  have hpow : 2 ^ (s + k) = 2 ^ s * 2 ^ k := Nat.pow_add 2 s k
  cases num with
  | ofNat m =>
    change Int.ofNat ((m * 2 ^ k) / 2 ^ (s + k)) = Int.ofNat (m / 2 ^ s)
    rw [hpow, Nat.mul_div_mul_right m (2 ^ s) hkpos]
  | negSucc m =>
    have hmul : Int.negSucc m * Int.ofNat (2 ^ k) = Int.neg (Int.ofNat ((m + 1) * 2 ^ k)) := by
      change -(Int.ofNat (m + 1)) * Int.ofNat (2 ^ k) = -(Int.ofNat ((m + 1) * 2 ^ k))
      rw [Int.neg_mul]
      rfl
    rw [hmul]
    have hdiv : ((m + 1) * 2 ^ k) / 2 ^ (s + k) = (m + 1) / 2 ^ s := by
      rw [hpow, Nat.mul_div_mul_right (m + 1) (2 ^ s) hkpos]
    cases hz : (m + 1) * 2 ^ k with
    | zero =>
      have hbad : 0 < (m + 1) * 2 ^ k := Nat.mul_pos (Nat.succ_pos m) hkpos
      rw [hz] at hbad
      cases hbad
    | succ t =>
      have hneg : Int.neg (Int.ofNat (t + 1)) = Int.negSucc t := rfl
      rw [hneg]
      change Int.neg (Int.ofNat ((t + 1) / 2 ^ (s + k))) = Int.neg (Int.ofNat ((m + 1) / 2 ^ s))
      rw [← hz, hdiv]

/-! ## Section 2: `BitVec` `IntToInt` (`sext`, `zext`, `trunc`) Semantics and Asymmetry -/

/-- Check whether the sign bit (MSB) of `x : BitVec w` is `1` (`w > 0 ∧ 2^(w-1) ≤ x.toNat`). -/
noncomputable def bvIsNeg {w : Nat} (x : BitVec w) : Bool :=
  decide (0 < w) && decide (2 ^ (w - 1) ≤ x.toNat)

/-- Two's-complement mathematical integer interpretation of `x : BitVec w`. -/
noncomputable def bvToInt {w : Nat} (x : BitVec w) : Int :=
  if bvIsNeg x then
    Int.ofNat x.toNat - Int.ofNat (2 ^ w)
  else
    Int.ofNat x.toNat

/-- Zero-extension or truncation of `x : BitVec srcW` to `dstW` bits (`zext`/`trunc`). -/
noncomputable def bvZeroExtend (dstW : Nat) {srcW : Nat} (x : BitVec srcW) : BitVec dstW :=
  BitVec.ofNat dstW x.toNat

/-- Truncation of `x : BitVec srcW` to `dstW` bits (`trunc`). -/
noncomputable def bvTruncate (dstW : Nat) {srcW : Nat} (x : BitVec srcW) : BitVec dstW :=
  BitVec.ofNat dstW x.toNat

/-- Sign-extension (for `srcW < dstW`) or truncation (for `dstW ≤ srcW`) of `x : BitVec srcW`
    to `dstW` bits (`sext`/`trunc`), matching `rustc_codegen_ssa::mir::rvalue::cast_immediate`
    (`bx.intcast(imm, to_backend_ty, is_signed)`). -/
noncomputable def bvSignExtend (dstW : Nat) {srcW : Nat} (x : BitVec srcW) : BitVec dstW :=
  if bvIsNeg x && decide (srcW < dstW) then
    BitVec.ofNat dstW (x.toNat + (2 ^ dstW - 2 ^ srcW))
  else
    BitVec.ofNat dstW x.toNat

/-- Unified MIR `CastKind::IntToInt` lowering parameterized by source signedness `srcSigned`. -/
noncomputable def castIntToInt (srcSigned : Bool) (srcW dstW : Nat) (x : BitVec srcW) :
    BitVec dstW :=
  if srcSigned then bvSignExtend dstW x else bvZeroExtend dstW x

/-- MIR `CastKind::IntToInt` lowering from `bool` (`zext i1 %b to iN`). -/
noncomputable def castBoolToInt (dstW : Nat) (b : Bool) : BitVec dstW :=
  BitVec.ofNat dstW (if b then 1 else 0)

theorem bvZeroExtend_eq_trunc {srcW dstW : Nat} (x : BitVec srcW) :
    bvZeroExtend dstW x = bvTruncate dstW x := rfl

/-- Same-width `IntToInt` cast is an exact identity regardless of `srcSigned`
    (`rust-lang/reference` `r[expr.as.numeric.int-same-size]`). -/
theorem castIntToInt_same_width_noop (srcSigned : Bool) (w : Nat) (x : BitVec w) :
    castIntToInt srcSigned w w x = x := by
  have hlt : ¬ (w < w) := Nat.lt_irrefl w
  have hdec : decide (w < w) = false := decide_eq_false hlt
  apply BitVec.toNat_eq.mpr
  cases srcSigned
  · change (BitVec.ofNat w x.toNat).toNat = x.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]
  · change (if bvIsNeg x && decide (w < w) then BitVec.ofNat w (x.toNat + (2 ^ w - 2 ^ w))
            else BitVec.ofNat w x.toNat).toNat = x.toNat
    rw [hdec, Bool.and_false]
    change (BitVec.ofNat w x.toNat).toNat = x.toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-- Narrowing or equal-width `IntToInt` (`dstW ≤ srcW`) truncates identically to `bvTruncate`
    regardless of source signedness (`cast_from_int_like` `size.truncate(v)`). -/
theorem castIntToInt_narrow_truncates_independently_of_sign
    {srcW dstW : Nat} (h : dstW ≤ srcW) (x : BitVec srcW) :
    castIntToInt true srcW dstW x = bvTruncate dstW x ∧
    castIntToInt false srcW dstW x = bvTruncate dstW x := by
  have hnotlt : ¬ (srcW < dstW) := Nat.not_lt_of_ge h
  have hdec : decide (srcW < dstW) = false := decide_eq_false hnotlt
  constructor
  · change (if bvIsNeg x && decide (srcW < dstW) then _ else BitVec.ofNat dstW x.toNat) =
      BitVec.ofNat dstW x.toNat
    rw [hdec, Bool.and_false]
    rfl
  · rfl

/-- Narrowing truncation composition: `w₃ ≤ w₂ ≤ w₁` collapses consecutive truncations
    to a single direct truncation (`castIntToInt s₂ w₂ w₃ (castIntToInt s₁ w₁ w₂ x)`). -/
theorem castIntToInt_trunc_composition
    (s₁ s₂ : Bool) {w₁ w₂ w₃ : Nat}
    (h₃₂ : w₃ ≤ w₂) (h₂₁ : w₂ ≤ w₁) (x : BitVec w₁) :
    castIntToInt s₂ w₂ w₃ (castIntToInt s₁ w₁ w₂ x) =
      castIntToInt s₁ w₁ w₃ x := by
  have h₃₁ : w₃ ≤ w₁ := Nat.le_trans h₃₂ h₂₁
  have hleft1 := castIntToInt_narrow_truncates_independently_of_sign h₂₁ x
  have hmid : castIntToInt s₁ w₁ w₂ x = bvTruncate w₂ x := by
    cases s₁
    · exact hleft1.2
    · exact hleft1.1
  rw [hmid]
  have hleft2 := castIntToInt_narrow_truncates_independently_of_sign h₃₂ (bvTruncate w₂ x)
  have hstep2 : castIntToInt s₂ w₂ w₃ (bvTruncate w₂ x) = bvTruncate w₃ (bvTruncate w₂ x) := by
    cases s₂
    · exact hleft2.2
    · exact hleft2.1
  have hright := castIntToInt_narrow_truncates_independently_of_sign h₃₁ x
  have hr : castIntToInt s₁ w₁ w₃ x = bvTruncate w₃ x := by
    cases s₁
    · exact hright.2
    · exact hright.1
  rw [hstep2, hr]
  apply BitVec.toNat_eq.mpr
  change (BitVec.ofNat w₃ (BitVec.ofNat w₂ x.toNat).toNat).toNat = (BitVec.ofNat w₃ x.toNat).toNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd x.toNat (pow2_dvd_pow2 h₃₂)

/-- Zero-extension `bvZeroExtend` preserves `.toNat` exactly whenever `srcW ≤ dstW`. -/
theorem bvZeroExtend_toNat_of_le {srcW dstW : Nat} (h : srcW ≤ dstW) (x : BitVec srcW) :
    (bvZeroExtend dstW x).toNat = x.toNat := by
  change (BitVec.ofNat dstW x.toNat).toNat = x.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (pow2_le_pow2 h))

/-- Zero-extension preserves `bvIsNeg = false` when widening strictly (`srcW < dstW`). -/
theorem bvZeroExtend_strict_nonneg {srcW dstW : Nat} (h : srcW < dstW) (x : BitVec srcW) :
    bvIsNeg (bvZeroExtend dstW x) = false := by
  have htonat : (bvZeroExtend dstW x).toNat = x.toNat :=
    bvZeroExtend_toNat_of_le (Nat.le_of_lt h) x
  have hpow : 2 ^ srcW ≤ 2 ^ (dstW - 1) := pow2_le_pow2_pred h
  have hlt : x.toNat < 2 ^ (dstW - 1) := Nat.lt_of_lt_of_le x.isLt hpow
  have hnotle : ¬ (2 ^ (dstW - 1) ≤ (bvZeroExtend dstW x).toNat) := by
    rw [htonat]
    exact Nat.not_le_of_gt hlt
  unfold bvIsNeg
  rw [decide_eq_false hnotle, Bool.and_false]

/-- Chained zero-extensions (`w₁ ≤ w₂ ≤ w₃`) compose into a single zero-extension. -/
theorem castIntToInt_zext_composition
    {w₁ w₂ w₃ : Nat} (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (x : BitVec w₁) :
    castIntToInt false w₂ w₃ (castIntToInt false w₁ w₂ x) =
      castIntToInt false w₁ w₃ x := by
  apply BitVec.toNat_eq.mpr
  change (bvZeroExtend w₃ (bvZeroExtend w₂ x)).toNat = (bvZeroExtend w₃ x).toNat
  rw [bvZeroExtend_toNat_of_le h₂₃, bvZeroExtend_toNat_of_le h₁₂,
      bvZeroExtend_toNat_of_le (Nat.le_trans h₁₂ h₂₃)]

/-- When `bvIsNeg x = false` (non-negative two's complement), `sext` equals `zext` at any width. -/
theorem castIntToInt_sext_eq_zext_of_nonneg
    {srcW dstW : Nat} {x : BitVec srcW} (h : bvIsNeg x = false) :
    castIntToInt true srcW dstW x = castIntToInt false srcW dstW x := by
  change (if bvIsNeg x && decide (srcW < dstW) then _ else BitVec.ofNat dstW x.toNat) =
    BitVec.ofNat dstW x.toNat
  rw [h, Bool.false_and]
  rfl

/-- Exact `.toNat` value of `bvSignExtend` when `0 < srcW < dstW` and `bvIsNeg x = true`. -/
theorem bvSignExtend_neg_toNat {srcW dstW : Nat} (hpos : 0 < srcW) (hlt : srcW < dstW)
    (x : BitVec srcW) (hneg : bvIsNeg x = true) :
    (bvSignExtend dstW x).toNat = x.toNat + (2 ^ dstW - 2 ^ srcW) := by
  have hdec : decide (srcW < dstW) = true := decide_eq_true hlt
  have hpow : 2 ^ srcW ≤ 2 ^ dstW := pow2_le_pow2 (Nat.le_of_lt hlt)
  have hbound : x.toNat + (2 ^ dstW - 2 ^ srcW) < 2 ^ dstW := by
    have hsum : x.toNat + (2 ^ dstW - 2 ^ srcW) < 2 ^ srcW + (2 ^ dstW - 2 ^ srcW) :=
      Nat.add_lt_add_right x.isLt (2 ^ dstW - 2 ^ srcW)
    rw [Nat.add_sub_of_le hpow] at hsum
    exact hsum
  have _ := hpos
  unfold bvSignExtend
  rw [hneg, hdec]
  change (BitVec.ofNat dstW (x.toNat + (2 ^ dstW - 2 ^ srcW))).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]

/-- Sign-extension preserves `bvIsNeg` for all `0 < srcW ≤ dstW`. -/
theorem bvSignExtend_preserves_bvIsNeg {srcW dstW : Nat}
    (hpos : 0 < srcW) (hle : srcW ≤ dstW) (x : BitVec srcW) :
    bvIsNeg (bvSignExtend dstW x) = bvIsNeg x := by
  cases hlt : decide (srcW < dstW) with
  | false =>
    have hnotlt : ¬ (srcW < dstW) := of_decide_eq_false hlt
    have heq : srcW = dstW := Nat.le_antisymm hle (Nat.ge_of_not_lt hnotlt)
    subst heq
    have hnoop : bvSignExtend srcW x = x := castIntToInt_same_width_noop true srcW x
    rw [hnoop]
  | true =>
    have hlt' : srcW < dstW := of_decide_eq_true hlt
    have hdstpos : 0 < dstW := Nat.lt_trans hpos hlt'
    cases hneg : bvIsNeg x with
    | false =>
      have hsext : bvSignExtend dstW x = bvZeroExtend dstW x :=
        castIntToInt_sext_eq_zext_of_nonneg hneg
      rw [hsext]
      exact bvZeroExtend_strict_nonneg hlt' x
    | true =>
      have htonat := bvSignExtend_neg_toNat hpos hlt' x hneg
      have hsrc_ge : 2 ^ srcW ≤ 2 ^ (dstW - 1) := pow2_le_pow2_pred hlt'
      have hdst_half : 2 ^ dstW - 2 ^ (dstW - 1) = 2 ^ (dstW - 1) := by
        have h2 : 2 ^ dstW = 2 ^ (dstW - 1) + 2 ^ (dstW - 1) := (pow2_pred_add_self hdstpos).symm
        rw [h2, Nat.add_sub_cancel]
      have hsub_ge : 2 ^ (dstW - 1) ≤ 2 ^ dstW - 2 ^ srcW := by
        rw [← hdst_half]
        exact Nat.sub_le_sub_left hsrc_ge (2 ^ dstW)
      have hge : 2 ^ (dstW - 1) ≤ (bvSignExtend dstW x).toNat := by
        rw [htonat]
        exact Nat.le_trans hsub_ge (Nat.le_add_left (2 ^ dstW - 2 ^ srcW) x.toNat)
      unfold bvIsNeg
      rw [decide_eq_true hdstpos, decide_eq_true hge]
      rfl

/-- Sign-extension preserves exact mathematical two's-complement integer value `bvToInt`
    for all `0 < srcW ≤ dstW`. -/
theorem bvSignExtend_preserves_bvToInt {srcW dstW : Nat}
    (hpos : 0 < srcW) (hle : srcW ≤ dstW) (x : BitVec srcW) :
    bvToInt (bvSignExtend dstW x) = bvToInt x := by
  cases hlt : decide (srcW < dstW) with
  | false =>
    have hnotlt : ¬ (srcW < dstW) := of_decide_eq_false hlt
    have heq : srcW = dstW := Nat.le_antisymm hle (Nat.ge_of_not_lt hnotlt)
    subst heq
    have hnoop : bvSignExtend srcW x = x := castIntToInt_same_width_noop true srcW x
    rw [hnoop]
  | true =>
    have hlt' : srcW < dstW := of_decide_eq_true hlt
    have hneg_pres : bvIsNeg (bvSignExtend dstW x) = bvIsNeg x :=
      bvSignExtend_preserves_bvIsNeg hpos hle x
    unfold bvToInt
    rw [hneg_pres]
    cases hneg : bvIsNeg x with
    | false =>
      have hsext : bvSignExtend dstW x = bvZeroExtend dstW x :=
        castIntToInt_sext_eq_zext_of_nonneg hneg
      rw [hsext, bvZeroExtend_toNat_of_le hle x]
      rfl
    | true =>
      have htonat := bvSignExtend_neg_toNat hpos hlt' x hneg
      change (if true = true then Int.ofNat (bvSignExtend dstW x).toNat - Int.ofNat (2 ^ dstW)
              else Int.ofNat (bvSignExtend dstW x).toNat) =
             (if true = true then Int.ofNat x.toNat - Int.ofNat (2 ^ srcW)
              else Int.ofNat x.toNat)
      rw [htonat]
      have hpow : 2 ^ srcW ≤ 2 ^ dstW := pow2_le_pow2 hle
      have hnat : Int.ofNat (2 ^ dstW - 2 ^ srcW) = Int.ofNat (2 ^ dstW) - Int.ofNat (2 ^ srcW) :=
        Int.ofNat_sub hpow
      change (Int.ofNat x.toNat + Int.ofNat (2 ^ dstW - 2 ^ srcW)) - Int.ofNat (2 ^ dstW) =
        Int.ofNat x.toNat - Int.ofNat (2 ^ srcW)
      rw [hnat, Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
      rw [Int.add_assoc (Int.ofNat x.toNat)]
      rw [Int.add_comm (Int.ofNat (2 ^ dstW)) (-Int.ofNat (2 ^ srcW))]
      rw [Int.add_assoc (-Int.ofNat (2 ^ srcW)) (Int.ofNat (2 ^ dstW)) (-Int.ofNat (2 ^ dstW))]
      rw [← @Int.sub_eq_add_neg (Int.ofNat (2 ^ dstW)) (Int.ofNat (2 ^ dstW)), Int.sub_self, Int.add_zero]

/-- Chained sign-extensions (`0 < w₁ ≤ w₂ ≤ w₃`) compose into a single sign-extension. -/
theorem castIntToInt_sext_composition
    {w₁ w₂ w₃ : Nat} (hpos : 0 < w₁) (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (x : BitVec w₁) :
    castIntToInt true w₂ w₃ (castIntToInt true w₁ w₂ x) =
      castIntToInt true w₁ w₃ x := by
  have h₁₃ : w₁ ≤ w₃ := Nat.le_trans h₁₂ h₂₃
  have h₂pos : 0 < w₂ := Nat.lt_of_lt_of_le hpos h₁₂
  apply BitVec.toNat_eq.mpr
  cases hlt₁₂ : decide (w₁ < w₂) with
  | false =>
    have heq : w₁ = w₂ := Nat.le_antisymm h₁₂ (Nat.ge_of_not_lt (of_decide_eq_false hlt₁₂))
    subst heq
    have hnoop : castIntToInt true w₁ w₁ x = x := castIntToInt_same_width_noop true w₁ x
    rw [hnoop]
  | true =>
    cases hlt₂₃ : decide (w₂ < w₃) with
    | false =>
      have heq : w₂ = w₃ := Nat.le_antisymm h₂₃ (Nat.ge_of_not_lt (of_decide_eq_false hlt₂₃))
      subst heq
      have hnoop : castIntToInt true w₂ w₂ (castIntToInt true w₁ w₂ x) = castIntToInt true w₁ w₂ x :=
        castIntToInt_same_width_noop true w₂ _
      rw [hnoop]
    | true =>
      have hlt₁₂' : w₁ < w₂ := of_decide_eq_true hlt₁₂
      have hlt₂₃' : w₂ < w₃ := of_decide_eq_true hlt₂₃
      have hlt₁₃' : w₁ < w₃ := Nat.lt_trans hlt₁₂' hlt₂₃'
      cases hneg : bvIsNeg x with
      | false =>
        have hs1 : castIntToInt true w₁ w₂ x = bvZeroExtend w₂ x :=
          castIntToInt_sext_eq_zext_of_nonneg hneg
        have hneg2 : bvIsNeg (bvZeroExtend w₂ x) = false := bvZeroExtend_strict_nonneg hlt₁₂' x
        have hs2 : castIntToInt true w₂ w₃ (bvZeroExtend w₂ x) = bvZeroExtend w₃ (bvZeroExtend w₂ x) :=
          castIntToInt_sext_eq_zext_of_nonneg hneg2
        have hs3 : castIntToInt true w₁ w₃ x = bvZeroExtend w₃ x :=
          castIntToInt_sext_eq_zext_of_nonneg hneg
        rw [hs1, hs2, hs3, bvZeroExtend_toNat_of_le h₂₃, bvZeroExtend_toNat_of_le h₁₂,
            bvZeroExtend_toNat_of_le h₁₃]
      | true =>
        have hneg2 : bvIsNeg (bvSignExtend w₂ x) = true := by
          rw [bvSignExtend_preserves_bvIsNeg hpos h₁₂ x, hneg]
        change (bvSignExtend w₃ (bvSignExtend w₂ x)).toNat = (bvSignExtend w₃ x).toNat
        rw [bvSignExtend_neg_toNat h₂pos hlt₂₃' (bvSignExtend w₂ x) hneg2,
            bvSignExtend_neg_toNat hpos hlt₁₂' x hneg,
            bvSignExtend_neg_toNat hpos hlt₁₃' x hneg]
        have hp12 : 2 ^ w₁ ≤ 2 ^ w₂ := pow2_le_pow2 h₁₂
        have hp23 : 2 ^ w₂ ≤ 2 ^ w₃ := pow2_le_pow2 h₂₃
        rw [Nat.add_assoc, Nat.add_comm (2 ^ w₂ - 2 ^ w₁) (2 ^ w₃ - 2 ^ w₂)]
        rw [← Nat.add_sub_assoc hp12 (2 ^ w₃ - 2 ^ w₂), Nat.sub_add_cancel hp23]

/-- Exact `sext` vs. `zext` asymmetry on negative inputs (`0 < w₁ < w₂`, `bvIsNeg x = true`):
    `sext` adds `(2^w₂ - 2^w₁) > 0` to `x.toNat`, so the widened bitvectors strictly differ. -/
theorem castIntToInt_sext_vs_zext_neg_exact
    {w₁ w₂ : Nat} (hpos : 0 < w₁) (hlt : w₁ < w₂) (x : BitVec w₁) (hneg : bvIsNeg x = true) :
    (castIntToInt true w₁ w₂ x).toNat = x.toNat + (2 ^ w₂ - 2 ^ w₁) ∧
    (castIntToInt false w₁ w₂ x).toNat = x.toNat ∧
    castIntToInt true w₁ w₂ x ≠ castIntToInt false w₁ w₂ x := by
  have h1 : (castIntToInt true w₁ w₂ x).toNat = x.toNat + (2 ^ w₂ - 2 ^ w₁) :=
    bvSignExtend_neg_toNat hpos hlt x hneg
  have h2 : (castIntToInt false w₁ w₂ x).toNat = x.toNat :=
    bvZeroExtend_toNat_of_le (Nat.le_of_lt hlt) x
  refine ⟨h1, h2, ?_⟩
  intro heq
  have hnat : (castIntToInt true w₁ w₂ x).toNat = (castIntToInt false w₁ w₂ x).toNat := by
    rw [heq]
  rw [h1, h2] at hnat
  have hdiff_pos : 0 < 2 ^ w₂ - 2 ^ w₁ := Nat.sub_pos_of_lt (pow2_lt_pow2 hlt)
  have hlt_add : x.toNat < x.toNat + (2 ^ w₂ - 2 ^ w₁) := Nat.lt_add_of_pos_right hdiff_pos
  rw [hnat] at hlt_add
  exact Nat.lt_irrefl x.toNat hlt_add

/-- Widening followed by narrowing back to original width `w₁` recovers `x` losslessly,
    regardless of source and target signedness `s₁, s₂`. -/
theorem castIntToInt_widen_then_narrow_roundtrip
    (s₁ s₂ : Bool) {w₁ w₂ : Nat} (hpos : 0 < w₁) (hle : w₁ ≤ w₂) (x : BitVec w₁) :
    castIntToInt s₂ w₂ w₁ (castIntToInt s₁ w₁ w₂ x) = x := by
  have hn := castIntToInt_narrow_truncates_independently_of_sign hle (castIntToInt s₁ w₁ w₂ x)
  have hstep : castIntToInt s₂ w₂ w₁ (castIntToInt s₁ w₁ w₂ x) =
      bvTruncate w₁ (castIntToInt s₁ w₁ w₂ x) := by
    cases s₂
    · exact hn.2
    · exact hn.1
  rw [hstep]
  apply BitVec.toNat_eq.mpr
  change (BitVec.ofNat w₁ (castIntToInt s₁ w₁ w₂ x).toNat).toNat = x.toNat
  rw [BitVec.toNat_ofNat]
  cases s₁ with
  | false =>
    change (bvZeroExtend w₂ x).toNat % 2 ^ w₁ = x.toNat
    rw [bvZeroExtend_toNat_of_le hle x, Nat.mod_eq_of_lt x.isLt]
  | true =>
    cases hlt : decide (w₁ < w₂) with
    | false =>
      have heq : w₁ = w₂ := Nat.le_antisymm hle (Nat.ge_of_not_lt (of_decide_eq_false hlt))
      subst heq
      rw [castIntToInt_same_width_noop true w₁ x, Nat.mod_eq_of_lt x.isLt]
    | true =>
      have hlt' : w₁ < w₂ := of_decide_eq_true hlt
      cases hneg : bvIsNeg x with
      | false =>
        have hsext : castIntToInt true w₁ w₂ x = bvZeroExtend w₂ x :=
          castIntToInt_sext_eq_zext_of_nonneg hneg
        rw [hsext, bvZeroExtend_toNat_of_le hle x, Nat.mod_eq_of_lt x.isLt]
      | true =>
        change (bvSignExtend w₂ x).toNat % 2 ^ w₁ = x.toNat
        rw [bvSignExtend_neg_toNat hpos hlt' x hneg]
        have hdvd : 2 ^ w₁ ∣ 2 ^ w₂ - 2 ^ w₁ := by
          have hsub : 2 ^ w₂ - 2 ^ w₁ = 2 ^ w₁ * (2 ^ (w₂ - w₁) - 1) := by
            have hk : w₂ = w₁ + (w₂ - w₁) := (Nat.add_sub_of_le hle).symm
            have hpow_eq : 2 ^ w₂ = 2 ^ w₁ * 2 ^ (w₂ - w₁) := by
              rw [← Nat.pow_add, ← hk]
            symm
            rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← hpow_eq]
          rw [hsub]
          exact Nat.dvd_mul_right (2 ^ w₁) (2 ^ (w₂ - w₁) - 1)
        cases hdvd with
        | intro q hq =>
          rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]

/-- Witness matching live `rustc` IR & execution (`cast_i8_u32` vs `cast_i8_u8_u32` vs `cast_u32_i8`):
    `-1i8 as u32 = 0xffffffff`, `(-1i8 as u8) as u32 = 255`, `0x12345678u32 as i8 = 0x78`. -/
theorem witness_intToInt_asymmetry_and_trunc :
    let negOneI8 : BitVec 8 := BitVec.ofNat 8 255
    castIntToInt true 8 32 negOneI8 = BitVec.ofNat 32 0xffffffff ∧
    castIntToInt false 8 32 (castIntToInt true 8 8 negOneI8) = BitVec.ofNat 32 255 ∧
    castIntToInt false 32 8 (BitVec.ofNat 32 0x12345678) = BitVec.ofNat 8 0x78 ∧
    castBoolToInt 32 true = BitVec.ofNat 32 1 ∧
    castBoolToInt 32 false = BitVec.ofNat 32 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 3: Exact Dyadic Floats, Total Saturating `FloatToInt`, and Open-Interval Refinement -/

/-- Exact dyadic rational `num / 2 ^ exp`, representing any finite IEEE-754 value without
    rounding loss or classical real numbers. -/
structure Dyadic where
  num : Int
  exp : Nat

/-- Constructive dyadic embedding of an exact mathematical integer `z`. -/
noncomputable def dyadicOfInt (z : Int) : Dyadic :=
  { num := z, exp := 0 }

/-- Exact ordering `a ≤ b` on dyadic rationals (`a.num * 2^b.exp ≤ b.num * 2^a.exp`). -/
noncomputable def dyadicLe (a b : Dyadic) : Prop :=
  a.num * Int.ofNat (2 ^ b.exp) ≤ b.num * Int.ofNat (2 ^ a.exp)

/-- Exact strict ordering `a < b` on dyadic rationals (`a.num * 2^b.exp < b.num * 2^a.exp`). -/
noncomputable def dyadicLt (a b : Dyadic) : Prop :=
  a.num * Int.ofNat (2 ^ b.exp) < b.num * Int.ofNat (2 ^ a.exp)

/-- IEEE-754 floating-point value domain preserving NaN sign/quietness/payload,
    signed infinities, and exact finite dyadics. -/
inductive FloatVal where
  | nan (sign : Bool) (isQuiet : Bool) (payload : Nat)
  | inf (neg : Bool)
  | finite (d : Dyadic)

/-- Ordering relation on non-NaN `FloatVal` (`-∞ ≤ finite d₁ ≤ finite d₂ ≤ +∞`). -/
noncomputable def floatOrderedLe : FloatVal → FloatVal → Prop
  | .inf true, .inf true => True
  | .inf true, .finite _ => True
  | .inf true, .inf false => True
  | .finite d₁, .finite d₂ => dyadicLe d₁ d₂
  | .finite _, .inf false => True
  | .inf false, .inf false => True
  | _, _ => False

/-- Minimum integer representable at width `w` (`0` if unsigned, `-2^(w-1)` if signed). -/
noncomputable def intMin (signed : Bool) (w : Nat) : Int :=
  if signed then Int.neg (Int.ofNat (2 ^ (w - 1))) else 0

/-- Maximum integer representable at width `w` (`2^w - 1` if unsigned, `2^(w-1) - 1` if signed). -/
noncomputable def intMax (signed : Bool) (w : Nat) : Int :=
  if signed then Int.ofNat (2 ^ (w - 1)) - 1 else Int.ofNat (2 ^ w) - 1

/-- Clamp `x : Int` into closed interval `[lo, hi]`. -/
noncomputable def clampInt (lo hi x : Int) : Int :=
  match decide (x < lo) with
  | true => lo
  | false =>
    match decide (hi < x) with
    | true => hi
    | false => x

/-- Total saturating `CastKind::FloatToInt` mathematical result, modeling LLVM
    `@llvm.fptosi.sat.*` / `@llvm.fptoui.sat.*` and `rustc_apfloat`'s `to_i128` / `to_u128`. -/
noncomputable def satFloatToInt (signed : Bool) (w : Nat) (f : FloatVal) : Int :=
  match f with
  | .nan _ _ _ => 0
  | .inf true => intMin signed w
  | .inf false => intMax signed w
  | .finite d => clampInt (intMin signed w) (intMax signed w) (truncDivPow2 d.num d.exp)

/-- Bitvector-typed saturating `CastKind::FloatToInt` result (`BitVec w`). -/
noncomputable def satFloatToIntBV (signed : Bool) (w : Nat) (f : FloatVal) : BitVec w :=
  BitVec.ofInt w (satFloatToInt signed w f)

/-- Unchecked truncating conversion (`core::intrinsics::float_to_int_unchecked` / LLVM
    `fptosi` + `noundef`), returning `none` (UB) for NaN, `±Inf`, or truncated out-of-range. -/
noncomputable def uncheckedFloatToInt (signed : Bool) (w : Nat) (f : FloatVal) : Option Int :=
  match f with
  | .nan _ _ _ => none
  | .inf _ => none
  | .finite d =>
    let q := truncDivPow2 d.num d.exp
    if decide (intMin signed w ≤ q) && decide (q ≤ intMax signed w) then
      some q
    else
      none

/-- Open rational interval `(intMin - 1, intMax + 1)` governing `float_to_int_unchecked`. -/
noncomputable def inOpenInterval (signed : Bool) (w : Nat) (d : Dyadic) : Prop :=
  dyadicLt (dyadicOfInt (intMin signed w - 1)) d ∧
  dyadicLt d (dyadicOfInt (intMax signed w + 1))

theorem intMin_le_zero (signed : Bool) (w : Nat) : intMin signed w ≤ 0 := by
  unfold intMin
  cases signed with
  | false => exact Int.le_refl 0
  | true =>
    cases h : 2 ^ (w - 1) with
    | zero => exact Int.le_refl 0
    | succ k =>
      change Int.negSucc k ≤ 0
      exact Int.le_of_lt (Int.negSucc_lt_zero k)

theorem zero_le_intMax (signed : Bool) {w : Nat} (_hw : 0 < w) : 0 ≤ intMax signed w := by
  unfold intMax
  cases signed with
  | false =>
    have hp : 1 ≤ 2 ^ w := pow2_pos w
    have hsub : Int.ofNat (2 ^ w) - 1 = Int.ofNat (2 ^ w - 1) := (Int.ofNat_sub hp).symm
    change 0 ≤ Int.ofNat (2 ^ w) - 1
    rw [hsub]
    exact Int.natCast_nonneg (2 ^ w - 1)
  | true =>
    have hp : 1 ≤ 2 ^ (w - 1) := pow2_pos (w - 1)
    have hsub : Int.ofNat (2 ^ (w - 1)) - 1 = Int.ofNat (2 ^ (w - 1) - 1) := (Int.ofNat_sub hp).symm
    change 0 ≤ Int.ofNat (2 ^ (w - 1)) - 1
    rw [hsub]
    exact Int.natCast_nonneg (2 ^ (w - 1) - 1)

theorem intMin_le_intMax (signed : Bool) {w : Nat} (hw : 0 < w) :
    intMin signed w ≤ intMax signed w :=
  Int.le_trans (intMin_le_zero signed w) (zero_le_intMax signed hw)

theorem clampInt_bounds {lo hi x : Int} (h : lo ≤ hi) :
    lo ≤ clampInt lo hi x ∧ clampInt lo hi x ≤ hi := by
  unfold clampInt
  cases hlt1 : decide (x < lo) with
  | true =>
    dsimp only
    exact ⟨Int.le_refl lo, h⟩
  | false =>
    have hnot1 : ¬ (x < lo) := of_decide_eq_false hlt1
    have hge : lo ≤ x := Int.not_lt.mp hnot1
    dsimp only
    cases hlt2 : decide (hi < x) with
    | true =>
      dsimp only
      exact ⟨h, Int.le_refl hi⟩
    | false =>
      have hnot2 : ¬ (hi < x) := of_decide_eq_false hlt2
      dsimp only
      exact ⟨hge, Int.not_lt.mp hnot2⟩

theorem clampInt_mono {lo hi x₁ x₂ : Int} (hlh : lo ≤ hi) (h : x₁ ≤ x₂) :
    clampInt lo hi x₁ ≤ clampInt lo hi x₂ := by
  unfold clampInt
  cases h1 : decide (x₁ < lo) with
  | true =>
    dsimp only
    exact (clampInt_bounds hlh).1
  | false =>
    have hn1 : ¬ (x₁ < lo) := of_decide_eq_false h1
    have hge1 : lo ≤ x₁ := Int.not_lt.mp hn1
    have hge2 : lo ≤ x₂ := Int.le_trans hge1 h
    have h2 : decide (x₂ < lo) = false := decide_eq_false (Int.not_lt.mpr hge2)
    rw [h2]
    dsimp only
    cases h3 : decide (hi < x₁) with
    | true =>
      have h3' : hi < x₁ := of_decide_eq_true h3
      have h4' : hi < x₂ := Int.lt_of_lt_of_le h3' h
      have h4 : decide (hi < x₂) = true := decide_eq_true h4'
      rw [h4]
      exact Int.le_refl hi
    | false =>
      have hn3 : ¬ (hi < x₁) := of_decide_eq_false h3
      dsimp only
      cases h4 : decide (hi < x₂) with
      | true =>
        dsimp only
        exact Int.not_lt.mp hn3
      | false =>
        dsimp only
        exact h

/-- Total UB-freedom and range invariance: for every `0 < w` and ANY `FloatVal`,
    `satFloatToInt` yields a valid integer strictly inside `[intMin signed w, intMax signed w]`. -/
theorem satFloatToInt_bounds (signed : Bool) {w : Nat} (hw : 0 < w) (f : FloatVal) :
    intMin signed w ≤ satFloatToInt signed w f ∧
    satFloatToInt signed w f ≤ intMax signed w := by
  cases f with
  | nan _ _ _ =>
    unfold satFloatToInt
    exact ⟨intMin_le_zero signed w, zero_le_intMax signed hw⟩
  | inf neg =>
    cases neg with
    | false => exact ⟨intMin_le_intMax signed hw, Int.le_refl _⟩
    | true => exact ⟨Int.le_refl _, intMin_le_intMax signed hw⟩
  | finite d =>
    unfold satFloatToInt
    exact clampInt_bounds (intMin_le_intMax signed hw)

/-- Any NaN (quiet or signaling, either sign, any payload) saturates to `0`. -/
theorem satFloatToInt_nan_zero (signed : Bool) (w : Nat)
    (sign isQuiet : Bool) (payload : Nat) :
    satFloatToInt signed w (.nan sign isQuiet payload) = 0 := rfl

/-- `+Inf` saturates to `intMax signed w`; `-Inf` saturates to `intMin signed w` (`0` for unsigned). -/
theorem satFloatToInt_inf_clamps (signed : Bool) (w : Nat) :
    satFloatToInt signed w (.inf false) = intMax signed w ∧
    satFloatToInt signed w (.inf true) = intMin signed w := ⟨rfl, rfl⟩

/-- Finite clamping cases for `satFloatToInt`: below `MIN -> MIN`, above `MAX -> MAX`,
    inside `[MIN, MAX] -> truncTowardZero d`. -/
theorem satFloatToInt_finite_clamps (signed : Bool) {w : Nat} (hw : 0 < w) (d : Dyadic) :
    (truncDivPow2 d.num d.exp < intMin signed w →
      satFloatToInt signed w (.finite d) = intMin signed w) ∧
    (intMax signed w < truncDivPow2 d.num d.exp →
      satFloatToInt signed w (.finite d) = intMax signed w) ∧
    (intMin signed w ≤ truncDivPow2 d.num d.exp →
      truncDivPow2 d.num d.exp ≤ intMax signed w →
      satFloatToInt signed w (.finite d) = truncDivPow2 d.num d.exp) := by
  have hbounds : intMin signed w ≤ intMax signed w := intMin_le_intMax signed hw
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    have hdec : decide (truncDivPow2 d.num d.exp < intMin signed w) = true := decide_eq_true hlt
    change clampInt (intMin signed w) (intMax signed w) (truncDivPow2 d.num d.exp) = intMin signed w
    unfold clampInt
    rw [hdec]
  · intro hgt
    have hnlt : decide (truncDivPow2 d.num d.exp < intMin signed w) = false :=
      decide_eq_false (Int.not_lt.mpr (Int.le_trans hbounds (Int.le_of_lt hgt)))
    have hgt' : decide (intMax signed w < truncDivPow2 d.num d.exp) = true := decide_eq_true hgt
    change clampInt (intMin signed w) (intMax signed w) (truncDivPow2 d.num d.exp) = intMax signed w
    unfold clampInt
    rw [hnlt, hgt']
  · intro hlo hhi
    have hnlt : decide (truncDivPow2 d.num d.exp < intMin signed w) = false :=
      decide_eq_false (Int.not_lt.mpr hlo)
    have hngt : decide (intMax signed w < truncDivPow2 d.num d.exp) = false :=
      decide_eq_false (Int.not_lt.mpr hhi)
    change clampInt (intMin signed w) (intMax signed w) (truncDivPow2 d.num d.exp) = truncDivPow2 d.num d.exp
    unfold clampInt
    rw [hnlt, hngt]

/-- Monotonicity of saturating `FloatToInt` over all ordered non-NaN floats (`-∞ ≤ d₁ ≤ d₂ ≤ +∞`). -/
theorem satFloatToInt_monotone_non_nan (signed : Bool) {w : Nat} (hw : 0 < w)
    {f₁ f₂ : FloatVal} (h : floatOrderedLe f₁ f₂) :
    satFloatToInt signed w f₁ ≤ satFloatToInt signed w f₂ := by
  have hbounds := intMin_le_intMax signed hw
  cases f₁ with
  | nan _ _ _ => cases h
  | inf neg₁ =>
    cases neg₁ with
    | true =>
      exact (satFloatToInt_bounds signed hw f₂).1
    | false =>
      cases f₂ with
      | nan _ _ _ => cases h
      | inf neg₂ =>
        cases neg₂ with
        | true => cases h
        | false => exact Int.le_refl _
      | finite _ => cases h
  | finite d₁ =>
    cases f₂ with
    | nan _ _ _ => cases h
    | inf neg₂ =>
      cases neg₂ with
      | true => cases h
      | false =>
        exact (satFloatToInt_bounds signed hw (.finite d₁)).2
    | finite d₂ =>
      have hd : dyadicLe d₁ d₂ := h
      have hs : d₁.num * Int.ofNat (2 ^ d₂.exp) ≤ d₂.num * Int.ofNat (2 ^ d₁.exp) := hd
      have ht1 : truncDivPow2 d₁.num d₁.exp =
          truncDivPow2 (d₁.num * Int.ofNat (2 ^ d₂.exp)) (d₁.exp + d₂.exp) :=
        (truncDivPow2_scale d₁.num d₁.exp d₂.exp).symm
      have ht2 : truncDivPow2 d₂.num d₂.exp =
          truncDivPow2 (d₂.num * Int.ofNat (2 ^ d₁.exp)) (d₁.exp + d₂.exp) := by
        rw [Nat.add_comm d₁.exp d₂.exp]
        exact (truncDivPow2_scale d₂.num d₂.exp d₁.exp).symm
      have htrunc : truncDivPow2 d₁.num d₁.exp ≤ truncDivPow2 d₂.num d₂.exp := by
        rw [ht1, ht2]
        exact truncDivPow2_mono hs
      unfold satFloatToInt
      exact clampInt_mono hbounds htrunc

/-- Witness that NaN breaks full float monotonicity: `-∞` maps to `-2^31` for `i32` while
    `NaN` maps to `0`. -/
theorem witness_nan_breaks_full_monotonicity :
    satFloatToInt true 32 (.inf true) < satFloatToInt true 32 (.nan false true 0) := by
  decide

theorem nat_div_pow2_lt_of_lt_mul {a s m : Nat} (h : a < m * 2 ^ s) :
    a / 2 ^ s < m := by
  cases hdec : decide (m ≤ a / 2 ^ s) with
  | false => exact Nat.lt_of_not_le (of_decide_eq_false hdec)
  | true =>
    have hle : m ≤ a / 2 ^ s := of_decide_eq_true hdec
    have hmul : m * 2 ^ s ≤ (a / 2 ^ s) * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hle
    have hbad : m * 2 ^ s ≤ a := Nat.le_trans hmul (nat_div_pow2_bounds a s).1
    exact absurd h (Nat.not_lt_of_ge hbad)

theorem nat_le_div_pow2_of_mul_le {a s m : Nat} (h : m * 2 ^ s ≤ a) :
    m ≤ a / 2 ^ s := by
  cases hdec : decide (m ≤ a / 2 ^ s) with
  | true => exact of_decide_eq_true hdec
  | false =>
    have hlt : a / 2 ^ s + 1 ≤ m := Nat.lt_of_not_le (of_decide_eq_false hdec)
    have hmul : (a / 2 ^ s + 1) * 2 ^ s ≤ m * 2 ^ s := Nat.mul_le_mul_right (2 ^ s) hlt
    have hbad : (a / 2 ^ s + 1) * 2 ^ s ≤ a := Nat.le_trans hmul h
    exact absurd (nat_div_pow2_bounds a s).2 (Nat.not_lt_of_ge hbad)

/-- Natural-number division boundary helper: `a / 2^s ≤ k ↔ a < (k + 1) * 2^s`. -/
theorem nat_div_pow2_le_iff_lt_mul (a s k : Nat) :
    a / 2 ^ s ≤ k ↔ a < (k + 1) * 2 ^ s := by
  constructor
  · intro hle
    have hlt := (nat_div_pow2_bounds a s).2
    have hmul : (a / 2 ^ s + 1) * 2 ^ s ≤ (k + 1) * 2 ^ s :=
      Nat.mul_le_mul_right (2 ^ s) (Nat.succ_le_succ hle)
    exact Nat.lt_of_lt_of_le hlt hmul
  · intro hlt
    exact Nat.le_of_lt_succ (nat_div_pow2_lt_of_lt_mul hlt)

/-- Exact equivalence between post-truncation bounds and the open rational interval
    `(intMin - 1, intMax + 1)` governing `core::intrinsics::float_to_int_unchecked`. -/
theorem truncDivPow2_bounds_iff_open_interval (signed : Bool) {w : Nat} (hw : 0 < w) (d : Dyadic) :
    (intMin signed w ≤ truncDivPow2 d.num d.exp ∧ truncDivPow2 d.num d.exp ≤ intMax signed w) ↔
    inOpenInterval signed w d := by
  have hmin0 : intMin signed w ≤ 0 := intMin_le_zero signed w
  have hmax0 : 0 ≤ intMax signed w := zero_le_intMax signed hw
  have hspos : Int.ofNat (2 ^ d.exp) > 0 := Int.ofNat_lt.mpr (pow2_pos d.exp)
  unfold inOpenInterval dyadicLt dyadicOfInt
  rw [Nat.pow_zero]
  change (intMin signed w ≤ truncDivPow2 d.num d.exp ∧ truncDivPow2 d.num d.exp ≤ intMax signed w) ↔
         ((intMin signed w - 1) * Int.ofNat (2 ^ d.exp) < d.num * 1 ∧
          d.num * 1 < (intMax signed w + 1) * Int.ofNat (2 ^ d.exp))
  rw [Int.mul_one]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · cases hnum : d.num with
      | ofNat m =>
        have hm1 : intMin signed w - 1 < 0 :=
          Int.lt_of_lt_of_le (Int.sub_lt_self (intMin signed w) (by decide)) hmin0
        have hmul_neg : (intMin signed w - 1) * Int.ofNat (2 ^ d.exp) < 0 := by
          have := Int.mul_lt_mul_of_pos_right hm1 hspos
          rw [Int.zero_mul] at this
          exact this
        exact Int.lt_of_lt_of_le hmul_neg (Int.natCast_nonneg m)
      | negSucc m =>
        rw [hnum] at hlo
        change intMin signed w ≤ -(Int.ofNat ((m + 1) / 2 ^ d.exp)) at hlo
        cases hmin : intMin signed w with
        | ofNat km =>
          have hkm0 : km = 0 := by
            have hle0 : Int.ofNat km ≤ 0 := by rw [← hmin]; exact hmin0
            exact Nat.eq_zero_of_le_zero (Int.ofNat_le.mp hle0)
          subst hkm0
          rw [hmin] at hlo
          have hdiv0 : (m + 1) / 2 ^ d.exp = 0 := by
            cases hdv : (m + 1) / 2 ^ d.exp with
            | zero => rfl
            | succ q =>
              rw [hdv] at hlo
              have hltz : -(Int.ofNat (q + 1)) < (0 : Int) := by
                change Int.negSucc q < 0
                exact Int.negSucc_lt_zero q
              exact absurd (Int.lt_of_le_of_lt hlo hltz) (Int.lt_irrefl 0)
          have hlt_pow : m + 1 < (0 + 1) * 2 ^ d.exp :=
            (nat_div_pow2_le_iff_lt_mul (m + 1) d.exp 0).mp (Nat.le_of_eq hdiv0)
          change -(Int.ofNat (1 * 2 ^ d.exp)) < -(Int.ofNat (m + 1))
          rw [Int.neg_lt_neg_iff]
          exact Int.ofNat_lt.mpr hlt_pow
        | negSucc km =>
          rw [hmin] at hlo
          have hdiv_le : (m + 1) / 2 ^ d.exp ≤ km + 1 := by
            have hneg_le : -(Int.ofNat (km + 1)) ≤ -(Int.ofNat ((m + 1) / 2 ^ d.exp)) := hlo
            exact Int.ofNat_le.mp (Int.neg_le_neg_iff.mp hneg_le)
          have hlt_pow : m + 1 < ((km + 1) + 1) * 2 ^ d.exp :=
            (nat_div_pow2_le_iff_lt_mul (m + 1) d.exp (km + 1)).mp hdiv_le
          have hl : Int.negSucc km - 1 = -(Int.ofNat ((km + 1) + 1)) := rfl
          rw [hl, Int.neg_mul]
          change -(Int.ofNat (((km + 1) + 1) * 2 ^ d.exp)) < -(Int.ofNat (m + 1))
          rw [Int.neg_lt_neg_iff]
          exact Int.ofNat_lt.mpr hlt_pow
    · cases hnum : d.num with
      | negSucc m =>
        have hpos1 : 0 < intMax signed w + 1 :=
          Int.lt_of_le_of_lt hmax0 (Int.lt_add_of_pos_right (intMax signed w) (by decide))
        have hmul_pos : 0 < (intMax signed w + 1) * Int.ofNat (2 ^ d.exp) := by
          have := Int.mul_lt_mul_of_pos_right hpos1 hspos
          rw [Int.zero_mul] at this
          exact this
        exact Int.lt_trans (Int.negSucc_lt_zero m) hmul_pos
      | ofNat m =>
        rw [hnum] at hhi
        change Int.ofNat (m / 2 ^ d.exp) ≤ intMax signed w at hhi
        cases hmax : intMax signed w with
        | negSucc k =>
          have hbad : Int.negSucc k < 0 := Int.negSucc_lt_zero k
          rw [← hmax] at hbad
          exact absurd hmax0 (Int.not_le_of_gt hbad)
        | ofNat k =>
          rw [hmax] at hhi
          have hdiv_le : m / 2 ^ d.exp ≤ k := Int.ofNat_le.mp hhi
          have hlt_pow : m < (k + 1) * 2 ^ d.exp :=
            (nat_div_pow2_le_iff_lt_mul m d.exp k).mp hdiv_le
          change Int.ofNat m < Int.ofNat ((k + 1) * 2 ^ d.exp)
          exact Int.ofNat_lt.mpr hlt_pow
  · rintro ⟨hlo, hhi⟩
    constructor
    · cases hnum : d.num with
      | ofNat m => exact Int.le_trans hmin0 truncDivPow2_nonneg
      | negSucc m =>
        change intMin signed w ≤ -(Int.ofNat ((m + 1) / 2 ^ d.exp))
        cases hmin : intMin signed w with
        | ofNat km =>
          have hkm0 : km = 0 := by
            have hle0 : Int.ofNat km ≤ 0 := by rw [← hmin]; exact hmin0
            exact Nat.eq_zero_of_le_zero (Int.ofNat_le.mp hle0)
          subst hkm0
          rw [hnum, hmin] at hlo
          have hlt_pow : m + 1 < (0 + 1) * 2 ^ d.exp := by
            have hneg : -(Int.ofNat (1 * 2 ^ d.exp)) < -(Int.ofNat (m + 1)) := hlo
            exact Int.ofNat_lt.mp (Int.neg_lt_neg_iff.mp hneg)
          have hdiv0 : (m + 1) / 2 ^ d.exp ≤ 0 :=
            (nat_div_pow2_le_iff_lt_mul (m + 1) d.exp 0).mpr hlt_pow
          have hzero : (m + 1) / 2 ^ d.exp = 0 := Nat.eq_zero_of_le_zero hdiv0
          rw [hzero]
          exact Int.le_refl 0
        | negSucc km =>
          rw [hnum, hmin] at hlo
          have hl : Int.negSucc km - 1 = -(Int.ofNat ((km + 1) + 1)) := rfl
          rw [hl, Int.neg_mul] at hlo
          have hlt_pow : m + 1 < ((km + 1) + 1) * 2 ^ d.exp := by
            have hneg : -(Int.ofNat (((km + 1) + 1) * 2 ^ d.exp)) < -(Int.ofNat (m + 1)) := hlo
            exact Int.ofNat_lt.mp (Int.neg_lt_neg_iff.mp hneg)
          have hdiv_le : (m + 1) / 2 ^ d.exp ≤ km + 1 :=
            (nat_div_pow2_le_iff_lt_mul (m + 1) d.exp (km + 1)).mpr hlt_pow
          change -(Int.ofNat (km + 1)) ≤ -(Int.ofNat ((m + 1) / 2 ^ d.exp))
          rw [Int.neg_le_neg_iff]
          exact Int.ofNat_le.mpr hdiv_le
    · cases hnum : d.num with
      | negSucc m => exact Int.le_trans truncDivPow2_nonpos_negSucc hmax0
      | ofNat m =>
        change Int.ofNat (m / 2 ^ d.exp) ≤ intMax signed w
        cases hmax : intMax signed w with
        | negSucc k =>
          have hbad : Int.negSucc k < 0 := Int.negSucc_lt_zero k
          rw [← hmax] at hbad
          exact absurd hmax0 (Int.not_le_of_gt hbad)
        | ofNat k =>
          rw [hnum, hmax] at hhi
          have hlt_pow : m < (k + 1) * 2 ^ d.exp := Int.ofNat_lt.mp hhi
          have hdiv_le : m / 2 ^ d.exp ≤ k :=
            (nat_div_pow2_le_iff_lt_mul m d.exp k).mpr hlt_pow
          exact Int.ofNat_le.mpr hdiv_le

/-- Sound refinement: on every input where `uncheckedFloatToInt` is defined (`some z`),
    `satFloatToInt` agrees identically (`= z`). -/
theorem satFloatToInt_refines_unchecked (signed : Bool) {w : Nat} (hw : 0 < w)
    (f : FloatVal) (z : Int) (h : uncheckedFloatToInt signed w f = some z) :
    satFloatToInt signed w f = z := by
  cases f with
  | nan _ _ _ => cases h
  | inf _ => cases h
  | finite d =>
    unfold uncheckedFloatToInt at h
    dsimp only at h
    cases h1 : decide (intMin signed w ≤ truncDivPow2 d.num d.exp) with
    | false => rw [h1, Bool.false_and] at h; cases h
    | true =>
      cases h2 : decide (truncDivPow2 d.num d.exp ≤ intMax signed w) with
      | false => rw [h1, h2, Bool.and_false] at h; cases h
      | true =>
        rw [h1, h2, Bool.and_true] at h
        cases h
        exact (satFloatToInt_finite_clamps signed hw d).2.2
          (of_decide_eq_true h1) (of_decide_eq_true h2)

/-- Differential witnesses matching live `rustc` and Miri probes:
    - `NaN -> 0`, `±Inf -> MAX/MIN`, `-1.0 as u32 -> 0` (saturating ok vs unchecked UB),
      `-0.999 as u32 -> 0` (defined under both), `2^31 as i32 -> i32::MAX` (saturating ok vs unchecked UB). -/
theorem witness_floatToInt_sat_vs_unchecked :
    satFloatToInt true 32 (.nan false true 0) = 0 ∧
    satFloatToInt true 32 (.nan true false 1) = 0 ∧
    satFloatToInt false 32 (.inf false) = Int.ofNat (2 ^ 32 - 1) ∧
    satFloatToInt false 32 (.inf true) = 0 ∧
    satFloatToInt true 32 (.inf false) = Int.ofNat (2 ^ 31 - 1) ∧
    satFloatToInt true 32 (.inf true) = Int.neg (Int.ofNat (2 ^ 31)) ∧
    satFloatToInt false 32 (.finite ⟨-1, 0⟩) = 0 ∧
    uncheckedFloatToInt false 32 (.finite ⟨-1, 0⟩) = none ∧
    uncheckedFloatToInt false 32 (.finite ⟨-999, 10⟩) = some 0 ∧
    satFloatToInt false 32 (.finite ⟨-999, 10⟩) = 0 ∧
    satFloatToInt true 32 (.finite ⟨Int.ofNat (2 ^ 31), 0⟩) = Int.ofNat (2 ^ 31 - 1) ∧
    uncheckedFloatToInt true 32 (.finite ⟨Int.ofNat (2 ^ 31), 0⟩) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 4: IEEE-754 `IntToFloat` Round-to-Nearest Ties-to-Even (`roundTiesToEven`) -/

/-- IEEE-754 binary32 (`f32`) abstract result for integer-to-float (`uitofp`/`sitofp`)
    with normalized 24-bit significand (`2^23 ≤ sig < 2^24` when `exp2 > 0`). -/
inductive F32Val where
  | f32Zero (neg : Bool)
  | f32ExactSmall (neg : Bool) (mag : Nat)
  | f32Finite (neg : Bool) (sig : Nat) (exp2 : Nat)
  | f32Inf (neg : Bool)

/-- Exact non-negative integer value of an `F32Val` (when finite and non-negative). -/
noncomputable def f32NatVal : F32Val → Option Nat
  | .f32Zero _ => some 0
  | .f32ExactSmall false mag => some mag
  | .f32Finite false sig exp2 => some (sig * 2 ^ exp2)
  | _ => none

/-- Fuel-indexed floor binary logarithm helper finding `e` such that `2^e ≤ n < 2^(e+1)`. -/
noncomputable def findExp2Aux (fuel k n : Nat) : Nat :=
  match fuel with
  | 0 => k
  | fuel' + 1 =>
    match decide (n < 2 ^ (k + 1)) with
    | true => k
    | false => findExp2Aux fuel' (k + 1) n

theorem findExp2Aux_spec (fuel k n : Nat) (hle : 2 ^ k ≤ n) (hlt : n < 2 ^ (k + fuel)) :
    2 ^ (findExp2Aux fuel k n) ≤ n ∧ n < 2 ^ (findExp2Aux fuel k n + 1) := by
  induction fuel generalizing k with
  | zero =>
    have hkbad : n < 2 ^ k := hlt
    exact absurd hle (Nat.not_le_of_gt hkbad)
  | succ fuel' ih =>
    unfold findExp2Aux
    cases hcmp : decide (n < 2 ^ (k + 1)) with
    | true =>
      have hlt' : n < 2 ^ (k + 1) := of_decide_eq_true hcmp
      dsimp only
      exact ⟨hle, hlt'⟩
    | false =>
      have hnlt : ¬ (n < 2 ^ (k + 1)) := of_decide_eq_false hcmp
      dsimp only
      have hge : 2 ^ (k + 1) ≤ n := Nat.ge_of_not_lt hnlt
      have hadd : k + 1 + fuel' = k + (fuel' + 1) := Nat.add_right_comm k 1 fuel'
      have hlt' : n < 2 ^ (k + 1 + fuel') := by rw [hadd]; exact hlt
      exact ih (k + 1) hge hlt'

/-- IEEE-754 `roundTiesToEven` rounding of non-negative integer `n : Nat` to `F32Val`
    (`uitofp iN %x to float` / `Single::from_u128`), covering all integers up to `u128::MAX`. -/
noncomputable def roundNatToF32 (n : Nat) : F32Val :=
  match Nat.beq n 0 with
  | true => .f32Zero false
  | false =>
    match decide (n < 2 ^ 24) with
    | true => .f32ExactSmall false n
    | false =>
      let e := findExp2Aux 130 0 n
      let shift := e - 23
      let q := n / 2 ^ shift
      let r := n % 2 ^ shift
      let half := 2 ^ (shift - 1)
      let sig0 :=
        match decide (r < half) with
        | true => q
        | false =>
          match decide (half < r) with
          | true => q + 1
          | false =>
            match Nat.beq (q % 2) 0 with
            | true => q
            | false => q + 1
      let (sig1, exp1) :=
        match Nat.beq sig0 (2 ^ 24) with
        | true => (2 ^ 23, shift + 1)
        | false => (sig0, shift)
      match decide (104 < exp1) with
      | true => .f32Inf false
      | false => .f32Finite false sig1 exp1

/-- IEEE-754 `roundTiesToEven` rounding of signed integer `z : Int` to `F32Val`
    (`sitofp iN %x to float` / `Single::from_i128`). -/
noncomputable def roundIntToF32 (z : Int) : F32Val :=
  match z with
  | .ofNat n => roundNatToF32 n
  | .negSucc m =>
    match roundNatToF32 (m + 1) with
    | .f32Zero _ => .f32Zero true
    | .f32ExactSmall _ mag => .f32ExactSmall true mag
    | .f32Finite _ sig exp2 => .f32Finite true sig exp2
    | .f32Inf _ => .f32Inf true

/-- Exactness below `2 ^ 24`: every unsigned integer `< 16,777,216` converts to `f32`
    with zero rounding loss. -/
theorem roundNatToF32_exact_below_2p24 {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 24) :
    f32NatVal (roundNatToF32 n) = some n := by
  have hne : Nat.beq n 0 = false := by
    cases n with
    | zero => cases hpos
    | succ _ => rfl
  have hdec : decide (n < 2 ^ 24) = true := decide_eq_true hlt
  unfold roundNatToF32
  rw [hne, hdec]
  rfl

/-- Exactness of `0`: `0u32 as f32` produces `+0.0`. -/
theorem roundNatToF32_zero : roundNatToF32 0 = .f32Zero false := rfl

/-- Ties-to-even nearest-approximation guarantee for `roundNatToF32`:
    when `2 ^ 24 ≤ n < 2 ^ 130`, `e = findExp2Aux 130 0 n` satisfies `24 ≤ e`, `shift = e - 23 ≥ 1`,
    so `roundNatToF32` picks either `q * 2^shift` or `(q + 1) * 2^shift` with distance `≤ 2^(shift - 1)`,
    and whenever `r = 2^(shift - 1)` (exact halfway tie), `sig` is strictly even (`sig % 2 = 0`). -/
theorem roundNatToF32_ties_to_even_invariant
    {n : Nat} (hge : 2 ^ 24 ≤ n) (hlt : n < 2 ^ 130) :
    let e := findExp2Aux 130 0 n
    let shift := e - 23
    let q := n / 2 ^ shift
    let r := n % 2 ^ shift
    let half := 2 ^ (shift - 1)
    24 ≤ e ∧ 1 ≤ shift ∧ 2 ^ 23 ≤ q ∧ q < 2 ^ 24 ∧
    (r = half → (match Nat.beq (q % 2) 0 with | true => q | false => q + 1) % 2 = 0) := by
  have h1le : 2 ^ 0 ≤ n := Nat.le_trans (pow2_pos 24) hge
  have he := findExp2Aux_spec 130 0 n h1le (by rw [Nat.zero_add]; exact hlt)
  have he24 : 24 ≤ findExp2Aux 130 0 n := by
    cases hdec : decide (24 ≤ findExp2Aux 130 0 n) with
    | true => exact of_decide_eq_true hdec
    | false =>
      have hlt24 : findExp2Aux 130 0 n < 24 := Nat.lt_of_not_le (of_decide_eq_false hdec)
      have hpow : 2 ^ (findExp2Aux 130 0 n + 1) ≤ 2 ^ 24 := pow2_le_pow2 hlt24
      have hbad : n < 2 ^ 24 := Nat.lt_of_lt_of_le he.2 hpow
      exact absurd hge (Nat.not_le_of_gt hbad)
  have hshift1 : 1 ≤ findExp2Aux 130 0 n - 23 := Nat.le_sub_of_add_le he24
  have hqlo : 2 ^ 23 ≤ n / 2 ^ (findExp2Aux 130 0 n - 23) := by
    apply nat_le_div_pow2_of_mul_le
    have hpow_eq : 2 ^ 23 * 2 ^ (findExp2Aux 130 0 n - 23) = 2 ^ (findExp2Aux 130 0 n) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_trans (by decide) he24)]
    rw [hpow_eq]
    exact he.1
  have hqhi : n / 2 ^ (findExp2Aux 130 0 n - 23) < 2 ^ 24 := by
    apply nat_div_pow2_lt_of_lt_mul
    have hpow_eq : 2 ^ 24 * 2 ^ (findExp2Aux 130 0 n - 23) = 2 ^ (findExp2Aux 130 0 n + 1) := by
      rw [← Nat.pow_add]
      have heq : 24 + (findExp2Aux 130 0 n - 23) = findExp2Aux 130 0 n + 1 := by
        rw [Nat.add_comm 24 _]
        have h1 : (findExp2Aux 130 0 n - 23) + 23 = findExp2Aux 130 0 n :=
          Nat.sub_add_cancel (Nat.le_trans (by decide) he24)
        rw [← h1]
        exact Nat.add_assoc _ 23 1
      rw [heq]
    rw [hpow_eq]
    exact he.2
  refine ⟨he24, hshift1, hqlo, hqhi, ?_⟩
  intro _
  cases hmod : (n / 2 ^ (findExp2Aux 130 0 n - 23)) % 2 with
  | zero =>
    dsimp only
    exact hmod
  | succ k =>
    have hlt2 : (n / 2 ^ (findExp2Aux 130 0 n - 23)) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk0 : k = 0 := by
      rw [hmod] at hlt2
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hlt2))
    subst hk0
    dsimp only
    rw [Nat.add_mod, hmod]

/-- Kernel-reduced `IntToFloat` witnesses matching live `rustc` and Miri execution:
    - `(1 << 24) + 1` -> `16777216` (`2^23 * 2^1`, tie down to even)
    - `(1 << 24) + 2` -> `16777218` (`(2^23 + 1) * 2^1`, exact)
    - `(1 << 24) + 3` -> `16777220` (`(2^23 + 2) * 2^1`, tie up to even)
    - `(1 << 24) + 4` -> `16777220` (`(2^23 + 2) * 2^1`, exact)
    - `i32::MAX` (`2^31 - 1`) -> `2^31 = 2147483648` (`2^23 * 2^8`)
    - `u128::MAX` (`2^128 - 1`) -> `+Inf` (`f32Inf false`)
    - `f32::MAX` boundary `((2^24 - 1) * 2^104 + 2^103 - 1)` -> finite `(2^24 - 1) * 2^104`
    - `i128::MIN` (`-2^127`) -> `-2^127` (`f32Finite true (2^23) 104`, finite). -/
theorem witness_intToFloat_ties_to_even_and_overflow :
    f32NatVal (roundNatToF32 (2 ^ 24 + 1)) = some (2 ^ 24) ∧
    f32NatVal (roundNatToF32 (2 ^ 24 + 2)) = some (2 ^ 24 + 2) ∧
    f32NatVal (roundNatToF32 (2 ^ 24 + 3)) = some (2 ^ 24 + 4) ∧
    f32NatVal (roundNatToF32 (2 ^ 24 + 4)) = some (2 ^ 24 + 4) ∧
    f32NatVal (roundNatToF32 (2 ^ 31 - 1)) = some (2 ^ 31) ∧
    roundNatToF32 (2 ^ 128 - 1) = .f32Inf false ∧
    roundNatToF32 ((2 ^ 24 - 1) * 2 ^ 104 + 2 ^ 103 - 1) = .f32Finite false (2 ^ 24 - 1) 104 ∧
    roundIntToF32 (Int.neg (Int.ofNat (2 ^ 127))) = .f32Finite true (2 ^ 23) 104 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 5: `PtrToPtr` Wide-to-Thin Projection and Strict vs. Exposed Provenance Soundness -/

/-- Allocation provenance tag mirroring Miri `Provenance`:
    - `none`: integer-derived dangling pointer (`ptr::without_provenance`)
    - `concrete id`: unique allocation provenance (`AllocId`)
    - `wildcard`: exposed-set indeterminate provenance (`PointerWithExposedProvenance`). -/
inductive ProvTag where
  | none
  | concrete (id : Nat)
  | wildcard

/-- Thin pointer abstract value `(addr, prov)`. -/
structure PtrVal where
  addr : Nat
  prov : ProvTag

/-- Wide pointer abstract value `(ScalarPair(data, meta))`: slice length or vtable metadata. -/
structure WidePtrVal where
  thin : PtrVal
  metaWord : Nat

/-- `CastKind::PtrToPtr` wide-to-thin lowering (`cast_immediate` `ScalarPair(data, _)` -> `Scalar(data)`):
    discards metadata while preserving exact address and provenance tag. -/
noncomputable def ptrToPtrWideToThin (w : WidePtrVal) : PtrVal :=
  w.thin

/-- `core::ptr::const_ptr::with_addr`: preserves provenance tag across signed `wrapping_byte_offset`,
    replacing only the numeric address. -/
noncomputable def withAddrPtr (p : PtrVal) (newAddr : Nat) : PtrVal :=
  { addr := newAddr, prov := p.prov }

/-- `core::ptr::without_provenance`: constructs a pointer with provenance `.none`. -/
noncomputable def withoutProvPtr (addr : Nat) : PtrVal :=
  { addr := addr, prov := .none }

/-- Heap/stack allocation block tracking numeric bounds, liveness, and Miri `exposed` flag. -/
structure AllocEntry where
  allocId : Nat
  baseAddr : Nat
  size : Nat
  live : Bool
  exposed : Bool
  initByte : Nat

/-- Provenance enforcement mode matching Miri:
    - `strict`: `-Zmiri-strict-provenance` (rejects `PointerWithExposedProvenance`; `expose_provenance` is no-op)
    - `exposedPermissive`: Miri `Default` warning / `-Zmiri-permissive-provenance`. -/
inductive ProvMode where
  | strict
  | exposedPermissive

/-- Typed register values for the abstract provenance machine. -/
inductive RegVal where
  | int (v : Nat)
  | ptr (p : PtrVal)
  | wide (w : WidePtrVal)

/-- Execution failures separating strict-provenance rejection from memory UB. -/
inductive ExecError where
  | unsupportedStrictIntToPtr
  | typeMismatch
  | missingReg
  | outOfBoundsOrDangling
  | noProvenance
  | wildcardUnexposed
  | nullZstAccess

/-- Outcome monad avoiding `Except` dependencies. -/
inductive StepRes (α : Type) where
  | ok (val : α)
  | error (err : ExecError)

/-- Machine state capturing register file, allocation list, observable output trace, and mode. -/
structure MachineState where
  mode : ProvMode
  regs : List (Nat × RegVal)
  mem : List AllocEntry
  trace : List Nat

/-- MIR-level provenance and pointer-cast statement subset. -/
inductive Stmt where
  | mkAlloc (dst : Nat) (baseAddr size initByte : Nat)
  | loadIntConst (dst : Nat) (v : Nat)
  | wideFromThin (dst ptrSrc : Nat) (metaWord : Nat)
  | castPtrToPtrWideToThin (dst wideSrc : Nat)
  | ptrAddrStrict (dst ptrSrc : Nat)
  | ptrWithAddrStrict (dst ptrSrc addrSrc : Nat)
  | ptrWithoutProv (dst addrSrc : Nat)
  | castPtrExposeProv (dst ptrSrc : Nat)
  | castPtrWithExposedProv (dst addrSrc : Nat)
  | readPtr (dst ptrSrc : Nat) (reqSize : Nat)
  | emitInt (intSrc : Nat)

noncomputable def lookupReg (regs : List (Nat × RegVal)) (r : Nat) : Option RegVal :=
  match regs with
  | [] => Option.none
  | (k, v) :: rest =>
    match Nat.beq k r with
    | true => some v
    | false => lookupReg rest r

noncomputable def setReg (regs : List (Nat × RegVal)) (r : Nat) (v : RegVal) : List (Nat × RegVal) :=
  (r, v) :: regs

noncomputable def lookupAlloc (mem : List AllocEntry) (id : Nat) : Option AllocEntry :=
  match mem with
  | [] => Option.none
  | e :: rest =>
    match Nat.beq e.allocId id with
    | true => some e
    | false => lookupAlloc rest id

noncomputable def allocInRange (e : AllocEntry) (addr reqSize : Nat) : Bool :=
  e.live && decide (e.baseAddr ≤ addr) && decide (addr + reqSize ≤ e.baseAddr + e.size)

noncomputable def findExposedAlloc (mem : List AllocEntry) (addr reqSize : Nat) : Option AllocEntry :=
  match mem with
  | [] => Option.none
  | e :: rest =>
    match e.exposed && allocInRange e addr reqSize with
    | true => some e
    | false => findExposedAlloc rest addr reqSize

noncomputable def exposeAlloc (mem : List AllocEntry) (id : Nat) : List AllocEntry :=
  match mem with
  | [] => []
  | e :: rest =>
    (match Nat.beq e.allocId id with
     | true => { allocId := e.allocId, baseAddr := e.baseAddr, size := e.size,
                 live := e.live, exposed := true, initByte := e.initByte }
     | false => e) :: exposeAlloc rest id

noncomputable def readViaPtr (mem : List AllocEntry) (p : PtrVal) (reqSize : Nat) : StepRes Nat :=
  match Nat.beq reqSize 0 with
  | true =>
    match Nat.beq p.addr 0 with
    | true => .error .nullZstAccess
    | false => .ok 0
  | false =>
    match p.prov with
    | .none => .error .noProvenance
    | .concrete id =>
      match lookupAlloc mem id with
      | Option.none => .error .outOfBoundsOrDangling
      | some e =>
        match allocInRange e p.addr reqSize with
        | true => .ok e.initByte
        | false => .error .outOfBoundsOrDangling
    | .wildcard =>
      match findExposedAlloc mem p.addr reqSize with
      | Option.none => .error .wildcardUnexposed
      | some e => .ok e.initByte

noncomputable def stepStmt (st : MachineState) (s : Stmt) : StepRes MachineState :=
  match s with
  | .mkAlloc dst baseAddr size initByte =>
    let e : AllocEntry :=
      { allocId := st.mem.length
        baseAddr := baseAddr
        size := size
        live := true
        exposed := false
        initByte := initByte }
    let p : PtrVal := { addr := baseAddr, prov := .concrete e.allocId }
    .ok { mode := st.mode
          regs := setReg st.regs dst (.ptr p)
          mem := e :: st.mem
          trace := st.trace }
  | .loadIntConst dst v =>
    .ok { mode := st.mode
          regs := setReg st.regs dst (.int v)
          mem := st.mem
          trace := st.trace }
  | .wideFromThin dst ptrSrc metaWord =>
    match lookupReg st.regs ptrSrc with
    | Option.none => .error .missingReg
    | some (.ptr p) =>
      .ok { mode := st.mode
            regs := setReg st.regs dst (.wide { thin := p, metaWord := metaWord })
            mem := st.mem
            trace := st.trace }
    | some _ => .error .typeMismatch
  | .castPtrToPtrWideToThin dst wideSrc =>
    match lookupReg st.regs wideSrc with
    | Option.none => .error .missingReg
    | some (.wide w) =>
      .ok { mode := st.mode
            regs := setReg st.regs dst (.ptr (ptrToPtrWideToThin w))
            mem := st.mem
            trace := st.trace }
    | some _ => .error .typeMismatch
  | .ptrAddrStrict dst ptrSrc =>
    match lookupReg st.regs ptrSrc with
    | Option.none => .error .missingReg
    | some (.ptr p) =>
      .ok { mode := st.mode
            regs := setReg st.regs dst (.int p.addr)
            mem := st.mem
            trace := st.trace }
    | some _ => .error .typeMismatch
  | .ptrWithAddrStrict dst ptrSrc addrSrc =>
    match lookupReg st.regs ptrSrc, lookupReg st.regs addrSrc with
    | some (.ptr p), some (.int a) =>
      .ok { mode := st.mode
            regs := setReg st.regs dst (.ptr (withAddrPtr p a))
            mem := st.mem
            trace := st.trace }
    | Option.none, _ => .error .missingReg
    | _, Option.none => .error .missingReg
    | _, _ => .error .typeMismatch
  | .ptrWithoutProv dst addrSrc =>
    match lookupReg st.regs addrSrc with
    | Option.none => .error .missingReg
    | some (.int a) =>
      .ok { mode := st.mode
            regs := setReg st.regs dst (.ptr (withoutProvPtr a))
            mem := st.mem
            trace := st.trace }
    | some _ => .error .typeMismatch
  | .castPtrExposeProv dst ptrSrc =>
    match lookupReg st.regs ptrSrc with
    | Option.none => .error .missingReg
    | some (.ptr p) =>
      let newMem :=
        match st.mode, p.prov with
        | .strict, _ => st.mem
        | .exposedPermissive, .concrete id => exposeAlloc st.mem id
        | .exposedPermissive, _ => st.mem
      .ok { mode := st.mode
            regs := setReg st.regs dst (.int p.addr)
            mem := newMem
            trace := st.trace }
    | some _ => .error .typeMismatch
  | .castPtrWithExposedProv dst addrSrc =>
    match lookupReg st.regs addrSrc with
    | Option.none => .error .missingReg
    | some (.int a) =>
      match st.mode with
      | .strict => .error .unsupportedStrictIntToPtr
      | .exposedPermissive =>
        .ok { mode := st.mode
              regs := setReg st.regs dst (.ptr { addr := a, prov := .wildcard })
              mem := st.mem
              trace := st.trace }
    | some _ => .error .typeMismatch
  | .readPtr dst ptrSrc reqSize =>
    match lookupReg st.regs ptrSrc with
    | Option.none => .error .missingReg
    | some (.ptr p) =>
      match readViaPtr st.mem p reqSize with
      | .error err => .error err
      | .ok v =>
        .ok { mode := st.mode
              regs := setReg st.regs dst (.int v)
              mem := st.mem
              trace := st.trace ++ [v] }
    | some _ => .error .typeMismatch
  | .emitInt intSrc =>
    match lookupReg st.regs intSrc with
    | Option.none => .error .missingReg
    | some (.int v) =>
      .ok { mode := st.mode
            regs := st.regs
            mem := st.mem
            trace := st.trace ++ [v] }
    | some _ => .error .typeMismatch

noncomputable def evalProg (prog : List Stmt) (st : MachineState) : StepRes MachineState :=
  match prog with
  | [] => .ok st
  | s :: rest =>
    match stepStmt st s with
    | .error err => .error err
    | .ok st' => evalProg rest st'

noncomputable def initState (mode : ProvMode) : MachineState :=
  { mode := mode, regs := [], mem := [], trace := [] }

/-- Register-level invariant asserting that no thin or wide pointer carries `.wildcard` provenance. -/
noncomputable def regValNoWildcard : RegVal → Prop
  | .int _ => True
  | .ptr p => p.prov ≠ .wildcard
  | .wide w => w.thin.prov ≠ .wildcard

noncomputable def RegsNoWildcard (regs : List (Nat × RegVal)) : Prop :=
  ∀ r v, lookupReg regs r = some v → regValNoWildcard v

/-- Simulation relation equating two machines up to provenance mode and per-allocation `exposed` flags. -/
noncomputable def entrySameIgnoringExposed (e₁ e₂ : AllocEntry) : Prop :=
  e₁.allocId = e₂.allocId ∧
  e₁.baseAddr = e₂.baseAddr ∧
  e₁.size = e₂.size ∧
  e₁.live = e₂.live ∧
  e₁.initByte = e₂.initByte

noncomputable def MemSameIgnoringExposed : List AllocEntry → List AllocEntry → Prop
  | [], [] => True
  | e₁ :: r₁, e₂ :: r₂ => entrySameIgnoringExposed e₁ e₂ ∧ MemSameIgnoringExposed r₁ r₂
  | _, _ => False

noncomputable def StatesRelated (s₁ s₂ : MachineState) : Prop :=
  s₁.regs = s₂.regs ∧ MemSameIgnoringExposed s₁.mem s₂.mem ∧ s₁.trace = s₂.trace

/-- `PtrToPtr` wide-to-thin projection preserves both numeric address and provenance tag. -/
theorem ptrToPtrWideToThin_preserves_addr_and_prov (w : WidePtrVal) :
    (ptrToPtrWideToThin w).addr = w.thin.addr ∧
    (ptrToPtrWideToThin w).prov = w.thin.prov :=
  ⟨rfl, rfl⟩

/-- `withAddrPtr` preserves exact provenance while updating address to `newAddr`. -/
theorem withAddrPtr_preserves_prov (p : PtrVal) (newAddr : Nat) :
    (withAddrPtr p newAddr).addr = newAddr ∧
    (withAddrPtr p newAddr).prov = p.prov :=
  ⟨rfl, rfl⟩

/-- `ptrAddrStrict` never modifies memory allocations or exposes provenance in either mode. -/
theorem ptrAddrStrict_preserves_mem {st st' : MachineState} {dst src : Nat}
    (h : stepStmt st (.ptrAddrStrict dst src) = .ok st') :
    st'.mem = st.mem := by
  unfold stepStmt at h
  dsimp only at h
  cases hreg : lookupReg st.regs src with
  | none => rw [hreg] at h; cases h
  | some rv =>
    rw [hreg] at h
    cases rv with
    | int _ => cases h
    | wide _ => cases h
    | ptr _ => cases h; rfl

/-- `PointerExposeProvenance` in `strict` mode never mutates `mem` (`exposed` flags remain untouched). -/
theorem castPtrExposeProv_strict_preserves_mem {st st' : MachineState} {dst src : Nat}
    (hmode : st.mode = .strict)
    (h : stepStmt st (.castPtrExposeProv dst src) = .ok st') :
    st'.mem = st.mem := by
  unfold stepStmt at h
  dsimp only at h
  cases hreg : lookupReg st.regs src with
  | none => rw [hreg] at h; cases h
  | some rv =>
    rw [hreg] at h
    cases rv with
    | int _ => cases h
    | wide _ => cases h
    | ptr _ =>
      rw [hmode] at h
      dsimp only at h
      cases h
      rfl

theorem regsNoWildcard_set {regs : List (Nat × RegVal)} {r : Nat} {v : RegVal}
    (hregs : RegsNoWildcard regs) (hv : regValNoWildcard v) :
    RegsNoWildcard (setReg regs r v) := by
  intro k u hlook
  unfold setReg lookupReg at hlook
  cases hbeq : Nat.beq r k with
  | true =>
    rw [hbeq] at hlook
    dsimp only at hlook
    cases hlook
    exact hv
  | false =>
    rw [hbeq] at hlook
    dsimp only at hlook
    exact hregs k u hlook

/-- Every succeeding statement step preserves `mode`. -/
theorem stepStmt_preserves_mode {st st' : MachineState} {s : Stmt}
    (h : stepStmt st s = .ok st') :
    st'.mode = st.mode := by
  cases s with
  | mkAlloc _ _ _ _ =>
    unfold stepStmt at h; dsimp only at h; cases h; rfl
  | loadIntConst _ _ =>
    unfold stepStmt at h; dsimp only at h; cases h; rfl
  | wideFromThin _ ptrSrc _ =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs ptrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl
  | castPtrToPtrWideToThin _ wideSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs wideSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl
  | ptrAddrStrict _ ptrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs ptrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl
  | ptrWithAddrStrict _ ptrSrc addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr1 : lookupReg st.regs ptrSrc with
    | none => rw [hr1] at h; cases h
    | some rv1 =>
      rw [hr1] at h
      cases hr2 : lookupReg st.regs addrSrc with
      | none => rw [hr2] at h; cases rv1 <;> cases h
      | some rv2 =>
        rw [hr2] at h
        cases rv1 <;> cases rv2 <;> cases h; rfl
  | ptrWithoutProv _ addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs addrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl
  | castPtrExposeProv _ ptrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs ptrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl
  | castPtrWithExposedProv _ addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs addrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv with
      | ptr _ => cases h
      | wide _ => cases h
      | int _ =>
        cases hmode : st.mode with
        | strict => rw [hmode] at h; cases h
        | exposedPermissive => rw [hmode] at h; cases h; rfl
  | readPtr _ ptrSrc reqSize =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs ptrSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv with
      | int _ => cases h
      | wide _ => cases h
      | ptr p =>
        dsimp only at h
        cases hrd : readViaPtr st.mem p reqSize with
        | error _ => rw [hrd] at h; cases h
        | ok _ => rw [hrd] at h; cases h; rfl
  | emitInt intSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hr : lookupReg st.regs intSrc with
    | none => rw [hr] at h; cases h
    | some rv =>
      rw [hr] at h
      cases rv <;> cases h; rfl

/-- In `.strict` mode, every succeeding statement step preserves `RegsNoWildcard`. -/
theorem strict_step_preserves_no_wildcard {st st' : MachineState} {s : Stmt}
    (hmode : st.mode = .strict) (hwc : RegsNoWildcard st.regs)
    (h : stepStmt st s = .ok st') :
    RegsNoWildcard st'.regs ∧ st'.mode = .strict := by
  have hm' : st'.mode = .strict := (stepStmt_preserves_mode h).trans hmode
  refine ⟨?_, hm'⟩
  cases s with
  | mkAlloc dst baseAddr size initByte =>
    unfold stepStmt at h; dsimp only at h; cases h
    refine regsNoWildcard_set hwc ?_
    intro hc; cases hc
  | loadIntConst dst v =>
    unfold stepStmt at h; dsimp only at h; cases h
    exact regsNoWildcard_set hwc trivial
  | wideFromThin dst ptrSrc metaWord =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs ptrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | int _ => cases h
      | wide _ => cases h
      | ptr p =>
        cases h
        exact regsNoWildcard_set hwc (hwc ptrSrc (.ptr p) hreg)
  | castPtrToPtrWideToThin dst wideSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs wideSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | int _ => cases h
      | ptr _ => cases h
      | wide w =>
        cases h
        exact regsNoWildcard_set hwc (hwc wideSrc (.wide w) hreg)
  | ptrAddrStrict dst ptrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs ptrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | int _ => cases h
      | wide _ => cases h
      | ptr _ =>
        cases h
        exact regsNoWildcard_set hwc trivial
  | ptrWithAddrStrict dst ptrSrc addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg1 : lookupReg st.regs ptrSrc with
    | none => rw [hreg1] at h; cases h
    | some rv1 =>
      rw [hreg1] at h
      cases hreg2 : lookupReg st.regs addrSrc with
      | none => rw [hreg2] at h; cases rv1 <;> cases h
      | some rv2 =>
        rw [hreg2] at h
        cases rv1 with
        | int _ => cases h
        | wide _ => cases h
        | ptr p =>
          cases rv2 with
          | ptr _ => cases h
          | wide _ => cases h
          | int a =>
            cases h
            exact regsNoWildcard_set hwc (hwc ptrSrc (.ptr p) hreg1)
  | ptrWithoutProv dst addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs addrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | ptr _ => cases h
      | wide _ => cases h
      | int a =>
        cases h
        refine regsNoWildcard_set hwc ?_
        intro hc; cases hc
  | castPtrExposeProv dst ptrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs ptrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | int _ => cases h
      | wide _ => cases h
      | ptr _ =>
        cases h
        exact regsNoWildcard_set hwc trivial
  | castPtrWithExposedProv dst addrSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs addrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | ptr _ => cases h
      | wide _ => cases h
      | int a =>
        rw [hmode] at h
        cases h
  | readPtr dst ptrSrc reqSize =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs ptrSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | int _ => cases h
      | wide _ => cases h
      | ptr p =>
        dsimp only at h
        cases hrd : readViaPtr st.mem p reqSize with
        | error _ => rw [hrd] at h; cases h
        | ok v =>
          rw [hrd] at h
          cases h
          exact regsNoWildcard_set hwc trivial
  | emitInt intSrc =>
    unfold stepStmt at h; dsimp only at h
    cases hreg : lookupReg st.regs intSrc with
    | none => rw [hreg] at h; cases h
    | some rv =>
      rw [hreg] at h
      cases rv with
      | ptr _ => cases h
      | wide _ => cases h
      | int _ =>
        cases h
        exact hwc

theorem memSameIgnoringExposed_length {m₁ m₂ : List AllocEntry}
    (h : MemSameIgnoringExposed m₁ m₂) : m₁.length = m₂.length := by
  induction m₁ generalizing m₂ with
  | nil =>
    cases m₂ with
    | nil => rfl
    | cons _ _ => cases h
  | cons e₁ r₁ ih =>
    cases m₂ with
    | nil => cases h
    | cons e₂ r₂ =>
      dsimp only [List.length_cons]
      exact congrArg Nat.succ (ih h.2)

theorem memSameIgnoringExposed_expose_right {m₁ m₂ : List AllocEntry} (id : Nat)
    (h : MemSameIgnoringExposed m₁ m₂) :
    MemSameIgnoringExposed m₁ (exposeAlloc m₂ id) := by
  induction m₁ generalizing m₂ with
  | nil =>
    cases m₂ with
    | nil => exact trivial
    | cons _ _ => cases h
  | cons e₁ r₁ ih =>
    cases m₂ with
    | nil => cases h
    | cons e₂ r₂ =>
      unfold exposeAlloc
      constructor
      · cases hbeq : Nat.beq e₂.allocId id with
        | true => dsimp only; exact h.1
        | false => dsimp only; exact h.1
      · exact ih h.2

theorem memSameIgnoringExposed_lookupAlloc_read {m₁ m₂ : List AllocEntry} (id addr reqSize : Nat)
    (hm : MemSameIgnoringExposed m₁ m₂) :
    (lookupAlloc m₁ id = Option.none ∧ lookupAlloc m₂ id = Option.none) ∨
    (∃ e₁ e₂, lookupAlloc m₁ id = some e₁ ∧ lookupAlloc m₂ id = some e₂ ∧
      allocInRange e₁ addr reqSize = allocInRange e₂ addr reqSize ∧
      e₁.initByte = e₂.initByte) := by
  induction m₁ generalizing m₂ with
  | nil =>
    cases m₂ with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons _ _ => cases hm
  | cons e₁ r₁ ih =>
    cases m₂ with
    | nil => cases hm
    | cons e₂ r₂ =>
      have hid : e₁.allocId = e₂.allocId := hm.1.1
      unfold lookupAlloc
      rw [hid]
      cases hbeq : Nat.beq e₂.allocId id with
      | true =>
        dsimp only
        refine Or.inr ⟨e₁, e₂, rfl, rfl, ?_, hm.1.2.2.2.2⟩
        unfold allocInRange
        rw [hm.1.2.1, hm.1.2.2.1, hm.1.2.2.2.1]
      | false =>
        dsimp only
        exact ih hm.2

theorem memSameIgnoringExposed_readViaPtr {m₁ m₂ : List AllocEntry} {p : PtrVal} {reqSize : Nat}
    (hm : MemSameIgnoringExposed m₁ m₂) (hnowc : p.prov ≠ .wildcard) :
    readViaPtr m₁ p reqSize = readViaPtr m₂ p reqSize := by
  unfold readViaPtr
  cases Nat.beq reqSize 0 with
  | true => rfl
  | false =>
    dsimp only
    cases hprov : p.prov with
    | none => rfl
    | wildcard => exact absurd hprov hnowc
    | concrete id =>
      dsimp only
      rcases memSameIgnoringExposed_lookupAlloc_read id p.addr reqSize hm with
        ⟨hl₁, hl₂⟩ | ⟨e₁, e₂, hl₁, hl₂, hrange, hbyte⟩
      · rw [hl₁, hl₂]
      · rw [hl₁, hl₂]
        dsimp only
        rw [hrange, hbyte]

/-- Single-step forward simulation: any succeeding step under `.strict` provenance is simulated
    by `.exposedPermissive` with identical registers and observable trace, preserving `StatesRelated`. -/
theorem strict_step_simulates_to_exposed {s₁ s₁' s₂ : MachineState} {s : Stmt}
    (hm₁ : s₁.mode = .strict) (hm₂ : s₂.mode = .exposedPermissive)
    (hwc : RegsNoWildcard s₁.regs) (hrel : StatesRelated s₁ s₂)
    (hstep : stepStmt s₁ s = .ok s₁') :
    ∃ s₂', stepStmt s₂ s = .ok s₂' ∧ StatesRelated s₁' s₂' := by
  rcases hrel with ⟨hregs, hmem, htrace⟩
  cases s with
  | mkAlloc dst baseAddr size initByte =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hstep
    have hlen : s₁.mem.length = s₂.mem.length := memSameIgnoringExposed_length hmem
    refine ⟨_, rfl, ?_, ?_, htrace⟩
    · rw [hregs, hlen]
    · constructor
      · refine ⟨?_, rfl, rfl, rfl, rfl⟩
        exact hlen
      · exact hmem
  | loadIntConst dst v =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hstep
    exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | wideFromThin dst ptrSrc metaWord =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs ptrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs ptrSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | int _ => cases hstep
      | wide _ => cases hstep
      | ptr _ =>
        cases hstep
        exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | castPtrToPtrWideToThin dst wideSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs wideSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs wideSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | int _ => cases hstep
      | ptr _ => cases hstep
      | wide _ =>
        cases hstep
        exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | ptrAddrStrict dst ptrSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs ptrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs ptrSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | int _ => cases hstep
      | wide _ => cases hstep
      | ptr _ =>
        cases hstep
        exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | ptrWithAddrStrict dst ptrSrc addrSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg1 : lookupReg s₁.regs ptrSrc with
    | none => rw [hreg1] at hstep; cases hstep
    | some rv1 =>
      rw [hreg1] at hstep
      have hreg1' : lookupReg s₂.regs ptrSrc = some rv1 := by rw [← hregs]; exact hreg1
      rw [hreg1']
      cases hreg2 : lookupReg s₁.regs addrSrc with
      | none =>
        rw [hreg2] at hstep
        cases rv1 <;> cases hstep
      | some rv2 =>
        rw [hreg2] at hstep
        have hreg2' : lookupReg s₂.regs addrSrc = some rv2 := by rw [← hregs]; exact hreg2
        rw [hreg2']
        cases rv1 with
        | int _ => cases hstep
        | wide _ => cases hstep
        | ptr _ =>
          cases rv2 with
          | ptr _ => cases hstep
          | wide _ => cases hstep
          | int _ =>
            cases hstep
            exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | ptrWithoutProv dst addrSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs addrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs addrSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | ptr _ => cases hstep
      | wide _ => cases hstep
      | int _ =>
        cases hstep
        exact ⟨_, rfl, by rw [hregs], hmem, htrace⟩
  | castPtrExposeProv dst ptrSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs ptrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs ptrSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | int _ => cases hstep
      | wide _ => cases hstep
      | ptr p =>
        rw [hm₁] at hstep
        rw [hm₂]
        dsimp only at hstep ⊢
        cases hstep
        refine ⟨_, rfl, by rw [hregs], ?_, htrace⟩
        cases hp : p.prov with
        | none => exact hmem
        | wildcard => exact hmem
        | concrete id => exact memSameIgnoringExposed_expose_right id hmem
  | castPtrWithExposedProv dst addrSrc =>
    unfold stepStmt at hstep
    dsimp only at hstep
    cases hreg : lookupReg s₁.regs addrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      cases rv with
      | ptr _ => cases hstep
      | wide _ => cases hstep
      | int _ =>
        rw [hm₁] at hstep
        cases hstep
  | readPtr dst ptrSrc reqSize =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs ptrSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs ptrSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | int _ => cases hstep
      | wide _ => cases hstep
      | ptr p =>
        dsimp only at hstep ⊢
        have hnowc : p.prov ≠ .wildcard := hwc ptrSrc (.ptr p) hreg
        have hreadEq : readViaPtr s₁.mem p reqSize = readViaPtr s₂.mem p reqSize :=
          memSameIgnoringExposed_readViaPtr hmem hnowc
        rw [← hreadEq]
        cases hrd : readViaPtr s₁.mem p reqSize with
        | error _ => rw [hrd] at hstep; cases hstep
        | ok v =>
          rw [hrd] at hstep
          dsimp only at hstep
          cases hstep
          exact ⟨_, rfl, by rw [hregs], hmem, by rw [htrace]⟩
  | emitInt intSrc =>
    unfold stepStmt at hstep ⊢
    dsimp only at hstep ⊢
    cases hreg : lookupReg s₁.regs intSrc with
    | none => rw [hreg] at hstep; cases hstep
    | some rv =>
      rw [hreg] at hstep
      have hreg2 : lookupReg s₂.regs intSrc = some rv := by rw [← hregs]; exact hreg
      rw [hreg2]
      cases rv with
      | ptr _ => cases hstep
      | wide _ => cases hstep
      | int _ =>
        cases hstep
        exact ⟨_, rfl, hregs, hmem, by rw [htrace]⟩

/-- General program-level Strict Provenance Refinement Theorem:
    every program executing cleanly from related strict/permissive states under `.strict`
    executes cleanly under `.exposedPermissive` with identical final registers and observable trace. -/
theorem strict_provenance_refinement_aux (prog : List Stmt) :
    ∀ s₁ s₁' s₂ : MachineState,
      s₁.mode = .strict → s₂.mode = .exposedPermissive →
      RegsNoWildcard s₁.regs → StatesRelated s₁ s₂ →
      evalProg prog s₁ = .ok s₁' →
      ∃ s₂', evalProg prog s₂ = .ok s₂' ∧ StatesRelated s₁' s₂' := by
  induction prog with
  | nil =>
    intro s₁ s₁' s₂ _ _ _ hrel heval
    unfold evalProg at heval ⊢
    cases heval
    exact ⟨s₂, rfl, hrel⟩
  | cons s rest ih =>
    intro s₁ s₁' s₂ hm₁ hm₂ hwc hrel heval
    unfold evalProg at heval ⊢
    cases hstep : stepStmt s₁ s with
    | error _ => rw [hstep] at heval; cases heval
    | ok s₁Mid =>
      rw [hstep] at heval
      rcases strict_step_preserves_no_wildcard hm₁ hwc hstep with ⟨hwcMid, hmMid⟩
      rcases strict_step_simulates_to_exposed hm₁ hm₂ hwc hrel hstep with ⟨s₂Mid, hstep2, hrelMid⟩
      rw [hstep2]
      dsimp only at heval ⊢
      have hm2Mid : s₂Mid.mode = .exposedPermissive := (stepStmt_preserves_mode hstep2).trans hm₂
      exact ih s₁Mid s₁' s₂Mid hmMid hm2Mid hwcMid hrelMid heval

/-- Corollary from initial machine states: any program succeeding under `-Zmiri-strict-provenance`
    succeeds identically under permissive exposed-provenance Miri semantics with equal observable trace. -/
theorem strict_provenance_refinement (prog : List Stmt) (s₁' : MachineState)
    (heval : evalProg prog (initState .strict) = .ok s₁') :
    ∃ s₂', evalProg prog (initState .exposedPermissive) = .ok s₂' ∧ s₂'.trace = s₁'.trace := by
  have hwc0 : RegsNoWildcard (initState .strict).regs := by
    intro _ _ h; cases h
  have hrel0 : StatesRelated (initState .strict) (initState .exposedPermissive) :=
    ⟨rfl, trivial, rfl⟩
  rcases strict_provenance_refinement_aux prog (initState .strict) s₁' (initState .exposedPermissive)
    rfl rfl hwc0 hrel0 heval with ⟨s₂', heval2, hrel'⟩
  exact ⟨s₂', heval2, hrel'.2.2.symm⟩

/-- Separation Witness 1: `expose_provenance` + `with_exposed_provenance` succeeds (`trace = [42]`)
    under `.exposedPermissive`, yet is rejected with `.unsupportedStrictIntToPtr` under `.strict`
    (refuting reverse refinement). -/
noncomputable def progExposedRoundtrip : List Stmt :=
  [ .mkAlloc 0 0x1000 4 42
  , .castPtrExposeProv 1 0
  , .castPtrWithExposedProv 2 1
  , .readPtr 3 2 4 ]

theorem exposed_provenance_separation_witness :
    evalProg progExposedRoundtrip (initState .strict) = .error .unsupportedStrictIntToPtr ∧
    ∃ st', evalProg progExposedRoundtrip (initState .exposedPermissive) = .ok st' ∧
           st'.trace = [42] := by
  refine ⟨rfl, ⟨_, rfl, rfl⟩⟩

/-- Witness 2 (`expose_only_no_int_to_ptr` in live Miri): `PointerExposeProvenance` alone without
    any `PointerWithExposedProvenance` cast succeeds in BOTH `.strict` and `.exposedPermissive`. -/
noncomputable def progExposeOnly : List Stmt :=
  [ .mkAlloc 0 0x1000 4 42
  , .castPtrExposeProv 1 0
  , .emitInt 1
  , .readPtr 2 0 4 ]

theorem exposeOnly_succeeds_both_modes :
    (∃ st₁, evalProg progExposeOnly (initState .strict) = .ok st₁ ∧ st₁.trace = [0x1000, 42]) ∧
    (∃ st₂, evalProg progExposeOnly (initState .exposedPermissive) = .ok st₂ ∧ st₂.trace = [0x1000, 42]) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- Witness 3 (`addr_without_expose_then_int_to_ptr_ub`): using strict `addr()` (no expose) followed by
    `PointerWithExposedProvenance` fails in BOTH modes (`unsupportedStrictIntToPtr` in `.strict`,
    `wildcardUnexposed` on dereference in `.exposedPermissive`). -/
noncomputable def progAddrWithoutExpose : List Stmt :=
  [ .mkAlloc 0 0x1000 4 42
  , .ptrAddrStrict 1 0
  , .castPtrWithExposedProv 2 1
  , .readPtr 3 2 4 ]

theorem addrWithoutExpose_rejected_both_modes :
    evalProg progAddrWithoutExpose (initState .strict) = .error .unsupportedStrictIntToPtr ∧
    evalProg progAddrWithoutExpose (initState .exposedPermissive) = .error .wildcardUnexposed :=
  ⟨rfl, rfl⟩

/-- Witness 4 (`wildcard_wrapping_offset_to_exposed_alloc_ok` vs `wildcard_unexposed_target_alloc_ub`):
    a `.wildcard` pointer shifted onto a distinct *exposed* allocation reads `22` under
    `.exposedPermissive`, whereas shifting onto an *unexposed* allocation fails with `.wildcardUnexposed`. -/
noncomputable def progWildcardCrossExposed : List Stmt :=
  [ .mkAlloc 0 0x1000 4 11
  , .mkAlloc 1 0x2000 4 22
  , .castPtrExposeProv 2 0
  , .castPtrExposeProv 3 1
  , .castPtrWithExposedProv 4 2
  , .ptrWithAddrStrict 5 4 3
  , .readPtr 6 5 4 ]

noncomputable def progWildcardCrossUnexposed : List Stmt :=
  [ .mkAlloc 0 0x1000 4 11
  , .mkAlloc 1 0x2000 4 22
  , .castPtrExposeProv 2 0
  , .ptrAddrStrict 3 1
  , .castPtrWithExposedProv 4 2
  , .ptrWithAddrStrict 5 4 3
  , .readPtr 6 5 4 ]

theorem wildcardCrossAlloc_separation_witness :
    evalProg progWildcardCrossExposed (initState .strict) = .error .unsupportedStrictIntToPtr ∧
    (∃ st', evalProg progWildcardCrossExposed (initState .exposedPermissive) = .ok st' ∧
            st'.trace = [22]) ∧
    evalProg progWildcardCrossUnexposed (initState .exposedPermissive) = .error .wildcardUnexposed :=
  ⟨rfl, ⟨_, rfl, rfl⟩, rfl⟩

/-- Witness 5 (`without_provenance_zst_ok` vs `without_provenance_deref_ub`): `ptr::without_provenance`
    succeeds for non-null aligned ZST read (`reqSize = 0`) in BOTH modes, yet fails with `.noProvenance`
    for `reqSize = 4` in BOTH modes. -/
noncomputable def progWithoutProvZst : List Stmt :=
  [ .loadIntConst 0 0x10
  , .ptrWithoutProv 1 0
  , .readPtr 2 1 0 ]

noncomputable def progWithoutProvNonZst : List Stmt :=
  [ .loadIntConst 0 0x1000
  , .ptrWithoutProv 1 0
  , .readPtr 2 1 4 ]

theorem withoutProvenance_zst_vs_nonzst_witness :
    (∃ st₁, evalProg progWithoutProvZst (initState .strict) = .ok st₁ ∧ st₁.trace = [0]) ∧
    (∃ st₂, evalProg progWithoutProvZst (initState .exposedPermissive) = .ok st₂ ∧ st₂.trace = [0]) ∧
    evalProg progWithoutProvNonZst (initState .strict) = .error .noProvenance ∧
    evalProg progWithoutProvNonZst (initState .exposedPermissive) = .error .noProvenance :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl⟩

/-- Witness 6: wide-to-thin `CastKind::PtrToPtr` + strict `addr()` + `with_addr()` succeeds cleanly
    in BOTH `.strict` and `.exposedPermissive` modes. -/
noncomputable def progWideToThinStrict : List Stmt :=
  [ .mkAlloc 0 0x1000 8 99
  , .wideFromThin 1 0 2
  , .castPtrToPtrWideToThin 2 1
  , .ptrAddrStrict 3 2
  , .ptrWithAddrStrict 4 2 3
  , .readPtr 5 4 4 ]

theorem wideToThin_strict_provenance_witness :
    (∃ st₁, evalProg progWideToThinStrict (initState .strict) = .ok st₁ ∧ st₁.trace = [99]) ∧
    (∃ st₂, evalProg progWideToThinStrict (initState .exposedPermissive) = .ok st₂ ∧ st₂.trace = [99]) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end MirCastKindSoundness
