/- Probe E1: kernel-checkable (no bv_decide) proofs of 64-bit mul/div/shift identities that a
   RISC-V RV64IM model needs, using only Init lemmas + omega/simp/grind.  Every theorem is
   followed by `#print axioms`; the allowed set is [propext, Classical.choice, Quot.sound]. -/

-- (1) multiply by power of two = shift left (SLLI vs MUL)
theorem e1_mul8_shl (x : BitVec 64) : x * 8#64 = x <<< 3 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
#print axioms e1_mul8_shl

-- (2) unsigned divide by power of two = logical shift right (SRLI vs DIVU)
theorem e1_udiv8_shr (x : BitVec 64) : x / 8#64 = x >>> 3 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
#print axioms e1_udiv8_shr

-- (3) DIVU/REMU reconstruction: y ≠ 0 → (x / y) * y + x % y = x   (mod 2^64)
theorem e1_divu_remu (x y : BitVec 64) : (x / y) * y + x % y = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
  have hx := x.isLt
  rcases Nat.eq_zero_or_pos y.toNat with h0 | hpos
  · simp [h0]; omega
  · have hle : x.toNat / y.toNat * y.toNat ≤ x.toNat := Nat.div_mul_le_self _ _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hx), Nat.div_add_mod' x.toNat y.toNat,
      Nat.mod_eq_of_lt hx]
#print axioms e1_divu_remu

-- (4) REMU bound
theorem e1_remu_lt (x y : BitVec 64) (h : y ≠ 0#64) : x % y < y :=
  BitVec.umod_lt x (by
    rw [BitVec.lt_def]; have : y.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    simp; omega)
#print axioms e1_remu_lt

-- (5) MULHU as Nat: the high 64 bits of the 128-bit product
theorem e1_mulhu_nat (x y : BitVec 64) :
    ((x.zeroExtend 128 * y.zeroExtend 128).toNat) = x.toNat * y.toNat := by
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth]
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by decide))),
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by decide)))]
  apply Nat.mod_eq_of_lt
  have : x.toNat * y.toNat < 2^64 * 2^64 := Nat.mul_lt_mul_of_lt_of_lt hx hy
  simpa [← Nat.pow_add] using this
#print axioms e1_mulhu_nat

-- (6) ring identities over BitVec 64 via grind's commutative-ring module
theorem e1_grind_ring (a b c : BitVec 64) : (a + b) * c - a * c = b * c := by grind
#print axioms e1_grind_ring

-- (7) sub as add of two's complement (SUB vs ADD/XORI -1/ADDI 1)
theorem e1_sub_not (x y : BitVec 64) : x - y = x + ~~~y + 1 := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]; rfl
#print axioms e1_sub_not

-- (8) ADDW: low-32-bit add then sign-extend equals sign-extend of truncated 64-bit add
theorem e1_addw (x y : BitVec 64) :
    ((x.setWidth 32 + y.setWidth 32).signExtend 64) = ((x + y).setWidth 32).signExtend 64 := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega
#print axioms e1_addw

-- (9) RISC-V DIVU by zero returns all-ones, but Lean's `/` returns 0: a model-level guard
--     (closed instance by kernel decide; universal by the Init lemma `BitVec.udiv_zero`)
theorem e1_udiv_zero (x : BitVec 64) : x / 0#64 = 0#64 := BitVec.udiv_zero
#print axioms e1_udiv_zero

-- (10) bit-level identity via `BitVec.eq_of_getLsbD_eq` + simp (riscv-zkvm style), no SAT
theorem e1_and_or (x y : BitVec 64) : (x &&& y) ||| (x &&& ~~~y) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true,
    Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
#print axioms e1_and_or

-- (11) disjoint-bit add = or (byte/half assembly), via `BitVec.add_eq_or_of_and_eq_zero` + per-bit simp
theorem e1_concat (hi lo : BitVec 32) :
    (hi.setWidth 64 <<< 32) + lo.setWidth 64 = (hi.setWidth 64 <<< 32) ||| lo.setWidth 64 := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  by_cases h : i < 32 <;> simp [h, hi']
  exact fun _ => BitVec.getLsbD_of_ge lo i (by omega)
#print axioms e1_concat
