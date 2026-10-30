/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Round 2 — Track 4 Probe: Signed `MulWithOverflow`, 128-Bit Multi-Word
# Arithmetic, `BTL` Read-Only VTable Symbolic Memory, and `aegraph` Hoisting

This standalone Lean 4.34.1 mechanization resolves all four open questions and
deferred boundaries from Round 1 Track 5 without `bv_decide` or
`Lean.ofReduceBool`:

1. **Signed 64-Bit `MulWithOverflow` & 128-Bit Arithmetic (Section 1):**
   - Proves `riscv_smul_overflow_iff_spec` and
     `riscv_smul_overflow_bv_iff_spec`:
     for any 128-bit signed product `P = a * b ∈ [-2^127, 2^127 - 1]` split into
     floor quotient `hi = P / 2^64` (RISC-V `mulh` / AArch64 `smulh`) and
     non-negative remainder `lo = P % 2^64` (RISC-V `mul`) with arithmetic
     sign-extension `sgn = if lo ≥ 2^63 then -1 else 0` (`srai lo, 63`),
     `hi ≠ sgn ↔ (P < -2^63 ∨ P ≥ 2^63)`.
   - Proves `u128_add_pair_correct` and `u128_sub_pair_correct`: decomposing a
     128-bit integer `U128Pair (lo hi : BitVec 64)` into two 64-bit words with
     flagless carry `(lo₁ + lo₂) <ᵤ lo₁` and borrow `lo₁ <ᵤ (lo₁ - lo₂)`
     (`cranelift_codegen/v0_132/src/isa/riscv64/{lower.isle,inst.isle}`)
     computes the exact 128-bit modular sum/difference and 129-bit carry/borrow
     flag for all 64-bit word pairs.
   - Proves `u128_mul_pair_algebraic_identity` and `compiler_builtins_umulo_*`
     for multi-word 128-bit wrapping and checked multiplication
     (`compiler-builtins/src/int/mul.rs`).

2. **Partitioned Symbolic Memory (`smem`) for Read-Only VTable Loads vs. Stack
   Stores in `BTL` Superblock Validation (Section 2):**
   - Extends `SymState` with partitioned symbolic memory separating immutable
     `.rodata` / vtable loads (`MemExpr.loadRo`) from mutable stack stores
     (`SymStateWithMem.stackStores` and `MemExpr.stackSelect`).
   - Proves `validateSuperblockWithMem_sound`: `validateSuperblockWithMem`
     soundly validates superblocks that hoist and CSE read-only vtable loads
     (`vptr + 16` for `MetadataAlign`, `vptr + idx * 8` for `TraitVPtr`) across
     intervening stack stores (`storeStack`), while rejecting hoisting a
     `loadStack` across a potentially aliasing `storeStack`
     (`canary_hoist_stack_load_across_aliasing_store_rejected`).
   - Formalizes `GlobalRelocTable` to discharge `vtableStoredAt` across
     secondary supertrait `TraitVPtr` relocations at module initialization time
     (`relocTable_discharges_vtableStoredAt`).

3. **Acyclic E-Graph (`aegraph`) Loop-Invariant Code Motion (`loop_hoist_level`)
   and Trap-Guard Dominance (Section 3):**
   - Formalizes Cranelift's `loop_hoist_level` computation
     (`cranelift_codegen/v0_132/src/egraph/elaborate.rs:562-623`) and proves
     `pure_loop_hoist_sound`: hoisting a pure, non-trapping instruction whose
     operands are loop-invariant into the loop preheader preserves exact
     semantics across all trip counts `k : Nat` (including `k = 0`).
   - Proves the negative canary theorem
     `canary_hoist_trapping_div_above_zero_iteration_loop_unsound`: hoisting a
     trapping division (`udiv`) out of a zero-trip loop (`k = 0`) introduces a
     spurious division-by-zero trap when `denom = 0`, explaining why
     `is_pure_for_egraph` (`inst_predicates.rs:46-69`) excludes trapping
     instructions from the acyclic e-graph.
-/

namespace Round2Track4Probe

/-!
## Section 1: Signed 64-Bit `MulWithOverflow` and 128-Bit Lowering

In `rustc_codegen_cranelift/src/num.rs:285-296`, 64-bit signed multiplication
overflow (`BinOp::MulWithOverflow` on `i64`) is lowered to the 5-instruction
RISC-V sequence:
- `mulh hi, a, b` (`smulhi(lhs, rhs)`)
- `mul lo, a, b` (`imul(lhs, rhs)`)
- `srai sgn, lo, 63` (`sshr_imm_u(val, 63)`)
- `xor t, hi, sgn` (`bxor(val_hi, val_sign)`)
- `snez ovf, t` (`icmp_imm_u(IntCC::NotEqual, xor, 0)`)

On AArch64 (`cranelift_codegen/v0_132/src/isa/aarch64/lower.isle:3179-3192`),
the equivalent sequence is `mul out, a, b; smulh tmp, a, b; cmp tmp, out,
ASR #63; cset of, ne`.

Why does comparing the upper 64 bits `hi` against the sign-extended bit 63 of
the lower 64 bits `lo` exactly detect 64-bit signed multiplication overflow?
Because any integer `P : Int` admits a unique Euclidean division decomposition
`P = hi * 2^64 + lo` with `0 ≤ lo < 2^64` and `hi = P / 2^64` (floor division,
since `2^64 > 0`). The signed value of the truncated 64-bit word `lo` is
`lo - 2^64` when `lo ≥ 2^63` (sign bit 1, so `lo >>>ₛ 63 = -1`) and `lo` when
`lo < 2^63` (sign bit 0, so `lo >>>ₛ 63 = 0`). Thus `P` equals the signed 64-bit
interpretation of `lo` if and only if `P ∈ [-2^63, 2^63 - 1]`, which holds if
and only if `hi = sgn`.
-/

/-- Universal mathematical theorem for 64-bit signed multiplication overflow:
for any integer product `P : Int` decomposed via Euclidean floor division into
`hi = P / 2^64` and `lo = P % 2^64` with sign-extension word
`sgn = if lo ≥ 2^63 then -1 else 0`, `hi ≠ sgn` holds if and only if `P` lies
outside the signed 64-bit range `[-2^63, 2^63 - 1]`. Proved purely via `omega`
without `bv_decide` or `Lean.ofReduceBool`. -/
theorem riscv_smul_overflow_iff_spec (P : Int) :
    let hi : Int := P / (2 ^ 64 : Int)
    let lo : Int := P % (2 ^ 64 : Int)
    let sgn : Int := if lo ≥ (2 ^ 63 : Int) then -1 else 0
    (hi ≠ sgn) ↔ (P < -(2 ^ 63 : Int) ∨ P ≥ (2 ^ 63 : Int)) := by
  intro hi lo sgn
  omega

/-- Specification of 64-bit signed multiplication overflow over `BitVec 64`:
the exact integer product `a.toInt * b.toInt` falls outside
`[-2^63, 2^63 - 1]`. -/
def smulOverflowSpec (a b : BitVec 64) : Bool :=
  let P : Int := a.toInt * b.toInt
  decide (P < -(2 ^ 63 : Int) ∨ P ≥ (2 ^ 63 : Int))

/-- Models the RISC-V / Cranelift `i64` signed `MulWithOverflow` lowering
(`rustc_codegen_cranelift/src/num.rs:285-296`): splits the 128-bit signed
product `P = a.toInt * b.toInt` into `hi = P / 2^64` and `lo = P % 2^64`,
computes `sgn = if lo ≥ 2^63 then -1 else 0`, and tests `hi != sgn`. -/
def riscvSmulOverflowCheck (a b : BitVec 64) : Bool :=
  let P : Int := a.toInt * b.toInt
  let hi : Int := P / (2 ^ 64 : Int)
  let lo : Int := P % (2 ^ 64 : Int)
  let sgn : Int := if lo ≥ (2 ^ 63 : Int) then -1 else 0
  decide (hi ≠ sgn)

/-- Universal soundness of `riscvSmulOverflowCheck` for all `a b : BitVec 64`,
proved without `bv_decide`. -/
theorem riscv_smul_overflow_bv_iff_spec (a b : BitVec 64) :
    riscvSmulOverflowCheck a b = smulOverflowSpec a b := by
  simp only [riscvSmulOverflowCheck, smulOverflowSpec]
  apply decide_eq_decide.mpr
  exact riscv_smul_overflow_iff_spec (a.toInt * b.toInt)

/-- Furthermore, we prove that for any two 64-bit signed integers `a` and `b`,
their exact product `P = a.toInt * b.toInt` satisfies `hi ∈ [-2^63, 2^63]`, so
`hi` and `sgn ∈ {-1, 0}` never wrap modulo `2^64`: testing `hi ≠ sgn` in `Int`
is equivalent to testing `(hi % 2^64) ≠ (sgn % 2^64)` (RISC-V `xor t, hi, sgn;
snez ovf, t` on 64-bit registers). -/
theorem riscv_smul_xor_snez_iff_spec (P : Int)
    (hLo : -(2 ^ 127 : Int) ≤ P) (hHi : P ≤ (2 ^ 127 : Int) - 1) :
    let hiMod : Int := (P / (2 ^ 64 : Int)) % (2 ^ 64 : Int)
    let lo : Int := P % (2 ^ 64 : Int)
    let sgnMod : Int :=
      (if lo ≥ (2 ^ 63 : Int) then (-1 : Int) else 0) % (2 ^ 64 : Int)
    (hiMod ≠ sgnMod) ↔ (P < -(2 ^ 63 : Int) ∨ P ≥ (2 ^ 63 : Int)) := by
  intro hiMod lo sgnMod
  omega

/-!
### 1.2 Multi-Word 128-Bit (`u128` / `i128`) Addition, Subtraction, and Mul

On 64-bit targets (`RV64GC`, AArch64, x86-64), Cranelift legalizes `types::I128`
values into register pairs `ValueRegs(lo, hi)`:
- **128-bit Addition (`isa/riscv64/lower.isle:106-114, 340-353`):**
  Computes `sum_lo = x_lo + y_lo`, `carry = sltu(sum_lo, x_lo)`,
  `sum_hi = x_hi + y_hi`, `sum_hi_with_carry = sum_hi + carry`, and overflow:
  `sltu(sum_hi_with_carry, x_hi) | (carry & seqz(sum_hi_with_carry ^ x_hi))`.
- **128-bit Subtraction (`isa/riscv64/inst.isle:2848-2860`):**
  Computes `low = x_lo - y_lo`, `borrow = sltu(x_lo, low)`,
  `high_tmp = x_hi - y_hi`, and `high = high_tmp - borrow`.
-/

/-- A 128-bit unsigned integer represented as a pair of 64-bit registers
`(lo, hi)` (`ValueRegs` in Cranelift). -/
structure U128Pair where
  lo : BitVec 64
  hi : BitVec 64
  deriving DecidableEq, Repr

/-- Mathematical value of a `U128Pair` in `Nat`: `lo + hi * 2^64`. -/
def U128Pair.toNat (x : U128Pair) : Nat :=
  x.lo.toNat + x.hi.toNat * (2 ^ 64)

/-- Every `U128Pair` represents a natural number strictly less than `2^128`. -/
theorem U128Pair.toNat_lt (x : U128Pair) : x.toNat < 2 ^ 128 := by
  unfold U128Pair.toNat
  have hlo : x.lo.toNat < 2 ^ 64 := x.lo.isLt
  have hhi : x.hi.toNat < 2 ^ 64 := x.hi.isLt
  omega

/-- RISC-V 128-bit addition with overflow (`isa/riscv64/lower.isle:340-353`):
implements carry-chaining across `(lo, hi)` using flagless `sltu` comparisons.
-/
def riscvU128AddOverflow (x y : U128Pair) : U128Pair × Bool :=
  let sumLo := x.lo + y.lo
  let carryBool := BitVec.ult sumLo x.lo
  let carry : BitVec 64 := if carryBool then 1#64 else 0#64
  let sumHi := x.hi + y.hi
  let sumHiWithCarry := sumHi + carry
  let overflow :=
    BitVec.ult sumHiWithCarry x.hi ||
      (carryBool && (sumHiWithCarry == x.hi))
  ({ lo := sumLo, hi := sumHiWithCarry }, overflow)

/-- Helper lemma expressing `(a + b).toNat` for 64-bit bitvectors without
modular division:
`(a + b).toNat = a.toNat + b.toNat - (if (a+b) <ᵤ a then 2^64 else 0)`. -/
theorem bv64_add_toNat_carry (a b : BitVec 64) :
    (a + b).toNat =
      if a.toNat + b.toNat ≥ 2 ^ 64 then
        a.toNat + b.toNat - 2 ^ 64
      else
        a.toNat + b.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_add]
  split
  · rename_i hge
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_eq_of_lt (by omega)
  · rename_i hlt
    exact Nat.mod_eq_of_lt (by omega)

/-- Helper lemma: `BitVec.ult (a + b) a` is true iff `a.toNat + b.toNat ≥ 2^64`.
-/
theorem bv64_ult_add_iff (a b : BitVec 64) :
    (BitVec.ult (a + b) a = true) ↔ a.toNat + b.toNat ≥ 2 ^ 64 := by
  simp only [BitVec.ult, decide_eq_true_eq]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [bv64_add_toNat_carry]
  split <;> omega

/-- Helper lemma combining boolean `||` of two `decide` propositions. -/
theorem decide_or_eq_decide (P Q R : Prop) [Decidable P] [Decidable Q]
    [Decidable R] (h : (P ∨ Q) ↔ R) :
    (decide P || decide Q) = decide R := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq] at h ⊢ <;> exact h

/-- Universal correctness of Cranelift's RISC-V 128-bit `uadd_overflow` lowering
(`isa/riscv64/lower.isle:340-353`):

For all 128-bit register pairs `x` and `y`:
1. The returned pair `(sum_lo, sum_hi_with_carry)` has mathematical value
   `(x.toNat + y.toNat) % 2^128`.
2. The returned `overflow` boolean is `true` if and only if
   `x.toNat + y.toNat ≥ 2^128`.

Proved purely via `Nat` arithmetic and `omega`, with zero `Lean.ofReduceBool`.
-/
theorem u128_add_pair_correct (x y : U128Pair) :
    (riscvU128AddOverflow x y).1.toNat = (x.toNat + y.toNat) % (2 ^ 128) ∧
    (riscvU128AddOverflow x y).2 = decide (x.toNat + y.toNat ≥ 2 ^ 128) := by
  unfold riscvU128AddOverflow U128Pair.toNat
  dsimp only
  have hxlo : x.lo.toNat < 2 ^ 64 := x.lo.isLt
  have hxhi : x.hi.toNat < 2 ^ 64 := x.hi.isLt
  have hylo : y.lo.toNat < 2 ^ 64 := y.lo.isLt
  have hyhi : y.hi.toNat < 2 ^ 64 := y.hi.isLt
  have hCarryIff := bv64_ult_add_iff x.lo y.lo
  have hBeq : ∀ (u v : BitVec 64), (u == v) = decide (u.toNat = v.toNat) := by
    intro u v
    by_cases h : u = v
    · subst h; simp
    · have hne : u.toNat ≠ v.toNat := fun heq => h (BitVec.eq_of_toNat_eq heq)
      simp [h, hne]
  rw [hBeq]
  clear hBeq
  by_cases hlo_ovf : x.lo.toNat + y.lo.toNat ≥ 2 ^ 64
  · have hCarryTrue : BitVec.ult (x.lo + y.lo) x.lo = true :=
      hCarryIff.mpr hlo_ovf
    clear hCarryIff
    simp only [hCarryTrue, ↓reduceIte, Bool.true_and]
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    constructor
    · omega
    · apply decide_or_eq_decide
      omega
  · have hCarryFalse : BitVec.ult (x.lo + y.lo) x.lo = false :=
      Bool.eq_false_iff.mpr (fun ht => hlo_ovf (hCarryIff.mp ht))
    clear hCarryIff
    simp only [hCarryFalse, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
      Bool.or_false]
    simp only [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat]
    constructor
    · omega
    · apply decide_eq_decide.mpr
      omega

/-- Helper lemma expressing `(a - b).toNat` for 64-bit bitvectors. -/
theorem bv64_sub_toNat_borrow (a b : BitVec 64) :
    (a - b).toNat =
      if a.toNat < b.toNat then
        2 ^ 64 - b.toNat + a.toNat
      else
        a.toNat - b.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_sub]
  split
  · rename_i hlt
    exact Nat.mod_eq_of_lt (by omega)
  · rename_i hge
    have hge' : 2 ^ 64 - b.toNat + a.toNat ≥ 2 ^ 64 := by omega
    rw [Nat.mod_eq_sub_mod hge']
    have hsub : 2 ^ 64 - b.toNat + a.toNat - 2 ^ 64 = a.toNat - b.toNat := by
      omega
    rw [hsub]
    exact Nat.mod_eq_of_lt (by omega)

/-- Helper lemma: `BitVec.ult a (a - b)` is true iff `a.toNat < b.toNat`. -/
theorem bv64_ult_sub_iff (a b : BitVec 64) :
    (BitVec.ult a (a - b) = true) ↔ a.toNat < b.toNat := by
  simp only [BitVec.ult, decide_eq_true_eq]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [bv64_sub_toNat_borrow]
  split <;> omega

/-- RISC-V 128-bit subtraction (`sub_i128` in `isa/riscv64/inst.isle:2848-2860`)
paired with 128-bit unsigned borrow detection:
computes `low = x.lo - y.lo`, `borrow = sltu(x.lo, low)`,
`high_tmp = x.hi - y.hi`, `high = high_tmp - borrow`, and
`underflow = (x.hi <ᵤ y.hi) || ((x.hi == y.hi) && borrow)`. -/
def riscvU128SubOverflow (x y : U128Pair) : U128Pair × Bool :=
  let diffLo := x.lo - y.lo
  let borrowBool := BitVec.ult x.lo diffLo
  let borrow : BitVec 64 := if borrowBool then 1#64 else 0#64
  let diffHiTmp := x.hi - y.hi
  let diffHi := diffHiTmp - borrow
  let underflow :=
    BitVec.ult x.hi y.hi || ((x.hi == y.hi) && borrowBool)
  ({ lo := diffLo, hi := diffHi }, underflow)

/-- Universal correctness of Cranelift's RISC-V 128-bit subtraction (`sub_i128`
in `isa/riscv64/inst.isle:2848-2860`) and borrow check:

For all 128-bit register pairs `x` and `y`:
1. The returned pair `(low, high)` has mathematical value
   `(2^128 - y.toNat + x.toNat) % 2^128`.
2. The returned `underflow` boolean is `true` if and only if
   `x.toNat < y.toNat`.

Proved purely via `Nat` arithmetic and `omega`, with zero `Lean.ofReduceBool`.
-/
theorem u128_sub_pair_correct (x y : U128Pair) :
    (riscvU128SubOverflow x y).1.toNat =
      (2 ^ 128 - y.toNat + x.toNat) % (2 ^ 128) ∧
    (riscvU128SubOverflow x y).2 = decide (x.toNat < y.toNat) := by
  unfold riscvU128SubOverflow U128Pair.toNat
  dsimp only
  have hxlo : x.lo.toNat < 2 ^ 64 := x.lo.isLt
  have hxhi : x.hi.toNat < 2 ^ 64 := x.hi.isLt
  have hylo : y.lo.toNat < 2 ^ 64 := y.lo.isLt
  have hyhi : y.hi.toNat < 2 ^ 64 := y.hi.isLt
  have hBorrowIff := bv64_ult_sub_iff x.lo y.lo
  have hBeq : ∀ (u v : BitVec 64), (u == v) = decide (u.toNat = v.toNat) := by
    intro u v
    by_cases h : u = v
    · subst h; simp
    · have hne : u.toNat ≠ v.toNat := fun heq => h (BitVec.eq_of_toNat_eq heq)
      simp [h, hne]
  rw [hBeq]
  clear hBeq
  by_cases hlo_borrow : x.lo.toNat < y.lo.toNat
  · have hBorrowTrue : BitVec.ult x.lo (x.lo - y.lo) = true :=
      hBorrowIff.mpr hlo_borrow
    clear hBorrowIff
    simp only [hBorrowTrue, ↓reduceIte, Bool.and_true]
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
    constructor
    · omega
    · apply decide_or_eq_decide
      omega
  · have hBorrowFalse : BitVec.ult x.lo (x.lo - y.lo) = false :=
      Bool.eq_false_iff.mpr (fun ht => hlo_borrow (hBorrowIff.mp ht))
    clear hBorrowIff
    simp only [hBorrowFalse, Bool.false_eq_true, ↓reduceIte, Bool.and_false,
      Bool.or_false]
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
    constructor
    · omega
    · apply decide_eq_decide.mpr
      omega

/-- Helper bilinear expansion for two-word radix-`B` integers. -/
theorem radix_mul_expand (xLo xHi yLo yHi B : Nat) :
    (xLo + xHi * B) * (yLo + yHi * B) =
      xLo * yLo + (xLo * yHi + xHi * yLo) * B + (xHi * yHi) * (B * B) := by
  calc
    (xLo + xHi * B) * (yLo + yHi * B)
      = xLo * (yLo + yHi * B) + (xHi * B) * (yLo + yHi * B) := by
        rw [Nat.add_mul]
    _ = (xLo * yLo + xLo * (yHi * B)) +
          ((xHi * B) * yLo + (xHi * B) * (yHi * B)) := by
        rw [Nat.mul_add, Nat.mul_add]
    _ = (xLo * yLo + (xLo * yHi) * B) +
          ((xHi * yLo) * B + (xHi * yHi) * (B * B)) := by
        rw [← Nat.mul_assoc xLo yHi B, Nat.mul_assoc xHi B yLo,
            Nat.mul_comm B yLo, ← Nat.mul_assoc xHi yLo B,
            Nat.mul_assoc xHi B (yHi * B), ← Nat.mul_assoc B yHi B,
            Nat.mul_comm B yHi, Nat.mul_assoc yHi B B,
            ← Nat.mul_assoc xHi yHi (B * B)]
    _ = xLo * yLo + (xLo * yHi + xHi * yLo) * B + (xHi * yHi) * (B * B) := by
        rw [Nat.add_mul (xLo * yHi) (xHi * yLo) B]
        omega

/-- 128-bit wrapping multiplication identity (`isa/riscv64/lower.isle:498-522`,
`isa/aarch64/lower.isle:797-822`, `isa/x64/lower.isle:1090-1119`):
Splitting `x = x_lo + x_hi * 2^64` and `y = y_lo + y_hi * 2^64`, the cross-term
`x_hi * y_hi * 2^128` vanishes modulo `2^128`, and decomposing
`x_lo * y_lo = mulhu(x_lo, y_lo) * 2^64 + (x_lo * y_lo) % 2^64` reduces the
entire 128-bit product modulo `2^128` to:
`dst_lo = (x_lo * y_lo) % 2^64` and
`dst_hi = (mulhu(x_lo, y_lo) + x_lo * y_hi + x_hi * y_lo) % 2^64`. -/
theorem u128_mul_pair_algebraic_identity (xLo xHi yLo yHi : Nat) :
    let prodLoFull := xLo * yLo
    let dstLo := prodLoFull % (2 ^ 64)
    let mulhu := prodLoFull / (2 ^ 64)
    let dstHi := (mulhu + xLo * yHi + xHi * yLo) % (2 ^ 64)
    dstLo + dstHi * (2 ^ 64) =
      ((xLo + xHi * (2 ^ 64)) * (yLo + yHi * (2 ^ 64))) % (2 ^ 128) := by
  intro prodLoFull dstLo mulhu dstHi
  have hExpand := radix_mul_expand xLo xHi yLo yHi (2 ^ 64)
  have hBB : (2 ^ 64) * (2 ^ 64) = 2 ^ 128 := (Nat.pow_add 2 64 64).symm
  rw [hBB] at hExpand
  rw [hExpand]
  dsimp [dstLo, mulhu, dstHi, prodLoFull]
  omega

/-- `compiler-builtins` `UMulo::mulo` (`compiler-builtins/src/int/mul.rs:33-54`)
for `__rust_u128_mulo` (called by
`rustc_codegen_cranelift/src/codegen_i128.rs:51-83`):
1. `(false, false)` (`xHi > 0 ∧ yHi > 0`): `x * y ≥ 2^64 * 2^64 = 2^128`, so
   overflow is guaranteed.
2. `(true, true)` (`xHi = 0 ∧ yHi = 0`): `x * y = xLo * yLo < 2^128`, so
   overflow is impossible.
3. `(true, false)` (`xHi = 0`): decomposing `mulLo = xLo * yLo` and
   `mulHi = xLo * yHi = mulHiLo + mulHiHi * 2^64`, the 128-bit product
   overflows `2^128` iff `mulLo + mulHiLo * 2^64 ≥ 2^128 ∨ mulHiHi > 0`. -/
theorem compiler_builtins_umulo_both_hi_nonzero_overflows
    (xLo xHi yLo yHi : Nat) (hxHi : xHi > 0) (hyHi : yHi > 0) :
    (xLo + xHi * (2 ^ 64)) * (yLo + yHi * (2 ^ 64)) ≥ 2 ^ 128 := by
  have h1 : xLo + xHi * (2 ^ 64) ≥ 2 ^ 64 := by omega
  have h2 : yLo + yHi * (2 ^ 64) ≥ 2 ^ 64 := by omega
  have h3 :
      (2 ^ 64) * (2 ^ 64) ≤ (xLo + xHi * (2 ^ 64)) * (yLo + yHi * (2 ^ 64)) :=
    Nat.mul_le_mul h1 h2
  omega

theorem compiler_builtins_umulo_both_hi_zero_no_overflow (xLo yLo : Nat)
    (hxLo : xLo < 2 ^ 64) (hyLo : yLo < 2 ^ 64) :
    xLo * yLo < 2 ^ 128 := by
  have h : xLo * yLo < (2 ^ 64) * (2 ^ 64) := Nat.mul_lt_mul'' hxLo hyLo
  have hBB : (2 ^ 64) * (2 ^ 64) = 2 ^ 128 := (Nat.pow_add 2 64 64).symm
  omega

theorem compiler_builtins_umulo_lhs_hi_zero_iff (xLo yLo yHi : Nat) :
    let mulLo := xLo * yLo
    let mulHi := xLo * yHi
    let mulHiLo := mulHi % (2 ^ 64)
    let mulHiHi := mulHi / (2 ^ 64)
    (xLo * (yLo + yHi * (2 ^ 64)) ≥ 2 ^ 128) ↔
      (mulLo + mulHiLo * (2 ^ 64) ≥ 2 ^ 128 ∨ mulHiHi > 0) := by
  intro mulLo mulHi mulHiLo mulHiHi
  rw [Nat.mul_add, ← Nat.mul_assoc]
  dsimp [mulLo, mulHiLo, mulHiHi, mulHi]
  omega

/-!
## Section 2: Partitioned Symbolic Memory (`smem`) for Read-Only VTables in `BTL`

In Round 1 (Questions 1 & 4), `symExecSuperblock` tracked only register
expressions and trap guards. However, lowering dynamic DST field projections
(`dstTailOffsetDyn`) and Rust 1.86 secondary supertrait upcasts
(`coerceDynUpcast`) emits memory loads from vtable pointers (`vptr + 16` and
`vptr + idx * 8`) with `MemFlags::trusted().with_readonly()`
(`rustc_codegen_cranelift/src/vtable.rs:8-42`, `unsize.rs:50-57`).

In Cranelift (`inst_predicates.rs:46-54`), loads with `readonly && notrap &&
can_move` are classified as pure e-graph nodes, allowing them to be hoisted,
deduplicated (CSE'd), and folded into RISC-V `Zba`/`Zbb`/`AMode` instructions
across intervening stack stores (`StackStore`).

Following Chamois-CompCert's `BTL_SEsimuref.v`, we extend our expression AST and
symbolic state with **partitioned symbolic memory**:
- `.loadRo (addr : MemExpr)` reads from the immutable `.rodata` / vtable memory
  partition (`roMem : WordMem`). Because `storeStack` only mutates `stackMem`,
  `.loadRo` expressions do not depend on the symbolic stack memory token!
- `.initStackLoad (addr : MemExpr)` and `.stackSelect storeAddr storeVal
  fallback loadAddr` represent reads from the symbolic stack memory log
  `stackStores : List (MemExpr × MemExpr)`, accurately tracking store-to-load
  forwarding and potential aliasing on the stack.
-/

abbrev Reg := Nat
abbrev WordMem := BitVec 64 → BitVec 64
abbrev RegEnv := Reg → BitVec 64

/-- Unified 64-bit expression AST extended with partitioned symbolic memory
reads (`loadRo` for immutable `.rodata`/vtable memory and `initStackLoad` /
`stackSelect` for stack memory). -/
inductive MemExpr where
  | var (r : Reg)
  | const (c : BitVec 64)
  | not_ (x : MemExpr)
  | add (x y : MemExpr)
  | sub (x y : MemExpr)
  | mul (x y : MemExpr)
  | and_ (x y : MemExpr)
  | or_ (x y : MemExpr)
  | shl (x y : MemExpr)
  | ult (x y : MemExpr)
  | sh1add (idx base : MemExpr)
  | sh2add (idx base : MemExpr)
  | sh3add (idx base : MemExpr)
  | andn (x y : MemExpr)
  | amodeAddImm (base : MemExpr) (disp : BitVec 64)
  /-- Immutable `.rodata` / vtable word load (`vtable_memflags()`).
  Depends only on the address expression `addr`, never on `stackMem`. -/
  | loadRo (addr : MemExpr)
  /-- Word load from the initial entry stack memory at `addr`. -/
  | initStackLoad (addr : MemExpr)
  /-- Symbolic store-buffer selection (`BTL` `smem` read after `storeStack`):
  if `loadAddr` evaluates to the same address as `storeAddr`, yields `storeVal`;
  otherwise yields `fallback`. -/
  | stackSelect (storeAddr storeVal fallback loadAddr : MemExpr)
  deriving DecidableEq, Repr

/-- Denotational semantics of `MemExpr` under initial register environment
`env`, immutable read-only memory `roMem`, and initial stack memory `initStack`.
-/
def MemExpr.eval (env : RegEnv) (roMem initStack : WordMem) :
    MemExpr → BitVec 64
  | .var r => env r
  | .const c => c
  | .not_ x => ~~~(x.eval env roMem initStack)
  | .add x y => x.eval env roMem initStack + y.eval env roMem initStack
  | .sub x y => x.eval env roMem initStack - y.eval env roMem initStack
  | .mul x y => x.eval env roMem initStack * y.eval env roMem initStack
  | .and_ x y => x.eval env roMem initStack &&& y.eval env roMem initStack
  | .or_ x y => x.eval env roMem initStack ||| y.eval env roMem initStack
  | .shl x y => x.eval env roMem initStack <<< y.eval env roMem initStack
  | .ult x y =>
    if BitVec.ult (x.eval env roMem initStack) (y.eval env roMem initStack) then
      1#64
    else
      0#64
  | .sh1add idx base =>
    base.eval env roMem initStack + (idx.eval env roMem initStack <<< 1#64)
  | .sh2add idx base =>
    base.eval env roMem initStack + (idx.eval env roMem initStack <<< 2#64)
  | .sh3add idx base =>
    base.eval env roMem initStack + (idx.eval env roMem initStack <<< 3#64)
  | .andn x y => x.eval env roMem initStack &&& ~~~(y.eval env roMem initStack)
  | .amodeAddImm base disp => base.eval env roMem initStack + disp
  | .loadRo addr => roMem (addr.eval env roMem initStack)
  | .initStackLoad addr => initStack (addr.eval env roMem initStack)
  | .stackSelect storeAddr storeVal fallback loadAddr =>
    if loadAddr.eval env roMem initStack ==
       storeAddr.eval env roMem initStack then
      storeVal.eval env roMem initStack
    else
      fallback.eval env roMem initStack

/-- Multiplication by 2, 4, 8 and alignment mask helper lemmas (reused for
`normMemExpr`). -/
theorem bv64_mul_two_eq_shl_one (x : BitVec 64) :
    x * 2#64 = x <<< 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

theorem bv64_mul_four_eq_shl_two (x : BitVec 64) :
    x * 4#64 = x <<< 2#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

theorem bv64_mul_eight_eq_shl_three (x : BitVec 64) :
    x * 8#64 = x <<< 3#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft]
  omega

theorem bv64_not_sub_one_eq_neg (align : BitVec 64) :
    ~~~(align - 1#64) = 0#64 - align := by
  bv_omega

/-- Canonical expression normalizer for `MemExpr`: expands target-specific
`Zba` (`sh1add`, `sh2add`, `sh3add`), `Zbb` (`andn`), `amodeAddImm`, and
two's-complement alignment masks into canonical form, recursively normalizing
inside `loadRo`, `initStackLoad`, and `stackSelect`. -/
def normMemExpr : MemExpr → MemExpr
  | .var r => .var r
  | .const c => .const c
  | .not_ x => .not_ (normMemExpr x)
  | .add x y => .add (normMemExpr x) (normMemExpr y)
  | .sub x y => .sub (normMemExpr x) (normMemExpr y)
  | .mul x y =>
    let nx := normMemExpr x
    let ny := normMemExpr y
    match ny with
    | .const 2#64 => .shl nx (.const 1#64)
    | .const 4#64 => .shl nx (.const 2#64)
    | .const 8#64 => .shl nx (.const 3#64)
    | _ => .mul nx ny
  | .and_ x y =>
    let nx := normMemExpr x
    let ny := normMemExpr y
    match ny with
    | .sub (.const 0#64) align =>
      .and_ nx (.not_ (.sub align (.const 1#64)))
    | _ => .and_ nx ny
  | .or_ x y => .or_ (normMemExpr x) (normMemExpr y)
  | .shl x y => .shl (normMemExpr x) (normMemExpr y)
  | .ult x y => .ult (normMemExpr x) (normMemExpr y)
  | .sh1add idx base =>
    .add (normMemExpr base) (.shl (normMemExpr idx) (.const 1#64))
  | .sh2add idx base =>
    .add (normMemExpr base) (.shl (normMemExpr idx) (.const 2#64))
  | .sh3add idx base =>
    .add (normMemExpr base) (.shl (normMemExpr idx) (.const 3#64))
  | .andn x y => .and_ (normMemExpr x) (.not_ (normMemExpr y))
  | .amodeAddImm base disp => .add (normMemExpr base) (.const disp)
  | .loadRo addr => .loadRo (normMemExpr addr)
  | .initStackLoad addr => .initStackLoad (normMemExpr addr)
  | .stackSelect sAddr sVal fb lAddr =>
    .stackSelect (normMemExpr sAddr) (normMemExpr sVal)
      (normMemExpr fb) (normMemExpr lAddr)

/-- Universal soundness of `normMemExpr`. -/
theorem normMemExpr_sound (env : RegEnv) (roMem initStack : WordMem)
    (e : MemExpr) :
    (normMemExpr e).eval env roMem initStack = e.eval env roMem initStack := by
  induction e with
  | var r => rfl
  | const c => rfl
  | not_ x ih => simp [normMemExpr, MemExpr.eval, ih]
  | add x y ihx ihy => simp [normMemExpr, MemExpr.eval, ihx, ihy]
  | sub x y ihx ihy => simp [normMemExpr, MemExpr.eval, ihx, ihy]
  | mul x y ihx ihy =>
    simp only [normMemExpr]
    split
    · rename_i heq
      have hy : (normMemExpr y).eval env roMem initStack = 2#64 := by
        rw [heq]; rfl
      simp [MemExpr.eval, ihx, ← ihy, hy, bv64_mul_two_eq_shl_one]
    · rename_i heq
      have hy : (normMemExpr y).eval env roMem initStack = 4#64 := by
        rw [heq]; rfl
      simp [MemExpr.eval, ihx, ← ihy, hy, bv64_mul_four_eq_shl_two]
    · rename_i heq
      have hy : (normMemExpr y).eval env roMem initStack = 8#64 := by
        rw [heq]; rfl
      simp [MemExpr.eval, ihx, ← ihy, hy, bv64_mul_eight_eq_shl_three]
    · simp [MemExpr.eval, ihx, ihy]
  | and_ x y ihx ihy =>
    simp only [normMemExpr]
    split
    · rename_i align heq
      have hy :
          (MemExpr.sub (.const 0#64) align).eval env roMem initStack =
            y.eval env roMem initStack := by
        rw [← heq, ihy]
      simp only [MemExpr.eval] at hy ⊢
      rw [ihx, ← hy, bv64_not_sub_one_eq_neg]
    · simp [MemExpr.eval, ihx, ihy]
  | or_ x y ihx ihy => simp [normMemExpr, MemExpr.eval, ihx, ihy]
  | shl x y ihx ihy => simp [normMemExpr, MemExpr.eval, ihx, ihy]
  | ult x y ihx ihy => simp [normMemExpr, MemExpr.eval, ihx, ihy]
  | sh1add idx base ih1 ih2 => simp [normMemExpr, MemExpr.eval, ih1, ih2]
  | sh2add idx base ih1 ih2 => simp [normMemExpr, MemExpr.eval, ih1, ih2]
  | sh3add idx base ih1 ih2 => simp [normMemExpr, MemExpr.eval, ih1, ih2]
  | andn x y ih1 ih2 => simp [normMemExpr, MemExpr.eval, ih1, ih2]
  | amodeAddImm base disp ih => simp [normMemExpr, MemExpr.eval, ih]
  | loadRo addr ih => simp only [normMemExpr, MemExpr.eval, ih]
  | initStackLoad addr ih => simp only [normMemExpr, MemExpr.eval, ih]
  | stackSelect sAddr sVal fb lAddr ih1 ih2 ih3 ih4 =>
    simp only [normMemExpr, MemExpr.eval, ih1, ih2, ih3, ih4]

/-- Substitutes symbolic register mapping `sregs` into `e`. -/
def substMemExpr (sregs : Reg → MemExpr) : MemExpr → MemExpr
  | .var r => sregs r
  | .const c => .const c
  | .not_ x => .not_ (substMemExpr sregs x)
  | .add x y => .add (substMemExpr sregs x) (substMemExpr sregs y)
  | .sub x y => .sub (substMemExpr sregs x) (substMemExpr sregs y)
  | .mul x y => .mul (substMemExpr sregs x) (substMemExpr sregs y)
  | .and_ x y => .and_ (substMemExpr sregs x) (substMemExpr sregs y)
  | .or_ x y => .or_ (substMemExpr sregs x) (substMemExpr sregs y)
  | .shl x y => .shl (substMemExpr sregs x) (substMemExpr sregs y)
  | .ult x y => .ult (substMemExpr sregs x) (substMemExpr sregs y)
  | .sh1add idx base =>
    .sh1add (substMemExpr sregs idx) (substMemExpr sregs base)
  | .sh2add idx base =>
    .sh2add (substMemExpr sregs idx) (substMemExpr sregs base)
  | .sh3add idx base =>
    .sh3add (substMemExpr sregs idx) (substMemExpr sregs base)
  | .andn x y => .andn (substMemExpr sregs x) (substMemExpr sregs y)
  | .amodeAddImm base disp => .amodeAddImm (substMemExpr sregs base) disp
  | .loadRo addr => .loadRo (substMemExpr sregs addr)
  | .initStackLoad addr => .initStackLoad (substMemExpr sregs addr)
  | .stackSelect sAddr sVal fb lAddr =>
    .stackSelect (substMemExpr sregs sAddr) (substMemExpr sregs sVal)
      (substMemExpr sregs fb) (substMemExpr sregs lAddr)

theorem substMemExpr_eval (initEnv : RegEnv) (roMem initStack : WordMem)
    (sregs : Reg → MemExpr) (e : MemExpr) :
    (substMemExpr sregs e).eval initEnv roMem initStack =
      e.eval (fun r => (sregs r).eval initEnv roMem initStack)
        roMem initStack := by
  induction e <;> simp only [substMemExpr, MemExpr.eval, *]

/-- Superblock instructions with partitioned memory operations:
- `assign dst rhs`: register assignment
- `loadRo dst addr`: read-only load from `.rodata` / vtable memory
- `loadStack dst addr`: load from stack frame memory
- `storeStack addr val`: store to stack frame memory
- `assertNonZero cond`: trap guard assertion -/
inductive MemSBInstr where
  | assign (dst : Reg) (rhs : MemExpr)
  | loadRo (dst : Reg) (addr : MemExpr)
  | loadStack (dst : Reg) (addr : MemExpr)
  | storeStack (addr : MemExpr) (val : MemExpr)
  | assertNonZero (cond : MemExpr)
  deriving DecidableEq, Repr

/-- Concrete execution state of a superblock: registers `regs` and mutable stack
memory `stackMem` (with `roMem` held immutable as a context parameter). -/
structure ConcreteMemState where
  regs : RegEnv
  stackMem : WordMem

/-- Concrete execution of a `List MemSBInstr` superblock. -/
def execSuperblockWithMem (roMem initStack : WordMem) (st : ConcreteMemState) :
    List MemSBInstr → Option ConcreteMemState
  | [] => some st
  | .assign dst rhs :: rest =>
    let v := rhs.eval st.regs roMem initStack
    execSuperblockWithMem roMem initStack
      { st with regs := fun r => if r = dst then v else st.regs r } rest
  | .loadRo dst addr :: rest =>
    let a := addr.eval st.regs roMem initStack
    let v := roMem a
    execSuperblockWithMem roMem initStack
      { st with regs := fun r => if r = dst then v else st.regs r } rest
  | .loadStack dst addr :: rest =>
    let a := addr.eval st.regs roMem initStack
    let v := st.stackMem a
    execSuperblockWithMem roMem initStack
      { st with regs := fun r => if r = dst then v else st.regs r } rest
  | .storeStack addr val :: rest =>
    let a := addr.eval st.regs roMem initStack
    let v := val.eval st.regs roMem initStack
    let stackMem' : WordMem := fun p => if p == a then v else st.stackMem p
    execSuperblockWithMem roMem initStack
      { st with stackMem := stackMem' } rest
  | .assertNonZero cond :: rest =>
    if cond.eval st.regs roMem initStack == 0#64 then none
    else execSuperblockWithMem roMem initStack st rest

/-- Symbolic state (`BTL` `SymState` extended with symbolic stack store log
`stackStores : List (MemExpr × MemExpr)`). Read-only vtable memory requires no
mutable symbolic token because `roMem` is invariant across all instructions. -/
structure SymStateWithMem where
  sregs : Reg → MemExpr
  stackStores : List (MemExpr × MemExpr)
  guards : List MemExpr

def initSymStateWithMem : SymStateWithMem :=
  { sregs := MemExpr.var, stackStores := [], guards := [] }

/-- Symbolically reads a stack address `loadAddr` against the symbolic store log
`stackStores`. Performs exact store-to-load forwarding when `loadAddr ==
storeAddr`, and constructs a `.stackSelect` node otherwise. -/
def symReadStack : List (MemExpr × MemExpr) → MemExpr → MemExpr
  | [], loadAddr => .initStackLoad loadAddr
  | (storeAddr, storeVal) :: rest, loadAddr =>
    if loadAddr == storeAddr then
      storeVal
    else
      .stackSelect storeAddr storeVal (symReadStack rest loadAddr) loadAddr

/-- Evaluates a symbolic stack store log under `(initEnv, roMem, initStack)`. -/
def evalSymStackStores (initEnv : RegEnv) (roMem initStack : WordMem) :
    List (MemExpr × MemExpr) → WordMem
  | [] => initStack
  | (storeAddr, storeVal) :: rest =>
    let prev := evalSymStackStores initEnv roMem initStack rest
    let a := storeAddr.eval initEnv roMem initStack
    let v := storeVal.eval initEnv roMem initStack
    fun p => if p == a then v else prev p

/-- Key lemma: evaluating `symReadStack stackStores loadAddr` equals reading
`loadAddr` from the concrete stack produced by `evalSymStackStores`. -/
theorem symReadStack_eval (initEnv : RegEnv) (roMem initStack : WordMem)
    (stackStores : List (MemExpr × MemExpr)) (loadAddr : MemExpr) :
    (symReadStack stackStores loadAddr).eval initEnv roMem initStack =
      evalSymStackStores initEnv roMem initStack stackStores
        (loadAddr.eval initEnv roMem initStack) := by
  induction stackStores with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨sAddr, sVal⟩
    simp only [symReadStack, evalSymStackStores]
    by_cases hEq : (loadAddr == sAddr) = true
    · simp only [hEq, ↓reduceIte]
      have hIdent : loadAddr = sAddr := eq_of_beq hEq
      subst hIdent
      simp
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte, MemExpr.eval, ih]

/-- Symbolic execution of a `List MemSBInstr` superblock. Notice how `.loadRo`
produces `.loadRo symAddr` completely independent of `st.stackStores`, enabling
read-only vtable loads to be freely hoisted and CSE'd across `storeStack`! -/
def symExecWithMem (st : SymStateWithMem) : List MemSBInstr → SymStateWithMem
  | [] => st
  | .assign dst rhs :: rest =>
    let symVal := normMemExpr (substMemExpr st.sregs rhs)
    symExecWithMem
      { st with sregs := fun r => if r = dst then symVal else st.sregs r } rest
  | .loadRo dst addr :: rest =>
    let symAddr := normMemExpr (substMemExpr st.sregs addr)
    let symVal := MemExpr.loadRo symAddr
    symExecWithMem
      { st with sregs := fun r => if r = dst then symVal else st.sregs r } rest
  | .loadStack dst addr :: rest =>
    let symAddr := normMemExpr (substMemExpr st.sregs addr)
    let symVal := symReadStack st.stackStores symAddr
    symExecWithMem
      { st with sregs := fun r => if r = dst then symVal else st.sregs r } rest
  | .storeStack addr val :: rest =>
    let symAddr := normMemExpr (substMemExpr st.sregs addr)
    let symVal := normMemExpr (substMemExpr st.sregs val)
    symExecWithMem
      { st with stackStores := (symAddr, symVal) :: st.stackStores } rest
  | .assertNonZero cond :: rest =>
    let symCond := normMemExpr (substMemExpr st.sregs cond)
    symExecWithMem { st with guards := st.guards ++ [symCond] } rest

/-- Evaluates a `SymStateWithMem` into an `Option ConcreteMemState`. -/
def evalSymStateWithMem (initEnv : RegEnv) (roMem initStack : WordMem)
    (st : SymStateWithMem) : Option ConcreteMemState :=
  if st.guards.any (fun g => g.eval initEnv roMem initStack == 0#64) then
    none
  else
    some {
      regs := fun r => (st.sregs r).eval initEnv roMem initStack
      stackMem := evalSymStackStores initEnv roMem initStack st.stackStores
    }

/-- Simulation theorem for `symExecWithMem`: symbolic execution commutes with
concrete execution for all instructions (`assign`, `loadRo`, `loadStack`,
`storeStack`, `assertNonZero`). -/
theorem symExecWithMem_correct (initEnv : RegEnv) (roMem initStack : WordMem)
    (st : SymStateWithMem) (block : List MemSBInstr) :
    evalSymStateWithMem initEnv roMem initStack (symExecWithMem st block) =
      match evalSymStateWithMem initEnv roMem initStack st with
      | none => none
      | some cst => execSuperblockWithMem roMem initStack cst block := by
  induction block generalizing st with
  | nil =>
    unfold symExecWithMem execSuperblockWithMem
    cases evalSymStateWithMem initEnv roMem initStack st <;> rfl
  | cons instr rest ih =>
    cases instr with
    | assign dst rhs =>
      simp only [symExecWithMem, ih]
      unfold evalSymStateWithMem
      by_cases hg :
          (st.guards.any fun g => g.eval initEnv roMem initStack == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, execSuperblockWithMem]
        congr 1
        simp only [ConcreteMemState.mk.injEq, and_true]
        funext r
        split
        · rw [normMemExpr_sound, substMemExpr_eval]
        · rfl
    | loadRo dst addr =>
      simp only [symExecWithMem, ih]
      unfold evalSymStateWithMem
      by_cases hg :
          (st.guards.any fun g => g.eval initEnv roMem initStack == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, execSuperblockWithMem]
        congr 1
        simp only [ConcreteMemState.mk.injEq, and_true]
        funext r
        split
        · simp only [MemExpr.eval, normMemExpr_sound, substMemExpr_eval]
        · rfl
    | loadStack dst addr =>
      simp only [symExecWithMem, ih]
      unfold evalSymStateWithMem
      by_cases hg :
          (st.guards.any fun g => g.eval initEnv roMem initStack == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, execSuperblockWithMem]
        congr 1
        simp only [ConcreteMemState.mk.injEq, and_true]
        funext r
        split
        · rw [symReadStack_eval, normMemExpr_sound, substMemExpr_eval]
        · rfl
    | storeStack addr val =>
      simp only [symExecWithMem, ih]
      unfold evalSymStateWithMem
      by_cases hg :
          (st.guards.any fun g => g.eval initEnv roMem initStack == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_eq_true, ↓reduceIte, execSuperblockWithMem,
          evalSymStackStores, normMemExpr_sound, substMemExpr_eval]
    | assertNonZero cond =>
      simp only [symExecWithMem, ih]
      unfold evalSymStateWithMem
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
      by_cases hg :
          (st.guards.any fun g => g.eval initEnv roMem initStack == 0#64) = true
      · simp [hg]
      · simp only [hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
          execSuperblockWithMem, normMemExpr_sound, substMemExpr_eval]
        by_cases hc :
            (cond.eval (fun r => (st.sregs r).eval initEnv roMem initStack)
              roMem initStack == 0#64) = true
        · simp [hc]
        · simp [hc]

/-- Superblock validator with partitioned memory (`roMem` + `stackMem`): checks
that trap guards, symbolic stack stores, and all `liveOut` registers match after
canonical normalization. -/
def validateSuperblockWithMem (src opt : List MemSBInstr)
    (liveOut : List Reg) : Bool :=
  let stSrc := symExecWithMem initSymStateWithMem src
  let stOpt := symExecWithMem initSymStateWithMem opt
  (stSrc.guards == stOpt.guards) &&
    (stSrc.stackStores == stOpt.stackStores) &&
    liveOut.all (fun r => stSrc.sregs r == stOpt.sregs r)

/-- Main soundness theorem for `validateSuperblockWithMem`: if validation
returns `true`, then for every initial register environment `initEnv`, read-only
memory `roMem`, and initial stack `initStack`, `src` traps iff `opt` traps, and
when both succeed, their resulting stack memories are identical and their final
register files agree on all `r ∈ liveOut`. -/
theorem validateSuperblockWithMem_sound (initEnv : RegEnv)
    (roMem initStack : WordMem) (src opt : List MemSBInstr)
    (liveOut : List Reg)
    (hval : validateSuperblockWithMem src opt liveOut = true) :
    let initCst : ConcreteMemState := { regs := initEnv, stackMem := initStack }
    match execSuperblockWithMem roMem initStack initCst src,
          execSuperblockWithMem roMem initStack initCst opt with
    | none, none => True
    | some cstSrc, some cstOpt =>
      cstSrc.stackMem = cstOpt.stackMem ∧
      ∀ r ∈ liveOut, cstSrc.regs r = cstOpt.regs r
    | _, _ => False := by
  intro initCst
  have hInit :
      evalSymStateWithMem initEnv roMem initStack initSymStateWithMem =
        some initCst := rfl
  have hSrc :=
    symExecWithMem_correct initEnv roMem initStack initSymStateWithMem src
  have hOpt :=
    symExecWithMem_correct initEnv roMem initStack initSymStateWithMem opt
  rw [hInit] at hSrc hOpt
  dsimp only at hSrc hOpt
  rw [← hSrc, ← hOpt]
  unfold validateSuperblockWithMem at hval
  rcases Bool.and_eq_true_iff.mp hval with ⟨hGS, hRegs⟩
  rcases Bool.and_eq_true_iff.mp hGS with ⟨hGuards, hStores⟩
  have hGuardsEq := eq_of_beq hGuards
  have hStoresEq := eq_of_beq hStores
  unfold evalSymStateWithMem
  rw [hGuardsEq, hStoresEq]
  by_cases hg :
      ((symExecWithMem initSymStateWithMem opt).guards.any
        fun g => g.eval initEnv roMem initStack == 0#64) = true
  · simp [hg]
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, ?_⟩
    intro r hr
    have hrBeq := List.all_eq_true.mp hRegs r hr
    have hrEq := eq_of_beq hrBeq
    rw [hrEq]

/-- **Positive Verification Example (`vtableHoistAndCseAcrossStackStore`):**
Consider a basic block that:
1. Loads `vtable.align` from `vptr + 16` (`loadRo 3 (var 1 + 16)`),
2. Spills an intermediate value `var 2` to the stack at `sp + 8`
   (`storeStack (var 0 + 8) (var 2)`),
3. Reloads `vtable.align` from `vptr + 16` (`loadRo 4 (var 1 + 16)`) to align a
   custom DST tail offset `(4 + (align - 1)) &&& (0 - align)`.

The optimized superblock `vtableCseOptBlock` hoists and CSEs the second
read-only vtable load across the intervening `storeStack`, lowers `vptr + 16`
and `sp + 8` to `amodeAddImm`, and lowers the alignment mask to RISC-V `Zbb`
`andn`. `validateSuperblockWithMem` verifies this transformation by `rfl`! -/
def vtableUnoptBlock : List MemSBInstr :=
  [ .loadRo 3 (.add (.var 1) (.const 16#64)),
    .storeStack (.add (.var 0) (.const 8#64)) (.var 2),
    .loadRo 4 (.add (.var 1) (.const 16#64)),
    .assign 5 (.and_ (.add (.const 4#64) (.sub (.var 4) (.const 1#64)))
                     (.sub (.const 0#64) (.var 4))) ]

def vtableCseOptBlock : List MemSBInstr :=
  [ .loadRo 3 (.amodeAddImm (.var 1) 16#64),
    .assign 5 (.andn (.add (.const 4#64) (.sub (.var 3) (.const 1#64)))
                     (.sub (.var 3) (.const 1#64))),
    .storeStack (.amodeAddImm (.var 0) 8#64) (.var 2) ]

theorem vtableHoistAndCseAcrossStackStore_verified
    (initEnv : RegEnv) (roMem initStack : WordMem) :
    let initCst : ConcreteMemState := { regs := initEnv, stackMem := initStack }
    match execSuperblockWithMem roMem initStack initCst vtableUnoptBlock,
          execSuperblockWithMem roMem initStack initCst vtableCseOptBlock with
    | none, none => True
    | some cstSrc, some cstOpt =>
      cstSrc.stackMem = cstOpt.stackMem ∧
      ∀ r ∈ [3, 5], cstSrc.regs r = cstOpt.regs r
    | _, _ => False :=
  validateSuperblockWithMem_sound initEnv roMem initStack
    vtableUnoptBlock vtableCseOptBlock [3, 5] rfl

/-- **Positive Verification Example 2 (`stackStoreToLoadForwarding_verified`):**
Validates store-to-load forwarding across an intervening vtable load: storing
`var 2` to `sp + 16` (`var 0 + 16`), loading `vtable.size` from `vptr + 8`
(`loadRo 3 (var 1 + 8)`), and reloading from `sp + 16` via `amodeAddImm` is
validated by `rfl` against directly reusing `var 2`. -/
def stackForwardSrcBlock : List MemSBInstr :=
  [ .storeStack (.add (.var 0) (.const 16#64)) (.var 2),
    .loadRo 3 (.add (.var 1) (.const 8#64)),
    .loadStack 4 (.amodeAddImm (.var 0) 16#64),
    .assign 5 (.add (.var 3) (.var 4)) ]

def stackForwardOptBlock : List MemSBInstr :=
  [ .loadRo 3 (.amodeAddImm (.var 1) 8#64),
    .storeStack (.amodeAddImm (.var 0) 16#64) (.var 2),
    .assign 5 (.add (.var 3) (.var 2)) ]

theorem stackStoreToLoadForwarding_verified
    (initEnv : RegEnv) (roMem initStack : WordMem) :
    let initCst : ConcreteMemState := { regs := initEnv, stackMem := initStack }
    match execSuperblockWithMem roMem initStack initCst stackForwardSrcBlock,
          execSuperblockWithMem roMem initStack initCst
            stackForwardOptBlock with
    | none, none => True
    | some cstSrc, some cstOpt =>
      cstSrc.stackMem = cstOpt.stackMem ∧
      ∀ r ∈ [3, 5], cstSrc.regs r = cstOpt.regs r
    | _, _ => False :=
  validateSuperblockWithMem_sound initEnv roMem initStack
    stackForwardSrcBlock stackForwardOptBlock [3, 5] rfl

/-- **Negative Canary
(`canary_hoist_stack_load_across_aliasing_store_rejected`):**

Unlike `loadRo`, a mutable stack load (`loadStack 3 (var 1)`) CANNOT be hoisted
across a potentially aliasing `storeStack (var 0) (var 2)`:
1. `validateSuperblockWithMem` rejects the hoisted block (`= false`).
2. When `var 0 = var 1 = 0x7000`, `var 2 = 99`, and `initStack 0x7000 = 10`,
   the unoptimized block produces `r3 = 99` whereas the illegally hoisted block
   produces `r3 = 10` (`99 ≠ 10`). -/
def stackLoadAfterStoreSrc : List MemSBInstr :=
  [ .storeStack (.var 0) (.var 2),
    .loadStack 3 (.var 1) ]

def stackLoadHoistedBuggy : List MemSBInstr :=
  [ .loadStack 3 (.var 1),
    .storeStack (.var 0) (.var 2) ]

theorem canary_hoist_stack_load_across_aliasing_store_rejected :
    validateSuperblockWithMem stackLoadAfterStoreSrc stackLoadHoistedBuggy [3] =
      false ∧
    (let env : RegEnv := fun r =>
       if r = 0 then 0x7000#64
       else if r = 1 then 0x7000#64
       else if r = 2 then 99#64
       else 0#64
     let roMem : WordMem := fun _ => 0#64
     let initStack : WordMem := fun _ => 10#64
     let initCst : ConcreteMemState := { regs := env, stackMem := initStack }
     match execSuperblockWithMem roMem initStack initCst stackLoadAfterStoreSrc,
           execSuperblockWithMem roMem initStack initCst
             stackLoadHoistedBuggy with
     | some cstSrc, some cstBuggy =>
       cstSrc.regs 3 = 99#64 ∧
       cstBuggy.regs 3 = 10#64 ∧
       cstSrc.regs 3 ≠ cstBuggy.regs 3
     | _, _ => False) := by
  refine ⟨rfl, ⟨rfl, rfl, by decide⟩⟩

/-!
### 2.2 Global Relocation Table (`GlobalRelocTable`) Discharging `vtableStoredAt`

To resolve Round 1 Question 4 (the Track 3 / Track 4 interface for `.rodata`
vtables), we model how `rustc`
(`rustc_trait_selection/src/traits/vtable.rs:146-156` and
`rustc_codegen_cranelift/src/vtable.rs:64-85`) emits vtables as global
read-only allocations containing symbolic relocations (`AllocId` for secondary
supertrait sub-vtables and `FnId` for trait methods).
-/

/-- Concrete vtable entry after relocation resolution. -/
inductive VtblEntry where
  | metadataDropInPlace (fnPtr : BitVec 64)
  | metadataSize (sizeBytes : BitVec 64)
  | metadataAlign (alignBytes : BitVec 64)
  | vacant
  | method (fnPtr : BitVec 64)
  | traitVPtr (subVtableAddr : BitVec 64)
  deriving DecidableEq, Repr

def VtblEntry.toWord : VtblEntry → BitVec 64
  | .metadataDropInPlace fnPtr => fnPtr
  | .metadataSize s => s
  | .metadataAlign a => a
  | .vacant => 0#64
  | .method fnPtr => fnPtr
  | .traitVPtr subVtableAddr => subVtableAddr

def vtableStoredAt (roMem : WordMem) (vtableAddr : BitVec 64)
    (entries : List VtblEntry) : Prop :=
  ∀ (idx : Nat) (entry : VtblEntry),
    entries[idx]? = some entry →
    roMem (vtableAddr + BitVec.ofNat 64 (idx * 8)) = entry.toWord

/-- Pre-linking symbolic vtable entry in the compiler's global `.rodata`
allocation table: references function symbol IDs (`fnSymId`) and vtable
allocation IDs (`subVtableAllocId`). -/
inductive RelocVtblEntry where
  | metadataDropInPlace (fnSymId : Nat)
  | metadataSize (sizeBytes : BitVec 64)
  | metadataAlign (alignBytes : BitVec 64)
  | vacant
  | method (fnSymId : Nat)
  | traitVPtr (subVtableAllocId : Nat)
  deriving DecidableEq, Repr

/-- Module-level global relocation table mapping symbol IDs and vtable
`AllocId`s to their relocated `.rodata` / `.text` base addresses. -/
structure GlobalRelocTable where
  fnSymAddr : Nat → BitVec 64
  vtableAllocAddr : Nat → BitVec 64
  vtableAllocEntries : Nat → List RelocVtblEntry

/-- Resolves a symbolic `RelocVtblEntry` using `GlobalRelocTable`. -/
def GlobalRelocTable.resolveEntry (tbl : GlobalRelocTable) :
    RelocVtblEntry → VtblEntry
  | .metadataDropInPlace sym => .metadataDropInPlace (tbl.fnSymAddr sym)
  | .metadataSize s => .metadataSize s
  | .metadataAlign a => .metadataAlign a
  | .vacant => .vacant
  | .method sym => .method (tbl.fnSymAddr sym)
  | .traitVPtr allocId => .traitVPtr (tbl.vtableAllocAddr allocId)

/-- Resolves all entries of vtable allocation `allocId`. -/
def GlobalRelocTable.resolveVtable (tbl : GlobalRelocTable) (allocId : Nat) :
    List VtblEntry :=
  (tbl.vtableAllocEntries allocId).map tbl.resolveEntry

/-- Module initialization invariant: `roMem` loads the relocated words of every
vtable allocation `allocId` at `tbl.vtableAllocAddr allocId`. -/
def roMemInitializedFromRelocTable (tbl : GlobalRelocTable)
    (roMem : WordMem) : Prop :=
  ∀ (allocId : Nat) (idx : Nat) (rentry : RelocVtblEntry),
    (tbl.vtableAllocEntries allocId)[idx]? = some rentry →
    roMem (tbl.vtableAllocAddr allocId + BitVec.ofNat 64 (idx * 8)) =
      (tbl.resolveEntry rentry).toWord

/-- Automatic discharge of `vtableStoredAt` for every vtable allocation in a
relocated module (`Round 1 Question 4`). -/
theorem relocTable_discharges_vtableStoredAt (tbl : GlobalRelocTable)
    (roMem : WordMem) (hInit : roMemInitializedFromRelocTable tbl roMem)
    (allocId : Nat) :
    vtableStoredAt roMem (tbl.vtableAllocAddr allocId)
      (tbl.resolveVtable allocId) := by
  intro idx entry hGet
  unfold GlobalRelocTable.resolveVtable at hGet
  rw [List.getElem?_map] at hGet
  cases hRaw : (tbl.vtableAllocEntries allocId)[idx]? with
  | none =>
    rw [hRaw] at hGet
    contradiction
  | some rentry =>
    rw [hRaw] at hGet
    injection hGet with hEq
    subst hEq
    exact hInit allocId idx rentry hRaw

/-- Furthermore, when a primary vtable `subAllocId` contains
`RelocVtblEntry.traitVPtr superAllocId` at `entryIdx`, loading slot `entryIdx`
from `roMem` yields `tbl.vtableAllocAddr superAllocId`, which itself satisfies
`vtableStoredAt` for the secondary supertrait's vtable! -/
theorem relocTable_chained_traitVPtr_stored (tbl : GlobalRelocTable)
    (roMem : WordMem) (hInit : roMemInitializedFromRelocTable tbl roMem)
    (subAllocId superAllocId entryIdx : Nat)
    (hSlot :
      (tbl.vtableAllocEntries subAllocId)[entryIdx]? =
        some (.traitVPtr superAllocId)) :
    let subVptr := tbl.vtableAllocAddr subAllocId
    let loadedSuperVptr := roMem (subVptr + BitVec.ofNat 64 (entryIdx * 8))
    loadedSuperVptr = tbl.vtableAllocAddr superAllocId ∧
    vtableStoredAt roMem loadedSuperVptr (tbl.resolveVtable superAllocId) := by
  intro subVptr loadedSuperVptr
  have hLoad := hInit subAllocId entryIdx (.traitVPtr superAllocId) hSlot
  simp only [GlobalRelocTable.resolveEntry, VtblEntry.toWord] at hLoad
  dsimp only [loadedSuperVptr, subVptr]
  rw [hLoad]
  exact ⟨rfl, relocTable_discharges_vtableStoredAt tbl roMem hInit superAllocId⟩

/-!
## Section 3: Acyclic E-Graph Loop Hoisting (`loop_hoist_level`) and Trap Guards

In `cranelift_codegen/v0_132/src/egraph/elaborate.rs:562-623`, when elaborating
an instruction `inst` inside a nested loop stack `self.loop_stack`, Cranelift
computes `loop_hoist_level`:
```rust
let loop_hoist_level = arg_values
    .iter()
    .map(|&value| {
        self.loop_stack
            .iter()
            .position(|loop_entry| {
                !self.loop_analysis.is_in_loop(value.in_block, loop_entry.lp)
            })
            .unwrap_or(self.loop_stack.len())
    })
    .max()
    .unwrap_or(self.loop_stack.len().saturating_sub(1));
```
If `loop_hoist_level < self.loop_stack.len()`, the instruction is hoisted out of
all inner loops `loop_stack[loop_hoist_level..]` and placed at the end of
`loop_stack[loop_hoist_level].hoist_block` (the immediate dominator of that
loop's header).

Crucially, `elaborate.rs:722-725` asserts `is_pure_for_egraph(self.func, inst)`.
We now mechanize:
1. `computeLoopHoistLevel` and its loop-invariance guarantee.
2. **Positive Theorem (`pure_loop_hoist_sound`):** Hoisting a pure, non-trapping
   instruction whose operands are not modified by the loop body into the loop
   preheader (`hoist_block`) preserves exact semantics across **all** iteration
   counts `k : Nat` (including `k = 0`, where the hoisted instruction executes
   once in the preheader and its destination register is dead outside the loop).
3. **Negative Canary
   (`canary_hoist_trapping_div_above_zero_iteration_loop_unsound`):**
   Hoisting a potentially trapping instruction (`udiv` when `denom = 0`) into
   the preheader above a loop that executes `k = 0` iterations introduces a
   spurious trap on `k = 0`, refuting semantic preservation!
-/

abbrev BlockId := Nat
abbrev LoopId := Nat

/-- Entry in `Elaborator.loop_stack` (`elaborate.rs:102-114`). -/
structure LoopStackEntry where
  lp : LoopId
  hoistBlock : BlockId
  scopeDepth : Nat
  deriving DecidableEq, Repr

/-- Finds the first index in `xs` satisfying `p`, returning `xs.length` if none
matches (mirroring Rust's `iter().position(p).unwrap_or(xs.len())`). -/
def findPosOrLen (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if p x then 0 else 1 + findPosOrLen p xs

theorem findPosOrLen_le_length (p : α → Bool) (xs : List α) :
    findPosOrLen p xs ≤ xs.length := by
  induction xs with
  | nil => simp [findPosOrLen]
  | cons x xs ih =>
    simp only [findPosOrLen, List.length_cons]
    split <;> omega

/-- Mirrors Cranelift's per-argument hoist-level calculation
(`elaborate.rs:569-575`): finds the outermost loop in `loopStack` that does not
contain `argDefBlock`. -/
def argHoistLevel (isInLoop : BlockId → LoopId → Bool)
    (loopStack : List LoopStackEntry) (argDefBlock : BlockId) : Nat :=
  findPosOrLen (fun entry => !isInLoop argDefBlock entry.lp) loopStack

/-- Mirrors Cranelift's `loop_hoist_level` (`elaborate.rs:562-583`) across all
argument defining blocks `argBlocks`. -/
def computeLoopHoistLevel (isInLoop : BlockId → LoopId → Bool)
    (loopStack : List LoopStackEntry) (argBlocks : List BlockId) : Nat :=
  match argBlocks with
  | [] => loopStack.length - 1
  | b :: bs =>
    bs.foldl
      (fun acc blk => Nat.max acc (argHoistLevel isInLoop loopStack blk))
      (argHoistLevel isInLoop loopStack b)

/-- Every argument's individual `argHoistLevel` is bounded above by the folded
maximum. -/
theorem foldl_max_ge_init (f : α → Nat) (init : Nat) (xs : List α) :
    init ≤ xs.foldl (fun acc x => Nat.max acc (f x)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl init
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h1 : init ≤ Nat.max init (f x) := Nat.le_max_left init (f x)
    have h2 := ih (Nat.max init (f x))
    omega

theorem foldl_max_ge_mem (f : α → Nat) (init : Nat) (xs : List α) (y : α)
    (hy : y ∈ xs) :
    f y ≤ xs.foldl (fun acc x => Nat.max acc (f x)) init := by
  induction xs generalizing init with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hrest
    · have h1 : f y ≤ Nat.max init (f y) := Nat.le_max_right init (f y)
      have h2 := foldl_max_ge_init f (Nat.max init (f y)) xs
      omega
    · exact ih (Nat.max init (f x)) hrest

/-- Soundness of `argHoistLevel`: if `argHoistLevel isInLoop loopStack b = lvl`
and `lvl < loopStack.length`, then `loopStack[lvl]` is a loop in `loopStack`
outside which `b` is defined (`isInLoop b entry.lp = false`). -/
theorem argHoistLevel_not_in_loop (isInLoop : BlockId → LoopId → Bool)
    (loopStack : List LoopStackEntry) (b : BlockId) (entry : LoopStackEntry)
    (hGet : loopStack[argHoistLevel isInLoop loopStack b]? = some entry) :
    isInLoop b entry.lp = false := by
  induction loopStack with
  | nil =>
    simp [argHoistLevel, findPosOrLen] at hGet
  | cons hd tl ih =>
    unfold argHoistLevel findPosOrLen at hGet
    by_cases hOut : (!isInLoop b hd.lp) = true
    · simp only [hOut, ↓reduceIte, List.getElem?_cons_zero,
        Option.some.injEq] at hGet
      subst hGet
      exact Bool.not_eq_true' (isInLoop b hd.lp) |>.mp hOut
    · simp only [hOut, Bool.false_eq_true, ↓reduceIte] at hGet
      have hGet' : tl[argHoistLevel isInLoop tl b]? = some entry := by
        unfold argHoistLevel
        simpa [Nat.add_comm 1] using hGet
      exact ih hGet'

/-- Instructions in a loop body, distinguishing pure ALU expressions (`assign`)
from potentially trapping unsigned division (`udiv`, which traps on division by
zero). -/
inductive LoopInstr where
  | assign (dst : Reg) (rhs : MemExpr)
  | udiv (dst : Reg) (num : Reg) (denom : Reg)
  deriving DecidableEq, Repr

/-- Free registers read by a `MemExpr`. -/
def MemExpr.vars : MemExpr → List Reg
  | .var r => [r]
  | .const _ => []
  | .not_ x | .amodeAddImm x _ | .loadRo x | .initStackLoad x => x.vars
  | .add x y | .sub x y | .mul x y | .and_ x y | .or_ x y
  | .shl x y | .ult x y | .sh1add x y | .sh2add x y | .sh3add x y
  | .andn x y => x.vars ++ y.vars
  | .stackSelect a b c d => a.vars ++ b.vars ++ c.vars ++ d.vars

/-- If two register environments agree on all variables in `e.vars`, then `e`
evaluates to the same value in both environments. -/
theorem MemExpr.eval_eq_of_vars_eq (env1 env2 : RegEnv)
    (roMem initStack : WordMem) (e : MemExpr)
    (hAgree : ∀ r ∈ e.vars, env1 r = env2 r) :
    e.eval env1 roMem initStack = e.eval env2 roMem initStack := by
  induction e with
  | var r =>
    exact hAgree r (List.mem_singleton.mpr rfl)
  | const c => rfl
  | not_ x ih =>
    simp [MemExpr.eval, ih hAgree]
  | amodeAddImm x disp ih =>
    simp [MemExpr.eval, ih hAgree]
  | loadRo x ih =>
    simp [MemExpr.eval, ih hAgree]
  | initStackLoad x ih =>
    simp [MemExpr.eval, ih hAgree]
  | add x y ihx ihy | sub x y ihx ihy | mul x y ihx ihy
  | and_ x y ihx ihy | or_ x y ihx ihy | shl x y ihx ihy
  | ult x y ihx ihy | sh1add x y ihx ihy | sh2add x y ihx ihy
  | sh3add x y ihx ihy | andn x y ihx ihy =>
    have hx : ∀ r ∈ x.vars, env1 r = env2 r := fun r hr =>
      hAgree r (List.mem_append_left _ hr)
    have hy : ∀ r ∈ y.vars, env1 r = env2 r := fun r hr =>
      hAgree r (List.mem_append_right _ hr)
    simp [MemExpr.eval, ihx hx, ihy hy]
  | stackSelect a b c d iha ihb ihc ihd =>
    have ha : ∀ r ∈ a.vars, env1 r = env2 r := fun r hr =>
      hAgree r (by simp [MemExpr.vars, hr])
    have hb : ∀ r ∈ b.vars, env1 r = env2 r := fun r hr =>
      hAgree r (by simp [MemExpr.vars, hr])
    have hc : ∀ r ∈ c.vars, env1 r = env2 r := fun r hr =>
      hAgree r (by simp [MemExpr.vars, hr])
    have hd : ∀ r ∈ d.vars, env1 r = env2 r := fun r hr =>
      hAgree r (by simp [MemExpr.vars, hr])
    simp [MemExpr.eval, iha ha, ihb hb, ihc hc, ihd hd]

/-- Concrete execution of a single `LoopInstr`. `udiv` traps (`none`) when the
divisor register is `0#64`. -/
def execLoopInstr (roMem initStack : WordMem) (env : RegEnv) :
    LoopInstr → Option RegEnv
  | .assign dst rhs =>
    let v := rhs.eval env roMem initStack
    some (fun r => if r = dst then v else env r)
  | .udiv dst num denom =>
    if env denom == 0#64 then
      none
    else
      let v := env num / env denom
      some (fun r => if r = dst then v else env r)

/-- Concrete execution of a loop body (`List LoopInstr`). -/
def execLoopBody (roMem initStack : WordMem) (env : RegEnv) :
    List LoopInstr → Option RegEnv
  | [] => some env
  | i :: rest =>
    match execLoopInstr roMem initStack env i with
    | none => none
    | some env' => execLoopBody roMem initStack env' rest

/-- Concrete execution of `k` iterations of a loop body. -/
def execLoopIterations (roMem initStack : WordMem) :
    Nat → RegEnv → List LoopInstr → Option RegEnv
  | 0, env, _ => some env
  | k + 1, env, body =>
    match execLoopBody roMem initStack env body with
    | none => none
    | some env' => execLoopIterations roMem initStack k env' body

/-- Predicate checking that a loop body `rest` neither writes to `dst` nor
writes to any register in `invVars`, and that `dst ∉ invVars`. -/
def instrPreservesRegs (dst : Reg) (invVars : List Reg) : LoopInstr → Bool
  | .assign d _ => (d != dst) && !(invVars.contains d)
  | .udiv d _ _ => (d != dst) && !(invVars.contains d)

def bodyPreservesRegs (dst : Reg) (invVars : List Reg)
    (rest : List LoopInstr) : Bool :=
  !(invVars.contains dst) && rest.all (instrPreservesRegs dst invVars)

/-- If `bodyPreservesRegs dst rhs.vars rest = true`, then executing `rest` from
any environment `env` where `env dst = rhs.eval env roMem initStack` preserves
both `env' dst = rhs.eval env roMem initStack` and the values of all registers
in `rhs.vars`. -/
theorem execLoopBody_preserves_invariant_aux (roMem initStack : WordMem)
    (dst : Reg) (rhs : MemExpr) (rest : List LoopInstr) (baseEnv env : RegEnv)
    (hAll : rest.all (instrPreservesRegs dst rhs.vars) = true)
    (hVars : ∀ r ∈ rhs.vars, env r = baseEnv r)
    (hDst : env dst = rhs.eval baseEnv roMem initStack) :
    match execLoopBody roMem initStack env rest with
    | none => True
    | some env' =>
      (∀ r ∈ rhs.vars, env' r = baseEnv r) ∧
      env' dst = rhs.eval baseEnv roMem initStack := by
  induction rest generalizing env with
  | nil =>
    simp only [execLoopBody]
    exact ⟨hVars, hDst⟩
  | cons i tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hAll
    rcases hAll with ⟨hi, htl⟩
    cases i with
    | assign d e =>
      simp only [instrPreservesRegs, Bool.and_eq_true, bne_iff_ne,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hi
      rcases hi with ⟨hd_ne_dst, hd_not_in_vars⟩
      simp only [execLoopBody, execLoopInstr]
      apply ih _ htl
      · intro r hr
        have hr_ne_d : r ≠ d := fun heq => hd_not_in_vars (heq ▸ hr)
        simp [hr_ne_d, hVars r hr]
      · simp [Ne.symm hd_ne_dst, hDst]
    | udiv d num denom =>
      simp only [instrPreservesRegs, Bool.and_eq_true, bne_iff_ne,
        Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hi
      rcases hi with ⟨hd_ne_dst, hd_not_in_vars⟩
      simp only [execLoopBody, execLoopInstr]
      by_cases hZero : (env denom == 0#64) = true
      · simp [hZero]
      · simp only [hZero, Bool.false_eq_true, ↓reduceIte]
        apply ih _ htl
        · intro r hr
          have hr_ne_d : r ≠ d := fun heq => hd_not_in_vars (heq ▸ hr)
          simp [hr_ne_d, hVars r hr]
        · simp [Ne.symm hd_ne_dst, hDst]

theorem execLoopBody_preserves_invariant (roMem initStack : WordMem)
    (dst : Reg) (rhs : MemExpr) (rest : List LoopInstr) (baseEnv env : RegEnv)
    (hPres : bodyPreservesRegs dst rhs.vars rest = true)
    (hVars : ∀ r ∈ rhs.vars, env r = baseEnv r)
    (hDst : env dst = rhs.eval baseEnv roMem initStack) :
    match execLoopBody roMem initStack env rest with
    | none => True
    | some env' =>
      (∀ r ∈ rhs.vars, env' r = baseEnv r) ∧
      env' dst = rhs.eval baseEnv roMem initStack := by
  unfold bodyPreservesRegs at hPres
  rcases Bool.and_eq_true_iff.mp hPres with ⟨_, hAll⟩
  exact execLoopBody_preserves_invariant_aux roMem initStack dst rhs rest
    baseEnv env hAll hVars hDst

/-- Executing `[LoopInstr.assign dst rhs] ++ rest` from an environment `env`
that ALREADY satisfies `env dst = rhs.eval env roMem initStack` is identical to
executing `rest` directly, because assigning `dst := rhs.eval env` is a no-op
write of the value already held in `env dst`! -/
theorem assign_idempotent_when_already_equal (roMem initStack : WordMem)
    (dst : Reg) (rhs : MemExpr) (env : RegEnv)
    (hAlready : env dst = rhs.eval env roMem initStack) :
    (fun r =>
      if r = dst then rhs.eval env roMem initStack else env r) = env := by
  funext r
  split
  · rename_i heq
    subst heq
    exact hAlready.symm
  · rfl

/-- Core inductive lemma for loop-invariant code motion (`k` iterations):
Once the preheader has initialized `env dst = rhs.eval baseEnv roMem initStack`
and `env` agrees with `baseEnv` on `rhs.vars`, running `k` iterations of the
unhoisted loop body `(.assign dst rhs :: rest)` produces the **exact** same
`Option RegEnv` as running `k` iterations of the hoisted loop body `rest`! -/
theorem loop_hoist_iterations_equiv (roMem initStack : WordMem)
    (dst : Reg) (rhs : MemExpr) (rest : List LoopInstr)
    (k : Nat) (baseEnv env : RegEnv)
    (hPres : bodyPreservesRegs dst rhs.vars rest = true)
    (hVars : ∀ r ∈ rhs.vars, env r = baseEnv r)
    (hDst : env dst = rhs.eval baseEnv roMem initStack) :
    execLoopIterations roMem initStack k env (.assign dst rhs :: rest) =
      execLoopIterations roMem initStack k env rest := by
  induction k generalizing env with
  | zero => rfl
  | succ k' ih =>
    simp only [execLoopIterations]
    have hEvalEq :
        rhs.eval env roMem initStack = rhs.eval baseEnv roMem initStack :=
      MemExpr.eval_eq_of_vars_eq env baseEnv roMem initStack rhs hVars
    have hNoop :
        (fun r => if r = dst then rhs.eval env roMem initStack else env r) =
          env :=
      assign_idempotent_when_already_equal roMem initStack dst rhs env
        (hDst.trans hEvalEq.symm)
    simp only [execLoopBody, execLoopInstr, hNoop]
    have hInv :=
      execLoopBody_preserves_invariant roMem initStack dst rhs rest baseEnv env
        hPres hVars hDst
    cases hBody : execLoopBody roMem initStack env rest with
    | none => rfl
    | some env' =>
      rw [hBody] at hInv
      exact ih env' hInv.1 hInv.2

/-- **Positive Theorem (`pure_loop_hoist_sound`):**
Hoisting a pure, non-trapping instruction `LoopInstr.assign dst rhs` whose
operands `rhs.vars` are loop-invariant (`bodyPreservesRegs dst rhs.vars rest =
true`) out of the loop into the preheader (`hoist_block`) preserves exact
program semantics across **all** iteration counts `k : Nat` (including `k = 0`)
for every live-out register `r ∈ liveOut` (where the loop-internal temporary
`dst ∉ liveOut` when `k = 0`, and even for `dst` itself whenever `k ≥ 1`)! -/
theorem pure_loop_hoist_sound (roMem initStack : WordMem)
    (dst : Reg) (rhs : MemExpr) (rest : List LoopInstr)
    (liveOut : List Reg) (k : Nat) (initEnv : RegEnv)
    (hPres : bodyPreservesRegs dst rhs.vars rest = true)
    (hDstScratch : dst ∉ liveOut) :
    let preheaderEnv : RegEnv :=
      fun r => if r = dst then rhs.eval initEnv roMem initStack else initEnv r
    let unhoistedResult :=
      execLoopIterations roMem initStack k initEnv (.assign dst rhs :: rest)
    let hoistedResult :=
      execLoopIterations roMem initStack k preheaderEnv rest
    match unhoistedResult, hoistedResult with
    | none, none => True
    | some envUnhoisted, some envHoisted =>
      ∀ r ∈ liveOut, envUnhoisted r = envHoisted r
    | _, _ => False := by
  intro preheaderEnv unhoistedResult hoistedResult
  have hDstNotInVars : dst ∉ rhs.vars := by
    unfold bodyPreservesRegs at hPres
    rcases Bool.and_eq_true_iff.mp hPres with ⟨hNotMem, _⟩
    simpa [List.contains_eq_mem] using hNotMem
  have hPreVars : ∀ r ∈ rhs.vars, preheaderEnv r = initEnv r := by
    intro r hr
    have hr_ne : r ≠ dst := fun heq => hDstNotInVars (heq ▸ hr)
    simp [preheaderEnv, hr_ne]
  have hPreDst : preheaderEnv dst = rhs.eval initEnv roMem initStack := by
    simp [preheaderEnv]
  cases k with
  | zero =>
    dsimp [unhoistedResult, hoistedResult, execLoopIterations]
    intro r hr
    have hr_ne : r ≠ dst := fun heq => hDstScratch (heq ▸ hr)
    simp [preheaderEnv, hr_ne]
  | succ k' =>
    have hEquiv :=
      loop_hoist_iterations_equiv roMem initStack dst rhs rest (k' + 1)
        initEnv preheaderEnv hPres hPreVars hPreDst
    have hFirstStep :
        execLoopIterations roMem initStack (k' + 1) initEnv
          (.assign dst rhs :: rest) =
        execLoopIterations roMem initStack (k' + 1) preheaderEnv
          (.assign dst rhs :: rest) := by
      simp only [execLoopIterations, execLoopBody, execLoopInstr]
      have hEvalEq :
          rhs.eval preheaderEnv roMem initStack =
            rhs.eval initEnv roMem initStack :=
        MemExpr.eval_eq_of_vars_eq preheaderEnv initEnv roMem initStack rhs
          hPreVars
      have hEnvEq :
          (fun r =>
            if r = dst then rhs.eval initEnv roMem initStack else initEnv r) =
          (fun r =>
            if r = dst then rhs.eval preheaderEnv roMem initStack
            else preheaderEnv r) := by
        funext r
        by_cases hr : r = dst
        · subst hr; simp [hEvalEq]
        · simp [hr, preheaderEnv]
      rw [hEnvEq]
    dsimp [unhoistedResult, hoistedResult]
    rw [hFirstStep, hEquiv]
    cases execLoopIterations roMem initStack (k' + 1) preheaderEnv rest with
    | none => trivial
    | some envFinal =>
      intro r _
      rfl

/-- **Negative Canary
(`canary_hoist_trapping_div_above_zero_iteration_loop_unsound`):**

Why does Cranelift's `is_pure_for_egraph` (`inst_predicates.rs:46-69`) exclude
trapping instructions (`opcode.can_trap()`, such as `udiv` / `sdiv` / `urem` /
`srem` and loads without `notrap`) from the acyclic e-graph?

Because `elaborate_domtree` hoists loop-invariant e-graph nodes into
`hoist_block` (the preheader dominating the loop header, `elaborate.rs:600-623`)
**before** the loop trip-count condition is tested!

If `LoopInstr.udiv 3 1 2` (`r3 := r1 / r2`) is hoisted into the preheader of a
loop that executes `k = 0` iterations when `r2 = 0` (`denom = 0`):
- The unhoisted loop executes `0` iterations and terminates normally
  (`some initEnv`).
- The hoisted program executes `udiv 3 1 2` unconditionally in the preheader
  and **traps** (`none`)! -/
def runLoopWithHoistedInstr (roMem initStack : WordMem)
    (hoisted : LoopInstr) (k : Nat) (initEnv : RegEnv)
    (rest : List LoopInstr) : Option RegEnv :=
  match execLoopInstr roMem initStack initEnv hoisted with
  | none => none
  | some preEnv => execLoopIterations roMem initStack k preEnv rest

theorem canary_hoist_trapping_div_above_zero_iteration_loop_unsound :
    let roMem : WordMem := fun _ => 0#64
    let initStack : WordMem := fun _ => 0#64
    let initEnv : RegEnv := fun r =>
      if r = 1 then 42#64
      else if r = 2 then 0#64 -- divisor `r2 = 0` when trip count `k = 0`!
      else 0#64
    let divInstr := LoopInstr.udiv 3 1 2
    let unhoistedZeroTrip :=
      execLoopIterations roMem initStack 0 initEnv [divInstr]
    let hoistedZeroTrip :=
      runLoopWithHoistedInstr roMem initStack divInstr 0 initEnv []
    unhoistedZeroTrip = some initEnv ∧
    hoistedZeroTrip = none ∧
    unhoistedZeroTrip ≠ hoistedZeroTrip := by
  refine ⟨rfl, rfl, fun h => by cases h⟩

/-!
## Section 4: Axiom Footprint Verification (`TrustedBoundary.lean` Compliance)

We audit all theorems in this probe with `#guard_msgs in #print axioms` to
confirm that zero `sorryAx` and zero `Lean.ofReduceBool` axioms are used.
-/

/-- info: 'Round2Track4Probe.riscv_smul_overflow_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riscv_smul_overflow_iff_spec

/-- info: 'Round2Track4Probe.riscv_smul_overflow_bv_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riscv_smul_overflow_bv_iff_spec

/-- info: 'Round2Track4Probe.riscv_smul_xor_snez_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riscv_smul_xor_snez_iff_spec

/-- info: 'Round2Track4Probe.u128_add_pair_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u128_add_pair_correct

/-- info: 'Round2Track4Probe.u128_sub_pair_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms u128_sub_pair_correct

/-- info: 'Round2Track4Probe.u128_mul_pair_algebraic_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms u128_mul_pair_algebraic_identity

/-- info: 'Round2Track4Probe.compiler_builtins_umulo_both_hi_nonzero_overflows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compiler_builtins_umulo_both_hi_nonzero_overflows

/-- info: 'Round2Track4Probe.compiler_builtins_umulo_both_hi_zero_no_overflow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms compiler_builtins_umulo_both_hi_zero_no_overflow

/-- info: 'Round2Track4Probe.compiler_builtins_umulo_lhs_hi_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiler_builtins_umulo_lhs_hi_zero_iff

/-- info: 'Round2Track4Probe.validateSuperblockWithMem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validateSuperblockWithMem_sound

/--
info: 'Round2Track4Probe.vtableHoistAndCseAcrossStackStore_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms vtableHoistAndCseAcrossStackStore_verified

/-- info: 'Round2Track4Probe.stackStoreToLoadForwarding_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stackStoreToLoadForwarding_verified

/-- info: 'Round2Track4Probe.canary_hoist_stack_load_across_aliasing_store_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary_hoist_stack_load_across_aliasing_store_rejected

/-- info: 'Round2Track4Probe.relocTable_discharges_vtableStoredAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms relocTable_discharges_vtableStoredAt

/-- info: 'Round2Track4Probe.relocTable_chained_traitVPtr_stored' depends on axioms: [propext] -/
#guard_msgs in
#print axioms relocTable_chained_traitVPtr_stored

/-- info: 'Round2Track4Probe.argHoistLevel_not_in_loop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms argHoistLevel_not_in_loop

/-- info: 'Round2Track4Probe.pure_loop_hoist_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pure_loop_hoist_sound

/-- info: 'Round2Track4Probe.canary_hoist_trapping_div_above_zero_iteration_loop_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary_hoist_trapping_div_above_zero_iteration_loop_unsound

end Round2Track4Probe
