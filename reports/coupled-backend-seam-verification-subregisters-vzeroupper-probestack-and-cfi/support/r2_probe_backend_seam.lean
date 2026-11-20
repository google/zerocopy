/-!
Kernel-Checked Lean v4.34.1 Proof & Counterexample Suite for Backend Seam Synthesis:
Coupled Backend Seam (`MiniMach` `ISLE` Lowering × Sub-Register `WriteMode` RegAlloc ×
CFG-Aware `vzeroupper` × Inline Stack Probes / Outlining / `.eh_frame` CFI / LSDA / `DW_OP_fbreg`).

Strict TCB & Tactic Discipline:
- Zero `sorry` (`sorryAx`)
- Zero `bv_decide` / `native_decide` (`Lean.ofReduceBool`)
- Zero `omega`
- Zero `partial`, zero `@[extern]`
- Zero `Classical.choice` (constructive/decidable proofs only)
-/

namespace VrustcProbe.BackendSeam

/-! ## Section 1: `BitVec 64` / `BitVec 256` `WriteMode` Algebra & `MiniMach` `ISLE` Lowering Bridge -/

inductive MiniMachLaneView where
  | full64
  | lo32Zext
  | lo16Keep
  | lo8Keep
  | hi8Keep
  deriving DecidableEq, Repr

inductive IsleSimdEncoding where
  | legacySse
  | vex128
  | vex256
  deriving DecidableEq, Repr

inductive SubRegSlice where
  | lo8
  | hi8
  | lo16
  | lo32
  | hi32
  | full64
  | xmm128
  | ymm256
  deriving DecidableEq, Repr

inductive WriteMode where
  | preserveUpper
  | zeroExtend64
  | zeroExtend256
  deriving DecidableEq, Repr

inductive LaneId where
  | b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 | xmmHi | ymmHi
  deriving DecidableEq, Repr

def maskLo32_64  : BitVec 64 := 0x0000_0000_FFFF_FFFF#64
def maskLo16_64  : BitVec 64 := 0x0000_0000_0000_FFFF#64
def maskLo8_64   : BitVec 64 := 0x0000_0000_0000_00FF#64
def maskHi8_64   : BitVec 64 := 0x0000_0000_0000_FF00#64
def keepHi16_64  : BitVec 64 := 0xFFFF_FFFF_FFFF_0000#64
def keepHi8_64   : BitVec 64 := 0xFFFF_FFFF_FFFF_FF00#64
def keepExHi8_64 : BitVec 64 := 0xFFFF_FFFF_FFFF_00FF#64

def gprWrite64 (lv : MiniMachLaneView) (old new64 : BitVec 64) : BitVec 64 :=
  match lv with
  | .full64   => new64
  | .lo32Zext => new64 &&& maskLo32_64
  | .lo16Keep => (old &&& keepHi16_64) ||| (new64 &&& maskLo16_64)
  | .lo8Keep  => (old &&& keepHi8_64)  ||| (new64 &&& maskLo8_64)
  | .hi8Keep  => (old &&& keepExHi8_64) ||| ((new64 &&& maskLo8_64) <<< 8)

def maskXmmLo256 : BitVec 256 := BitVec.ofNat 256 (2 ^ 128 - 1)
def maskYmmHi256 : BitVec 256 := ~~~maskXmmLo256

def ymmWrite256 (enc : IsleSimdEncoding) (old new256 : BitVec 256) : BitVec 256 :=
  match enc with
  | .legacySse => (old &&& maskYmmHi256) ||| (new256 &&& maskXmmLo256)
  | .vex128    => new256 &&& maskXmmLo256
  | .vex256    => new256

private theorem bv_getLsbD_false_of_not_lt {w : Nat} (x : BitVec w) (i : Nat) (hnot : ¬(i < w)) :
    x.getLsbD i = false := by
  cases h : x.getLsbD i with
  | false => rfl
  | true => exact False.elim (hnot (BitVec.lt_of_getLsbD h))

private theorem bv64_shift_and_zero (x m : BitVec 64) (k : Nat) (hm : m >>> k = 0#64) :
    (x &&& m) >>> k = 0#64 := by
  rw [BitVec.ushiftRight_and_distrib, hm, BitVec.and_zero]

private theorem testBit_maskLo8_add8 (k : Nat) : maskLo8_64.getLsbD (8 + k) = false := by
  change (maskLo8_64.toNat).testBit (8 + k) = false
  rw [← Nat.testBit_shiftRight]
  have hz : maskLo8_64.toNat >>> 8 = 0 := rfl
  rw [hz, Nat.zero_testBit]

private theorem testBit_maskLo16_add16 (k : Nat) : maskLo16_64.getLsbD (16 + k) = false := by
  change (maskLo16_64.toNat).testBit (16 + k) = false
  rw [← Nat.testBit_shiftRight]
  have hz : maskLo16_64.toNat >>> 16 = 0 := rfl
  rw [hz, Nat.zero_testBit]

private theorem testBit_maskXmmLo256_add128 (k : Nat) : maskXmmLo256.getLsbD (128 + k) = false := by
  change (maskXmmLo256.toNat).testBit (128 + k) = false
  rw [← Nat.testBit_shiftRight]
  have hz : maskXmmLo256.toNat >>> 128 = 0 := rfl
  rw [hz, Nat.zero_testBit]

private theorem testBit_pow2_sub_one_constructive : ∀ (n i : Nat),
    Nat.testBit (2 ^ n - 1) i = decide (i < n)
  | 0, _ => by simp [Nat.zero_testBit]
  | n + 1, 0 => by
      have hpos : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        rw [hpos]
        cases h : 2 ^ n with
        | zero => rw [h] at hge; cases hge
        | succ m => rfl
      rw [heq]
      simp [Nat.testBit_zero]
  | n + 1, i + 1 => by
      have hpos : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        rw [hpos]
        cases h : 2 ^ n with
        | zero => rw [h] at hge; cases hge
        | succ m => rfl
      rw [heq, Nat.testBit_succ]
      have hdiv : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by
        rw [Nat.mul_add_div (by decide : 0 < 2)]
        simp
      rw [hdiv, testBit_pow2_sub_one_constructive n i]
      exact decide_eq_decide.mpr ⟨Nat.succ_lt_succ, Nat.lt_of_succ_lt_succ⟩

private theorem bv64_shiftLeft8_and_lo8_zero (x : BitVec 64) : (x <<< 8) &&& maskLo8_64 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · rw [show k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 + k from Nat.add_comm k 8,
        testBit_maskLo8_add8, Bool.and_false]

private theorem bv64_shiftLeft8_shiftRight16_zero (x : BitVec 64) :
    ((x &&& maskLo8_64) <<< 8) >>> 16 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases h1 : decide (16 + i < 64) with
  | false => simp
  | true =>
      have hge8 : decide (16 + i < 8) = false :=
        decide_eq_false (Nat.not_lt_of_le (Nat.le_trans (by decide : 8 ≤ 16) (Nat.le_add_right 16 i)))
      have hsub : 16 + i - 8 = 8 + i := by
        rw [show (16 : Nat) + i = 8 + (8 + i) from Nat.add_assoc 8 8 i, Nat.add_sub_cancel_left]
      rw [hge8, hsub, testBit_maskLo8_add8]
      simp

private theorem bv64_shiftLeft8_and_hi8_shiftRight8 (x : BitVec 64) :
    (((x &&& maskLo8_64) <<< 8) &&& maskHi8_64) >>> 8 = x &&& maskLo8_64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | k
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · simp [maskLo8_64, maskHi8_64]
  · rw [show k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 + k from Nat.add_comm k 8]
    have hm : maskLo8_64.getLsbD (8 + k) = false := testBit_maskLo8_add8 k
    have hmhi : maskHi8_64.getLsbD (8 + (8 + k)) = false := by
      change (maskHi8_64.toNat).testBit (8 + (8 + k)) = false
      rw [← Nat.add_assoc, ← Nat.testBit_shiftRight]
      have hz : maskHi8_64.toNat >>> 16 = 0 := rfl
      rw [hz, Nat.zero_testBit]
    rw [hm, hmhi]
    simp

private theorem bv64_shiftRight16_and_lo48 (x : BitVec 64) :
    (x >>> 16) &&& 0x0000_FFFF_FFFF_FFFF#64 = x >>> 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  cases hlt : decide (16 + i < 64) with
  | false =>
      have hnot := of_decide_eq_false hlt
      rw [bv_getLsbD_false_of_not_lt x (16 + i) hnot, Bool.false_and]
  | true =>
      have hyes := of_decide_eq_true hlt
      have hij : i < 48 := Nat.lt_of_add_lt_add_left (show 16 + i < 16 + 48 from hyes)
      have hmask : (0x0000_FFFF_FFFF_FFFF#64).getLsbD i = true := by
        change Nat.testBit (2 ^ 48 - 1) i = true
        rw [testBit_pow2_sub_one_constructive 48 i]
        exact decide_eq_true hij
      rw [hmask, Bool.and_true]

private theorem bv256_shiftRight128_and_lo128 (x : BitVec 256) :
    (x >>> 128) &&& maskXmmLo256 = x >>> 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  cases hlt : decide (128 + i < 256) with
  | false =>
      have hnot := of_decide_eq_false hlt
      rw [bv_getLsbD_false_of_not_lt x (128 + i) hnot, Bool.false_and]
  | true =>
      have hyes := of_decide_eq_true hlt
      have hij : i < 128 := Nat.lt_of_add_lt_add_left (show 128 + i < 128 + 128 from hyes)
      have hmask : maskXmmLo256.getLsbD i = true := by
        change Nat.testBit (2 ^ 128 - 1) i = true
        rw [testBit_pow2_sub_one_constructive 128 i]
        exact decide_eq_true hij
      rw [hmask, Bool.and_true]

/-- Theorem 1: `x86_64` 32-bit GPR write (`movl`) zeroes `[63:32]` over raw `BitVec 64`. -/
theorem movl_zeroes_upper32_bv64 (old v : BitVec 64) :
    (gprWrite64 .lo32Zext old v) >>> 32 = 0#64 :=
  bv64_shift_and_zero v maskLo32_64 32 rfl

/-- Theorem 2: `x86_64` 8-bit `movb` writes to `AL` (`lo8Keep`) and `AH` (`hi8Keep`) commute
    disjointly and preserve `[63:16]` over raw `BitVec 64`. -/
theorem movb_lo8_hi8_commute_and_preserve_upper_bv64 (old vAl vAh : BitVec 64) :
    let r1 := gprWrite64 .lo8Keep old vAl
    let r2 := gprWrite64 .hi8Keep r1 vAh
    (r2 &&& maskLo8_64 = vAl &&& maskLo8_64) ∧
    ((r2 &&& maskHi8_64) >>> 8 = vAh &&& maskLo8_64) ∧
    (r2 >>> 16 = old >>> 16) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [gprWrite64, BitVec.and_or_distrib_right, BitVec.and_assoc]
    rw [show keepHi8_64 &&& (keepExHi8_64 &&& maskLo8_64) = 0#64 from rfl]
    rw [show maskLo8_64 &&& (keepExHi8_64 &&& maskLo8_64) = maskLo8_64 from rfl]
    rw [BitVec.and_zero, BitVec.zero_or, bv64_shiftLeft8_and_lo8_zero, BitVec.or_zero]
  · simp only [gprWrite64, BitVec.and_or_distrib_right, BitVec.and_assoc]
    rw [show keepExHi8_64 &&& maskHi8_64 = 0#64 from rfl]
    simp only [BitVec.and_zero, BitVec.zero_or]
    exact bv64_shiftLeft8_and_hi8_shiftRight8 vAh
  · simp only [gprWrite64, BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib]
    rw [show maskLo8_64 >>> 16 = 0#64 from rfl, BitVec.and_zero, BitVec.or_zero]
    rw [bv64_shiftLeft8_shiftRight16_zero vAh, BitVec.or_zero]
    rw [show keepHi8_64 >>> 16 = 0x0000_FFFF_FFFF_FFFF#64 from rfl]
    rw [show keepExHi8_64 >>> 16 = 0x0000_FFFF_FFFF_FFFF#64 from rfl]
    rw [bv64_shiftRight16_and_lo48, bv64_shiftRight16_and_lo48]

/-- Theorem 3: `x86_64` 16-bit `movw` write to `AX` (`lo16Keep`) sets `[15:0]` and preserves `[63:16]`. -/
theorem movw_ax_preserves_upper48_bv64 (old vAx : BitVec 64) :
    let r1 := gprWrite64 .lo16Keep old vAx
    (r1 &&& maskLo16_64 = vAx &&& maskLo16_64) ∧
    (r1 >>> 16 = old >>> 16) := by
  refine ⟨?_, ?_⟩
  · simp only [gprWrite64, BitVec.and_or_distrib_right, BitVec.and_assoc]
    rw [show keepHi16_64 &&& maskLo16_64 = 0#64 from rfl, BitVec.and_zero, BitVec.zero_or]
    rw [show maskLo16_64 &&& maskLo16_64 = maskLo16_64 from rfl]
  · simp only [gprWrite64, BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib]
    rw [show maskLo16_64 >>> 16 = 0#64 from rfl, BitVec.and_zero, BitVec.or_zero]
    rw [show keepHi16_64 >>> 16 = 0x0000_FFFF_FFFF_FFFF#64 from rfl]
    exact bv64_shiftRight16_and_lo48 old

/-- Theorem 4: Legacy SSE 128-bit write preserves `YMM[255:128]` over raw `BitVec 256`. -/
theorem sse128_preserves_ymmHi_bv256 (old v : BitVec 256) :
    (ymmWrite256 .legacySse old v) >>> 128 = old >>> 128 := by
  simp only [ymmWrite256, BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib]
  rw [show maskXmmLo256 >>> 128 = 0#256 from rfl, BitVec.and_zero, BitVec.or_zero]
  rw [show maskYmmHi256 >>> 128 = maskXmmLo256 from rfl]
  exact bv256_shiftRight128_and_lo128 old

/-- Theorem 5: VEX-128 128-bit write zeroes `YMM[255:128]` over raw `BitVec 256`. -/
theorem vex128_zeroes_ymmHi_bv256 (old v : BitVec 256) :
    (ymmWrite256 .vex128 old v) >>> 128 = 0#256 := by
  simp only [ymmWrite256, BitVec.ushiftRight_and_distrib]
  rw [show maskXmmLo256 >>> 128 = 0#256 from rfl, BitVec.and_zero]

/-- Structured 256-bit architectural register (`b0..b7 : BitVec 8`, `xmmHi : BitVec 64`,
    `ymmHi : BitVec 128`) unifying GPR sub-registers and AVX2 `YMM` lanes. -/
structure Reg256 where
  b0    : BitVec 8 := 0#8
  b1    : BitVec 8 := 0#8
  b2    : BitVec 8 := 0#8
  b3    : BitVec 8 := 0#8
  b4    : BitVec 8 := 0#8
  b5    : BitVec 8 := 0#8
  b6    : BitVec 8 := 0#8
  b7    : BitVec 8 := 0#8
  xmmHi : BitVec 64 := 0#64
  ymmHi : BitVec 128 := 0#128
  deriving DecidableEq, Repr

inductive LaneVal where
  | u8 (v : BitVec 8)
  | u64 (v : BitVec 64)
  | u128 (v : BitVec 128)
  deriving DecidableEq, Repr

def readLane (l : LaneId) (r : Reg256) : LaneVal :=
  match l with
  | .b0    => .u8 r.b0
  | .b1    => .u8 r.b1
  | .b2    => .u8 r.b2
  | .b3    => .u8 r.b3
  | .b4    => .u8 r.b4
  | .b5    => .u8 r.b5
  | .b6    => .u8 r.b6
  | .b7    => .u8 r.b7
  | .xmmHi => .u64 r.xmmHi
  | .ymmHi => .u128 r.ymmHi

def sliceLanes : SubRegSlice → List LaneId
  | .lo8    => [.b0]
  | .hi8    => [.b1]
  | .lo16   => [.b0, .b1]
  | .lo32   => [.b0, .b1, .b2, .b3]
  | .hi32   => [.b4, .b5, .b6, .b7]
  | .full64 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7]
  | .xmm128 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7, .xmmHi]
  | .ymm256 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7, .xmmHi, .ymmHi]

def laneInSlice (l : LaneId) (s : SubRegSlice) : Bool :=
  (sliceLanes s).contains l

def zeroedByMode (s : SubRegSlice) (m : WriteMode) (l : LaneId) : Bool :=
  if laneInSlice l s then false
  else match m with
  | .preserveUpper => false
  | .zeroExtend64  => laneInSlice l .full64
  | .zeroExtend256 => true

def touchedByWrite (s : SubRegSlice) (m : WriteMode) (l : LaneId) : Bool :=
  laneInSlice l s || zeroedByMode s m l

def applyReg256Write (s : SubRegSlice) (m : WriteMode) (payload dst : Reg256) : Reg256 :=
  let step {w : Nat} (l : LaneId) (cur src : BitVec w) : BitVec w :=
    if laneInSlice l s then src
    else if zeroedByMode s m l then 0#w
    else cur
  { b0    := step .b0    dst.b0    payload.b0
  , b1    := step .b1    dst.b1    payload.b1
  , b2    := step .b2    dst.b2    payload.b2
  , b3    := step .b3    dst.b3    payload.b3
  , b4    := step .b4    dst.b4    payload.b4
  , b5    := step .b5    dst.b5    payload.b5
  , b6    := step .b6    dst.b6    payload.b6
  , b7    := step .b7    dst.b7    payload.b7
  , xmmHi := step .xmmHi dst.xmmHi payload.xmmHi
  , ymmHi := step .ymmHi dst.ymmHi payload.ymmHi }

def extractSlice (s : SubRegSlice) (r : Reg256) : List LaneVal :=
  (sliceLanes s).map (fun l => readLane l r)

def packSlice (s : SubRegSlice) (vals : List LaneVal) : Reg256 :=
  match s, vals with
  | .lo8, [.u8 x0] => { b0 := x0 }
  | .hi8, [.u8 x0] => { b1 := x0 }
  | .lo16, [.u8 x0, .u8 x1] => { b0 := x0, b1 := x1 }
  | .lo32, [.u8 x0, .u8 x1, .u8 x2, .u8 x3] => { b0 := x0, b1 := x1, b2 := x2, b3 := x3 }
  | .hi32, [.u8 x0, .u8 x1, .u8 x2, .u8 x3] => { b4 := x0, b5 := x1, b6 := x2, b7 := x3 }
  | .full64, [.u8 x0, .u8 x1, .u8 x2, .u8 x3, .u8 x4, .u8 x5, .u8 x6, .u8 x7] =>
      { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7 }
  | .xmm128, [.u8 x0, .u8 x1, .u8 x2, .u8 x3, .u8 x4, .u8 x5, .u8 x6, .u8 x7, .u64 xh] =>
      { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7, xmmHi := xh }
  | .ymm256, [.u8 x0, .u8 x1, .u8 x2, .u8 x3, .u8 x4, .u8 x5, .u8 x6, .u8 x7, .u64 xh, .u128 yh] =>
      { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7, xmmHi := xh, ymmHi := yh }
  | _, _ => {}

/-- Theorem 6 (Sub-Register `Reg256` Lane Framing): Any lane `l` outside `touchedByWrite s m`
    is strictly preserved by `applyReg256Write s m payload dst`. -/
theorem applyReg256Write_preserves_untouched
    (s : SubRegSlice) (m : WriteMode) (payload dst : Reg256) (l : LaneId)
    (h_untouched : touchedByWrite s m l = false) :
    readLane l (applyReg256Write s m payload dst) = readLane l dst := by
  unfold touchedByWrite at h_untouched
  cases l <;> simp only [Bool.or_eq_false_iff] at h_untouched <;>
    rcases h_untouched with ⟨h_in, h_zero⟩ <;>
    simp [readLane, applyReg256Write, h_in, h_zero]

/-- Theorem 7 (Written Slice Read-Back): Every lane `l` inside `s` reads back from `payload`. -/
theorem applyReg256Write_reads_written
    (s : SubRegSlice) (m : WriteMode) (payload dst : Reg256) (l : LaneId)
    (h_in : laneInSlice l s = true) :
    readLane l (applyReg256Write s m payload dst) = readLane l payload := by
  cases l <;> simp [readLane, applyReg256Write, h_in]

def embedMiniMachLaneView : MiniMachLaneView → SubRegSlice × WriteMode
  | .full64   => (.full64, .preserveUpper)
  | .lo32Zext => (.lo32,   .zeroExtend64)
  | .lo16Keep => (.lo16,   .preserveUpper)
  | .lo8Keep  => (.lo8,    .preserveUpper)
  | .hi8Keep  => (.hi8,    .preserveUpper)

def embedIsleSimd : IsleSimdEncoding → SubRegSlice × WriteMode
  | .legacySse => (.xmm128, .preserveUpper)
  | .vex128    => (.xmm128, .zeroExtend256)
  | .vex256    => (.ymm256, .zeroExtend256)

/-- Theorem 8 (`ISLE -> MiniMach` Lowering Soundness & Gap Witness):
    1. Embedding `MiniMachLaneView` into `(SubRegSlice, WriteMode)` preserves exact lane readback,
       zeroes `[63:32]` on `.lo32Zext`, and preserves `[255:128]` (`ymmHi`) across GPR ops.
    2. `embedIsleSimd .legacySse` preserves `ymmHi` whereas `embedIsleSimd .vex128` zeroes `ymmHi`,
       exposing why `MiniMachLaneView` alone cannot express SIMD VEX-128 vs SSE-128 without `WriteMode`. -/
theorem embedMiniMachLaneView_exact (lv : MiniMachLaneView) (dst payload : Reg256) :
    let (sl, wm) := embedMiniMachLaneView lv
    let post := applyReg256Write sl wm payload dst
    (∀ l, laneInSlice l sl = true → readLane l post = readLane l payload) ∧
    post.ymmHi = dst.ymmHi ∧
    (lv = .lo32Zext → post.b4 = 0#8 ∧ post.b5 = 0#8 ∧ post.b6 = 0#8 ∧ post.b7 = 0#8) ∧
    (readLane .ymmHi (applyReg256Write (embedIsleSimd .legacySse).1 (embedIsleSimd .legacySse).2 payload dst) =
       readLane .ymmHi dst) ∧
    ((applyReg256Write (embedIsleSimd .vex128).1 (embedIsleSimd .vex128).2 payload dst).ymmHi = 0#128) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact applyReg256Write_reads_written (embedMiniMachLaneView lv).1 (embedMiniMachLaneView lv).2 payload dst l hl
  · cases lv <;> simp [applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]
  · intro hlv
    subst hlv
    simp [applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]
  · simp [embedIsleSimd, readLane, applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]
  · simp [embedIsleSimd, applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]

/-! ## Section 2: `Virt -> Alloc` Splitting, Spill/Reload, Remat & Repaired `MoveAndScratchResolver` -/

abbrev PRegId := Fin 16
abbrev SlotId := Nat
abbrev VRegId := Nat

inductive PhysLoc where
  | reg   (r : PRegId) (slice : SubRegSlice)
  | spill (slot : SlotId) (slice : SubRegSlice)
  deriving DecidableEq, Repr

def locSlice : PhysLoc → SubRegSlice
  | .reg _ sl   => sl
  | .spill _ sl => sl

structure AllocState where
  regs   : PRegId → Reg256
  stack  : SlotId → Reg256
  roPool : SlotId → Reg256

def readPhysLoc (st : AllocState) : PhysLoc → List LaneVal
  | .reg r sl   => extractSlice sl (st.regs r)
  | .spill s sl => extractSlice sl (st.stack s)

def updateReg (st : AllocState) (r : PRegId) (v : Reg256) : AllocState :=
  { st with regs := fun r' => if r' = r then v else st.regs r' }

def updateStack (st : AllocState) (s : SlotId) (v : Reg256) : AllocState :=
  { st with stack := fun s' => if s' = s then v else st.stack s' }

def writePhysLoc (st : AllocState) (loc : PhysLoc) (m : WriteMode) (vals : List LaneVal) : AllocState :=
  match loc with
  | .reg r sl =>
      updateReg st r (applyReg256Write sl m (packSlice sl vals) (st.regs r))
  | .spill s sl =>
      updateStack st s (applyReg256Write sl .preserveUpper (packSlice sl vals) (st.stack s))

def nonInterferingWrite (dst : PhysLoc) (m : WriteMode) (other : PhysLoc) : Bool :=
  match dst, other with
  | .reg r1 sl1, .reg r2 sl2 =>
      if r1 = r2 then
        (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 m l))
      else true
  | .spill s1 sl1, .spill s2 sl2 =>
      if s1 = s2 then
        (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 .preserveUpper l))
      else true
  | _, _ => true

private theorem readLane_packSlice_same (sl : SubRegSlice) (r : Reg256) (l : LaneId)
    (h_in : laneInSlice l sl = true) :
    readLane l (packSlice sl (extractSlice sl r)) = readLane l r := by
  cases sl <;> cases l <;> simp [laneInSlice, sliceLanes] at h_in <;>
    simp [packSlice, extractSlice, sliceLanes, readLane]

private theorem extractSlice_write_roundtrip (sl : SubRegSlice) (m : WriteMode) (src dst : Reg256) :
    extractSlice sl (applyReg256Write sl m (packSlice sl (extractSlice sl src)) dst) =
      extractSlice sl src := by
  cases sl <;>
    simp [extractSlice, sliceLanes, applyReg256Write, packSlice, laneInSlice, readLane]

private theorem extractSlice_preserved_of_all_untouched
    (sl1 : SubRegSlice) (m : WriteMode) (payload dst : Reg256) (sl2 : SubRegSlice)
    (h_disj : (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 m l)) = true) :
    extractSlice sl2 (applyReg256Write sl1 m payload dst) = extractSlice sl2 dst := by
  have h_lane : ∀ l, l ∈ sliceLanes sl2 →
      readLane l (applyReg256Write sl1 m payload dst) = readLane l dst := by
    intro l hl
    rw [List.all_eq_true] at h_disj
    have h_not := h_disj l hl
    simp only [Bool.not_eq_true'] at h_not
    exact applyReg256Write_preserves_untouched sl1 m payload dst l h_not
  have hb0 := h_lane .b0
  have hb1 := h_lane .b1
  have hb2 := h_lane .b2
  have hb3 := h_lane .b3
  have hb4 := h_lane .b4
  have hb5 := h_lane .b5
  have hb6 := h_lane .b6
  have hb7 := h_lane .b7
  have hxh := h_lane .xmmHi
  have hyh := h_lane .ymmHi
  cases sl2 <;> simp [sliceLanes] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hxh hyh <;>
    simp [extractSlice, sliceLanes, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hxh, hyh]

/-- Theorem 9 (Physical Location Framing): Non-interfering `writePhysLoc` preserves `other`. -/
theorem writePhysLoc_frame
    (st : AllocState) (dst : PhysLoc) (m : WriteMode) (vals : List LaneVal) (other : PhysLoc)
    (h_ni : nonInterferingWrite dst m other = true) :
    readPhysLoc (writePhysLoc st dst m vals) other = readPhysLoc st other := by
  cases dst with
  | reg r1 sl1 =>
    cases other with
    | reg r2 sl2 =>
      simp only [nonInterferingWrite] at h_ni
      by_cases h_eq : r1 = r2
      · subst h_eq
        simp only [↓reduceIte] at h_ni
        simp only [writePhysLoc, readPhysLoc, updateReg, ↓reduceIte]
        exact extractSlice_preserved_of_all_untouched sl1 m _ _ sl2 h_ni
      · have h_neq : r2 ≠ r1 := fun h => h_eq h.symm
        simp only [writePhysLoc, readPhysLoc, updateReg, h_neq, ↓reduceIte]
    | spill s2 sl2 => rfl
  | spill s1 sl1 =>
    cases other with
    | reg r2 sl2 => rfl
    | spill s2 sl2 =>
      simp only [nonInterferingWrite] at h_ni
      by_cases h_eq : s1 = s2
      · subst h_eq
        simp only [↓reduceIte] at h_ni
        simp only [writePhysLoc, readPhysLoc, updateStack, ↓reduceIte]
        exact extractSlice_preserved_of_all_untouched sl1 .preserveUpper _ _ sl2 h_ni
      · have h_neq : s2 ≠ s1 := fun h => h_eq h.symm
        simp only [writePhysLoc, readPhysLoc, updateStack, h_neq, ↓reduceIte]

theorem writePhysLoc_same (st : AllocState) (loc : PhysLoc) (m : WriteMode) (src : Reg256) :
    readPhysLoc (writePhysLoc st loc m (extractSlice (locSlice loc) src)) loc =
      extractSlice (locSlice loc) src := by
  cases loc with
  | reg r sl =>
    simp [locSlice, writePhysLoc, readPhysLoc, updateReg, extractSlice_write_roundtrip]
  | spill s sl =>
    simp [locSlice, writePhysLoc, readPhysLoc, updateStack, extractSlice_write_roundtrip]

abbrev SymState := List (PhysLoc × VRegId)
abbrev SsaEnv := VRegId → Reg256

def SymRefines (ssa : SsaEnv) (st : AllocState) (sym : SymState) : Prop :=
  ∀ loc v, (loc, v) ∈ sym → readPhysLoc st loc = extractSlice (locSlice loc) (ssa v)

def lookupSym (sym : SymState) (loc : PhysLoc) : Option VRegId :=
  match sym.find? (fun p => p.1 == loc) with
  | some (_, v) => some v
  | none        => none

private theorem lookupSym_mem (sym : SymState) (loc : PhysLoc) (v : VRegId)
    (h : lookupSym sym loc = some v) : (loc, v) ∈ sym := by
  unfold lookupSym at h
  cases hf : sym.find? (fun p => p.1 == loc) with
  | none => simp [hf] at h
  | some p =>
      simp only [hf] at h
      have hmem := List.mem_of_find?_eq_some hf
      have heq : p.1 = loc := by
        have hb := List.find?_some hf
        simp only [beq_iff_eq] at hb
        exact hb
      rcases p with ⟨l', v'⟩
      simp only at heq h
      cases h
      subst heq
      exact hmem

def sliceShapeEq (s1 s2 : SubRegSlice) : Bool :=
  (sliceLanes s1).length == (sliceLanes s2).length

def killOverlapping (sym : SymState) (dst : PhysLoc) (m : WriteMode) : SymState :=
  sym.filter (fun p => nonInterferingWrite dst m p.1)

def stepMoveRepaired (sym : SymState) (src dst : PhysLoc) (m : WriteMode) : SymState :=
  let cleaned := killOverlapping sym dst m
  match lookupSym sym src with
  | some v =>
      if sliceShapeEq (locSlice src) (locSlice dst) then (dst, v) :: cleaned
      else cleaned
  | none => cleaned

def stepMoveBuggyRegalloc2 (sym : SymState) (src dst : PhysLoc) : SymState :=
  match lookupSym sym src with
  | some v => (dst, v) :: sym.filter (fun p => p.1 != dst)
  | none   => sym

def execMoveConcrete (st : AllocState) (src dst : PhysLoc) (m : WriteMode) : AllocState :=
  writePhysLoc st dst m (readPhysLoc st src)

private theorem extractSlice_write_same_shape
    (sl1 sl2 : SubRegSlice) (m : WriteMode) (src dst : Reg256)
    (h_shape : sliceShapeEq sl1 sl2 = true) :
    extractSlice sl2 (applyReg256Write sl2 m (packSlice sl2 (extractSlice sl1 src)) dst) =
      extractSlice sl1 src := by
  cases sl1 <;> cases sl2 <;> simp [sliceShapeEq, sliceLanes] at h_shape <;>
    simp [extractSlice, sliceLanes, applyReg256Write, packSlice, laneInSlice, readLane]

private theorem writePhysLoc_readPhysLoc_same_shape
    (st0 st : AllocState) (dst orig : PhysLoc) (m : WriteMode)
    (h_shape : sliceShapeEq (locSlice orig) (locSlice dst) = true) :
    readPhysLoc (writePhysLoc st dst m (readPhysLoc st0 orig)) dst = readPhysLoc st0 orig := by
  cases dst <;> cases orig <;> simp only [locSlice] at h_shape ⊢
  · simp only [writePhysLoc, readPhysLoc, updateReg, ↓reduceIte]
    exact extractSlice_write_same_shape _ _ m _ _ h_shape
  · simp only [writePhysLoc, readPhysLoc, updateReg, ↓reduceIte]
    exact extractSlice_write_same_shape _ _ m _ _ h_shape
  · simp only [writePhysLoc, readPhysLoc, updateStack, ↓reduceIte]
    exact extractSlice_write_same_shape _ _ .preserveUpper _ _ h_shape
  · simp only [writePhysLoc, readPhysLoc, updateStack, ↓reduceIte]
    exact extractSlice_write_same_shape _ _ .preserveUpper _ _ h_shape

/-- Theorem 10 (Repaired `Edit::Move` Soundness): Unconditionally evicts `dst` and overlapping
    lanes before checking `lookupSym sym src`, preserving `SymRefines` even across clobbered
    or unallocated sources and `WriteMode` zero-extensions! -/
theorem stepMoveRepaired_sound
    (ssa : SsaEnv) (st : AllocState) (sym : SymState)
    (src dst : PhysLoc) (m : WriteMode)
    (h_same_slice : locSlice src = locSlice dst)
    (h_ref : SymRefines ssa st sym) :
    SymRefines ssa (execMoveConcrete st src dst m) (stepMoveRepaired sym src dst m) := by
  intro loc v h_mem
  unfold stepMoveRepaired at h_mem
  cases h_look : lookupSym sym src with
  | none =>
      simp only [h_look, killOverlapping, List.mem_filter] at h_mem
      rcases h_mem with ⟨h_in, h_ni⟩
      unfold execMoveConcrete
      rw [writePhysLoc_frame st dst m _ loc h_ni]
      exact h_ref loc v h_in
  | some v_src =>
      have h_shape : sliceShapeEq (locSlice src) (locSlice dst) = true := by
        rw [h_same_slice]
        cases locSlice dst <;> rfl
      simp only [h_look, h_shape, ↓reduceIte, List.mem_cons, killOverlapping, List.mem_filter] at h_mem
      rcases h_mem with h_pair | ⟨h_in, h_ni⟩
      · rcases h_pair with ⟨rfl, rfl⟩
        have h_src_in := lookupSym_mem sym src v h_look
        have h_src_val := h_ref src v h_src_in
        unfold execMoveConcrete
        rw [h_src_val, h_same_slice]
        exact writePhysLoc_same st _ m (ssa v)
      · unfold execMoveConcrete
        rw [writePhysLoc_frame st dst m _ loc h_ni]
        exact h_ref loc v h_in

def checkWriteSafe (sym : SymState) (dst : PhysLoc) (m : WriteMode) : Bool :=
  sym.all (fun (loc, _) => loc == dst || nonInterferingWrite dst m loc)

/-- Theorem 11 (Spill + Arbitrary Non-Stack Clobber + Safe Reload Soundness):
    Spilling `(src, v)` to `.spill slot sl`, running an arbitrary register-clobbering call/split
    that preserves `stack slot`, and reloading into `dst` guarded by `checkWriteSafe` preserves `SymRefines`. -/
theorem stepSpillAndReload_preserves_refinement
    (ssa : SsaEnv) (st0 stMid : AllocState) (sym0 symMid : SymState)
    (src dst : PhysLoc) (slot : SlotId) (sl : SubRegSlice) (mReload : WriteMode)
    (h_src_sl : locSlice src = sl)
    (h_dst_sl : locSlice dst = sl)
    (h_ref0 : SymRefines ssa st0 sym0)
    (_h_src_in : (src, v) ∈ sym0)
    (_h_spill_ok : nonInterferingWrite (.spill slot sl) .preserveUpper other = true → True)
    (h_mid_ref : SymRefines ssa stMid symMid)
    (h_mid_slot : (.spill slot sl, v) ∈ symMid)
    (h_reload_safe : checkWriteSafe symMid dst mReload = true) :
    let stSpill := execMoveConcrete st0 src (.spill slot sl) .preserveUpper
    SymRefines ssa stSpill (stepMoveRepaired sym0 src (.spill slot sl) .preserveUpper) ∧
    SymRefines ssa (execMoveConcrete stMid (.spill slot sl) dst mReload)
      ((dst, v) :: symMid.filter (fun p => p.1 != dst)) := by
  refine ⟨?_, ?_⟩
  · exact stepMoveRepaired_sound ssa st0 sym0 src (.spill slot sl) .preserveUpper h_src_sl h_ref0
  · intro loc v' h_mem
    simp only [List.mem_cons, List.mem_filter] at h_mem
    rcases h_mem with ⟨rfl, rfl⟩ | ⟨h_in, h_neq⟩
    · have h_slot_val := h_mid_ref (.spill slot sl) v h_mid_slot
      unfold execMoveConcrete
      rw [h_slot_val, ← h_dst_sl]
      exact writePhysLoc_same stMid dst mReload (ssa v)
    · unfold checkWriteSafe at h_reload_safe
      rw [List.all_eq_true] at h_reload_safe
      have h_each := h_reload_safe (loc, v') h_in
      simp only [Bool.or_eq_true] at h_each
      cases h_eq : (loc == dst) with
      | true =>
          simp [bne, h_eq] at h_neq
      | false =>
          rw [h_eq] at h_each
          rcases h_each with h_abs | h_ni
          · cases h_abs
          · unfold execMoveConcrete
            rw [writePhysLoc_frame stMid dst mReload _ loc h_ni]
            exact h_mid_ref loc v' h_in

/-- Theorem 12 (Live-Range Splitting Across Co-Allocated Lanes):
    Splitting `v_lo` across `spill -> reload` using `.preserveUpper` (e.g., legacy SSE `xmm128`
    or GPR `lo16`/`lo8`) strictly preserves a co-allocated live `v_hi` in `ymmHi` (or `hi32`)! -/
theorem liveRangeSplit_coallocated_lanes_sound
    (ssa : SsaEnv) (st : AllocState)
    (r : PRegId) (slot : SlotId) (v_lo v_hi : VRegId)
    (h_ref : SymRefines ssa st [(.reg r .ymm256, v_hi), (.spill slot .xmm128, v_lo)])
    (_h_hi_ok : checkWriteSafe [(.spill slot .xmm128, v_lo)] (.reg r .xmm128) .preserveUpper = true) :
    let st' := execMoveConcrete st (.spill slot .xmm128) (.reg r .xmm128) .preserveUpper
    readPhysLoc st' (.reg r .xmm128) = extractSlice .xmm128 (ssa v_lo) ∧
    (st'.regs r).ymmHi = (st.regs r).ymmHi := by
  refine ⟨?_, ?_⟩
  · have h_slot := h_ref (.spill slot .xmm128) v_lo (by simp)
    unfold execMoveConcrete
    rw [h_slot]
    exact writePhysLoc_same st (.reg r .xmm128) .preserveUpper (ssa v_lo)
  · simp [execMoveConcrete, writePhysLoc, updateReg, applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]

inductive RematOrigin where
  | imm32  (v : BitVec 32)
  | imm64  (v : BitVec 64)
  | roSlot (s : SlotId)
  deriving DecidableEq, Repr

def evalRematOrigin (st : AllocState) : RematOrigin → Reg256
  | .imm32 v =>
      let n := v.toNat
      { b0 := BitVec.ofNat 8 (n % 256)
      , b1 := BitVec.ofNat 8 ((n / 256) % 256)
      , b2 := BitVec.ofNat 8 ((n / 65536) % 256)
      , b3 := BitVec.ofNat 8 ((n / 16777216) % 256) }
  | .imm64 v =>
      let n := v.toNat
      { b0 := BitVec.ofNat 8 (n % 256)
      , b1 := BitVec.ofNat 8 ((n / 256) % 256)
      , b2 := BitVec.ofNat 8 ((n / 65536) % 256)
      , b3 := BitVec.ofNat 8 ((n / 16777216) % 256)
      , b4 := BitVec.ofNat 8 ((n / 4294967296) % 256)
      , b5 := BitVec.ofNat 8 ((n / 1099511627776) % 256)
      , b6 := BitVec.ofNat 8 ((n / 281474976710656) % 256)
      , b7 := BitVec.ofNat 8 ((n / 72057594037927936) % 256) }
  | .roSlot s => st.roPool s

def execRemat (st : AllocState) (orig : RematOrigin) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode) : AllocState :=
  writePhysLoc st (.reg dst sl) m (extractSlice sl (evalRematOrigin st orig))

def checkRematSafe (sym : SymState) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode) : Bool :=
  checkWriteSafe sym (.reg dst sl) m

/-- Theorem 13 (Verified Rematerialization Soundness): Guarded by `checkRematSafe`, rematerialization
    from immutable constants or `roPool` establishes `(dst, v)` and preserves all co-allocated lanes. -/
theorem stepRematSafe_sound
    (ssa : SsaEnv) (st : AllocState) (sym : SymState)
    (orig : RematOrigin) (v : VRegId) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode)
    (h_ref : SymRefines ssa st sym)
    (h_origin : extractSlice sl (evalRematOrigin st orig) = extractSlice sl (ssa v))
    (h_safe : checkRematSafe sym dst sl m = true) :
    SymRefines ssa (execRemat st orig dst sl m)
      ((.reg dst sl, v) :: sym.filter (fun p => p.1 != .reg dst sl)) := by
  intro loc v' h_mem
  simp only [List.mem_cons, List.mem_filter] at h_mem
  rcases h_mem with ⟨rfl, rfl⟩ | ⟨h_in, h_neq⟩
  · unfold execRemat
    rw [h_origin]
    exact writePhysLoc_same st (.reg dst sl) m (ssa v)
  · unfold checkRematSafe checkWriteSafe at h_safe
    rw [List.all_eq_true] at h_safe
    have h_each := h_safe (loc, v') h_in
    simp only [Bool.or_eq_true] at h_each
    cases h_eq : (loc == .reg dst sl) with
    | true => simp [bne, h_eq] at h_neq
    | false =>
        rw [h_eq] at h_each
        rcases h_each with h_abs | h_ni
        · cases h_abs
        · unfold execRemat
          rw [writePhysLoc_frame st (.reg dst sl) m _ loc h_ni]
          exact h_ref loc v' h_in

structure SeqMove where
  src  : PhysLoc
  dst  : PhysLoc
  mode : WriteMode
  deriving DecidableEq, Repr

def execMoveSeq (st : AllocState) : List SeqMove → AllocState
  | []      => st
  | m :: ms => execMoveSeq (execMoveConcrete st m.src m.dst m.mode) ms

abbrev OriginEnv := List (PhysLoc × PhysLoc)

def stepOriginMove (env : OriginEnv) (m : SeqMove) : Option OriginEnv :=
  if sliceShapeEq (locSlice m.src) (locSlice m.dst) then
    match env.find? (fun p => p.1 == m.src) with
    | none => none
    | some (_, srcOrig) =>
        let cleaned := env.filter (fun p => nonInterferingWrite m.dst m.mode p.1)
        some ((m.dst, srcOrig) :: cleaned)
  else none

def runOriginMoves : List SeqMove → OriginEnv → Option OriginEnv
  | [], env      => some env
  | m :: ms, env =>
      match stepOriginMove env m with
      | none      => none
      | some env' => runOriginMoves ms env'

def checkParMoveOnDomain (domain : List PhysLoc) (seq : List SeqMove) (spec : List (PhysLoc × PhysLoc)) : Bool :=
  let initEnv : OriginEnv := domain.map (fun l => (l, l))
  match runOriginMoves seq initEnv with
  | none => false
  | some finalEnv =>
      spec.all (fun p => finalEnv.any (fun q => q.1 == p.1 && q.2 == p.2))

def OriginRefines (st0 st : AllocState) (env : OriginEnv) : Prop :=
  ∀ loc orig, (loc, orig) ∈ env →
    sliceShapeEq (locSlice loc) (locSlice orig) = true ∧
    readPhysLoc st loc = readPhysLoc st0 orig

private theorem sliceShapeEq_symm (a b : SubRegSlice) (h : sliceShapeEq a b = true) :
    sliceShapeEq b a = true := by
  simp only [sliceShapeEq, beq_iff_eq] at h ⊢
  exact h.symm

private theorem sliceShapeEq_trans (a b c : SubRegSlice)
    (h1 : sliceShapeEq a b = true) (h2 : sliceShapeEq b c = true) :
    sliceShapeEq a c = true := by
  simp only [sliceShapeEq, beq_iff_eq] at h1 h2 ⊢
  exact h1.trans h2

/-- Theorem 14 (Repaired `MoveAndScratchResolver` Single-Step Soundness):
    When `m.src` is seeded/live in `OriginEnv` (`none` fails closed, repairing `regalloc2`'s
    silent pass on unallocated scratch slots!) and clobbered lanes are evicted via
    `nonInterferingWrite`, `OriginRefines` is preserved inductively. -/
theorem stepOriginMove_sound
    (st0 st : AllocState) (env env' : OriginEnv) (m : SeqMove)
    (h_ref : OriginRefines st0 st env)
    (h_step : stepOriginMove env m = some env') :
    OriginRefines st0 (execMoveConcrete st m.src m.dst m.mode) env' := by
  unfold stepOriginMove at h_step
  cases h_sl : sliceShapeEq (locSlice m.src) (locSlice m.dst)
  · simp [h_sl] at h_step
  · simp only [h_sl, ↓reduceIte] at h_step
    cases hf : env.find? (fun p => p.1 == m.src) with
    | none => simp [hf] at h_step
    | some p =>
        rcases p with ⟨l_src, o_src⟩
        simp only [hf, Option.some.injEq] at h_step
        subst h_step
        have h_eq_src : l_src = m.src := by
          have hb := List.find?_some hf
          simp only [beq_iff_eq] at hb
          exact hb
        subst h_eq_src
        have h_mem_src : (m.src, o_src) ∈ env := List.mem_of_find?_eq_some hf
        rcases h_ref m.src o_src h_mem_src with ⟨h_sl_orig, h_val_src⟩
        intro loc orig h_mem
        simp only [List.mem_cons, List.mem_filter] at h_mem
        rcases h_mem with h_pair | ⟨h_in, h_ni⟩
        · cases h_pair
          have h_orig_to_dst : sliceShapeEq (locSlice o_src) (locSlice m.dst) = true :=
            sliceShapeEq_trans _ _ _ (sliceShapeEq_symm _ _ h_sl_orig) h_sl
          have h_dst_orig : sliceShapeEq (locSlice m.dst) (locSlice o_src) = true :=
            sliceShapeEq_symm _ _ h_orig_to_dst
          refine ⟨h_dst_orig, ?_⟩
          unfold execMoveConcrete
          rw [h_val_src]
          exact writePhysLoc_readPhysLoc_same_shape st0 st m.dst o_src m.mode h_orig_to_dst
        · rcases h_ref loc orig h_in with ⟨h_sl_loc, h_val_loc⟩
          refine ⟨h_sl_loc, ?_⟩
          unfold execMoveConcrete
          rw [writePhysLoc_frame st m.dst m.mode _ loc h_ni]
          exact h_val_loc

/-- Theorem 15 (Repaired `MoveAndScratchResolver` 256-Bit Cycle + `AL`/`AH` Swap + Borrowed Scratch):
    Verifies a 3-way `ymm256` cycle `(y0, y1, y2) := (y1, y2, y0)` using a live borrowed
    scratch register `y3` saved/restored to `saveSlot`, PLUS simultaneous `AL <-> AH` swap
    using byte scratch `bl5` (`r5.lo8`)! -/
theorem moveAndScratchResolver_repaired_cycle_sound :
    let y0 := PhysLoc.reg ⟨0, by decide⟩ .ymm256
    let y1 := PhysLoc.reg ⟨1, by decide⟩ .ymm256
    let y2 := PhysLoc.reg ⟨2, by decide⟩ .ymm256
    let y3 := PhysLoc.reg ⟨3, by decide⟩ .ymm256
    let saveSlot := PhysLoc.spill 0 .ymm256
    let al4 := PhysLoc.reg ⟨4, by decide⟩ .lo8
    let ah4 := PhysLoc.reg ⟨4, by decide⟩ .hi8
    let bl5 := PhysLoc.reg ⟨5, by decide⟩ .lo8
    let domain := [y0, y1, y2, y3, al4, ah4, bl5]
    let seq : List SeqMove :=
      [ { src := y3,       dst := saveSlot, mode := .preserveUpper }
      , { src := y0,       dst := y3,       mode := .zeroExtend256 }
      , { src := y1,       dst := y0,       mode := .zeroExtend256 }
      , { src := y2,       dst := y1,       mode := .zeroExtend256 }
      , { src := y3,       dst := y2,       mode := .zeroExtend256 }
      , { src := saveSlot, dst := y3,       mode := .zeroExtend256 }
      , { src := al4,      dst := bl5,      mode := .preserveUpper }
      , { src := ah4,      dst := al4,      mode := .preserveUpper }
      , { src := bl5,      dst := ah4,      mode := .preserveUpper } ]
    let spec := [(y0, y1), (y1, y2), (y2, y0), (y3, y3), (al4, ah4), (ah4, al4)]
    checkParMoveOnDomain domain seq spec = true := by
  decide

/-- Theorem 16 (Counterexample: Naive 32-Bit Rematerialization Clobbers Co-Allocated `RAX[63:32]`):
    When `RAX[63:32]` holds live `v_hi`, rematerializing `imm32` into `EAX` via `movl`
    (`zeroExtend64`) zeroes `b4..b7` and is rejected (`false`) by `checkRematSafe`. -/
theorem cex_naive_32bit_remat_clobbers_coallocated_hi32 :
    let rax : PRegId := ⟨0, by decide⟩
    let hiLoc := PhysLoc.reg rax .hi32
    let sym : SymState := [(hiLoc, 1)]
    let st : AllocState :=
      { regs := fun _ => { b4 := 0xAA#8, b5 := 0xBB#8, b6 := 0xCC#8, b7 := 0xDD#8 }
      , stack := fun _ => {}
      , roPool := fun _ => {} }
    checkRematSafe sym rax .lo32 .zeroExtend64 = false ∧
    readPhysLoc (execRemat st (.imm32 0x2A#32) rax .lo32 .zeroExtend64) hiLoc =
      [.u8 0#8, .u8 0#8, .u8 0#8, .u8 0#8] := by
  refine ⟨rfl, rfl⟩

/-- Theorem 17 (Counterexample: VEX-128 Reload Clobbers Co-Allocated `YMM0[255:128]`):
    Reloading `xmm0` via VEX-128 `vmovdqu` (`zeroExtend256`) destroys live `YMM0[255:128]`,
    whereas legacy SSE `movdqu` (`preserveUpper`) keeps `YMM0[255:128]` intact. -/
theorem cex_vex128_reload_clobbers_coallocated_ymmHi :
    let r0 : PRegId := ⟨0, by decide⟩
    let ymm0 := PhysLoc.reg r0 .ymm256
    let xmm0 := PhysLoc.reg r0 .xmm128
    let spillSlot := PhysLoc.spill 0 .xmm128
    let sym : SymState := [(ymm0, 1), (spillSlot, 2)]
    let hiSeed : BitVec 128 := BitVec.ofNat 128 0xCAFEBABE_DEADBEEF
    let st : AllocState :=
      { regs := fun _ => { b0 := 1#8, ymmHi := hiSeed }
      , stack := fun _ => { b0 := 9#8 }
      , roPool := fun _ => {} }
    checkWriteSafe sym xmm0 .zeroExtend256 = false ∧
    checkWriteSafe [(.spill 0 .xmm128, 2)] xmm0 .preserveUpper = true ∧
    ((execMoveConcrete st spillSlot xmm0 .zeroExtend256).regs r0).ymmHi = 0#128 ∧
    ((execMoveConcrete st spillSlot xmm0 .preserveUpper).regs r0).ymmHi = hiSeed := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 18 (Counterexample: `regalloc2` Missing-`else` SaveSlot Corruption & Narrow Scratch Save):
    (a) `stepMoveBuggyRegalloc2` leaves stale `(p0, v0)` when restoring from an unallocated `saveSlot`
        (while `stepMoveRepaired` evicts it and `stepOriginMove` fails closed `= none`);
    (b) Saving a `ymm256`-live borrowed scratch via narrow `xmm128` fails `checkParMoveOnDomain`
        and leaves `YMM3[255:128]` clobbered after cycle + restore. -/
theorem cex_borrowed_scratch_missing_else_and_narrow_save_unsound :
    let r0 : PRegId := ⟨0, by decide⟩
    let r3 : PRegId := ⟨3, by decide⟩
    let p0 := PhysLoc.reg r0 .full64
    let saveSlot := PhysLoc.spill 9 .full64
    let sym : SymState := [(p0, 0)]
    let st : AllocState :=
      { regs := fun _ => { b0 := 0x11#8 }
      , stack := fun _ => { b0 := 0xEE#8 }
      , roPool := fun _ => {} }
    let ssa : SsaEnv := fun _ => { b0 := 0x11#8 }
    let y3Full := PhysLoc.reg r3 .ymm256
    let y3Lo   := PhysLoc.reg r3 .xmm128
    let narrowSave := PhysLoc.spill 1 .xmm128
    let narrowSeq : List SeqMove :=
      [ { src := y3Lo, dst := narrowSave, mode := .preserveUpper }
      , { src := PhysLoc.reg r0 .ymm256, dst := y3Full, mode := .zeroExtend256 }
      , { src := narrowSave, dst := y3Lo, mode := .zeroExtend256 } ]
    ((p0, 0) ∈ stepMoveBuggyRegalloc2 sym saveSlot p0) ∧
    ¬ SymRefines ssa (execMoveConcrete st saveSlot p0 .preserveUpper)
      (stepMoveBuggyRegalloc2 sym saveSlot p0) ∧
    ((p0, 0) ∉ stepMoveRepaired sym saveSlot p0 .preserveUpper) ∧
    (runOriginMoves [{ src := saveSlot, dst := p0, mode := .preserveUpper }] [(p0, p0)] = none) ∧
    (checkParMoveOnDomain [PhysLoc.reg r0 .ymm256, y3Full, y3Lo] narrowSeq [(y3Full, y3Full)] = false) := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · simp [stepMoveBuggyRegalloc2, lookupSym]
  · intro h_bad
    have h_eq := h_bad (PhysLoc.reg ⟨0, by decide⟩ .full64) 0
      (by simp [stepMoveBuggyRegalloc2, lookupSym])
    simp [execMoveConcrete, writePhysLoc, readPhysLoc, updateReg, applyReg256Write,
          packSlice, extractSlice, sliceLanes, readLane, laneInSlice, locSlice] at h_eq
  · simp [stepMoveRepaired, lookupSym, killOverlapping, nonInterferingWrite,
          sliceLanes, touchedByWrite, laneInSlice]

/-! ## Section 3: CFG-Aware `vzeroupper` Dataflow Across `ret`, Tail Calls, Calls & `panic=unwind` -/

abbrev DirtyYmmMask := PRegId → Bool

def cleanYmmMask : DirtyYmmMask := fun _ => false

def isCleanMask (m : DirtyYmmMask) : Bool :=
  (List.finRange 16).all (fun r => !(m r))

def leMask (m1 m2 : DirtyYmmMask) : Bool :=
  (List.finRange 16).all (fun r => !(m1 r) || m2 r)

def setDirtyMask (m : DirtyYmmMask) (r : PRegId) (dirty : Bool) : DirtyYmmMask :=
  fun r' => if r' = r then dirty else m r'

def MaskAgree (st : AllocState) (m : DirtyYmmMask) : Prop :=
  ∀ r : PRegId, m r = false → (st.regs r).ymmHi = 0#128

private theorem all_finRange_forall (p : PRegId → Bool)
    (h : (List.finRange 16).all p = true) : ∀ r : PRegId, p r = true := by
  rw [List.all_eq_true] at h
  intro r
  exact h r (List.mem_finRange r)

theorem isCleanMask_sound (st : AllocState) (m : DirtyYmmMask)
    (h_agree : MaskAgree st m) (h_clean : isCleanMask m = true) :
    ∀ r : PRegId, (st.regs r).ymmHi = 0#128 := by
  intro r
  have hall := all_finRange_forall (fun x => !(m x)) h_clean r
  simp only [Bool.not_eq_true'] at hall
  exact h_agree r hall

theorem leMask_preserves_agree (st : AllocState) (m1 m2 : DirtyYmmMask)
    (h_agree : MaskAgree st m1) (h_le : leMask m1 m2 = true) :
    MaskAgree st m2 := by
  intro r hm2
  have hall := all_finRange_forall (fun x => !(m1 x) || m2 x) h_le r
  rw [hm2, Bool.or_false, Bool.not_eq_true'] at hall
  exact h_agree r hall

def execVZeroUpper (st : AllocState) : AllocState :=
  { st with regs := fun r => { st.regs r with ymmHi := 0#128 } }

/-- Theorem 19 (`vzeroupper` Semantics & Lower-Lane Framing):
    `vzeroupper` zeroes `ymmHi` across all 16 registers while strictly preserving every
    GPR byte (`b0..b7`) and `XMM[127:64]` (`xmmHi`), plus every `.full64`/`.xmm128`/`.spill`
    binding in `SymState`. -/
theorem vzeroupper_clears_ymmHi_and_preserves_gpr_xmm128
    (st : AllocState) (ssa : SsaEnv) (sym : SymState)
    (h_ref : SymRefines ssa st sym)
    (h_no_ymm : ∀ loc v, (loc, v) ∈ sym → locSlice loc ≠ .ymm256) :
    let st' := execVZeroUpper st
    (∀ r : PRegId, (st'.regs r).ymmHi = 0#128) ∧
    (∀ r : PRegId, (st'.regs r).xmmHi = (st.regs r).xmmHi) ∧
    (∀ r : PRegId, (st'.regs r).b0 = (st.regs r).b0) ∧
    SymRefines ssa st' sym := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  intro loc v h_mem
  have h_prev := h_ref loc v h_mem
  have h_ny := h_no_ymm loc v h_mem
  cases loc with
  | spill s sl => exact h_prev
  | reg r sl =>
      cases sl with
      | ymm256 => exact False.elim (h_ny rfl)
      | lo8 | hi8 | lo16 | lo32 | hi32 | full64 | xmm128 =>
          simpa [execVZeroUpper, readPhysLoc, extractSlice, sliceLanes, readLane] using h_prev

/-- Theorem 20 (VEX-128 Single-Register Clear Does NOT Replace `vzeroupper`):
    Writing `xmm0` with `.zeroExtend256` (VEX-128) zeroes ONLY `YMM0[255:128]` and updates
    only `mask 0 := false`, leaving `YMM1[255:128]` dirty! -/
theorem vex128_clears_single_reg_leaves_other_ymm_dirty :
    let r0 : PRegId := ⟨0, by decide⟩
    let r1 : PRegId := ⟨1, by decide⟩
    let dirtySeed : BitVec 128 := BitVec.ofNat 128 0x1234_5678
    let st : AllocState :=
      { regs := fun _ => { ymmHi := dirtySeed }
      , stack := fun _ => {}
      , roPool := fun _ => {} }
    let m0 : DirtyYmmMask := fun _ => true
    let st1 := writePhysLoc st (.reg r0 .xmm128) .zeroExtend256 (extractSlice .xmm128 {})
    let m1 := setDirtyMask m0 r0 false
    (st1.regs r0).ymmHi = 0#128 ∧
    m1 r1 = true ∧
    (st1.regs r1).ymmHi = dirtySeed ∧
    isCleanMask m1 = false := by
  refine ⟨rfl, rfl, rfl, rfl⟩

inductive CfgOp where
  | writeYmm (r : PRegId) (sl : SubRegSlice) (wm : WriteMode) (val : Reg256)
  | vzeroupper
  | nopScalar
  deriving DecidableEq, Repr

inductive CfgTerm where
  | ret
  | tailCall
  | br (next : Nat)
  | condBr (t f : Nat)
  | callThen (needsCleanAbi : Bool) (next : Nat)
  | invoke (needsCleanAbi : Bool) (normal unwind : Nat)
  | unwindResume
  deriving DecidableEq, Repr

structure CfgBlock where
  ops  : List CfgOp
  term : CfgTerm
  deriving DecidableEq, Repr

def stepCfgOp (st : AllocState) : CfgOp → AllocState
  | .writeYmm r sl wm val =>
      updateReg st r (applyReg256Write sl wm val (st.regs r))
  | .vzeroupper => execVZeroUpper st
  | .nopScalar  => st

def stepCfgMask (m : DirtyYmmMask) : CfgOp → DirtyYmmMask
  | .writeYmm r sl wm _ =>
      match wm with
      | .zeroExtend256 =>
          match sl with
          | .ymm256 => setDirtyMask m r true
          | _       => setDirtyMask m r false
      | .preserveUpper | .zeroExtend64 =>
          match sl with
          | .ymm256 => setDirtyMask m r true
          | _       => m
  | .vzeroupper => cleanYmmMask
  | .nopScalar  => m

def runBlockOps (ops : List CfgOp) (st : AllocState) : AllocState :=
  ops.foldl stepCfgOp st

def runBlockMasks (ops : List CfgOp) (m : DirtyYmmMask) : DirtyYmmMask :=
  ops.foldl stepCfgMask m

theorem stepCfgOp_preserves_maskAgree (st : AllocState) (m : DirtyYmmMask) (op : CfgOp)
    (h : MaskAgree st m) :
    MaskAgree (stepCfgOp st op) (stepCfgMask m op) := by
  cases op with
  | nopScalar => exact h
  | vzeroupper =>
      intro r _
      rfl
  | writeYmm r sl wm val =>
      intro r' hr'
      simp only [stepCfgOp, updateReg]
      by_cases h_eq : r' = r
      · subst h_eq
        simp only [↓reduceIte]
        cases wm with
        | zeroExtend256 =>
            cases sl with
            | ymm256 =>
                simp [stepCfgMask, setDirtyMask] at hr'
            | lo8 | hi8 | lo16 | lo32 | hi32 | full64 | xmm128 =>
                simp [applyReg256Write, zeroedByMode, laneInSlice, sliceLanes]
        | preserveUpper =>
            cases sl with
            | ymm256 => simp [stepCfgMask, setDirtyMask] at hr'
            | lo8 | hi8 | lo16 | lo32 | hi32 | full64 | xmm128 =>
                simp [stepCfgMask] at hr'
                have h_prev := h r' hr'
                simp [applyReg256Write, zeroedByMode, laneInSlice, sliceLanes, h_prev]
        | zeroExtend64 =>
            cases sl with
            | ymm256 => simp [stepCfgMask, setDirtyMask] at hr'
            | lo8 | hi8 | lo16 | lo32 | hi32 | full64 | xmm128 =>
                simp [stepCfgMask] at hr'
                have h_prev := h r' hr'
                simp [applyReg256Write, zeroedByMode, laneInSlice, sliceLanes, h_prev]
      · simp only [h_eq, ↓reduceIte]
        have hr_old : m r' = false := by
          cases wm <;> cases sl <;> simp [stepCfgMask, setDirtyMask, h_eq] at hr' <;> exact hr'
        exact h r' hr_old

theorem runBlockOps_preserves_maskAgree (ops : List CfgOp) (st : AllocState) (m : DirtyYmmMask)
    (h : MaskAgree st m) :
    MaskAgree (runBlockOps ops st) (runBlockMasks ops m) := by
  induction ops generalizing st m with
  | nil => exact h
  | cons op tl ih =>
      exact ih (stepCfgOp st op) (stepCfgMask m op) (stepCfgOp_preserves_maskAgree st m op h)

def checkBlockVZeroUpper (entryMasks : List DirtyYmmMask) (idx : Nat) (blk : CfgBlock) : Bool :=
  match entryMasks[idx]? with
  | none => false
  | some mIn =>
      let mOut := runBlockMasks blk.ops mIn
      match blk.term with
      | .ret | .tailCall | .unwindResume => isCleanMask mOut
      | .br nxt =>
          match entryMasks[nxt]? with
          | some mNext => leMask mOut mNext
          | none => false
      | .condBr t f =>
          match entryMasks[t]?, entryMasks[f]? with
          | some mT, some mF => leMask mOut mT && leMask mOut mF
          | _, _ => false
      | .callThen needsClean nxt =>
          let okAbi := !needsClean || isCleanMask mOut
          let postM := if needsClean then cleanYmmMask else mOut
          match entryMasks[nxt]? with
          | some mNext => okAbi && leMask postM mNext
          | none => false
      | .invoke needsClean norm unw =>
          let okAbi := !needsClean || isCleanMask mOut
          let postM := if needsClean then cleanYmmMask else mOut
          match entryMasks[norm]?, entryMasks[unw]? with
          | some mNorm, some mUnw => okAbi && leMask postM mNorm && leMask postM mUnw
          | _, _ => false

def checkCfgVZeroUpperGo (entryMasks : List DirtyYmmMask) (idx : Nat) : List CfgBlock → Bool
  | [] => true
  | b :: bs => checkBlockVZeroUpper entryMasks idx b && checkCfgVZeroUpperGo entryMasks (idx + 1) bs

def checkCfgVZeroUpper (entryMasks : List DirtyYmmMask) (cfg : List CfgBlock) : Bool :=
  checkCfgVZeroUpperGo entryMasks 0 cfg

private theorem checkCfgVZeroUpper_go_mem (entryMasks : List DirtyYmmMask) :
    ∀ (base : Nat) (cfg : List CfgBlock) (k : Nat) (blk : CfgBlock),
      checkCfgVZeroUpperGo entryMasks base cfg = true →
      cfg[k]? = some blk →
      checkBlockVZeroUpper entryMasks (base + k) blk = true
  | _, [], _, _, _, hget => by simp at hget
  | base, b :: bs, 0, blk, hok, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [checkCfgVZeroUpperGo, Bool.and_eq_true] at hok
      rw [Nat.add_zero]
      exact hok.1
  | base, b :: bs, k + 1, blk, hok, hget => by
      simp only [List.getElem?_cons_succ] at hget
      simp only [checkCfgVZeroUpperGo, Bool.and_eq_true] at hok
      rw [Nat.add_comm k 1, ← Nat.add_assoc]
      exact checkCfgVZeroUpper_go_mem entryMasks (base + 1) bs k blk hok.2 hget

inductive CfgStep (cfg : List CfgBlock) : (Nat × AllocState) → (Nat × AllocState) → Prop where
  | br (pc next : Nat) (blk : CfgBlock) (st : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .br next) :
      CfgStep cfg (pc, st) (next, runBlockOps blk.ops st)
  | condT (pc t f : Nat) (blk : CfgBlock) (st : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .condBr t f) :
      CfgStep cfg (pc, st) (t, runBlockOps blk.ops st)
  | condF (pc t f : Nat) (blk : CfgBlock) (st : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .condBr t f) :
      CfgStep cfg (pc, st) (f, runBlockOps blk.ops st)
  | callStep (pc next : Nat) (needsClean : Bool) (blk : CfgBlock) (st stCallee : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .callThen needsClean next)
      (hcal : stCallee = if needsClean then execVZeroUpper (runBlockOps blk.ops st) else runBlockOps blk.ops st) :
      CfgStep cfg (pc, st) (next, stCallee)
  | invokeNormal (pc norm unw : Nat) (needsClean : Bool) (blk : CfgBlock) (st stCallee : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .invoke needsClean norm unw)
      (hcal : stCallee = if needsClean then execVZeroUpper (runBlockOps blk.ops st) else runBlockOps blk.ops st) :
      CfgStep cfg (pc, st) (norm, stCallee)
  | invokeUnwind (pc norm unw : Nat) (needsClean : Bool) (blk : CfgBlock) (st stCallee : AllocState)
      (hblk : cfg[pc]? = some blk) (ht : blk.term = .invoke needsClean norm unw)
      (hcal : stCallee = if needsClean then execVZeroUpper (runBlockOps blk.ops st) else runBlockOps blk.ops st) :
      CfgStep cfg (pc, st) (unw, stCallee)

inductive CfgReach (cfg : List CfgBlock) : Nat → (Nat × AllocState) → (Nat × AllocState) → Prop where
  | refl (s : Nat × AllocState) : CfgReach cfg 0 s s
  | step {n : Nat} {s0 s1 s2 : Nat × AllocState} :
      CfgStep cfg s0 s1 → CfgReach cfg n s1 s2 → CfgReach cfg (n + 1) s0 s2

def AtAbiBoundary (cfg : List CfgBlock) (pc : Nat) (st : AllocState) : Prop :=
  ∀ blk, cfg[pc]? = some blk →
    let stOut := runBlockOps blk.ops st
    match blk.term with
    | .ret | .tailCall | .unwindResume => ∀ r : PRegId, (stOut.regs r).ymmHi = 0#128
    | .callThen true _ => ∀ r : PRegId, (stOut.regs r).ymmHi = 0#128
    | .invoke true _ _ => ∀ r : PRegId, (stOut.regs r).ymmHi = 0#128
    | _ => True

/-- Theorem 21 (CFG-Aware `vzeroupper` Single-Step Invariant & ABI Boundary Soundness):
    Every `CfgStep` preserves `MaskAgree` against `entryMasks`, and every block's ABI
    exit (`ret`, `tailCall`, `callThen true`, `invoke true`, `unwindResume`) guarantees
    zero `YMM[255:128]` across all 16 registers. -/
theorem checkCfgVZeroUpper_step_sound
    (entryMasks : List DirtyYmmMask) (cfg : List CfgBlock)
    (hchk : checkCfgVZeroUpper entryMasks cfg = true)
    (pc : Nat) (st : AllocState) (mIn : DirtyYmmMask)
    (hmIn : entryMasks[pc]? = some mIn)
    (h_agree : MaskAgree st mIn) :
    AtAbiBoundary cfg pc st ∧
    (∀ pc' st', CfgStep cfg (pc, st) (pc', st') →
      ∃ mNext, entryMasks[pc']? = some mNext ∧ MaskAgree st' mNext) := by
  refine ⟨?_, ?_⟩
  · intro blk hblk
    have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
    rw [Nat.zero_add] at hbchk
    unfold checkBlockVZeroUpper at hbchk
    rw [hmIn] at hbchk
    dsimp only at hbchk
    have hOut := runBlockOps_preserves_maskAgree blk.ops st mIn h_agree
    cases ht : blk.term with
    | ret | tailCall | unwindResume =>
        rw [ht] at hbchk
        exact isCleanMask_sound _ _ hOut hbchk
    | br _ | condBr _ _ => trivial
    | callThen nc nxt =>
        cases nc with
        | false => trivial
        | true =>
            rw [ht] at hbchk
            cases hnx : entryMasks[nxt]? with
            | none => simp [hnx] at hbchk
            | some _ =>
                simp only [hnx, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hbchk
                exact isCleanMask_sound _ _ hOut hbchk.1
    | invoke nc norm unw =>
        cases nc with
        | false => trivial
        | true =>
            rw [ht] at hbchk
            cases hnm : entryMasks[norm]? with
            | none => simp [hnm] at hbchk
            | some _ =>
                cases huw : entryMasks[unw]? with
                | none => simp [hnm, huw] at hbchk
                | some _ =>
                    simp only [hnm, huw, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hbchk
                    exact isCleanMask_sound _ _ hOut hbchk.1.1
  · intro pc' st' hstep
    cases hstep with
    | br _ _ blk _ hblk ht =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases hnx : entryMasks[pc']? with
        | none => simp [hnx] at hbchk
        | some mNext =>
            simp only [hnx] at hbchk
            refine ⟨mNext, rfl, leMask_preserves_agree _ _ _ (runBlockOps_preserves_maskAgree blk.ops st mIn h_agree) hbchk⟩
    | condT _ _ f blk _ hblk ht =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases h1 : entryMasks[pc']? with
        | none => simp [h1] at hbchk
        | some mT =>
            cases h2 : entryMasks[f]? with
            | none => simp [h1, h2] at hbchk
            | some mF =>
                simp only [h1, h2, Bool.and_eq_true] at hbchk
                refine ⟨mT, rfl, leMask_preserves_agree _ _ _ (runBlockOps_preserves_maskAgree blk.ops st mIn h_agree) hbchk.1⟩
    | condF _ t _ blk _ hblk ht =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases h1 : entryMasks[t]? with
        | none => simp [h1] at hbchk
        | some mT =>
            cases h2 : entryMasks[pc']? with
            | none => simp [h1, h2] at hbchk
            | some mF =>
                simp only [h1, h2, Bool.and_eq_true] at hbchk
                refine ⟨mF, rfl, leMask_preserves_agree _ _ _ (runBlockOps_preserves_maskAgree blk.ops st mIn h_agree) hbchk.2⟩
    | callStep _ _ nc blk _ _ hblk ht hcal =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases h1 : entryMasks[pc']? with
        | none => simp [h1] at hbchk
        | some mNext =>
            have hOut := runBlockOps_preserves_maskAgree blk.ops st mIn h_agree
            cases nc with
            | false =>
                simp only [h1, Bool.not_false, Bool.true_or, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at hcal hbchk
                subst hcal
                exact ⟨mNext, rfl, leMask_preserves_agree _ _ _ hOut hbchk⟩
            | true =>
                simp only [h1, Bool.not_true, Bool.false_or, Bool.and_eq_true, ↓reduceIte] at hcal hbchk
                subst hcal
                refine ⟨mNext, rfl, leMask_preserves_agree _ _ _ (fun _ _ => rfl) hbchk.2⟩
    | invokeNormal _ _ unw nc blk _ _ hblk ht hcal =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases h1 : entryMasks[pc']? with
        | none => simp [h1] at hbchk
        | some mNorm =>
            cases h2 : entryMasks[unw]? with
            | none => simp [h1, h2] at hbchk
            | some mUnw =>
                have hOut := runBlockOps_preserves_maskAgree blk.ops st mIn h_agree
                cases nc with
                | false =>
                    simp only [h1, h2, Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true,
                               Bool.false_eq_true, ↓reduceIte] at hcal hbchk
                    subst hcal
                    exact ⟨mNorm, rfl, leMask_preserves_agree _ _ _ hOut hbchk.1⟩
                | true =>
                    simp only [h1, h2, Bool.not_true, Bool.false_or, Bool.and_eq_true, ↓reduceIte] at hcal hbchk
                    subst hcal
                    exact ⟨mNorm, rfl, leMask_preserves_agree _ _ _ (fun _ _ => rfl) hbchk.1.2⟩
    | invokeUnwind _ norm _ nc blk _ _ hblk ht hcal =>
        have hbchk := checkCfgVZeroUpper_go_mem entryMasks 0 cfg pc blk hchk hblk
        rw [Nat.zero_add] at hbchk
        unfold checkBlockVZeroUpper at hbchk
        rw [hmIn, ht] at hbchk
        dsimp only at hbchk
        cases h1 : entryMasks[norm]? with
        | none => simp [h1] at hbchk
        | some mNorm =>
            cases h2 : entryMasks[pc']? with
            | none => simp [h1, h2] at hbchk
            | some mUnw =>
                have hOut := runBlockOps_preserves_maskAgree blk.ops st mIn h_agree
                cases nc with
                | false =>
                    simp only [h1, h2, Bool.not_false, Bool.true_or, Bool.true_and, Bool.and_eq_true,
                               Bool.false_eq_true, ↓reduceIte] at hcal hbchk
                    subst hcal
                    exact ⟨mUnw, rfl, leMask_preserves_agree _ _ _ hOut hbchk.2⟩
                | true =>
                    simp only [h1, h2, Bool.not_true, Bool.false_or, Bool.and_eq_true, ↓reduceIte] at hcal hbchk
                    subst hcal
                    exact ⟨mUnw, rfl, leMask_preserves_agree _ _ _ (fun _ _ => rfl) hbchk.2⟩

private theorem checkCfgVZeroUpper_trace_sound_aux
    (entryMasks : List DirtyYmmMask) (cfg : List CfgBlock)
    (hchk : checkCfgVZeroUpper entryMasks cfg = true) :
    ∀ (steps : Nat) (s0 sK : Nat × AllocState),
      CfgReach cfg steps s0 sK →
      ∀ (m0 : DirtyYmmMask), entryMasks[s0.1]? = some m0 → MaskAgree s0.2 m0 →
      AtAbiBoundary cfg sK.1 sK.2 := by
  intro steps s0 sK h_reach
  induction h_reach with
  | refl s =>
      intro m0 hm0 hag0
      exact (checkCfgVZeroUpper_step_sound entryMasks cfg hchk s.1 s.2 m0 hm0 hag0).1
  | step hstep hrest ih =>
      intro m0 hm0 hag0
      rcases (checkCfgVZeroUpper_step_sound entryMasks cfg hchk _ _ m0 hm0 hag0).2 _ _ hstep
        with ⟨m1, hm1, hag1⟩
      exact ih m1 hm1 hag1

/-- Theorem 22 (CFG-Aware `vzeroupper` Multi-Step Trace Soundness):
    Across arbitrary normal and exceptional (`invoke -> landingpad -> unwindResume`) traces,
    every reachable ABI boundary satisfies `∀ r, (stOut.regs r).ymmHi = 0#128`. -/
theorem checkCfgVZeroUpper_trace_sound
    (entryMasks : List DirtyYmmMask) (cfg : List CfgBlock)
    (hchk : checkCfgVZeroUpper entryMasks cfg = true)
    (steps : Nat) (pc0 pcK : Nat) (st0 stK : AllocState)
    (m0 : DirtyYmmMask) (hm0 : entryMasks[pc0]? = some m0) (h_ag0 : MaskAgree st0 m0)
    (h_reach : CfgReach cfg steps (pc0, st0) (pcK, stK)) :
    AtAbiBoundary cfg pcK stK :=
  checkCfgVZeroUpper_trace_sound_aux entryMasks cfg hchk steps (pc0, st0) (pcK, stK) h_reach m0 hm0 h_ag0

def naiveLinearScanNoVzuBeforeRet (cfg : List CfgBlock) : Bool :=
  cfg.all (fun blk =>
    match blk.term with
    | .ret => blk.ops.contains .vzeroupper
    | _ => true)

/-- Theorem 23 (`memchr::find_avx2` Multi-Exit CFG Witness):
    A multi-exit AVX2 function with an early scalar exit (BB1, 0 `vzeroupper`) and an AVX2
    exit (BB2, `vzeroupper; ret`) passes `checkCfgVZeroUpper = true`, while naive linear-scan
    falsely rejects BB1 (`naiveLinearScanNoVzuBeforeRet = false`)! -/
theorem memchr_multi_exit_cfg_accepted_without_early_vzeroupper :
    let r0 : PRegId := ⟨0, by decide⟩
    let bb0 : CfgBlock := { ops := [.nopScalar], term := .condBr 1 2 }
    let bb1 : CfgBlock := { ops := [.nopScalar], term := .ret }
    let bb2 : CfgBlock := { ops := [.writeYmm r0 .ymm256 .zeroExtend256 {}, .vzeroupper], term := .ret }
    let cfg := [bb0, bb1, bb2]
    let masks := [cleanYmmMask, cleanYmmMask, cleanYmmMask]
    checkCfgVZeroUpper masks cfg = true ∧
    naiveLinearScanNoVzuBeforeRet cfg = false := by
  refine ⟨rfl, rfl⟩

/-- Theorem 24 (Counterexample: Missing `vzeroupper` on `unwindResume` Landing Pad):
    When BB1 invokes an internal vector helper (`needsCleanAbi = false`) after BB0 wrote
    `YMM0`, BB2 (`vzeroupper; ret`) is clean, but unwind landing pad BB3 omits `vzeroupper`
    before `unwindResume` — rejected by `checkCfgVZeroUpper` and concretely leaking
    `YMM0[255:128] ≠ 0#128` across the `invoke -> landingpad -> unwindResume` edge! -/
theorem cex_missing_vzeroupper_on_unwind_landingpad_leaks_dirty_ymm :
    let r0 : PRegId := ⟨0, by decide⟩
    let dirtyHi : BitVec 128 := BitVec.ofNat 128 0xDEADBEEF_CAFEBABE
    let bb0 : CfgBlock := { ops := [.writeYmm r0 .ymm256 .zeroExtend256 { ymmHi := dirtyHi }], term := .br 1 }
    let bb1 : CfgBlock := { ops := [.nopScalar], term := .invoke false 2 3 }
    let bb2 : CfgBlock := { ops := [.vzeroupper], term := .ret }
    let bb3 : CfgBlock := { ops := [.nopScalar], term := .unwindResume }
    let cfg := [bb0, bb1, bb2, bb3]
    let d0 := setDirtyMask cleanYmmMask r0 true
    let masks := [cleanYmmMask, d0, d0, d0]
    let stInit : AllocState := { regs := fun _ => {}, stack := fun _ => {}, roPool := fun _ => {} }
    let stAtBb3 := runBlockOps bb1.ops (runBlockOps bb0.ops stInit)
    checkCfgVZeroUpper masks cfg = false ∧
    ((runBlockOps bb3.ops stAtBb3).regs r0).ymmHi = dirtyHi := by
  refine ⟨rfl, rfl⟩

/-! ## Section 4: Inline Stack Probes (`> 4096` B), Cold-Panic Outlining (16-B Align),
       `.eh_frame` `DW_CFA_def_cfa_offset`, and `.debug_loclists` `DW_OP_fbreg` -/

structure StackMach where
  sp   : BitVec 64
  mem  : BitVec 64 → BitVec 64
  regs : PRegId → BitVec 64

inductive ProbeOp where
  | subRsp (bytes : Nat)
  | touchProbe
  deriving DecidableEq, Repr

def probeChunks : Nat → List ProbeOp
  | 0     => []
  | n + 1 => .subRsp 4096 :: .touchProbe :: probeChunks n

def expandFrameProbes (frameBytes : Nat) : List ProbeOp :=
  probeChunks (frameBytes / 4096) ++
    (if frameBytes % 4096 = 0 then [] else [.subRsp (frameBytes % 4096)])

def totalProbeSub : List ProbeOp → Nat
  | []                  => 0
  | .subRsp k :: rest   => k + totalProbeSub rest
  | .touchProbe :: rest => totalProbeSub rest

def checkStackProbeSteps (pageSize : Nat) : List ProbeOp → Bool
  | []                  => true
  | .subRsp k :: rest   => decide (k ≤ pageSize) && checkStackProbeSteps pageSize rest
  | .touchProbe :: rest => checkStackProbeSteps pageSize rest

def execProbeOps (ops : List ProbeOp) (st : StackMach) : StackMach :=
  ops.foldl (fun s op =>
    match op with
    | .subRsp k   => { s with sp := s.sp - BitVec.ofNat 64 k }
    | .touchProbe => s) st

def trackFdeCfaOffsets (ops : List ProbeOp) (cfa0 : Nat) : Nat :=
  ops.foldl (fun cfa op =>
    match op with
    | .subRsp k   => cfa + k
    | .touchProbe => cfa) cfa0

private theorem totalProbeSub_append (xs ys : List ProbeOp) :
    totalProbeSub (xs ++ ys) = totalProbeSub xs + totalProbeSub ys := by
  induction xs with
  | nil => simp [totalProbeSub]
  | cons x xs ih => cases x <;> simp [totalProbeSub, ih, Nat.add_assoc]

private theorem totalProbeSub_chunks (n : Nat) :
    totalProbeSub (probeChunks n) = 4096 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [probeChunks, totalProbeSub, ih]
      rw [Nat.mul_succ, Nat.add_comm]

private theorem checkStackProbeSteps_append (pageSize : Nat) (xs ys : List ProbeOp) :
    checkStackProbeSteps pageSize (xs ++ ys) =
      (checkStackProbeSteps pageSize xs && checkStackProbeSteps pageSize ys) := by
  induction xs with
  | nil => simp [checkStackProbeSteps]
  | cons x xs ih =>
      cases x with
      | subRsp k => simp [checkStackProbeSteps, ih, Bool.and_assoc]
      | touchProbe => simp [checkStackProbeSteps, ih]

private theorem checkStackProbeSteps_chunks (n : Nat) :
    checkStackProbeSteps 4096 (probeChunks n) = true := by
  induction n with
  | zero => rfl
  | succ k ih => simp [probeChunks, checkStackProbeSteps, ih]

private theorem trackFdeCfaOffsets_eq (ops : List ProbeOp) (cfa0 : Nat) :
    trackFdeCfaOffsets ops cfa0 = cfa0 + totalProbeSub ops := by
  induction ops generalizing cfa0 with
  | nil => simp [trackFdeCfaOffsets, totalProbeSub]
  | cons op xs ih =>
      cases op with
      | subRsp k =>
          simp only [trackFdeCfaOffsets, List.foldl_cons, totalProbeSub]
          change trackFdeCfaOffsets xs (cfa0 + k) = cfa0 + (k + totalProbeSub xs)
          rw [ih (cfa0 + k), Nat.add_assoc]
      | touchProbe =>
          simp only [trackFdeCfaOffsets, List.foldl_cons, totalProbeSub]
          change trackFdeCfaOffsets xs cfa0 = cfa0 + totalProbeSub xs
          exact ih cfa0

private theorem execProbeOps_sp_and_mem (ops : List ProbeOp) (st : StackMach) :
    (execProbeOps ops st).sp = st.sp - BitVec.ofNat 64 (totalProbeSub ops) ∧
    (execProbeOps ops st).mem = st.mem := by
  induction ops generalizing st with
  | nil =>
      refine ⟨?_, rfl⟩
      simp [execProbeOps, totalProbeSub]
  | cons op xs ih =>
      cases op with
      | subRsp k =>
          simp only [execProbeOps, List.foldl_cons, totalProbeSub]
          rcases ih { st with sp := st.sp - BitVec.ofNat 64 k } with ⟨hsp, hmem⟩
          refine ⟨?_, hmem⟩
          change (execProbeOps xs { st with sp := st.sp - BitVec.ofNat 64 k }).sp =
            st.sp - BitVec.ofNat 64 (k + totalProbeSub xs)
          rw [hsp, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
          rw [← BitVec.sub_eq_add_neg, ← BitVec.neg_add]
          rw [← BitVec.ofNat_add]
          rw [← BitVec.sub_eq_add_neg, Nat.add_comm k]
      | touchProbe =>
          simp only [execProbeOps, List.foldl_cons, totalProbeSub]
          change (execProbeOps xs st).sp = st.sp - BitVec.ofNat 64 (totalProbeSub xs) ∧
            (execProbeOps xs st).mem = st.mem
          exact ih st

def evalFdeFromMach (cfaOff raOff : Nat) (st : StackMach) : BitVec 64 × BitVec 64 :=
  let cfa := st.sp + BitVec.ofNat 64 cfaOff
  (cfa, st.mem (cfa - BitVec.ofNat 64 raOff))

/-- Theorem 25 (Inline Stack-Probe Expansion + Guard-Page Bound + Per-PC `.eh_frame` CFA):
    For arbitrary `frameBytes : Nat`, `expandFrameProbes` emits `≤ 4096`-byte steps whose
    total SP decrement equals `frameBytes`, AND at every intermediate prefix `pref` (`pref ++ suf`)
    the incremental FDE `DW_CFA_def_cfa_offset` recovers exact caller CFA and `retAddr`. -/
theorem expandPrologueProbes_step_bounded_and_cfa_exact
    (frameBytes savedCfaOff : Nat) (st0 : StackMach) (retAddr : BitVec 64)
    (h_entry_ret : st0.mem (st0.sp + BitVec.ofNat 64 savedCfaOff - 8#64) = retAddr) :
    let ops := expandFrameProbes frameBytes
    checkStackProbeSteps 4096 ops = true ∧
    totalProbeSub ops = frameBytes ∧
    (execProbeOps ops st0).sp = st0.sp - BitVec.ofNat 64 frameBytes ∧
    (∀ pref suf, ops = pref ++ suf →
      let stP := execProbeOps pref st0
      let cfaP := trackFdeCfaOffsets pref savedCfaOff
      evalFdeFromMach cfaP 8 stP = (st0.sp + BitVec.ofNat 64 savedCfaOff, retAddr)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold expandFrameProbes
    rw [checkStackProbeSteps_append, checkStackProbeSteps_chunks, Bool.true_and]
    cases hmod : (frameBytes % 4096 == 0) with
    | true =>
        have h0 : frameBytes % 4096 = 0 := by simpa using hmod
        simp [h0, checkStackProbeSteps]
    | false =>
        have hne : frameBytes % 4096 ≠ 0 := by simpa using hmod
        have hlt : frameBytes % 4096 ≤ 4096 := Nat.le_of_lt (Nat.mod_lt frameBytes (by decide : 0 < 4096))
        simp [hne, checkStackProbeSteps, decide_eq_true hlt]
  · have htot : totalProbeSub (expandFrameProbes frameBytes) = frameBytes := by
      unfold expandFrameProbes
      rw [totalProbeSub_append, totalProbeSub_chunks]
      cases hmod : (frameBytes % 4096 == 0) with
      | true =>
          have h0 : frameBytes % 4096 = 0 := by simpa using hmod
          simp only [h0, ↓reduceIte, totalProbeSub, Nat.add_zero]
          have hdm := Nat.div_add_mod frameBytes 4096
          rw [h0, Nat.add_zero] at hdm
          exact hdm
      | false =>
          have hne : frameBytes % 4096 ≠ 0 := by simpa using hmod
          simp only [hne, ↓reduceIte, totalProbeSub, Nat.add_zero]
          exact Nat.div_add_mod frameBytes 4096
    exact htot
  · have hsp := (execProbeOps_sp_and_mem (expandFrameProbes frameBytes) st0).1
    have htot : totalProbeSub (expandFrameProbes frameBytes) = frameBytes := by
      unfold expandFrameProbes
      rw [totalProbeSub_append, totalProbeSub_chunks]
      cases hmod : (frameBytes % 4096 == 0) with
      | true =>
          have h0 : frameBytes % 4096 = 0 := by simpa using hmod
          simp only [h0, ↓reduceIte, totalProbeSub, Nat.add_zero]
          have hdm := Nat.div_add_mod frameBytes 4096
          rw [h0, Nat.add_zero] at hdm
          exact hdm
      | false =>
          have hne : frameBytes % 4096 ≠ 0 := by simpa using hmod
          simp only [hne, ↓reduceIte, totalProbeSub, Nat.add_zero]
          exact Nat.div_add_mod frameBytes 4096
    rw [htot] at hsp
    exact hsp
  · intro pref suf _
    rcases execProbeOps_sp_and_mem pref st0 with ⟨hsp, hmem⟩
    have hcfa := trackFdeCfaOffsets_eq pref savedCfaOff
    simp only [evalFdeFromMach, hsp, hmem, hcfa]
    have hsum :
        (st0.sp - BitVec.ofNat 64 (totalProbeSub pref)) +
          BitVec.ofNat 64 (savedCfaOff + totalProbeSub pref) =
        st0.sp + BitVec.ofNat 64 savedCfaOff := by
      rw [Nat.add_comm savedCfaOff (totalProbeSub pref), BitVec.ofNat_add]
      rw [← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [hsum, h_entry_ret]

/-- Theorem 26 (Counterexample: Unprobed C-FFI `HUF_decompress` `25,496` B Frame):
    A single `sub rsp, 25496` without page probing violates `checkStackProbeSteps 4096`. -/
theorem cex_unprobed_huf_frame_violates_guard_page_bound :
    checkStackProbeSteps 4096 [.subRsp 25496] = false := by
  decide

def evalDwarfFbreg (cfaOff fbregRelCfa : BitVec 64) (st : StackMach) : BitVec 64 :=
  st.mem ((st.sp + cfaOff) + fbregRelCfa)

/-- Theorem 27 (`.eh_frame` CFA × `.debug_loclists` `DW_OP_fbreg` Duality Invariance):
    Whether computed from pre-shift `(sp, cfaOff)` or post-shift `(sp - d, cfaOff + d)`,
    `DW_OP_fbreg` resolves to the exact physical stack slot `[sp + (cfaOff + fbregRelCfa)]`
    and preserves the value across arbitrary `sp`/`cfa` frame adjustments! -/
theorem fbreg_cfa_duality_invariant_under_sp_shifts
    (st st' : StackMach) (cfaOff fbregRelCfa delta : BitVec 64)
    (h_sp' : st'.sp = st.sp - delta)
    (h_mem' : st'.mem = st.mem) :
    let cfaOff' := cfaOff + delta
    let spDisp := cfaOff + fbregRelCfa
    evalDwarfFbreg cfaOff fbregRelCfa st = st.mem (st.sp + spDisp) ∧
    evalDwarfFbreg cfaOff' fbregRelCfa st' = evalDwarfFbreg cfaOff fbregRelCfa st := by
  refine ⟨?_, ?_⟩
  · simp [evalDwarfFbreg, BitVec.add_assoc]
  · simp only [evalDwarfFbreg, h_sp', h_mem']
    have heq : (st.sp - delta) + (cfaOff + delta) = st.sp + cfaOff := by
      rw [BitVec.add_comm cfaOff delta, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [heq]

/-- Theorem 28 (Counterexample: Confusing Raw `spDisp` with `DW_OP_fbreg` Corrupts Reads):
    If a backend passes raw `[rsp + spDisp]` directly as a CFA-based `DW_OP_fbreg` offset
    when `cfaOff ≠ 0`, `evalDwarfFbreg` reads off-by-`cfaOff` stack bytes! -/
theorem cex_raw_sp_offset_in_fbreg_corrupts_loclists :
    let st : StackMach :=
      { sp := 0x10000#64
      , mem := fun a => a
      , regs := fun _ => 0#64 }
    let cfaOff : BitVec 64 := 6240#64
    let spDisp : BitVec 64 := 8#64
    evalDwarfFbreg cfaOff spDisp st ≠ st.mem (st.sp + spDisp) := by
  decide

def isAlign16 (addr : BitVec 64) : Bool :=
  BitVec.setWidth 4 addr == 0#4

private theorem setWidth4_sub_eq (a b : BitVec 64) :
    BitVec.setWidth 4 (a - b) = BitVec.setWidth 4 a + BitVec.setWidth 4 (-b) := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add a (-b) (by decide : 4 ≤ 64)]

/-- Theorem 29 (Counterexample: Naive `spShift = 8` Cold-Panic Outlined Thunk Breaks SysV `align16`):
    For ANY 16-byte aligned caller `callerSp` (`BitVec.setWidth 4 callerSp = 0#4`),
    entering an outlined thunk via `call` pushes 8 bytes (`callerSp - 8#64`), forcing
    `BitVec.setWidth 4 (callerSp - 8#64) = 8#4 ≠ 0#4` (`isAlign16 = false`) before a nested
    `call panic_bounds_check`! -/
theorem cex_call_outlined_thunk_8byte_shift_breaks_sysv_align16
    (callerSp : BitVec 64) (h_align : isAlign16 callerSp = true) :
    let thunkEntrySp := callerSp - 8#64
    BitVec.setWidth 4 thunkEntrySp = 8#4 ∧ isAlign16 thunkEntrySp = false := by
  have h4 : BitVec.setWidth 4 callerSp = 0#4 := by simpa [isAlign16] using h_align
  have hsub : BitVec.setWidth 4 (callerSp - 8#64) = 8#4 := by
    rw [setWidth4_sub_eq, h4, BitVec.zero_add]
    rfl
  refine ⟨hsub, ?_⟩
  simp [isAlign16, hsub]

structure LsdaEntry where
  callSiteRetPc : BitVec 64
  landingpadPc  : BitVec 64
  deriving DecidableEq, Repr

def lookupLsda (tbl : List LsdaEntry) (retPc : BitVec 64) : Option (BitVec 64) :=
  match tbl.find? (fun e => e.callSiteRetPc == retPc) with
  | some e => some e.landingpadPc
  | none   => none

def thunkEntryState (stCaller : StackMach) (callerSp callThunkRetPc : BitVec 64) : StackMach :=
  { stCaller with
    sp := callerSp - 8#64
    mem := fun a => if a = callerSp - 8#64 then callThunkRetPc else stCaller.mem a }

def thunkAlignedState (stCaller : StackMach) (callerSp callThunkRetPc : BitVec 64) : StackMach :=
  let stEntry := thunkEntryState stCaller callerSp callThunkRetPc
  { stEntry with
    sp := stEntry.sp - 8#64
    mem := fun a => if a = callerSp - 16#64 then 0#64 else stEntry.mem a }

/-- Theorem 30 (16-Byte-Aligned Throwing Outlined Thunk + FDE/LSDA + `DW_OP_fbreg` Consistency):
    Allocating `sub rsp, 8` inside a throwing cold-panic thunk (`spShift = 16#64`,
    `thunkFdeCfaOff = 16`):
    1. Restores exact `isAlign16 thunkSp = true` (`BitVec.setWidth 4 (callerSp - 16#64) = 0#4`)
       for arbitrary `callerSp` before calling `panic_bounds_check`;
    2. Shifted caller stack reads `[thunkSp + (off + 16#64)]` agree with `[callerSp + off]`
       whenever `off + 16#64 ∉ {0#64, 8#64}` (disjoint from both padding slot and return slot);
    3. Unwinding through the thunk's FDE (`CFA = thunkSp + 16`, `RA = [CFA - 8]`) restores
       `(callerSp, callThunkRetPc)`, matching the caller's LSDA landing pad `lpPc` and the
       caller's `DW_OP_fbreg` `DropGuard` slot `[callerSp + guardOff]`. -/
theorem aligned_throwing_outlined_thunk_16byte_shift_and_lsda_unwind_consistent
    (callerSp callThunkRetPc lpPc guardRelCfa callerCfaOff guardVal : BitVec 64)
    (lsda : List LsdaEntry)
    (stCaller : StackMach)
    (h_align : isAlign16 callerSp = true)
    (h_guard_mem : stCaller.mem ((callerSp + callerCfaOff) + guardRelCfa) = guardVal)
    (h_lsda : lookupLsda lsda callThunkRetPc = some lpPc)
    (h_guard_safe : (callerCfaOff + guardRelCfa) + 16#64 ≠ 0#64 ∧
                    (callerCfaOff + guardRelCfa) + 16#64 ≠ 8#64) :
    let stThunk := thunkAlignedState stCaller callerSp callThunkRetPc
    isAlign16 stThunk.sp = true ∧
    stThunk.sp = callerSp - 16#64 ∧
    stThunk.mem (stThunk.sp + ((callerCfaOff + guardRelCfa) + 16#64)) = guardVal ∧
    evalFdeFromMach 16 8 stThunk = (callerSp, callThunkRetPc) ∧
    (let (uwSp, uwPc) := evalFdeFromMach 16 8 stThunk
     lookupLsda lsda uwPc = some lpPc ∧
     evalDwarfFbreg callerCfaOff guardRelCfa { stThunk with sp := uwSp } = guardVal) := by
  have h_thunk_sp : (callerSp - 8#64) - 8#64 = callerSp - 16#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [show (-8#64 : BitVec 64) + -8#64 = -16#64 from rfl]
    rw [← BitVec.sub_eq_add_neg]
  have h4 : BitVec.setWidth 4 callerSp = 0#4 := by simpa [isAlign16] using h_align
  have h_al16 : isAlign16 (callerSp - 16#64) = true := by
    rw [isAlign16, setWidth4_sub_eq, h4, BitVec.zero_add]
    rfl
  have h_sp_16 : (thunkAlignedState stCaller callerSp callThunkRetPc).sp = callerSp - 16#64 := by
    change (callerSp - 8#64) - 8#64 = callerSp - 16#64
    exact h_thunk_sp
  have h_addr_guard :
      (callerSp - 16#64) + ((callerCfaOff + guardRelCfa) + 16#64) =
        (callerSp + callerCfaOff) + guardRelCfa := by
    rw [BitVec.add_comm (callerCfaOff + guardRelCfa) 16#64, ← BitVec.add_assoc]
    rw [BitVec.sub_add_cancel, BitVec.add_assoc]
  have h_ne_pad : (callerSp + callerCfaOff) + guardRelCfa ≠ callerSp - 16#64 := by
    intro heq
    apply h_guard_safe.1
    have h1 := congrArg (· + 16#64) heq
    rw [BitVec.sub_add_cancel] at h1
    rw [BitVec.add_assoc callerSp callerCfaOff guardRelCfa,
        BitVec.add_assoc callerSp (callerCfaOff + guardRelCfa) 16#64,
        BitVec.add_comm callerSp ((callerCfaOff + guardRelCfa) + 16#64)] at h1
    have h2 := congrArg (· - callerSp) h1
    rw [BitVec.add_sub_cancel, BitVec.sub_self] at h2
    exact h2
  have h_ne_ret : (callerSp + callerCfaOff) + guardRelCfa ≠ callerSp - 8#64 := by
    intro heq
    apply h_guard_safe.2
    have h1 := congrArg (· + 16#64) heq
    rw [BitVec.sub_eq_add_neg callerSp 8#64, BitVec.add_assoc callerSp (-8#64) 16#64,
        show (-8#64 : BitVec 64) + 16#64 = 8#64 from rfl] at h1
    rw [BitVec.add_assoc callerSp callerCfaOff guardRelCfa,
        BitVec.add_assoc callerSp (callerCfaOff + guardRelCfa) 16#64,
        BitVec.add_comm callerSp ((callerCfaOff + guardRelCfa) + 16#64)] at h1
    have h2 := congrArg (· - callerSp) h1
    rw [BitVec.add_sub_cancel, BitVec.add_comm callerSp 8#64, BitVec.add_sub_cancel] at h2
    exact h2
  have h_ra_ne_pad : callerSp - 8#64 ≠ callerSp - 16#64 := by
    intro heq
    have h1 := congrArg (· + 16#64) heq
    rw [BitVec.sub_add_cancel, BitVec.sub_eq_add_neg callerSp 8#64, BitVec.add_assoc callerSp (-8#64) 16#64] at h1
    rw [show (-8#64 : BitVec 64) + 16#64 = 8#64 from rfl] at h1
    have h2 := congrArg (· - callerSp) h1
    rw [BitVec.add_comm callerSp 8#64, BitVec.add_sub_cancel, BitVec.sub_self] at h2
    exact (by decide : (8#64 : BitVec 64) ≠ 0#64) h2
  have h_fde :
      evalFdeFromMach 16 8 (thunkAlignedState stCaller callerSp callThunkRetPc) = (callerSp, callThunkRetPc) := by
    simp only [evalFdeFromMach, thunkAlignedState, thunkEntryState, h_thunk_sp]
    have h16 : (callerSp - 16#64) + BitVec.ofNat 64 16 = callerSp := by
      change (callerSp - 16#64) + 16#64 = callerSp
      exact BitVec.sub_add_cancel callerSp 16#64
    rw [h16]
    simp [h_ra_ne_pad]
  refine ⟨?_, h_sp_16, ?_, h_fde, ?_⟩
  · simp only [h_sp_16, h_al16]
  · rw [h_sp_16, h_addr_guard]
    simp only [thunkAlignedState, thunkEntryState, h_ne_pad, h_ne_ret, ↓reduceIte]
    exact h_guard_mem
  · simp only [h_fde]
    refine ⟨h_lsda, ?_⟩
    simp only [evalDwarfFbreg, thunkAlignedState, thunkEntryState, h_ne_pad, h_ne_ret, ↓reduceIte]
    exact h_guard_mem

/-! ## Section 5: End-to-End 4-Stage Backend Seam Composition & Non-Vacuity Witness -/

structure CoupledFnSpec where
  frameBytes      : Nat
  savedCfaOff     : Nat
  entryMasks      : List DirtyYmmMask
  cfg             : List CfgBlock
  lsda            : List LsdaEntry
  thunkSpShift    : Nat
  thunkFdeCfaOff  : Nat

def checkCoupledBackendSeam (fn : CoupledFnSpec) : Bool :=
  checkStackProbeSteps 4096 (expandFrameProbes fn.frameBytes) &&
  checkCfgVZeroUpper fn.entryMasks fn.cfg &&
  (fn.thunkSpShift == 16) &&
  (fn.thunkFdeCfaOff == 16)

/-- Theorem 31 (End-to-End 4-Stage `MiniMach` Backend Seam Soundness):
    If `checkCoupledBackendSeam fn = true`, then simultaneously:
    1. Every inline stack-probe chunk is bounded by `4096` B and every intermediate prologue PC
       recovers exact caller CFA & `retAddr`;
    2. Every CFG normal return, tail call, ABI call, and `unwindResume` path keeps all 16
       `YMM[255:128]` lanes zeroed;
    3. The cold-panic outlined thunk maintains `isAlign16 thunkSp = true` (`spShift = 16`)
       and unwinds via FDE (`CFA = rsp + 16`) + LSDA to the caller's `DW_OP_fbreg` `Drop` guard! -/
theorem coupled_backend_seam_pipeline_sound
    (fn : CoupledFnSpec) (h_ok : checkCoupledBackendSeam fn = true)
    (stFrame0 : StackMach) (retAddr : BitVec 64)
    (h_ret : stFrame0.mem (stFrame0.sp + BitVec.ofNat 64 fn.savedCfaOff - 8#64) = retAddr)
    (steps : Nat) (pcK : Nat) (stCfg0 stCfgK : AllocState) (m0 : DirtyYmmMask)
    (hm0 : fn.entryMasks[0]? = some m0) (hag0 : MaskAgree stCfg0 m0)
    (h_reach : CfgReach fn.cfg steps (0, stCfg0) (pcK, stCfgK))
    (callerSp callRetPc lpPc guardRelCfa callerCfaOff guardVal : BitVec 64)
    (h_align : isAlign16 callerSp = true)
    (h_guard_mem : stFrame0.mem ((callerSp + callerCfaOff) + guardRelCfa) = guardVal)
    (h_lsda : lookupLsda fn.lsda callRetPc = some lpPc)
    (h_guard_safe : (callerCfaOff + guardRelCfa) + 16#64 ≠ 0#64 ∧
                    (callerCfaOff + guardRelCfa) + 16#64 ≠ 8#64) :
    (checkStackProbeSteps 4096 (expandFrameProbes fn.frameBytes) = true) ∧
    (∀ pref suf, expandFrameProbes fn.frameBytes = pref ++ suf →
      evalFdeFromMach (trackFdeCfaOffsets pref fn.savedCfaOff) 8 (execProbeOps pref stFrame0) =
        (stFrame0.sp + BitVec.ofNat 64 fn.savedCfaOff, retAddr)) ∧
    AtAbiBoundary fn.cfg pcK stCfgK ∧
    (let stThunk := thunkAlignedState stFrame0 callerSp callRetPc
     isAlign16 stThunk.sp = true ∧
     (let (uwSp, uwPc) := evalFdeFromMach 16 8 stThunk
      lookupLsda fn.lsda uwPc = some lpPc ∧
      evalDwarfFbreg callerCfaOff guardRelCfa { stThunk with sp := uwSp } = guardVal)) := by
  simp only [checkCoupledBackendSeam, Bool.and_eq_true, beq_iff_eq] at h_ok
  rcases h_ok with ⟨⟨⟨h_prb, h_vzu⟩, _⟩, _⟩
  have h1 := expandPrologueProbes_step_bounded_and_cfa_exact fn.frameBytes fn.savedCfaOff stFrame0 retAddr h_ret
  have h2 := checkCfgVZeroUpper_trace_sound fn.entryMasks fn.cfg h_vzu steps 0 pcK stCfg0 stCfgK m0 hm0 hag0 h_reach
  have h3 := aligned_throwing_outlined_thunk_16byte_shift_and_lsda_unwind_consistent
    callerSp callRetPc lpPc guardRelCfa callerCfaOff guardVal fn.lsda stFrame0
    h_align h_guard_mem h_lsda h_guard_safe
  exact ⟨h_prb, h1.2.2.2, h2, ⟨h3.1, h3.2.2.2.2⟩⟩

/-- Theorem 32 (Concrete Non-Vacuity Canary):
    A coupled AVX2 function with `6,208`-byte probed spill frame (`sub $4096; probe; sub $2112`),
    call across live `YMM` + `vzeroupper` before `call` + `Drop` `landingpad` + 16-byte-aligned
    cold-panic thunk passes `checkCoupledBackendSeam = true`! -/
theorem witness_coupled_avx2_spill_probe_unwind_verified :
    let r0 : PRegId := ⟨0, by decide⟩
    let bb0 : CfgBlock := { ops := [.writeYmm r0 .ymm256 .zeroExtend256 {}, .vzeroupper], term := .invoke true 1 2 }
    let bb1 : CfgBlock := { ops := [.writeYmm r0 .ymm256 .zeroExtend256 {}, .vzeroupper], term := .ret }
    let bb2 : CfgBlock := { ops := [.nopScalar], term := .unwindResume }
    let fn : CoupledFnSpec :=
      { frameBytes := 6208
      , savedCfaOff := 32
      , entryMasks := [cleanYmmMask, cleanYmmMask, cleanYmmMask]
      , cfg := [bb0, bb1, bb2]
      , lsda := [{ callSiteRetPc := 0x401080#64, landingpadPc := 0x401120#64 }]
      , thunkSpShift := 16
      , thunkFdeCfaOff := 16 }
    checkCoupledBackendSeam fn = true ∧
    expandFrameProbes 6208 = [.subRsp 4096, .touchProbe, .subRsp 2112] := by
  refine ⟨rfl, rfl⟩

end VrustcProbe.BackendSeam

-- Mandatory Axiom Audit Across All 32 Public Theorems (`0 sorryAx`, `0 ofReduceBool`, `0 Classical.choice`)
#print axioms VrustcProbe.BackendSeam.movl_zeroes_upper32_bv64
#print axioms VrustcProbe.BackendSeam.movb_lo8_hi8_commute_and_preserve_upper_bv64
#print axioms VrustcProbe.BackendSeam.movw_ax_preserves_upper48_bv64
#print axioms VrustcProbe.BackendSeam.sse128_preserves_ymmHi_bv256
#print axioms VrustcProbe.BackendSeam.vex128_zeroes_ymmHi_bv256
#print axioms VrustcProbe.BackendSeam.applyReg256Write_preserves_untouched
#print axioms VrustcProbe.BackendSeam.applyReg256Write_reads_written
#print axioms VrustcProbe.BackendSeam.embedMiniMachLaneView_exact
#print axioms VrustcProbe.BackendSeam.writePhysLoc_frame
#print axioms VrustcProbe.BackendSeam.stepMoveRepaired_sound
#print axioms VrustcProbe.BackendSeam.stepSpillAndReload_preserves_refinement
#print axioms VrustcProbe.BackendSeam.liveRangeSplit_coallocated_lanes_sound
#print axioms VrustcProbe.BackendSeam.stepRematSafe_sound
#print axioms VrustcProbe.BackendSeam.stepOriginMove_sound
#print axioms VrustcProbe.BackendSeam.moveAndScratchResolver_repaired_cycle_sound
#print axioms VrustcProbe.BackendSeam.cex_naive_32bit_remat_clobbers_coallocated_hi32
#print axioms VrustcProbe.BackendSeam.cex_vex128_reload_clobbers_coallocated_ymmHi
#print axioms VrustcProbe.BackendSeam.cex_borrowed_scratch_missing_else_and_narrow_save_unsound
#print axioms VrustcProbe.BackendSeam.vzeroupper_clears_ymmHi_and_preserves_gpr_xmm128
#print axioms VrustcProbe.BackendSeam.vex128_clears_single_reg_leaves_other_ymm_dirty
#print axioms VrustcProbe.BackendSeam.checkCfgVZeroUpper_step_sound
#print axioms VrustcProbe.BackendSeam.checkCfgVZeroUpper_trace_sound
#print axioms VrustcProbe.BackendSeam.memchr_multi_exit_cfg_accepted_without_early_vzeroupper
#print axioms VrustcProbe.BackendSeam.cex_missing_vzeroupper_on_unwind_landingpad_leaks_dirty_ymm
#print axioms VrustcProbe.BackendSeam.expandPrologueProbes_step_bounded_and_cfa_exact
#print axioms VrustcProbe.BackendSeam.cex_unprobed_huf_frame_violates_guard_page_bound
#print axioms VrustcProbe.BackendSeam.fbreg_cfa_duality_invariant_under_sp_shifts
#print axioms VrustcProbe.BackendSeam.cex_raw_sp_offset_in_fbreg_corrupts_loclists
#print axioms VrustcProbe.BackendSeam.cex_call_outlined_thunk_8byte_shift_breaks_sysv_align16
#print axioms VrustcProbe.BackendSeam.aligned_throwing_outlined_thunk_16byte_shift_and_lsda_unwind_consistent
#print axioms VrustcProbe.BackendSeam.coupled_backend_seam_pipeline_sound
#print axioms VrustcProbe.BackendSeam.witness_coupled_avx2_spill_probe_unwind_verified
