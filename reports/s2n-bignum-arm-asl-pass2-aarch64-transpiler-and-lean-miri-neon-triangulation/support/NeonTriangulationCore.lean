-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import IntrinsicAarch64Ext
import VendorArm64Ref.Machine
import WordArm64Pass2Correspondence

/-!
# `NeonTriangulationCore`

Core definitions, `.o` machine-word fixtures, closed fetch-decode combinators,
4 MIR-vs-NEON UB & cross-ISA AES asymmetry theorems, and the first 19 universal
3-way Pass-2 triangulation theorems (`p01..p15`) for `NeonTriangulation24`.
-/

namespace NeonTriangulation24

open VendorArm64Ref WordArm64

/-! ## Section 1: `LeanMiri` Portable `simd_*` UB Model & `IntrinsicAarch64Ext` Bridge -/

inductive SimdUb where
  | shiftOverflow (count : Nat)
  | intrinsicUnsupported (name : String)
  deriving DecidableEq, Repr

def miriLaneShl8 (x cnt : BitVec 8) : Except SimdUb (BitVec 8) :=
  if cnt.toNat >= 8 then .error (.shiftOverflow cnt.toNat)
  else .ok (x <<< cnt.toNat)

def miriLaneAshr32 (x cnt : BitVec 32) : Except SimdUb (BitVec 32) :=
  if cnt.toNat >= 32 then .error (.shiftOverflow cnt.toNat)
  else .ok (BitVec.sshiftRight x cnt.toNat)

def miriSimdShlBytes128 (a cnt : BitVec 128) : Except SimdUb (BitVec 128) :=
  let step (i : Nat) : Except SimdUb (BitVec 8) := miriLaneShl8 (getByte128 a i) (getByte128 cnt i)
  match step 0, step 1, step 2, step 3, step 4, step 5, step 6, step 7,
        step 8, step 9, step 10, step 11, step 12, step 13, step 14, step 15 with
  | .ok b0, .ok b1, .ok b2, .ok b3, .ok b4, .ok b5, .ok b6, .ok b7,
    .ok b8, .ok b9, .ok b10, .ok b11, .ok b12, .ok b13, .ok b14, .ok b15 =>
    .ok (((b15 ++ (b14 ++ (b13 ++ b12))) ++ (b11 ++ (b10 ++ (b9 ++ b8)))) ++
         ((b7  ++ (b6  ++ (b5  ++ b4)))  ++ (b3  ++ (b2  ++ (b1 ++ b0)))))
  | .error e, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, .error e, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, .error e, _, _, _, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, .error e, _, _, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, .error e, _, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, .error e, _, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, .error e, _, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, .error e, _, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, .error e, _, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, .error e, _, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, .error e, _, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, _, .error e, _, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, _, _, .error e, _, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, _, _, _, .error e, _, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, .error e, _ => .error e
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .error e => .error e

def miriSimdAshrWords128 (a cnt : BitVec 128) : Except SimdUb (BitVec 128) :=
  match miriLaneAshr32 (getWord128 a 0) (getWord128 cnt 0) with
  | .error e => .error e
  | .ok w0 =>
    match miriLaneAshr32 (getWord128 a 1) (getWord128 cnt 1) with
    | .error e => .error e
    | .ok w1 =>
      match miriLaneAshr32 (getWord128 a 2) (getWord128 cnt 2) with
      | .error e => .error e
      | .ok w2 =>
        match miriLaneAshr32 (getWord128 a 3) (getWord128 cnt 3) with
        | .error e => .error e
        | .ok w3 => .ok ((w3 ++ w2) ++ (w1 ++ w0))

def liftExt128 (name : String) (args : List IntrinsicAarch64Ext.ExtVal)
    : Except SimdUb (BitVec 128) :=
  match IntrinsicAarch64Ext.evalAarch64Ext name args with
  | some (.ok (.b128 r)) => .ok r
  | _ => .error (.intrinsicUnsupported name)

/-! ## Section 2: Exact ELF64 `.o` Machine Words Emitted by `rustc -O3` -/

def p01Words  : List (BitVec 32) := [0x4e208420#32, 0xd65f03c0#32] -- add v0.16b, v1.16b, v0.16b ; ret
def p02Words  : List (BitVec 32) := [0x6e218400#32, 0xd65f03c0#32] -- sub v0.16b, v0.16b, v1.16b ; ret
def p03Words  : List (BitVec 32) := [0x4e201c20#32, 0xd65f03c0#32] -- and v0.16b, v1.16b, v0.16b ; ret
def p04Words  : List (BitVec 32) := [0x4ea01c20#32, 0xd65f03c0#32] -- orr v0.16b, v1.16b, v0.16b ; ret
def p05Words  : List (BitVec 32) := [0x6e201c20#32, 0xd65f03c0#32] -- eor v0.16b, v1.16b, v0.16b ; ret
def p06Words  : List (BitVec 32) := [0x6e218c00#32, 0xd65f03c0#32] -- cmeq v0.16b, v0.16b, v1.16b ; ret
def p07Words  : List (BitVec 32) := [0x6e213400#32, 0xd65f03c0#32] -- cmhi v0.16b, v0.16b, v1.16b ; ret
def p08Words  : List (BitVec 32) := [0x4e203420#32, 0xd65f03c0#32] -- cmgt v0.16b, v1.16b, v0.16b ; ret
def p09Words  : List (BitVec 32) := [0x6e210c00#32, 0xd65f03c0#32] -- uqadd v0.16b, v0.16b, v1.16b ; ret
def p10Words  : List (BitVec 32) := [0x6e212c00#32, 0xd65f03c0#32] -- uqsub v0.16b, v0.16b, v1.16b ; ret
def p11Words  : List (BitVec 32) := [0x6e214400#32, 0xd65f03c0#32] -- ushl v0.16b, v0.16b, v1.16b ; ret
def p11bWords : List (BitVec 32) := [0x4e214400#32, 0xd65f03c0#32] -- sshl v0.16b, v0.16b, v1.16b ; ret
def p12Words  : List (BitVec 32) := [0x4f275400#32, 0xd65f03c0#32] -- shl v0.4s, v0.4s, #7 ; ret
def p12bWords : List (BitVec 32) := [0x6f390400#32, 0xd65f03c0#32] -- ushr v0.4s, v0.4s, #7 ; ret
def p12cWords : List (BitVec 32) := [0x6f00e400#32, 0xd65f03c0#32] -- movi v0.2d, #0 ; ret
def p12dWords : List (BitVec 32) := [0x4ea0a800#32, 0xd65f03c0#32] -- cmlt v0.4s, v0.4s, #0 ; ret
def p13Words  : List (BitVec 32) := [0x4e010000#32, 0xd65f03c0#32] -- tbl v0.16b, {v0.16b}, v1.16b ; ret
def p14Words  : List (BitVec 32) := [0x4e21bc00#32, 0xd65f03c0#32] -- addp v0.16b, v0.16b, v1.16b ; ret
def p15Words  : List (BitVec 32) := [0x6e202800#32, 0xd65f03c0#32] -- uaddlp v0.8h, v0.16b ; ret
def p16Words  : List (BitVec 32) := [0x6e303800#32, 0x1e260000#32, 0xd65f03c0#32] -- uaddlv h0, v0.16b ; fmov w0, s0 ; ret
def p17Words  : List (BitVec 32) := [0x6e30a800#32, 0x1e260000#32, 0xd65f03c0#32] -- umaxv b0, v0.16b ; fmov w0, s0 ; ret
def p17bWords : List (BitVec 32) := [0x6e31a800#32, 0x1e260000#32, 0xd65f03c0#32] -- uminv b0, v0.16b ; fmov w0, s0 ; ret
def p18Words  : List (BitVec 32) := [0x4e200800#32, 0xd65f03c0#32] -- rev64 v0.16b, v0.16b ; ret
def p18bWords : List (BitVec 32) := [0x0e200800#32, 0xd65f03c0#32] -- rev64 v0.8b, v0.8b ; ret
def p19Words  : List (BitVec 32) := [0x6e012800#32, 0xd65f03c0#32] -- ext v0.16b, v0.16b, v1.16b, #5 ; ret
def p20Words  : List (BitVec 32) := [0x6e621c20#32, 0xd65f03c0#32] -- bsl v0.16b, v1.16b, v2.16b ; ret
def p21Words  : List (BitVec 32) := [0x4e205800#32, 0xd65f03c0#32] -- cnt v0.16b, v0.16b ; ret
def p22Words  : List (BitVec 32) := [0x0e21e000#32, 0xd65f03c0#32] -- pmull v0.8h, v0.8b, v1.8b ; ret
def p22bWords : List (BitVec 32) := [
  0x9e670020#32, -- fmov d0, x1
  0x9e670001#32, -- fmov d1, x0
  0x0ee0e020#32, -- pmull v0.1q, v1.1d, v0.1d
  0x4e183c01#32, -- mov x1, v0.d[1]
  0x9e660000#32, -- fmov x0, d0
  0xd65f03c0#32  -- ret
]
def p23Words  : List (BitVec 32) := [0x4e284820#32, 0xd65f03c0#32] -- aese v0.16b, v1.16b ; ret
def p23bWords : List (BitVec 32) := [0x4e286800#32, 0xd65f03c0#32] -- aesmc v0.16b, v0.16b ; ret
def p24Words  : List (BitVec 32) := [0xce628020#32, 0xd65f03c0#32] -- sha512h q0, q1, v2.2d ; ret
def p24bWords : List (BitVec 32) := [0xcec08020#32, 0xd65f03c0#32] -- sha512su0 v0.2d, v1.2d ; ret
def p25Words  : List (BitVec 32) := [0x9ac15c00#32, 0xd65f03c0#32] -- crc32cx w0, w0, x1 ; ret

def mkCallVec (a b c : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) : MachineState :=
  { pc   := 0#64
    sp   := sp
    xreg := fun r => if r == reg30 then lr else 0#64
    vreg := fun v => if v == 0#5 then a else if v == 1#5 then b else if v == 2#5 then c else 0#128
    mem  := mem }

def mkCallGp (x0 x1 sp lr : BitVec 64) (mem : ByteMem) : MachineState :=
  { pc   := 0#64
    sp   := sp
    xreg := fun r => if r == 0#5 then x0 else if r == 1#5 then x1 else if r == reg30 then lr else 0#64
    mem  := mem }

/-- Closed `(code, pc)` fetch-and-decode projection, decoupling closed `.o` word
    decoding from symbolic `MachineState` execution so every universal theorem
    reduces in `< 1 ms` without `isDefEq` delta-backtracking over `s.pc`. -/
def fetchDecodeAt (code : CodeMap) (pc : BitVec 64) : Except ArmFault Instr :=
  match fetchWord32 code pc with
  | .error f => .error f
  | .ok w    => decodeWord32 w

theorem execStep_of_fetchDecode {code : CodeMap} {excl lse2 : Bool} {s : MachineState}
    {pc : BitVec 64} {ins : Instr}
    (hStop : (s.halted || s.fault.isSome) = false)
    (hPc : s.pc = pc)
    (hFD : fetchDecodeAt code pc = .ok ins) :
    execStep code excl lse2 s = execInstr excl lse2 ins s := by
  unfold execStep
  rw [hStop, hPc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold fetchDecodeAt at hFD
  cases hf : fetchWord32 code pc with
  | error f => rw [hf] at hFD; cases hFD
  | ok w =>
    dsimp only []
    rw [hf] at hFD; dsimp only [] at hFD
    rw [hFD]

theorem execSteps2_eq {words : List (BitVec 32)} {ins0 ins1 : Instr} {s0 : MachineState}
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl) :
    execStepsN (loadWordsAt 0#64 words) false false 2 s0 =
    execInstr false false ins1 (execInstr false false ins0 s0) := by
  change execStep _ false false (execStep _ false false s0) = _
  rw [execStep_of_fetchDecode hStop0 hPc0 hFD0]
  rw [execStep_of_fetchDecode hStop1 hPc1 hFD1]

theorem execSteps3_eq {words : List (BitVec 32)} {ins0 ins1 ins2 : Instr} {s0 : MachineState}
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hFD2 : fetchDecodeAt (loadWordsAt 0#64 words) 8#64 = .ok ins2)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hStop2 : (let s2 := execInstr false false ins1 (execInstr false false ins0 s0); s2.halted || s2.fault.isSome) = false := by rfl)
    (hPc2 : (execInstr false false ins1 (execInstr false false ins0 s0)).pc = 8#64 := by rfl) :
    execStepsN (loadWordsAt 0#64 words) false false 3 s0 =
    execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)) := by
  change execStep _ false false (execStep _ false false (execStep _ false false s0)) = _
  rw [execStep_of_fetchDecode hStop0 hPc0 hFD0]
  rw [execStep_of_fetchDecode hStop1 hPc1 hFD1]
  rw [execStep_of_fetchDecode hStop2 hPc2 hFD2]

theorem execSteps6_eq {words : List (BitVec 32)} {ins0 ins1 ins2 ins3 ins4 ins5 : Instr} {s0 : MachineState}
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64  = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64  = .ok ins1)
    (hFD2 : fetchDecodeAt (loadWordsAt 0#64 words) 8#64  = .ok ins2)
    (hFD3 : fetchDecodeAt (loadWordsAt 0#64 words) 12#64 = .ok ins3)
    (hFD4 : fetchDecodeAt (loadWordsAt 0#64 words) 16#64 = .ok ins4)
    (hFD5 : fetchDecodeAt (loadWordsAt 0#64 words) 20#64 = .ok ins5)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hStop2 : (let s2 := execInstr false false ins1 (execInstr false false ins0 s0); s2.halted || s2.fault.isSome) = false := by rfl)
    (hPc2 : (execInstr false false ins1 (execInstr false false ins0 s0)).pc = 8#64 := by rfl)
    (hStop3 : (let s3 := execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)); s3.halted || s3.fault.isSome) = false := by rfl)
    (hPc3 : (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))).pc = 12#64 := by rfl)
    (hStop4 : (let s4 := execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))); s4.halted || s4.fault.isSome) = false := by rfl)
    (hPc4 : (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))).pc = 16#64 := by rfl)
    (hStop5 : (let s5 := execInstr false false ins4 (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))); s5.halted || s5.fault.isSome) = false := by rfl)
    (hPc5 : (execInstr false false ins4 (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))))).pc = 20#64 := by rfl) :
    execStepsN (loadWordsAt 0#64 words) false false 6 s0 =
    execInstr false false ins5 (execInstr false false ins4 (execInstr false false ins3
      (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))))) := by
  change execStep _ false false (execStep _ false false (execStep _ false false
           (execStep _ false false (execStep _ false false (execStep _ false false s0))))) = _
  rw [execStep_of_fetchDecode hStop0 hPc0 hFD0]
  rw [execStep_of_fetchDecode hStop1 hPc1 hFD1]
  rw [execStep_of_fetchDecode hStop2 hPc2 hFD2]
  rw [execStep_of_fetchDecode hStop3 hPc3 hFD3]
  rw [execStep_of_fetchDecode hStop4 hPc4 hFD4]
  rw [execStep_of_fetchDecode hStop5 hPc5 hFD5]

/-! ## Section 3: Four Constructive UB & Cross-ISA Crypto Asymmetry Theorems -/

/-- **Asymmetry Theorem 1 (`unguarded_miri_simd_shl_ub_vs_neon_ushl_bidir`):**
    Raw portable MIR `simd_shl` triggers immediate UB on negative shift byte
    `0xfe` (`-2`, unsigned `254 >= 8`) and on oversize shift byte `0x08` (`8 >= 8`),
    whereas `vshlq_u8` (`p11Words`, `ushl v0.16b`) and `IntrinsicAarch64Ext`
    succeed without UB, shifting right to `0x21` and saturating left to `0x00`. -/
theorem unguarded_miri_simd_shl_ub_vs_neon_ushl_bidir :
    let a   : BitVec 128 := 0x0000000000000000_0000000000008484#128
    let cnt : BitVec 128 := 0x0000000000000000_00000000000008fe#128
    let s1  := execStepsN (loadWordsAt 0#64 p11Words) false false 2 (mkCallVec a cnt 0#128 0x80000#64 0x90000#64 (fun _ => 0#8))
    miriSimdShlBytes128 a cnt = .error (.shiftOverflow 254) ∧
    liftExt128 "llvm.aarch64.neon.ushl.v16i8" [.b128 a, .b128 cnt] = .ok 0x0000000000000000_0000000000000021#128 ∧
    s1.fault = none ∧
    s1.vreg 0#5 = 0x0000000000000000_0000000000000021#128 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sign-mask / arithmetic shift equivalence underlying LLVM's lowering of
    `vshrq_n_s32::<32>(a)` to `cmlt v0.4s, v0.4s, #0` (`0x4ea0a800`). -/
theorem cmltZero32_eq_sshiftRight31 (x : BitVec 32) :
    (if x.msb then 0xffffffff#32 else 0#32) = BitVec.sshiftRight x 31 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight x 31 i]
  have hmsb : x.getLsbD 31 = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
  match i with
  | 0  => rw [hmsb]; cases x.msb <;> rfl
  | 1  => cases x.msb <;> rfl | 2  => cases x.msb <;> rfl | 3  => cases x.msb <;> rfl
  | 4  => cases x.msb <;> rfl | 5  => cases x.msb <;> rfl | 6  => cases x.msb <;> rfl
  | 7  => cases x.msb <;> rfl | 8  => cases x.msb <;> rfl | 9  => cases x.msb <;> rfl
  | 10 => cases x.msb <;> rfl | 11 => cases x.msb <;> rfl | 12 => cases x.msb <;> rfl
  | 13 => cases x.msb <;> rfl | 14 => cases x.msb <;> rfl | 15 => cases x.msb <;> rfl
  | 16 => cases x.msb <;> rfl | 17 => cases x.msb <;> rfl | 18 => cases x.msb <;> rfl
  | 19 => cases x.msb <;> rfl | 20 => cases x.msb <;> rfl | 21 => cases x.msb <;> rfl
  | 22 => cases x.msb <;> rfl | 23 => cases x.msb <;> rfl | 24 => cases x.msb <;> rfl
  | 25 => cases x.msb <;> rfl | 26 => cases x.msb <;> rfl | 27 => cases x.msb <;> rfl
  | 28 => cases x.msb <;> rfl | 29 => cases x.msb <;> rfl | 30 => cases x.msb <;> rfl
  | 31 => cases x.msb <;> rfl
  | n + 32 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 n) hi)

theorem execSteps2_vreg0_eq {words : List (BitVec 32)} {ins0 ins1 : Instr}
    {s0 : MachineState} {v : BitVec 128}
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hReg : (execInstr false false ins1 (execInstr false false ins0 s0)).vreg 0#5 = v)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl) :
    (execStepsN (loadWordsAt 0#64 words) false false 2 s0).vreg 0#5 = v :=
  (congrArg (fun st => st.vreg 0#5) (execSteps2_eq hFD0 hFD1 hStop0 hPc0 hStop1 hPc1)).trans hReg

/-- **Asymmetry Theorem 2 (`unguarded_miri_simd_shr_32_ub_vs_rustc_cmlt_zero`):**
    Raw portable MIR `simd_shr(a, splat(32))` triggers UB (`.shiftOverflow 32`),
    whereas `stdarch` clamps `vshrq_n_s32::<32>` to `simd_shr(a, splat(31))` and
    `rustc -O3` emits `cmlt v0.4s, v0.4s, #0` (`p12dWords`), agreeing across all
    `2^128` input vectors! -/
theorem unguarded_miri_simd_shr_32_ub_vs_rustc_cmlt_zero (a : BitVec 128) :
    let splat32 : BitVec 128 := 0x00000020_00000020_00000020_00000020#128
    let splat31 : BitVec 128 := 0x0000001f_0000001f_0000001f_0000001f#128
    let s1 := execStepsN (loadWordsAt 0#64 p12dWords) false false 2 (mkCallVec a 0#128 0#128 0x80000#64 0x90000#64 (fun _ => 0#8))
    miriSimdAshrWords128 a splat32 = .error (.shiftOverflow 32) ∧
    miriSimdAshrWords128 a splat31 = .ok (s1.vreg 0#5) := by
  refine ⟨rfl, ?_⟩
  have hVreg : (execStepsN (loadWordsAt 0#64 p12dWords) false false 2
      (mkCallVec a 0#128 0#128 0x80000#64 0x90000#64 (fun _ => 0#8))).vreg 0#5 =
      ((BitVec.sshiftRight (getWord128 a 3) 31 ++ BitVec.sshiftRight (getWord128 a 2) 31) ++
       (BitVec.sshiftRight (getWord128 a 1) 31 ++ BitVec.sshiftRight (getWord128 a 0) 31)) := by
    refine execSteps2_vreg0_eq rfl rfl ?_
    change ((if (getWord128 a 3).msb then 0xffffffff#32 else 0#32) ++
            (if (getWord128 a 2).msb then 0xffffffff#32 else 0#32)) ++
           ((if (getWord128 a 1).msb then 0xffffffff#32 else 0#32) ++
            (if (getWord128 a 0).msb then 0xffffffff#32 else 0#32)) =
           (BitVec.sshiftRight (getWord128 a 3) 31 ++ BitVec.sshiftRight (getWord128 a 2) 31) ++
           (BitVec.sshiftRight (getWord128 a 1) 31 ++ BitVec.sshiftRight (getWord128 a 0) 31)
    rw [cmltZero32_eq_sshiftRight31, cmltZero32_eq_sshiftRight31,
        cmltZero32_eq_sshiftRight31, cmltZero32_eq_sshiftRight31]
  have hMiri : miriSimdAshrWords128 a 0x0000001f_0000001f_0000001f_0000001f#128 =
      .ok ((BitVec.sshiftRight (getWord128 a 3) 31 ++ BitVec.sshiftRight (getWord128 a 2) 31) ++
           (BitVec.sshiftRight (getWord128 a 1) 31 ++ BitVec.sshiftRight (getWord128 a 0) 31)) := rfl
  exact hMiri.trans (congrArg Except.ok hVreg.symm)

/-- **Asymmetry Theorem 3 (`arm_aese_aesmc_ne_x86_vaesenc_single_key`):**
    Arm `AESE` + `AESMC` is NOT a 1-key instruction drop-in for x86 `VAESENC`! -/
theorem arm_aese_aesmc_ne_x86_vaesenc_single_key :
    let pt  := 0x340737e0a29831318d305a88a8f64332#128
    let rk0 := 0x3c4fcf098815f7aba6d2ae2816157e2b#128
    aesmcVec (aeseVec pt rk0) ≠ IntrinsicAarch64Ext.x86Vaesenc128 pt rk0 := by
  dsimp only []
  intro h
  have hb := congrArg (fun v => getByte128 v 0) h
  exact absurd hb (by decide)

theorem ext_aesSbox_eq (b : BitVec 8) :
    IntrinsicAarch64Ext.aesSbox b = VendorArm64Ref.aesSbox b := rfl

theorem ext_aesShiftRows128_eq (s : BitVec 128) :
    IntrinsicAarch64Ext.aesShiftRows128 s = VendorArm64Ref.aesShiftRows128 s := rfl

theorem ext_aesSubBytes128_eq (s : BitVec 128) :
    IntrinsicAarch64Ext.aesSubBytes128 s = VendorArm64Ref.aesSubBytes128 s := by
  dsimp only [IntrinsicAarch64Ext.aesSubBytes128, VendorArm64Ref.aesSubBytes128,
              IntrinsicAarch64Ext.packBytes128, VendorArm64Ref.packBytes128,
              IntrinsicAarch64Ext.getByte128, VendorArm64Ref.getByte128]
  simp only [ext_aesSbox_eq]

theorem ext_aese128_eq (d k : BitVec 128) :
    IntrinsicAarch64Ext.aese128 d k = VendorArm64Ref.aeseVec d k := by
  unfold IntrinsicAarch64Ext.aese128 VendorArm64Ref.aeseVec
  rw [ext_aesShiftRows128_eq, ext_aesSubBytes128_eq]

theorem ext_aesmc128_eq (d : BitVec 128) :
    IntrinsicAarch64Ext.aesmc128 d = VendorArm64Ref.aesmcVec d := rfl

/-- **Asymmetry Theorem 4 (`arm_aese_aesmc_eor_eq_x86_vaesenc_universal`):**
    Universal 2-key cipher-round isomorphism across ALL `2^384` `(state, rk0, rk1)`
    triples: Arm `aesmc(aese(state, rk0)) ^ rk1` equals x86
    `vaesenc(state ^ rk0, rk1)` identically! -/
theorem arm_aese_aesmc_eor_eq_x86_vaesenc_universal (state rk0 rk1 : BitVec 128) :
    (aesmcVec (aeseVec state rk0)) ^^^ rk1 =
    IntrinsicAarch64Ext.x86Vaesenc128 (state ^^^ rk0) rk1 := by
  rw [← ext_aese128_eq, ← ext_aesmc128_eq]
  rfl

/-! ## Section 4: Algebraic Bitwidth Projection Lemmas for Multi-Instruction Sequences -/

theorem extract32_zeroExtend128_16 (x : BitVec 16) :
    (BitVec.extractLsb' 0 32 (x.zeroExtend 128)).zeroExtend 64 = x.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h16 : x.toNat < 2 ^ 16 := x.isLt
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans h16 (by decide)
  have h32  : x.toNat < 2 ^ 32  := Nat.lt_trans h16 (by decide)
  have h64  : x.toNat < 2 ^ 64  := Nat.lt_trans h16 (by decide)
  rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]

theorem extract32_zeroExtend128_8 (x : BitVec 8) :
    (BitVec.extractLsb' 0 32 (x.zeroExtend 128)).zeroExtend 64 = x.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h8   : x.toNat < 2 ^ 8   := x.isLt
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans h8 (by decide)
  have h32  : x.toNat < 2 ^ 32  := Nat.lt_trans h8 (by decide)
  have h64  : x.toNat < 2 ^ 64  := Nat.lt_trans h8 (by decide)
  rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]

theorem extract64_zeroExtend128_64 (x : BitVec 64) :
    BitVec.extractLsb' 0 64 (x.zeroExtend 128) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]
  have h64  : x.toNat < 2 ^ 64  := x.isLt
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans h64 (by decide)
  rw [Nat.shiftRight_zero, Nat.mod_eq_of_lt h128, Nat.mod_eq_of_lt h64]

theorem concat_hi64_lo64 (p : BitVec 128) :
    (BitVec.extractLsb' 64 64 p ++ BitVec.extractLsb' 0 64 p) = p :=
  @BitVec.extractLsb'_append_extractLsb' 64 64 p

/-! ## Section 5: Unified 3-Way Pass-2 Triangulation Predicates & Step Combinators -/

/-- 3-Way Triangulation for 128-bit vector return (`V0`):
    1. `LeanMiri / IntrinsicAarch64Ext` returns `.ok specVal` (zero UB);
    2. `VendorArm64Ref` executes the `.o` words with `fault = none`, returns to
       `pc = lr`, and places `specVal` in `V0`;
    3. `WordArm64.StepsN` simulates the exact multi-step `.o` trace. -/
def TriangulatedVec128 (miriRes : Except SimdUb (BitVec 128)) (specVal : BitVec 128)
    (words : List (BitVec 32)) (steps : Nat) (s0 : MachineState) (lr : BitVec 64) : Prop :=
  let code := loadWordsAt 0#64 words
  let sFinal := execStepsN code false false steps s0
  miriRes = .ok specVal ∧
  sFinal.fault = none ∧
  sFinal.pc = lr ∧
  sFinal.vreg 0#5 = specVal ∧
  WordArm64.StepsN code false steps (toWordState s0) (toWordState sFinal)

/-- 3-Way Triangulation for scalar `X0` / `W0` return (with 32-bit `W0` upper-32 zeroing). -/
def TriangulatedGp64 (miriRes : Except SimdUb (BitVec 64)) (specVal : BitVec 64)
    (words : List (BitVec 32)) (steps : Nat) (s0 : MachineState) (lr : BitVec 64) : Prop :=
  let code := loadWordsAt 0#64 words
  let sFinal := execStepsN code false false steps s0
  miriRes = .ok specVal ∧
  sFinal.fault = none ∧
  sFinal.pc = lr ∧
  sFinal.xreg 0#5 = specVal ∧
  WordArm64.StepsN code false steps (toWordState s0) (toWordState sFinal)

/-- 3-Way Triangulation for 128-bit `u128` GPR pair return (`X1:X0`, AAPCS64). -/
def TriangulatedGpPair128 (miriRes : Except SimdUb (BitVec 128)) (specVal : BitVec 128)
    (words : List (BitVec 32)) (steps : Nat) (s0 : MachineState) (lr : BitVec 64) : Prop :=
  let code := loadWordsAt 0#64 words
  let sFinal := execStepsN code false false steps s0
  miriRes = .ok specVal ∧
  sFinal.fault = none ∧
  sFinal.pc = lr ∧
  (sFinal.xreg 1#5 ++ sFinal.xreg 0#5) = specVal ∧
  WordArm64.StepsN code false steps (toWordState s0) (toWordState sFinal)

theorem mkTriVec128Fast {miriRes : Except SimdUb (BitVec 128)} {specVal : BitVec 128}
    {words : List (BitVec 32)} {ins0 ins1 : Instr} {s0 : MachineState} {lr : BitVec 64}
    (hMiri : miriRes = .ok specVal)
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hOut : (let sf := execInstr false false ins1 (execInstr false false ins0 s0);
             (sf.fault, sf.pc, sf.vreg 0#5)) = (none, lr, specVal) := by rfl) :
    TriangulatedVec128 miriRes specVal words 2 s0 lr :=
  let hRun := execSteps2_eq hFD0 hFD1 hStop0 hPc0 hStop1 hPc1
  ⟨hMiri,
   (congrArg MachineState.fault hRun).trans (congrArg (fun t => t.1) hOut),
   (congrArg MachineState.pc hRun).trans (congrArg (fun t => t.2.1) hOut),
   (congrArg (fun st => st.vreg 0#5) hRun).trans (congrArg (fun t => t.2.2) hOut),
   vendorArm64Ref_stepsN_sub_wordArm64_stepsN (loadWordsAt 0#64 words) false 2 s0 _
     (execStepsN_implies_stepsN (loadWordsAt 0#64 words) false false 2 s0)⟩

theorem mkTriVec128 {miriRes : Except SimdUb (BitVec 128)} {specVal : BitVec 128}
    {words : List (BitVec 32)} {ins0 ins1 : Instr} {s0 : MachineState} {lr : BitVec 64}
    (hMiri : miriRes = .ok specVal)
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hReg : (execInstr false false ins1 (execInstr false false ins0 s0)).vreg 0#5 = specVal)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hFp : (let sf := execInstr false false ins1 (execInstr false false ins0 s0);
            (sf.fault, sf.pc)) = (none, lr) := by rfl) :
    TriangulatedVec128 miriRes specVal words 2 s0 lr :=
  let hRun := execSteps2_eq hFD0 hFD1 hStop0 hPc0 hStop1 hPc1
  ⟨hMiri,
   (congrArg MachineState.fault hRun).trans (congrArg Prod.fst hFp),
   (congrArg MachineState.pc hRun).trans (congrArg Prod.snd hFp),
   (congrArg (fun st => st.vreg 0#5) hRun).trans hReg,
   vendorArm64Ref_stepsN_sub_wordArm64_stepsN (loadWordsAt 0#64 words) false 2 s0 _
     (execStepsN_implies_stepsN (loadWordsAt 0#64 words) false false 2 s0)⟩

theorem mkTriGp64_2 {miriRes : Except SimdUb (BitVec 64)} {specVal : BitVec 64}
    {words : List (BitVec 32)} {ins0 ins1 : Instr} {s0 : MachineState} {lr : BitVec 64}
    (hMiri : miriRes = .ok specVal)
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hReg : (execInstr false false ins1 (execInstr false false ins0 s0)).xreg 0#5 = specVal)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hFp : (let sf := execInstr false false ins1 (execInstr false false ins0 s0);
            (sf.fault, sf.pc)) = (none, lr) := by rfl) :
    TriangulatedGp64 miriRes specVal words 2 s0 lr :=
  let hRun := execSteps2_eq hFD0 hFD1 hStop0 hPc0 hStop1 hPc1
  ⟨hMiri,
   (congrArg MachineState.fault hRun).trans (congrArg Prod.fst hFp),
   (congrArg MachineState.pc hRun).trans (congrArg Prod.snd hFp),
   (congrArg (fun st => st.xreg 0#5) hRun).trans hReg,
   vendorArm64Ref_stepsN_sub_wordArm64_stepsN (loadWordsAt 0#64 words) false 2 s0 _
     (execStepsN_implies_stepsN (loadWordsAt 0#64 words) false false 2 s0)⟩

theorem mkTriGp64_3 {miriRes : Except SimdUb (BitVec 64)} {specVal : BitVec 64}
    {words : List (BitVec 32)} {ins0 ins1 ins2 : Instr} {s0 : MachineState} {lr : BitVec 64}
    (hMiri : miriRes = .ok specVal)
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64 = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64 = .ok ins1)
    (hFD2 : fetchDecodeAt (loadWordsAt 0#64 words) 8#64 = .ok ins2)
    (hReg : (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))).xreg 0#5 = specVal)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hStop2 : (let s2 := execInstr false false ins1 (execInstr false false ins0 s0); s2.halted || s2.fault.isSome) = false := by rfl)
    (hPc2 : (execInstr false false ins1 (execInstr false false ins0 s0)).pc = 8#64 := by rfl)
    (hFp : (let sf := execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0));
            (sf.fault, sf.pc)) = (none, lr) := by rfl) :
    TriangulatedGp64 miriRes specVal words 3 s0 lr :=
  let hRun := execSteps3_eq hFD0 hFD1 hFD2 hStop0 hPc0 hStop1 hPc1 hStop2 hPc2
  ⟨hMiri,
   (congrArg MachineState.fault hRun).trans (congrArg Prod.fst hFp),
   (congrArg MachineState.pc hRun).trans (congrArg Prod.snd hFp),
   (congrArg (fun st => st.xreg 0#5) hRun).trans hReg,
   vendorArm64Ref_stepsN_sub_wordArm64_stepsN (loadWordsAt 0#64 words) false 3 s0 _
     (execStepsN_implies_stepsN (loadWordsAt 0#64 words) false false 3 s0)⟩

theorem mkTriGpPair128_6 {miriRes : Except SimdUb (BitVec 128)} {specVal : BitVec 128}
    {words : List (BitVec 32)} {ins0 ins1 ins2 ins3 ins4 ins5 : Instr} {s0 : MachineState} {lr : BitVec 64}
    (hMiri : miriRes = .ok specVal)
    (hFD0 : fetchDecodeAt (loadWordsAt 0#64 words) 0#64  = .ok ins0)
    (hFD1 : fetchDecodeAt (loadWordsAt 0#64 words) 4#64  = .ok ins1)
    (hFD2 : fetchDecodeAt (loadWordsAt 0#64 words) 8#64  = .ok ins2)
    (hFD3 : fetchDecodeAt (loadWordsAt 0#64 words) 12#64 = .ok ins3)
    (hFD4 : fetchDecodeAt (loadWordsAt 0#64 words) 16#64 = .ok ins4)
    (hFD5 : fetchDecodeAt (loadWordsAt 0#64 words) 20#64 = .ok ins5)
    (hReg : (let sf := execInstr false false ins5 (execInstr false false ins4 (execInstr false false ins3
               (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))));
             sf.xreg 1#5 ++ sf.xreg 0#5) = specVal)
    (hStop0 : (s0.halted || s0.fault.isSome) = false := by rfl)
    (hPc0 : s0.pc = 0#64 := by rfl)
    (hStop1 : (let s1 := execInstr false false ins0 s0; s1.halted || s1.fault.isSome) = false := by rfl)
    (hPc1 : (execInstr false false ins0 s0).pc = 4#64 := by rfl)
    (hStop2 : (let s2 := execInstr false false ins1 (execInstr false false ins0 s0); s2.halted || s2.fault.isSome) = false := by rfl)
    (hPc2 : (execInstr false false ins1 (execInstr false false ins0 s0)).pc = 8#64 := by rfl)
    (hStop3 : (let s3 := execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)); s3.halted || s3.fault.isSome) = false := by rfl)
    (hPc3 : (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))).pc = 12#64 := by rfl)
    (hStop4 : (let s4 := execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))); s4.halted || s4.fault.isSome) = false := by rfl)
    (hPc4 : (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))).pc = 16#64 := by rfl)
    (hStop5 : (let s5 := execInstr false false ins4 (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))); s5.halted || s5.fault.isSome) = false := by rfl)
    (hPc5 : (execInstr false false ins4 (execInstr false false ins3 (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0))))).pc = 20#64 := by rfl)
    (hFp : (let sf := execInstr false false ins5 (execInstr false false ins4 (execInstr false false ins3
              (execInstr false false ins2 (execInstr false false ins1 (execInstr false false ins0 s0)))));
            (sf.fault, sf.pc)) = (none, lr) := by rfl) :
    TriangulatedGpPair128 miriRes specVal words 6 s0 lr :=
  let hRun := execSteps6_eq hFD0 hFD1 hFD2 hFD3 hFD4 hFD5
    hStop0 hPc0 hStop1 hPc1 hStop2 hPc2 hStop3 hPc3 hStop4 hPc4 hStop5 hPc5
  ⟨hMiri,
   (congrArg MachineState.fault hRun).trans (congrArg Prod.fst hFp),
   (congrArg MachineState.pc hRun).trans (congrArg Prod.snd hFp),
   (congrArg (fun st => st.xreg 1#5 ++ st.xreg 0#5) hRun).trans hReg,
   vendorArm64Ref_stepsN_sub_wordArm64_stepsN (loadWordsAt 0#64 words) false 6 s0 _
     (execStepsN_implies_stepsN (loadWordsAt 0#64 words) false false 6 s0)⟩

/-! ## Section 6: `StdarchArmSpec` Specifications & First 19 Universal Triangulation Theorems (`p01..p15`) -/

def spec_p01 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => getByte128 a i + getByte128 b i
def spec_p02 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => getByte128 a i - getByte128 b i
def spec_p03 (a b : BitVec 128) : BitVec 128 := a &&& b
def spec_p04 (a b : BitVec 128) : BitVec 128 := a ||| b
def spec_p05 (a b : BitVec 128) : BitVec 128 := a ^^^ b
def spec_p06 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => if getByte128 a i == getByte128 b i then 0xff#8 else 0#8
def spec_p07 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => if decide ((getByte128 a i).toNat > (getByte128 b i).toNat) then 0xff#8 else 0#8
def spec_p08 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => if decide ((getByte128 a i).toInt < (getByte128 b i).toInt) then 0xff#8 else 0#8
def spec_p09 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => uqaddW 8 (getByte128 a i) (getByte128 b i)
def spec_p10 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => uqsubW 8 (getByte128 a i) (getByte128 b i)
def spec_p11 (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => neonUshlLane 8 (getByte128 a i) (getByte128 b i)
def spec_p11b (a b : BitVec 128) : BitVec 128 := packBytes128 fun i => neonSshlLane 8 (getByte128 a i) (getByte128 b i)
def spec_p12 (a : BitVec 128) : BitVec 128 := packWords128 fun i => (getWord128 a i) <<< 7
def spec_p12b (a : BitVec 128) : BitVec 128 := packWords128 fun i => (getWord128 a i) >>> 7
def spec_p12c (_a : BitVec 128) : BitVec 128 := 0#128
def spec_p12d (a : BitVec 128) : BitVec 128 := packWords128 fun i => BitVec.sshiftRight (getWord128 a i) 31
def spec_p13 (a idx : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => let b := (getByte128 idx i).toNat; if b < 16 then getByte128 a b else 0#8
def spec_p14 (a b : BitVec 128) : BitVec 128 :=
  packBytes128 fun i =>
    if i < 8 then getByte128 a (2 * i) + getByte128 a (2 * i + 1)
    else getByte128 b (2 * (i - 8)) + getByte128 b (2 * (i - 8) + 1)
def spec_p15 (a : BitVec 128) : BitVec 128 :=
  packHalfs128 fun i => (getByte128 a (2 * i)).zeroExtend 16 + (getByte128 a (2 * i + 1)).zeroExtend 16
def spec_p16 (a : BitVec 128) : BitVec 64 := (BitVec.ofNat 16 (uaddlvLoop 16 8 a)).zeroExtend 64
def spec_p17 (a : BitVec 128) : BitVec 64 := (BitVec.ofNat 8 (umaxvLoop 16 8 a)).zeroExtend 64
def spec_p17b (a : BitVec 128) : BitVec 64 := (BitVec.ofNat 8 (uminvLoop 16 8 a)).zeroExtend 64
def spec_p18 (a : BitVec 128) : BitVec 128 := packBytes128 fun i => getByte128 a ((i / 8) * 8 + (7 - (i % 8)))
def spec_p18b (a : BitVec 128) : BitVec 128 :=
  (BitVec.extractLsb' 0 64 (packBytes128 fun i => getByte128 a ((i / 8) * 8 + (7 - (i % 8))))).zeroExtend 128
def spec_p19 (a b : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => let k := i + 5; if k < 16 then getByte128 a k else getByte128 b (k - 16)
def spec_p20 (mask a b : BitVec 128) : BitVec 128 := (a &&& mask) ||| (b &&& (~~~mask))
def spec_p21 (a : BitVec 128) : BitVec 128 := packBytes128 fun i => popcntByte (getByte128 a i)
def spec_p22 (a b : BitVec 128) : BitVec 128 := packHalfs128 fun i => pmullByte (getByte128 a i) (getByte128 b i)
def spec_p22b (a b : BitVec 64) : BitVec 128 := pmull64 a b
def spec_p23 (data key : BitVec 128) : BitVec 128 := aeseVec data key
def spec_p23b (data : BitVec 128) : BitVec 128 := aesmcVec data
def spec_p24 (a b c : BitVec 128) : BitVec 128 := sha512hVec a b c
def spec_p24b (a b : BitVec 128) : BitVec 128 := sha512su0Vec a b
def spec_p25 (crc data : BitVec 64) : BitVec 64 :=
  (crc32Multi true 8 (BitVec.extractLsb' 0 32 crc) data).zeroExtend 64

theorem getByte64_extract0 (a : BitVec 128) (i : Nat) (hi : i * 8 + 8 <= 64) :
    IntrinsicAarch64Ext.getByte64 (BitVec.extractLsb' 0 64 a) i = getByte128 a i := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [IntrinsicAarch64Ext.getByte64, getByte128, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, Nat.zero_add]
  have hlt : i * 8 + k < 64 := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk (i * 8)) hi
  simp [hlt]

def liftExtU16_zext64 (name : String) (args : List IntrinsicAarch64Ext.ExtVal)
    : Except SimdUb (BitVec 64) :=
  match IntrinsicAarch64Ext.evalAarch64Ext name args with
  | some (.ok (.b32 r)) => .ok ((BitVec.extractLsb' 0 16 r).zeroExtend 64)
  | _ => .error (.intrinsicUnsupported name)

def liftExtU8_zext64 (name : String) (args : List IntrinsicAarch64Ext.ExtVal)
    : Except SimdUb (BitVec 64) :=
  match IntrinsicAarch64Ext.evalAarch64Ext name args with
  | some (.ok (.b8 r)) => .ok (r.zeroExtend 64)
  | _ => .error (.intrinsicUnsupported name)

theorem packBytes128_congr (f g : Nat → BitVec 8) (h : ∀ i, f i = g i) :
    packBytes128 f = packBytes128 g := by
  unfold packBytes128
  simp only [h]

-- 1. `p01_vaddq_u8` (`add v0.16b, v1.16b, v0.16b`: `rustc -O3` commutes `v1 + v0`)
theorem triangulate_p01_vaddq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p01 a b)) (spec_p01 a b) p01Words 2 (mkCallVec a b 0#128 sp lr mem) lr := by
  refine mkTriVec128 rfl rfl rfl ?_
  change packBytes128 (fun i => getByte128 b i + getByte128 a i) =
         packBytes128 (fun i => getByte128 a i + getByte128 b i)
  exact packBytes128_congr _ _ (fun i => BitVec.add_comm (getByte128 b i) (getByte128 a i))

-- 2. `p02_vsubq_u8` (`sub v0.16b, v0.16b, v1.16b`)
theorem triangulate_p02_vsubq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p02 a b)) (spec_p02 a b) p02Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 3. `p03_vandq_u8` (`and v0.16b, v1.16b, v0.16b`: `rustc -O3` commutes `v1 &&& v0`)
theorem triangulate_p03_vandq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p03 a b)) (spec_p03 a b) p03Words 2 (mkCallVec a b 0#128 sp lr mem) lr := by
  refine mkTriVec128 rfl rfl rfl ?_
  change b &&& a = a &&& b
  exact BitVec.and_comm b a

-- 4. `p04_vorrq_u8` (`orr v0.16b, v1.16b, v0.16b`: `rustc -O3` commutes `v1 ||| v0`)
theorem triangulate_p04_vorrq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p04 a b)) (spec_p04 a b) p04Words 2 (mkCallVec a b 0#128 sp lr mem) lr := by
  refine mkTriVec128 rfl rfl rfl ?_
  change b ||| a = a ||| b
  exact BitVec.or_comm b a

-- 5. `p05_veorq_u8` (`eor v0.16b, v1.16b, v0.16b`: `rustc -O3` commutes `v1 ^^^ v0`)
theorem triangulate_p05_veorq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p05 a b)) (spec_p05 a b) p05Words 2 (mkCallVec a b 0#128 sp lr mem) lr := by
  refine mkTriVec128 rfl rfl rfl ?_
  change b ^^^ a = a ^^^ b
  exact BitVec.xor_comm b a

-- 6. `p06_vceqq_u8` (`cmeq v0.16b, v0.16b, v1.16b`)
theorem triangulate_p06_vceqq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p06 a b)) (spec_p06 a b) p06Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 7. `p07_vcgtq_u8` (`cmhi v0.16b, v0.16b, v1.16b`)
theorem triangulate_p07_vcgtq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p07 a b)) (spec_p07 a b) p07Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 8. `p08_vcltq_s8` (`cmgt v0.16b, v1.16b, v0.16b`: `b >s a` ≡ `a <s b`)
theorem triangulate_p08_vcltq_s8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p08 a b)) (spec_p08 a b) p08Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 9. `p09_vqaddq_u8` (`uqadd v0.16b, v0.16b, v1.16b`)
theorem triangulate_p09_vqaddq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p09 a b)) (spec_p09 a b) p09Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 10. `p10_vqsubq_u8` (`uqsub v0.16b, v0.16b, v1.16b`)
theorem triangulate_p10_vqsubq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p10 a b)) (spec_p10 a b) p10Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 11. `p11_vshlq_u8` (`ushl v0.16b, v0.16b, v1.16b`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p11_vshlq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.neon.ushl.v16i8" [.b128 a, .b128 b])
      (spec_p11 a b) p11Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 12. `p11b_vshlq_s8` (`sshl v0.16b, v0.16b, v1.16b`, bridged to `IntrinsicAarch64Ext`)
theorem triangulate_p11b_vshlq_s8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (liftExt128 "llvm.aarch64.neon.sshl.v16i8" [.b128 a, .b128 b])
      (spec_p11b a b) p11bWords 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 13. `p12_vshlq_n_u32_7` (`shl v0.4s, v0.4s, #7`)
theorem triangulate_p12_vshlq_n_u32_7 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p12 a)) (spec_p12 a) p12Words 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 14. `p12b_vshrq_n_u32_7` (`ushr v0.4s, v0.4s, #7`)
theorem triangulate_p12b_vshrq_n_u32_7 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p12b a)) (spec_p12b a) p12bWords 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 15. `p12c_vshrq_n_u32_32` (`movi v0.2d, #0`: `stdarch` boundary shift by 32)
theorem triangulate_p12c_vshrq_n_u32_32 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p12c a)) (spec_p12c a) p12cWords 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 16. `p12d_vshrq_n_s32_32` (`cmlt v0.4s, v0.4s, #0`: LLVM sign-mask lowering)
theorem triangulate_p12d_vshrq_n_s32_32 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p12d a)) (spec_p12d a) p12dWords 2 (mkCallVec a 0#128 0#128 sp lr mem) lr := by
  refine mkTriVec128 rfl rfl rfl ?_
  change ((if (getWord128 a 3).msb then 0xffffffff#32 else 0#32) ++
          (if (getWord128 a 2).msb then 0xffffffff#32 else 0#32)) ++
         ((if (getWord128 a 1).msb then 0xffffffff#32 else 0#32) ++
          (if (getWord128 a 0).msb then 0xffffffff#32 else 0#32)) =
         (BitVec.sshiftRight (getWord128 a 3) 31 ++ BitVec.sshiftRight (getWord128 a 2) 31) ++
         (BitVec.sshiftRight (getWord128 a 1) 31 ++ BitVec.sshiftRight (getWord128 a 0) 31)
  rw [cmltZero32_eq_sshiftRight31, cmltZero32_eq_sshiftRight31,
      cmltZero32_eq_sshiftRight31, cmltZero32_eq_sshiftRight31]

-- 17. `p13_vqtbl1q_u8` (`tbl v0.16b, {v0.16b}, v1.16b`)
theorem triangulate_p13_vqtbl1q_u8 (a idx : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p13 a idx)) (spec_p13 a idx) p13Words 2 (mkCallVec a idx 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 18. `p14_vpaddq_u8` (`addp v0.16b, v0.16b, v1.16b`)
theorem triangulate_p14_vpaddq_u8 (a b : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p14 a b)) (spec_p14 a b) p14Words 2 (mkCallVec a b 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

-- 19. `p15_vpaddlq_u8` (`uaddlp v0.8h, v0.16b`)
theorem triangulate_p15_vpaddlq_u8 (a : BitVec 128) (sp lr : BitVec 64) (mem : ByteMem) :
    TriangulatedVec128 (.ok (spec_p15 a)) (spec_p15 a) p15Words 2 (mkCallVec a 0#128 0#128 sp lr mem) lr :=
  mkTriVec128Fast rfl rfl rfl

end NeonTriangulation24
