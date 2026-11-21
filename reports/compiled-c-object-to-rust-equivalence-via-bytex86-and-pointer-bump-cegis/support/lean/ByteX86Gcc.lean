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
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import Init.Omega

/-!
# `ByteX86Gcc`

Standalone Pass-1 operational x86-64 byte-decoded machine model (`prelude` + `Init.*`
only, `0` `sorry`, `0` `isPartial`, `0` `VendorX86GccRef` imports) supporting
real `gcc 15.2.0` `-O2` and `-O3 -mavx2` ELF64 `.o` machine code:

1. **8/16/32/64-bit GP Sub-Register File (`Reg`, `SubReg8`, `OpSize`):**
   - Non-orthogonal x86-64 REX 8-bit register selection (`subReg8OfIdx`): without REX,
     indices `4..7` address high-byte `AH/CH/DH/BH` (`bits[15:8]`); with any active
     REX prefix (`0x40..0x4F`), indices `4..7` (`extBit = false`) redirect to low-byte
     `SPL/BPL/SIL/DIL` (`bits[7:0]`).
   - Constructive kernel-checked sub-register preservation & REX-nullification theorems
     (`writeSubReg8_hi8_preserves_lo8_and_hi48`, `rex_nullified_by_cs_flips_dil_to_bh`).
2. **Legacy Non-VEX SSE2 vs. VEX `L = 0` / `L = 1` Vector State (`SimdMode`):**
   - Legacy Non-VEX SSE2 (`writeXmm128 false`) preserves `YMM[255:128]`; VEX `L = 0`
     (`writeXmm128 true`) zeroes `YMM[255:128]`; `VZEROUPPER` clears all upper 128-bit
     lanes while preserving `XMM0..XMM15`.
   - Constructive state-transition separation theorems
     (`legacy_sse2_preserves_upper_ymm_vs_vex128_zeroes`,
      `legacy_movq_vs_vex_vmovq_three_band_split`,
      `sse_after_vzeroupper_clean_upper_ymm`).
3. **Two-Stage Variable-Length Byte Decoder (`decodeX64`) & Balanced `ByteCodeTree`:**
   - Splits prefix + instruction-length decoding (`scanPrefixes` + `ildBodyLen`) from
     exact-slice parsing (`parseExactBody (body.take bLen)`), admitting a universal
     prefix-invariance bridge (`decodeX64_prefix_invariant`) over arbitrary finite byte
     blocks without unfolding `parseExactBody`.
   - Stores object `.text` images in logarithmic-depth `ByteCodeTree` (`0` `._unsafe_rec`
     helpers via `ByteCodeTree.rec` and `Nat.rec`) so multi-hundred-byte AVX2 functions
     never hit Lean `v4.34.1`'s `maxRecDepth = 512` ceiling.
-/

namespace ByteX86Gcc

/-! ## Section 1: Architectural Registers, Sub-Registers, Vector Lanes, and Memory -/

inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def regOfNat (n : Nat) : Reg :=
  match n % 16 with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

def regUpd (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

@[simp] theorem regUpd_eq (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) :
    regUpd regs r v r = v := by
  simp [regUpd]

theorem regUpd_ne (regs : Reg → BitVec 64) {r r' : Reg} (h : r' ≠ r) (v : BitVec 64) :
    regUpd regs r v r' = regs r' := by
  simp [regUpd, h]

/-- System V AMD64 psABI §3.2.1 callee-saved general-purpose registers. -/
def isCalleeSaved (r : Reg) : Bool :=
  match r with
  | .rbx | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- 8-bit GP sub-register: `.lo8` (`bits[7:0]`) vs. `.hi8` (`bits[15:8]`, `AH/CH/DH/BH`). -/
inductive SubReg8 where
  | lo8 (r : Reg)
  | hi8 (r : Reg)
  deriving DecidableEq, Repr

def subReg8OfIdx (rexPresent extBit : Bool) (idx3 : BitVec 3) : SubReg8 :=
  if !rexPresent then
    match idx3.toNat with
    | 0 => .lo8 .rax | 1 => .lo8 .rcx | 2 => .lo8 .rdx | 3 => .lo8 .rbx
    | 4 => .hi8 .rax | 5 => .hi8 .rcx | 6 => .hi8 .rdx | _ => .hi8 .rbx
  else
    .lo8 (regOfNat ((if extBit then 8 else 0) + idx3.toNat))

def readSubReg8 (regs : Reg → BitVec 64) : SubReg8 → BitVec 8
  | .lo8 r => BitVec.extractLsb' 0 8 (regs r)
  | .hi8 r => BitVec.extractLsb' 8 8 (regs r)

def writeSubReg8 (regs : Reg → BitVec 64) (sr : SubReg8) (v : BitVec 8) : Reg → BitVec 64 :=
  match sr with
  | .lo8 r =>
    let old := regs r
    regUpd regs r (BitVec.extractLsb' 8 56 old ++ v)
  | .hi8 r =>
    let old := regs r
    regUpd regs r (BitVec.extractLsb' 16 48 old ++ (v ++ BitVec.extractLsb' 0 8 old))

inductive OpSize where
  | s16 | s32 | s64
  deriving DecidableEq, Repr

def readRegSz (sz : OpSize) (regs : Reg → BitVec 64) (r : Reg) : BitVec 64 :=
  match sz with
  | .s64 => regs r
  | .s32 => (BitVec.extractLsb' 0 32 (regs r)).zeroExtend 64
  | .s16 => (BitVec.extractLsb' 0 16 (regs r)).zeroExtend 64

def writeRegSz (sz : OpSize) (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  match sz with
  | .s64 => regUpd regs r v
  | .s32 => regUpd regs r ((BitVec.extractLsb' 0 32 v).zeroExtend 64)
  | .s16 => regUpd regs r (BitVec.extractLsb' 16 48 (regs r) ++ BitVec.extractLsb' 0 16 v)

abbrev YmmIdx := Fin 16

def ymmIdxOfNat (n : Nat) : YmmIdx := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def ymmUpd (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v : BitVec 256) : YmmIdx → BitVec 256 :=
  fun idx' => if idx' = idx then v else ymms idx'

@[simp] theorem ymmUpd_eq (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v : BitVec 256) :
    ymmUpd ymms idx v idx = v := by
  simp [ymmUpd]

theorem ymmUpd_ne (ymms : YmmIdx → BitVec 256) {i j : YmmIdx} (h : j ≠ i) (v : BitVec 256) :
    ymmUpd ymms i v j = ymms j := by
  simp [ymmUpd, h]

/-- Write 128-bit vector result: `isVex = true` zeroes `YMM[255:128]`; `isVex = false`
    (Legacy Non-VEX SSE2) preserves `YMM[255:128]`. -/
def writeXmm128 (isVex : Bool) (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v128 : BitVec 128) :
    YmmIdx → BitVec 256 :=
  match isVex with
  | true  => ymmUpd ymms idx (v128.zeroExtend 256)
  | false => ymmUpd ymms idx (BitVec.extractLsb' 128 128 (ymms idx) ++ v128)

def vzeroUpperAll (ymms : YmmIdx → BitVec 256) : YmmIdx → BitVec 256 :=
  fun idx => (BitVec.extractLsb' 0 128 (ymms idx)).zeroExtend 256

structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  deriving DecidableEq, Repr

structure UndefChoice where
  flags    : RFlags := {}
  undefGpr : BitVec 64 := 0#64
  deriving DecidableEq, Repr

abbrev ByteMem := BitVec 64 → BitVec 8
abbrev CodeMap := BitVec 64 → BitVec 8

def memUpd8 (m : ByteMem) (a : BitVec 64) (b : BitVec 8) : ByteMem :=
  fun a' => if a' = a then b else m a'

@[simp] theorem memUpd8_eq (m : ByteMem) (a : BitVec 64) (b : BitVec 8) :
    memUpd8 m a b a = b := by
  simp [memUpd8]

theorem memUpd8_ne (m : ByteMem) {a a' : BitVec 64} (h : a' ≠ a) (b : BitVec 8) :
    memUpd8 m a b a' = m a' := by
  simp [memUpd8, h]

def byteOf64 (v : BitVec 64) (k : Nat) : BitVec 8 :=
  BitVec.extractLsb' (k * 8) 8 v

def sext8To64 (b : BitVec 8) : BitVec 64 :=
  (if b.msb then 0xFFFFFFFFFFFFFF#56 else 0#56) ++ b

def sext16To64 (w : BitVec 16) : BitVec 64 :=
  (if w.msb then 0xFFFFFFFFFFFF#48 else 0#48) ++ w

def sext32To64 (w : BitVec 32) : BitVec 64 :=
  (if w.msb then 0xFFFFFFFF#32 else 0#32) ++ w

def pack8Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ (b6 ++ (b5 ++ (b4 ++ (b3 ++ (b2 ++ (b1 ++ b0))))))

def readMem8 (m : ByteMem) (a : BitVec 64) : BitVec 8 := m a

def readMem16 (m : ByteMem) (a : BitVec 64) : BitVec 16 :=
  m (a + 1#64) ++ m (a + 0#64)

def readMem32 (m : ByteMem) (a : BitVec 64) : BitVec 32 :=
  m (a + 3#64) ++ (m (a + 2#64) ++ (m (a + 1#64) ++ m (a + 0#64)))

def readMem64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  pack8Bytes (m (a + 0#64)) (m (a + 1#64)) (m (a + 2#64)) (m (a + 3#64))
             (m (a + 4#64)) (m (a + 5#64)) (m (a + 6#64)) (m (a + 7#64))

def readMem128 (m : ByteMem) (a : BitVec 64) : BitVec 128 :=
  readMem64 m (a + 8#64) ++ readMem64 m a

def readMem256 (m : ByteMem) (a : BitVec 64) : BitVec 256 :=
  readMem128 m (a + 16#64) ++ readMem128 m a

def writeMem16 (m : ByteMem) (a : BitVec 64) (v : BitVec 16) : ByteMem :=
  let m0 := memUpd8 m (a + 0#64) (BitVec.extractLsb' 0 8 v)
  memUpd8 m0 (a + 1#64) (BitVec.extractLsb' 8 8 v)

def writeMem32 (m : ByteMem) (a : BitVec 64) (v : BitVec 32) : ByteMem :=
  let m0 := memUpd8 m  (a + 0#64) (BitVec.extractLsb' 0  8 v)
  let m1 := memUpd8 m0 (a + 1#64) (BitVec.extractLsb' 8  8 v)
  let m2 := memUpd8 m1 (a + 2#64) (BitVec.extractLsb' 16 8 v)
  memUpd8 m2 (a + 3#64) (BitVec.extractLsb' 24 8 v)

def writeMem64 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m0 := memUpd8 m  (a + 0#64) (byteOf64 v 0)
  let m1 := memUpd8 m0 (a + 1#64) (byteOf64 v 1)
  let m2 := memUpd8 m1 (a + 2#64) (byteOf64 v 2)
  let m3 := memUpd8 m2 (a + 3#64) (byteOf64 v 3)
  let m4 := memUpd8 m3 (a + 4#64) (byteOf64 v 4)
  let m5 := memUpd8 m4 (a + 5#64) (byteOf64 v 5)
  let m6 := memUpd8 m5 (a + 6#64) (byteOf64 v 6)
  memUpd8 m6 (a + 7#64) (byteOf64 v 7)

def writeMem128 (m : ByteMem) (a : BitVec 64) (v : BitVec 128) : ByteMem :=
  let mLo := writeMem64 m a (BitVec.extractLsb' 0 64 v)
  writeMem64 mLo (a + 8#64) (BitVec.extractLsb' 64 64 v)

def writeMem256 (m : ByteMem) (a : BitVec 64) (v : BitVec 256) : ByteMem :=
  let mLo := writeMem128 m a (BitVec.extractLsb' 0 128 v)
  writeMem128 mLo (a + 16#64) (BitVec.extractLsb' 128 128 v)

/-! ### Fixed-Lane Vector Combinators -/

def getByte128 (v : BitVec 128) (i : Fin 16) : BitVec 8 :=
  BitVec.extractLsb' (i.val * 8) 8 v

def packBytes128 (f : Fin 16 → BitVec 8) : BitVec 128 :=
  f ⟨15, by decide⟩ ++ (f ⟨14, by decide⟩ ++ (f ⟨13, by decide⟩ ++ (f ⟨12, by decide⟩ ++
  (f ⟨11, by decide⟩ ++ (f ⟨10, by decide⟩ ++ (f ⟨9, by decide⟩  ++ (f ⟨8, by decide⟩ ++
  (f ⟨7, by decide⟩  ++ (f ⟨6, by decide⟩  ++ (f ⟨5, by decide⟩  ++ (f ⟨4, by decide⟩ ++
  (f ⟨3, by decide⟩  ++ (f ⟨2, by decide⟩  ++ (f ⟨1, by decide⟩  ++ f ⟨0, by decide⟩))))))))))))))

def getByte256 (v : BitVec 256) (i : Fin 32) : BitVec 8 :=
  BitVec.extractLsb' (i.val * 8) 8 v

def packBytes256 (f : Fin 32 → BitVec 8) : BitVec 256 :=
  packBytes128 (fun j => f ⟨j.val + 16, by omega⟩) ++
  packBytes128 (fun j => f ⟨j.val, by omega⟩)

def getWord128 (v : BitVec 128) (i : Fin 8) : BitVec 16 :=
  BitVec.extractLsb' (i.val * 16) 16 v

def packWords128 (f : Fin 8 → BitVec 16) : BitVec 128 :=
  f ⟨7, by decide⟩ ++ (f ⟨6, by decide⟩ ++ (f ⟨5, by decide⟩ ++ (f ⟨4, by decide⟩ ++
  (f ⟨3, by decide⟩ ++ (f ⟨2, by decide⟩ ++ (f ⟨1, by decide⟩ ++ f ⟨0, by decide⟩))))))

def getWord256 (v : BitVec 256) (i : Fin 16) : BitVec 16 :=
  BitVec.extractLsb' (i.val * 16) 16 v

def packWords256 (f : Fin 16 → BitVec 16) : BitVec 256 :=
  packWords128 (fun j => f ⟨j.val + 8, by omega⟩) ++
  packWords128 (fun j => f ⟨j.val, by omega⟩)

def getDword128 (v : BitVec 128) (i : Fin 4) : BitVec 32 :=
  BitVec.extractLsb' (i.val * 32) 32 v

def packDwords128 (f : Fin 4 → BitVec 32) : BitVec 128 :=
  f ⟨3, by decide⟩ ++ (f ⟨2, by decide⟩ ++ (f ⟨1, by decide⟩ ++ f ⟨0, by decide⟩))

def getDword256 (v : BitVec 256) (i : Fin 8) : BitVec 32 :=
  BitVec.extractLsb' (i.val * 32) 32 v

def packDwords256 (f : Fin 8 → BitVec 32) : BitVec 256 :=
  packDwords128 (fun j => f ⟨j.val + 4, by omega⟩) ++
  packDwords128 (fun j => f ⟨j.val, by omega⟩)

def getQword128 (v : BitVec 128) (i : Fin 2) : BitVec 64 :=
  BitVec.extractLsb' (i.val * 64) 64 v

def packQwords128 (f : Fin 2 → BitVec 64) : BitVec 128 :=
  f ⟨1, by decide⟩ ++ f ⟨0, by decide⟩

def getQword256 (v : BitVec 256) (i : Fin 4) : BitVec 64 :=
  BitVec.extractLsb' (i.val * 64) 64 v

def packQwords256 (f : Fin 4 → BitVec 64) : BitVec 256 :=
  packQwords128 (fun j => f ⟨j.val + 2, by omega⟩) ++
  packQwords128 (fun j => f ⟨j.val, by omega⟩)

/-! ### Bit-Slice Extraction & Memory Roundtrip Lemmas -/

theorem extractLsb_self {n : Nat} (x : BitVec n) :
    BitVec.extractLsb' 0 n x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', Nat.zero_add]
  simp [hk]

theorem extractLsb_append_right_off {m n s l : Nat} (hi : BitVec m) (lo : BitVec n) (h : s + l ≤ n) :
    BitVec.extractLsb' s l (hi ++ lo) = BitVec.extractLsb' s l lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have hlt : s + k < n := by omega
  simp [hk, hlt]

theorem extractLsb_append_left {m n s l : Nat} (hi : BitVec m) (lo : BitVec n) (hs : n ≤ s) :
    BitVec.extractLsb' s l (hi ++ lo) = BitVec.extractLsb' (s - n) l hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have hnot : ¬ (s + k < n) := by omega
  have hsub : s + k - n = s - n + k := by omega
  simp [hk, hnot, hsub]

/-- Writing high-byte `AH/CH/DH/BH` (`SubReg8.hi8 r`) updates `bits[15:8]` while
    preserving `bits[7:0]`, `bits[63:16]`, and every other GP register `r' ≠ r`. -/
theorem writeSubReg8_hi8_preserves_lo8_and_hi48 (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 8) :
    let regs' := writeSubReg8 regs (.hi8 r) v
    BitVec.extractLsb' 8 8 (regs' r) = v ∧
    BitVec.extractLsb' 0 8 (regs' r) = BitVec.extractLsb' 0 8 (regs r) ∧
    BitVec.extractLsb' 16 48 (regs' r) = BitVec.extractLsb' 16 48 (regs r) ∧
    (∀ r', r' ≠ r → regs' r' = regs r') := by
  dsimp only [writeSubReg8]
  refine ⟨?_, ?_, ?_, fun r' hne => regUpd_ne regs hne _⟩
  · rw [regUpd_eq, extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_left _ _ (by decide), extractLsb_self]
  · rw [regUpd_eq, extractLsb_append_right_off _ _ (by decide),
        extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  · rw [regUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]

/-- Writing low-byte `AL..R15B` (`SubReg8.lo8 r`, including REX-gated `SPL..DIL`)
    updates `bits[7:0]` while preserving `bits[63:8]` and every `r' ≠ r`. -/
theorem writeSubReg8_lo8_preserves_hi56 (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 8) :
    let regs' := writeSubReg8 regs (.lo8 r) v
    BitVec.extractLsb' 0 8 (regs' r) = v ∧
    BitVec.extractLsb' 8 56 (regs' r) = BitVec.extractLsb' 8 56 (regs r) ∧
    (∀ r', r' ≠ r → regs' r' = regs r') := by
  dsimp only [writeSubReg8]
  refine ⟨?_, ?_, fun r' hne => regUpd_ne regs hne _⟩
  · rw [regUpd_eq, extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  · rw [regUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]

theorem ifTrue {α : Type _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ifFalse {α : Type _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

theorem setWidth_eq_zero_append {m n : Nat} (x : BitVec n) :
    BitVec.setWidth (m + n) x = 0#m ++ x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hpow : 2 ^ n ≤ 2 ^ (m + n) := Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : x.toNat < 2 ^ (m + n) := Nat.lt_of_lt_of_le hx hpow
  simp [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.mod_eq_of_lt hlt]

/-- Writing 16-bit operand size (`OpSize.s16`) preserves `bits[63:16]`, whereas
    `OpSize.s32` zeroes `bits[63:32]`. -/
theorem writeRegSz_s16_preserves_hi48 (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) :
    BitVec.extractLsb' 16 48 (writeRegSz .s16 regs r v r) = BitVec.extractLsb' 16 48 (regs r) ∧
    BitVec.extractLsb' 32 32 (writeRegSz .s32 regs r v r) = 0#32 := by
  constructor
  · dsimp only [writeRegSz]
    rw [regUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]
  · dsimp [writeRegSz]
    rw [regUpd_eq, setWidth_eq_zero_append (m := 32),
        extractLsb_append_left _ _ (by decide), extractLsb_self]

theorem pack8_byteOf64 (v : BitVec 64) :
    pack8Bytes (byteOf64 v 0) (byteOf64 v 1) (byteOf64 v 2) (byteOf64 v 3)
               (byteOf64 v 4) (byteOf64 v 5) (byteOf64 v 6) (byteOf64 v 7) = v := by
  dsimp [pack8Bytes, byteOf64]
  have s1 : BitVec.extractLsb' 8 8 v ++ BitVec.extractLsb' 0 8 v = BitVec.extractLsb' 0 16 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s2 : BitVec.extractLsb' 16 8 v ++ BitVec.extractLsb' 0 16 v = BitVec.extractLsb' 0 24 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s3 : BitVec.extractLsb' 24 8 v ++ BitVec.extractLsb' 0 24 v = BitVec.extractLsb' 0 32 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s4 : BitVec.extractLsb' 32 8 v ++ BitVec.extractLsb' 0 32 v = BitVec.extractLsb' 0 40 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s5 : BitVec.extractLsb' 40 8 v ++ BitVec.extractLsb' 0 40 v = BitVec.extractLsb' 0 48 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s6 : BitVec.extractLsb' 48 8 v ++ BitVec.extractLsb' 0 48 v = BitVec.extractLsb' 0 56 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  have s7 : BitVec.extractLsb' 56 8 v ++ BitVec.extractLsb' 0 56 v = BitVec.extractLsb' 0 64 v :=
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl
  rw [s1, s2, s3, s4, s5, s6, s7]
  exact BitVec.extractLsb'_eq_self

theorem add_const64_ne (a : BitVec 64) {c1 c2 : BitVec 64} (hne : c1 ≠ c2) :
    a + c1 ≠ a + c2 := by
  intro heq
  have hsub : (a + c1) - a = (a + c2) - a := congrArg (fun x => x - a) heq
  rw [BitVec.add_comm a c1, BitVec.add_sub_cancel,
      BitVec.add_comm a c2, BitVec.add_sub_cancel] at hsub
  exact hne hsub

theorem readMem64_writeMem64_same (m : ByteMem) (a : BitVec 64) (v : BitVec 64) :
    readMem64 (writeMem64 m a v) a = v := by
  dsimp [readMem64, writeMem64]
  repeat first
    | rw [memUpd8_eq]
    | rw [memUpd8_ne _ (add_const64_ne a (by decide))]
  exact pack8_byteOf64 v

theorem writeMem64_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 64)
    (h : ∀ k, k < 8 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem64 m a v b = m b := by
  dsimp [writeMem64]
  rw [memUpd8_ne _ (h 7 (by decide)), memUpd8_ne _ (h 6 (by decide)),
      memUpd8_ne _ (h 5 (by decide)), memUpd8_ne _ (h 4 (by decide)),
      memUpd8_ne _ (h 3 (by decide)), memUpd8_ne _ (h 2 (by decide)),
      memUpd8_ne _ (h 1 (by decide)), memUpd8_ne _ (h 0 (by decide))]

theorem writeMem128_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 128)
    (h : ∀ k, k < 16 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem128 m a v b = m b := by
  dsimp [writeMem128]
  rw [writeMem64_byte_ne _ (a + 8#64) b _ (fun k hk => by
        have hadd : (a + 8#64) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (8 + k) := by
          rw [BitVec.add_assoc]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [hadd]; exact h (8 + k) (by omega)),
      writeMem64_byte_ne _ a b _ (fun k hk => h k (by omega))]

theorem writeMem256_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 256)
    (h : ∀ k, k < 32 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem256 m a v b = m b := by
  dsimp [writeMem256]
  rw [writeMem128_byte_ne _ (a + 16#64) b _ (fun k hk => by
        have hadd : (a + 16#64) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (16 + k) := by
          rw [BitVec.add_assoc]; congr 1
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [hadd]; exact h (16 + k) (by omega)),
      writeMem128_byte_ne _ a b _ (fun k hk => h k (by omega))]

/-! ## Section 2: Instruction AST & Two-Stage Split Length/Body Byte Decoder -/

inductive DecodeFault where
  | truncated
  | gp0LengthExceeds15
  | gp0Privilege
  | udIllegalLock
  | udVexPrefix
  | udVexField
  | udRegisterOperand
  | udExplicit
  | udUnmapped
  deriving DecidableEq, Repr

structure X64Addr where
  base   : Option Reg := none
  index  : Option (Reg × Nat) := none
  disp   : BitVec 64 := 0#64
  ripRel : Bool := false
  deriving DecidableEq, Repr

inductive X64Rm where
  | reg (r : Reg)
  | mem (a : X64Addr)
  deriving DecidableEq, Repr

inductive X64Rm8 where
  | reg8 (r : SubReg8)
  | mem8 (a : X64Addr)
  deriving DecidableEq, Repr

inductive X64XmmRm where
  | reg (r : YmmIdx)
  | mem (a : X64Addr)
  deriving DecidableEq, Repr

inductive AluOp where
  | add | or | adc | sbb | and | sub | xor | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp where
  | rol | ror | shl | shr | sar
  deriving DecidableEq, Repr

inductive UnaryOp where
  | inc | dec | not | neg
  deriving DecidableEq, Repr

inductive Cond where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

inductive SimdMode where
  | legacy128
  | vex128
  | vex256
  deriving DecidableEq, Repr

inductive VecElem where
  | e8 | e16 | e32 | e64
  deriving DecidableEq, Repr

inductive VecUnpackOp where
  | lbw | hbw | lwd | hwd | ldq | hdq | lqdq | hqdq
  deriving DecidableEq, Repr

inductive VecExtendOp where
  | zxbw | zxwd | zxdq | sxbw | sxwd | sxdq
  deriving DecidableEq, Repr

inductive X64Instr where
  | nop
  | endbr64
  | vzeroupper
  | ud2
  | cli
  | mov8Load   (dst : SubReg8) (src : X64Rm8)
  | mov8Store  (dst : X64Rm8) (src : SubReg8)
  | mov8Imm    (dst : X64Rm8) (imm : BitVec 8)
  | alu8RmReg  (op : AluOp) (dst : X64Rm8) (src : SubReg8)
  | alu8RegRm  (op : AluOp) (dst : SubReg8) (src : X64Rm8)
  | alu8Imm    (op : AluOp) (dst : X64Rm8) (imm : BitVec 8)
  | setcc8     (cc : Cond) (dst : X64Rm8)
  | movzx8     (sz : OpSize) (dst : Reg) (src : X64Rm8)
  | movzx16    (sz : OpSize) (dst : Reg) (src : X64Rm)
  | movsx8     (sz : OpSize) (dst : Reg) (src : X64Rm8)
  | movsx16    (sz : OpSize) (dst : Reg) (src : X64Rm)
  | movsxd     (dst : Reg) (src : X64Rm)
  | movLoad    (sz : OpSize) (dst : Reg) (src : X64Rm)
  | movStore   (sz : OpSize) (dst : X64Rm) (src : Reg)
  | movImm     (sz : OpSize) (dst : Reg) (imm : BitVec 64)
  | movRmImm32 (sz : OpSize) (dst : X64Rm) (imm : BitVec 64)
  | lea        (sz : OpSize) (dst : Reg) (addr : X64Addr)
  | xchg       (sz : OpSize) (r1 : Reg) (rm : X64Rm)
  | aluRmReg   (sz : OpSize) (op : AluOp) (dst : X64Rm) (src : Reg)
  | aluRegRm   (sz : OpSize) (op : AluOp) (dst : Reg) (src : X64Rm)
  | aluImm     (sz : OpSize) (op : AluOp) (dst : X64Rm) (imm : BitVec 64)
  | unaryRm    (sz : OpSize) (op : UnaryOp) (dst : X64Rm)
  | shiftImm   (sz : OpSize) (op : ShiftOp) (dst : X64Rm) (cnt : BitVec 8)
  | imul2      (sz : OpSize) (dst : Reg) (src : X64Rm)
  | imul3      (sz : OpSize) (dst : Reg) (src : X64Rm) (imm : BitVec 64)
  | bsf        (sz : OpSize) (dst : Reg) (src : X64Rm)
  | push64     (src : Reg)
  | pop64      (dst : Reg)
  | leave64
  | ret64
  | jmpRel     (rel : BitVec 64)
  | jccRel     (cc : Cond) (rel : BitVec 64)
  | simdMovLoad    (m : SimdMode) (dst : YmmIdx) (src : X64XmmRm)
  | simdMovStore   (m : SimdMode) (dst : X64XmmRm) (src : YmmIdx)
  | simdMovqLoad   (isVex : Bool) (dst : YmmIdx) (src : X64XmmRm)
  | simdMovqStore  (isVex : Bool) (dst : X64XmmRm) (src : YmmIdx)
  | simdMovGprToX  (isVex is64 : Bool) (dst : YmmIdx) (src : X64Rm)
  | simdMovXToGpr  (isVex is64 : Bool) (dst : X64Rm) (src : YmmIdx)
  | simdBitwise    (m : SimdMode) (op : AluOp) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdAdd        (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdSub        (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdCmpeq      (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdCmpgt      (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdUnpack     (m : SimdMode) (op : VecUnpackOp) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdExtend     (m : SimdMode) (op : VecExtendOp) (dst : YmmIdx) (src : X64XmmRm)
  | simdBroadcastB (m : SimdMode) (dst : YmmIdx) (src : X64XmmRm)
  | simdBroadcastQ (m : SimdMode) (dst : YmmIdx) (src : X64XmmRm)
  | simdPmullw     (m : SimdMode) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdPmulhuw    (m : SimdMode) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdPmulld     (m : SimdMode) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdPmaddwd    (m : SimdMode) (dst s1 : YmmIdx) (s2 : X64XmmRm)
  | simdPsrldq     (m : SimdMode) (dst src : YmmIdx) (imm : BitVec 8)
  | simdPsrlqImm   (m : SimdMode) (dst src : YmmIdx) (imm : BitVec 8)
  | simdPshufd     (m : SimdMode) (dst : YmmIdx) (src : X64XmmRm) (imm : BitVec 8)
  | simdPshuflw    (m : SimdMode) (dst : YmmIdx) (src : X64XmmRm) (imm : BitVec 8)
  | simdExtract128 (dst : X64XmmRm) (src : YmmIdx) (imm : BitVec 8)
  | simdPerm2i128  (dst s1 : YmmIdx) (s2 : X64XmmRm) (imm : BitVec 8)
  deriving DecidableEq, Repr

inductive DecodeOutcome where
  | ok    (ins : X64Instr) (len : Nat)
  | fault (fk : DecodeFault)
  deriving DecidableEq, Repr

inductive RepPfx where
  | none | repz | repnz
  deriving DecidableEq, Repr

structure PrefixState where
  has66      : Bool := false
  rep        : RepPfx := .none
  hasLock    : Bool := false
  hasSegOr67 : Bool := false
  rex        : Option (BitVec 4) := none
  count      : Nat := 0
  deriving DecidableEq, Repr

def isPrefixByte (b : BitVec 8) : Bool :=
  b == 0x66#8 || b == 0xF2#8 || b == 0xF3#8 || b == 0xF0#8 ||
  b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 ||
  b == 0x64#8 || b == 0x65#8 || b == 0x67#8 || (b &&& 0xF0#8) == 0x40#8

def rexBit (rex : Option (BitVec 4)) (idx : Nat) : Bool :=
  match rex with | none => false | some r => r.getLsbD idx

def rexB (rex : Option (BitVec 4)) : Bool := rexBit rex 0
def rexX (rex : Option (BitVec 4)) : Bool := rexBit rex 1
def rexR (rex : Option (BitVec 4)) : Bool := rexBit rex 2
def rexW (rex : Option (BitVec 4)) : Bool := rexBit rex 3

def opSizeOf (ps : PrefixState) : OpSize :=
  if rexW ps.rex then .s64 else if ps.has66 then .s16 else .s32

def mkRegIdx (hiBit : Bool) (lo3 : BitVec 3) : Nat :=
  (if hiBit then 8 else 0) + lo3.toNat

def readLe16? : List (BitVec 8) → Option (BitVec 16 × List (BitVec 8))
  | b0 :: b1 :: rest => some (b1 ++ b0, rest)
  | _ => none

def readLe32? : List (BitVec 8) → Option (BitVec 32 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: rest => some (b3 ++ (b2 ++ (b1 ++ b0)), rest)
  | _ => none

def readLe64? : List (BitVec 8) → Option (BitVec 64 × List (BitVec 8))
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    some (pack8Bytes b0 b1 b2 b3 b4 b5 b6 b7, rest)
  | _ => none

def stepPrefix (s : PrefixState) (b : BitVec 8) : Option PrefixState :=
  if b == 0x66#8 then
    some { s with has66 := true, rex := none, count := s.count + 1 }
  else if b == 0xF2#8 then
    some { s with rep := .repnz, rex := none, count := s.count + 1 }
  else if b == 0xF3#8 then
    some { s with rep := .repz, rex := none, count := s.count + 1 }
  else if b == 0xF0#8 then
    some { s with hasLock := true, rex := none, count := s.count + 1 }
  else if b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 ||
          b == 0x64#8 || b == 0x65#8 || b == 0x67#8 then
    some { s with hasSegOr67 := true, rex := none, count := s.count + 1 }
  else if (b &&& 0xF0#8) == 0x40#8 then
    some { s with rex := some (BitVec.extractLsb' 0 4 b), count := s.count + 1 }
  else
    none

def scanPrefixes (fuel : Nat) (st : PrefixState) (bs : List (BitVec 8)) :
    PrefixState × List (BitVec 8) :=
  Nat.rec (motive := fun _ => PrefixState → List (BitVec 8) → PrefixState × List (BitVec 8))
    (fun s rem => (s, rem))
    (fun _ ih s rem =>
      match rem with
      | [] => (s, [])
      | b :: rest =>
        match stepPrefix s b with
        | some s' => ih s' rest
        | none    => (s, b :: rest))
    fuel st bs

def condOfNib (n : Nat) : Cond :=
  match n % 16 with
  | 0  => .o  | 1  => .no | 2  => .b  | 3  => .ae
  | 4  => .e  | 5  => .ne | 6  => .be | 7  => .a
  | 8  => .s  | 9  => .ns | 10 => .p  | 11 => .np
  | 12 => .l  | 13 => .ge | 14 => .le | _  => .g

def aluOpOfIdx (idx : Nat) : Option AluOp :=
  match idx with
  | 0 => some .add | 1 => some .or  | 2 => some .adc | 3 => some .sbb
  | 4 => some .and | 5 => some .sub | 6 => some .xor | 7 => some .cmp
  | _ => none

def shiftOpOfIdx (idx : Nat) : Option ShiftOp :=
  match idx with
  | 0 => some .rol | 1 => some .ror | 4 => some .shl
  | 5 => some .shr | 7 => some .sar | _ => none

def modrmByteLen : List (BitVec 8) → Option Nat
  | [] => none
  | mrm :: rest =>
    let mod2 := (BitVec.extractLsb' 6 2 mrm).toNat
    let rm3  := (BitVec.extractLsb' 0 3 mrm).toNat
    if mod2 == 3 then some 1
    else if rm3 == 4 then
      match rest with
      | [] => none
      | sib :: _ =>
        let base3 := (BitVec.extractLsb' 0 3 sib).toNat
        if mod2 == 0 && base3 == 5 then some 6
        else if mod2 == 0 then some 2
        else if mod2 == 1 then some 3
        else some 6
    else if mod2 == 0 && rm3 == 5 then some 5
    else if mod2 == 0 then some 1
    else if mod2 == 1 then some 2
    else some 5

def ildVexBodyLen (mapSel : Nat) : List (BitVec 8) → Option Nat
  | [] => none
  | opc :: afterOpc =>
    if mapSel == 1 && opc == 0x77#8 then some 1
    else
      match modrmByteLen afterOpc with
      | none => none
      | some mLen =>
        let immBytes :=
          if mapSel == 1 && (opc == 0x70#8 || opc == 0x71#8 || opc == 0x72#8 || opc == 0x73#8) then 1
          else if mapSel == 3 then 1
          else 0
        some (1 + mLen + immBytes)

def ildBodyLen (ps : PrefixState) (body : List (BitVec 8)) : Option Nat :=
  match body with
  | [] => none
  | op0 :: rest0 =>
    if op0 == 0xC5#8 then
      match rest0 with
      | _b1 :: afterHdr => Option.map (· + 2) (ildVexBodyLen 1 afterHdr)
      | _ => none
    else if op0 == 0xC4#8 then
      match rest0 with
      | b1 :: _b2 :: afterHdr =>
        let mapSel := (BitVec.extractLsb' 0 5 b1).toNat
        Option.map (· + 3) (ildVexBodyLen mapSel afterHdr)
      | _ => none
    else if op0 == 0x90#8 || op0 == 0xC3#8 || op0 == 0xC9#8 || op0 == 0xFA#8 ||
            (op0.toNat >= 0x50 && op0.toNat <= 0x5F) then
      some 1
    else if op0 == 0xEB#8 || op0 == 0xA8#8 ||
            (op0.toNat >= 0x70 && op0.toNat <= 0x7F) ||
            (op0.toNat >= 0xB0 && op0.toNat <= 0xB7) then
      some 2
    else if op0 == 0xE9#8 then
      some 5
    else if op0.toNat >= 0xB8 && op0.toNat <= 0xBF then
      if rexW ps.rex then some 9 else if ps.has66 then some 3 else some 5
    else if op0 == 0x80#8 || op0 == 0x83#8 || op0 == 0xC0#8 || op0 == 0xC1#8 ||
            op0 == 0xC6#8 || op0 == 0x6B#8 || op0 == 0xF6#8 then
      Option.map (· + 2) (modrmByteLen rest0)
    else if op0 == 0x81#8 || op0 == 0xC7#8 || op0 == 0x69#8 then
      let immSz := if ps.has66 && !rexW ps.rex then 2 else 4
      Option.map (· + 1 + immSz) (modrmByteLen rest0)
    else if op0 == 0x0F#8 then
      match rest0 with
      | [] => none
      | op1 :: rest1 =>
        if op1 == 0x0B#8 then some 2
        else if op1.toNat >= 0x80 && op1.toNat <= 0x8F then some 6
        else if op1 == 0x70#8 || op1 == 0x71#8 || op1 == 0x72#8 || op1 == 0x73#8 then
          Option.map (· + 3) (modrmByteLen rest1)
        else
          Option.map (· + 2) (modrmByteLen rest1)
    else
      Option.map (· + 1) (modrmByteLen rest0)

def parseModRm (rBit xBit bBit : Bool) :
    List (BitVec 8) → Option (Nat × X64Rm × BitVec 8 × List (BitVec 8))
  | [] => none
  | mrm :: rest =>
    let mod2 := (BitVec.extractLsb' 6 2 mrm).toNat
    let reg3 := BitVec.extractLsb' 3 3 mrm
    let rm3  := BitVec.extractLsb' 0 3 mrm
    let regIdx := mkRegIdx rBit reg3
    let rmIdx  := mkRegIdx bBit rm3
    if mod2 == 3 then
      some (regIdx, .reg (regOfNat rmIdx), mrm, rest)
    else if rm3.toNat == 4 then
      match rest with
      | [] => none
      | sib :: restSib =>
        let scale2 := (BitVec.extractLsb' 6 2 sib).toNat
        let idx3   := BitVec.extractLsb' 3 3 sib
        let base3  := BitVec.extractLsb' 0 3 sib
        let idxFull := mkRegIdx xBit idx3
        let baseFull := mkRegIdx bBit base3
        let indexOpt : Option (Reg × Nat) :=
          if idxFull == 4 then none else some (regOfNat idxFull, scale2)
        if mod2 == 0 && base3.toNat == 5 then
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := none, index := indexOpt, disp := sext32To64 d32 }, mrm, restD)
        else if mod2 == 0 then
          some (regIdx, .mem { base := some (regOfNat baseFull), index := indexOpt, disp := 0#64 }, mrm, restSib)
        else if mod2 == 1 then
          match restSib with
          | [] => none
          | d8 :: restD =>
            some (regIdx, .mem { base := some (regOfNat baseFull), index := indexOpt, disp := sext8To64 d8 }, mrm, restD)
        else
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := some (regOfNat baseFull), index := indexOpt, disp := sext32To64 d32 }, mrm, restD)
    else if mod2 == 0 && rm3.toNat == 5 then
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := none, index := none, disp := sext32To64 d32, ripRel := true }, mrm, restD)
    else if mod2 == 0 then
      some (regIdx, .mem { base := some (regOfNat rmIdx), index := none, disp := 0#64 }, mrm, rest)
    else if mod2 == 1 then
      match rest with
      | [] => none
      | d8 :: restD =>
        some (regIdx, .mem { base := some (regOfNat rmIdx), index := none, disp := sext8To64 d8 }, mrm, restD)
    else
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := some (regOfNat rmIdx), index := none, disp := sext32To64 d32 }, mrm, restD)

def rmToRm8 (rexPresent bBit : Bool) (mrmByte : BitVec 8) : X64Rm → X64Rm8
  | .reg _ => .reg8 (subReg8OfIdx rexPresent bBit (BitVec.extractLsb' 0 3 mrmByte))
  | .mem a => .mem8 a

def rmToXmm (bBit : Bool) (mrmByte : BitVec 8) : X64Rm → X64XmmRm
  | .reg _ => .reg (ymmIdxOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 mrmByte)))
  | .mem a => .mem a

def parseSimdOpc (isVex rBit xBit bBit wBit lBit : Bool) (vvvv : Nat)
    (mapSel pp : Nat) (opc : BitVec 8) (afterOpc : List (BitVec 8)) :
    Except DecodeFault X64Instr :=
  let mode : SimdMode := if !isVex then .legacy128 else if lBit then .vex256 else .vex128
  if isVex && mapSel == 1 && opc == 0x77#8 then
    if pp == 0 && !lBit && vvvv == 0 then .ok .vzeroupper else .error .udVexField
  else
    match parseModRm rBit xBit bBit afterOpc with
    | none => .error .udUnmapped
    | some (regIdx, rm, mrm, tail) =>
      let regY  := ymmIdxOfNat regIdx
      let vvvvY := ymmIdxOfNat vvvv
      let s1Y   := if isVex then vvvvY else regY
      let xrm   := rmToXmm bBit mrm rm
      let noVvvv := !isVex || vvvv == 0
      if mapSel == 1 then
        if opc == 0x10#8 && pp == 0 && noVvvv then .ok (.simdMovLoad mode regY xrm)
        else if opc == 0x11#8 && pp == 0 && noVvvv then .ok (.simdMovStore mode xrm regY)
        else if opc == 0x6F#8 && (pp == 1 || pp == 2) && noVvvv then .ok (.simdMovLoad mode regY xrm)
        else if opc == 0x7F#8 && (pp == 1 || pp == 2) && noVvvv then .ok (.simdMovStore mode xrm regY)
        else if opc == 0x7E#8 && pp == 2 && !lBit && noVvvv then .ok (.simdMovqLoad isVex regY xrm)
        else if opc == 0xD6#8 && pp == 1 && !lBit && noVvvv then .ok (.simdMovqStore isVex xrm regY)
        else if opc == 0x6E#8 && pp == 1 && !lBit && noVvvv then .ok (.simdMovGprToX isVex wBit regY rm)
        else if opc == 0x7E#8 && pp == 1 && !lBit && noVvvv then .ok (.simdMovXToGpr isVex wBit rm regY)
        else if (opc == 0xEF#8 && pp == 1) || (opc == 0x57#8 && pp == 0) then .ok (.simdBitwise mode .xor regY s1Y xrm)
        else if (opc == 0xDB#8 && pp == 1) || (opc == 0x54#8 && pp == 0) then .ok (.simdBitwise mode .and regY s1Y xrm)
        else if (opc == 0xEB#8 && pp == 1) || (opc == 0x56#8 && pp == 0) then .ok (.simdBitwise mode .or  regY s1Y xrm)
        else if opc == 0xFC#8 && pp == 1 then .ok (.simdAdd mode .e8  regY s1Y xrm)
        else if opc == 0xFD#8 && pp == 1 then .ok (.simdAdd mode .e16 regY s1Y xrm)
        else if opc == 0xFE#8 && pp == 1 then .ok (.simdAdd mode .e32 regY s1Y xrm)
        else if opc == 0xD4#8 && pp == 1 then .ok (.simdAdd mode .e64 regY s1Y xrm)
        else if opc == 0xF8#8 && pp == 1 then .ok (.simdSub mode .e8  regY s1Y xrm)
        else if opc == 0xF9#8 && pp == 1 then .ok (.simdSub mode .e16 regY s1Y xrm)
        else if opc == 0xFA#8 && pp == 1 then .ok (.simdSub mode .e32 regY s1Y xrm)
        else if opc == 0xFB#8 && pp == 1 then .ok (.simdSub mode .e64 regY s1Y xrm)
        else if opc == 0x74#8 && pp == 1 then .ok (.simdCmpeq mode .e8  regY s1Y xrm)
        else if opc == 0x75#8 && pp == 1 then .ok (.simdCmpeq mode .e16 regY s1Y xrm)
        else if opc == 0x76#8 && pp == 1 then .ok (.simdCmpeq mode .e32 regY s1Y xrm)
        else if opc == 0x64#8 && pp == 1 then .ok (.simdCmpgt mode .e8  regY s1Y xrm)
        else if opc == 0x66#8 && pp == 1 then .ok (.simdCmpgt mode .e32 regY s1Y xrm)
        else if opc == 0x60#8 && pp == 1 then .ok (.simdUnpack mode .lbw  regY s1Y xrm)
        else if opc == 0x68#8 && pp == 1 then .ok (.simdUnpack mode .hbw  regY s1Y xrm)
        else if opc == 0x61#8 && pp == 1 then .ok (.simdUnpack mode .lwd  regY s1Y xrm)
        else if opc == 0x69#8 && pp == 1 then .ok (.simdUnpack mode .hwd  regY s1Y xrm)
        else if opc == 0x62#8 && pp == 1 then .ok (.simdUnpack mode .ldq  regY s1Y xrm)
        else if opc == 0x6A#8 && pp == 1 then .ok (.simdUnpack mode .hdq  regY s1Y xrm)
        else if opc == 0x6C#8 && pp == 1 then .ok (.simdUnpack mode .lqdq regY s1Y xrm)
        else if opc == 0x6D#8 && pp == 1 then .ok (.simdUnpack mode .hqdq regY s1Y xrm)
        else if opc == 0xD5#8 && pp == 1 then .ok (.simdPmullw  mode regY s1Y xrm)
        else if opc == 0xE4#8 && pp == 1 then .ok (.simdPmulhuw mode regY s1Y xrm)
        else if opc == 0xF5#8 && pp == 1 then .ok (.simdPmaddwd mode regY s1Y xrm)
        else if opc == 0x70#8 then
          match tail with
          | imm8 :: _ =>
            if !noVvvv then .error .udVexField
            else if pp == 1 then .ok (.simdPshufd  mode regY xrm imm8)
            else if pp == 3 then .ok (.simdPshuflw mode regY xrm imm8)
            else .error .udUnmapped
          | [] => .error .udUnmapped
        else if opc == 0x73#8 && pp == 1 then
          match xrm, tail with
          | .reg srcY, imm8 :: _ =>
            let dstY := if isVex then vvvvY else srcY
            let subop := (BitVec.extractLsb' 3 3 mrm).toNat
            if subop == 3 then .ok (.simdPsrldq mode dstY srcY imm8)
            else if subop == 2 then .ok (.simdPsrlqImm mode dstY srcY imm8)
            else .error .udUnmapped
          | _, _ => .error .udUnmapped
        else .error .udUnmapped
      else if isVex && mapSel == 2 && pp == 1 then
        if !noVvvv && opc != 0x40#8 then .error .udVexField
        else if opc == 0x30#8 then .ok (.simdExtend mode .zxbw regY xrm)
        else if opc == 0x33#8 then .ok (.simdExtend mode .zxwd regY xrm)
        else if opc == 0x35#8 then .ok (.simdExtend mode .zxdq regY xrm)
        else if opc == 0x20#8 then .ok (.simdExtend mode .sxbw regY xrm)
        else if opc == 0x23#8 then .ok (.simdExtend mode .sxwd regY xrm)
        else if opc == 0x25#8 then .ok (.simdExtend mode .sxdq regY xrm)
        else if opc == 0x78#8 then .ok (.simdBroadcastB mode regY xrm)
        else if opc == 0x59#8 then .ok (.simdBroadcastQ mode regY xrm)
        else if opc == 0x40#8 then .ok (.simdPmulld mode regY vvvvY xrm)
        else .error .udUnmapped
      else if isVex && mapSel == 3 && pp == 1 then
        match tail with
        | imm8 :: _ =>
          if (opc == 0x39#8 || opc == 0x19#8) && lBit && vvvv == 0 then
            .ok (.simdExtract128 xrm regY imm8)
          else if (opc == 0x46#8 || opc == 0x06#8) && lBit then
            .ok (.simdPerm2i128 regY vvvvY xrm imm8)
          else .error .udVexField
        | [] => .error .udUnmapped
      else .error .udUnmapped

def parseExactBody (ps : PrefixState) (bodySlice : List (BitVec 8)) : Except DecodeFault X64Instr :=
  let rBit := rexR ps.rex
  let xBit := rexX ps.rex
  let bBit := rexB ps.rex
  let wBit := rexW ps.rex
  let rexP := ps.rex.isSome
  let sz   := opSizeOf ps
  match bodySlice with
  | [] => .error .udUnmapped
  | op0 :: rest0 =>
    if op0 == 0xC5#8 then
      if ps.hasLock || ps.has66 || ps.rep != .none || rexP then .error .udVexPrefix
      else match rest0 with
      | b1 :: opc :: afterOpc =>
        let vR   := !(b1.getLsbD 7)
        let vvvv := (~~~(BitVec.extractLsb' 3 4 b1)).toNat
        let vL   := b1.getLsbD 2
        let pp   := (BitVec.extractLsb' 0 2 b1).toNat
        parseSimdOpc true vR false false false vL vvvv 1 pp opc afterOpc
      | _ => .error .udUnmapped
    else if op0 == 0xC4#8 then
      if ps.hasLock || ps.has66 || ps.rep != .none || rexP then .error .udVexPrefix
      else match rest0 with
      | b1 :: b2 :: opc :: afterOpc =>
        let vR     := !(b1.getLsbD 7)
        let vX     := !(b1.getLsbD 6)
        let vB     := !(b1.getLsbD 5)
        let mapSel := (BitVec.extractLsb' 0 5 b1).toNat
        let vW     := b2.getLsbD 7
        let vvvv   := (~~~(BitVec.extractLsb' 3 4 b2)).toNat
        let vL     := b2.getLsbD 2
        let pp     := (BitVec.extractLsb' 0 2 b2).toNat
        parseSimdOpc true vR vX vB vW vL vvvv mapSel pp opc afterOpc
      | _ => .error .udUnmapped
    else if ps.hasLock then .error .udIllegalLock
    else if op0 == 0x90#8 then
      if bBit then .ok (.xchg sz (regOfNat 8) (.reg .rax)) else .ok .nop
    else if op0 == 0xC3#8 then .ok .ret64
    else if op0 == 0xC9#8 then .ok .leave64
    else if op0 == 0xFA#8 then .error .gp0Privilege
    else if op0.toNat >= 0x50 && op0.toNat <= 0x57 then
      .ok (.push64 (regOfNat ((if bBit then 8 else 0) + (op0.toNat - 0x50))))
    else if op0.toNat >= 0x58 && op0.toNat <= 0x5F then
      .ok (.pop64 (regOfNat ((if bBit then 8 else 0) + (op0.toNat - 0x58))))
    else if op0 == 0xEB#8 then
      match rest0 with | d8 :: _ => .ok (.jmpRel (sext8To64 d8)) | [] => .error .udUnmapped
    else if op0 == 0xE9#8 then
      match readLe32? rest0 with | some (d32, _) => .ok (.jmpRel (sext32To64 d32)) | none => .error .udUnmapped
    else if op0.toNat >= 0x70 && op0.toNat <= 0x7F then
      match rest0 with | d8 :: _ => .ok (.jccRel (condOfNib (op0.toNat - 0x70)) (sext8To64 d8)) | [] => .error .udUnmapped
    else if op0 == 0xA8#8 then
      match rest0 with | imm8 :: _ => .ok (.alu8Imm .test (.reg8 (.lo8 .rax)) imm8) | [] => .error .udUnmapped
    else if op0.toNat >= 0xB0 && op0.toNat <= 0xB7 then
      match rest0 with
      | imm8 :: _ => .ok (.mov8Imm (.reg8 (subReg8OfIdx rexP bBit (BitVec.ofNat 3 (op0.toNat - 0xB0)))) imm8)
      | [] => .error .udUnmapped
    else if op0.toNat >= 0xB8 && op0.toNat <= 0xBF then
      let dst := regOfNat ((if bBit then 8 else 0) + (op0.toNat - 0xB8))
      if wBit then
        match readLe64? rest0 with | some (imm64, _) => .ok (.movImm .s64 dst imm64) | none => .error .udUnmapped
      else if ps.has66 then
        match readLe16? rest0 with | some (imm16, _) => .ok (.movImm .s16 dst (imm16.zeroExtend 64)) | none => .error .udUnmapped
      else
        match readLe32? rest0 with | some (imm32, _) => .ok (.movImm .s32 dst (imm32.zeroExtend 64)) | none => .error .udUnmapped
    else if op0 == 0x0F#8 then
      match rest0 with
      | [] => .error .udUnmapped
      | op1 :: rest1 =>
        if op1 == 0x0B#8 then .error .udExplicit
        else if op1.toNat >= 0x80 && op1.toNat <= 0x8F then
          match readLe32? rest1 with | some (d32, _) => .ok (.jccRel (condOfNib (op1.toNat - 0x80)) (sext32To64 d32)) | none => .error .udUnmapped
        else if op1 == 0x1E#8 then
          match parseModRm rBit xBit bBit rest1 with
          | some (_, _, mrm, _) => if ps.rep == .repz && mrm == 0xFA#8 then .ok .endbr64 else .ok .nop
          | none => .error .udUnmapped
        else if op1 == 0x1F#8 then
          match parseModRm rBit xBit bBit rest1 with | some _ => .ok .nop | none => .error .udUnmapped
        else if op1 == 0xB6#8 || op1 == 0xB7#8 || op1 == 0xBE#8 || op1 == 0xBF#8 ||
                op1 == 0xAF#8 || op1 == 0xBC#8 || (op1.toNat >= 0x90 && op1.toNat <= 0x9F) then
          match parseModRm rBit xBit bBit rest1 with
          | none => .error .udUnmapped
          | some (regIdx, rm, mrm, _) =>
            let dst := regOfNat regIdx
            let rm8 := rmToRm8 rexP bBit mrm rm
            if op1 == 0xB6#8 then .ok (.movzx8 sz dst rm8)
            else if op1 == 0xB7#8 then .ok (.movzx16 sz dst rm)
            else if op1 == 0xBE#8 then .ok (.movsx8 sz dst rm8)
            else if op1 == 0xBF#8 then .ok (.movsx16 sz dst rm)
            else if op1 == 0xAF#8 then .ok (.imul2 sz dst rm)
            else if op1 == 0xBC#8 then .ok (.bsf sz dst rm)
            else .ok (.setcc8 (condOfNib (op1.toNat - 0x90)) rm8)
        else
          let pp := match ps.rep with | .repz => 2 | .repnz => 3 | .none => if ps.has66 then 1 else 0
          parseSimdOpc false rBit xBit bBit wBit false 0 1 pp op1 rest1
    else
      match parseModRm rBit xBit bBit rest0 with
      | none => .error .udUnmapped
      | some (regIdx, rm, mrm, tail) =>
        let regG := regOfNat regIdx
        let reg3 := BitVec.extractLsb' 3 3 mrm
        let r8   := subReg8OfIdx rexP rBit reg3
        let rm8  := rmToRm8 rexP bBit mrm rm
        if op0 == 0x88#8 then .ok (.mov8Store rm8 r8)
        else if op0 == 0x8A#8 then .ok (.mov8Load r8 rm8)
        else if op0 == 0x89#8 then .ok (.movStore sz rm regG)
        else if op0 == 0x8B#8 then .ok (.movLoad sz regG rm)
        else if op0 == 0xC6#8 && reg3.toNat == 0 then
          match tail with | imm8 :: _ => .ok (.mov8Imm rm8 imm8) | [] => .error .udUnmapped
        else if op0 == 0xC7#8 && reg3.toNat == 0 then
          if sz == .s16 then
            match readLe16? tail with | some (i16, _) => .ok (.movRmImm32 .s16 rm (i16.zeroExtend 64)) | none => .error .udUnmapped
          else
            match readLe32? tail with | some (i32, _) => .ok (.movRmImm32 sz rm (sext32To64 i32)) | none => .error .udUnmapped
        else if op0 == 0x8D#8 then
          match rm with | .mem a => .ok (.lea sz regG a) | .reg _ => .error .udRegisterOperand
        else if op0 == 0x63#8 then
          if wBit then .ok (.movsxd regG rm) else .ok (.movLoad .s32 regG rm)
        else if op0 == 0x87#8 then .ok (.xchg sz regG rm)
        else if op0 == 0x84#8 then .ok (.alu8RmReg .test rm8 r8)
        else if op0 == 0x85#8 then .ok (.aluRmReg sz .test rm regG)
        else if op0 == 0xF6#8 && reg3.toNat == 0 then
          match tail with | imm8 :: _ => .ok (.alu8Imm .test rm8 imm8) | [] => .error .udUnmapped
        else if op0 == 0x80#8 then
          match aluOpOfIdx reg3.toNat, tail with | some op, imm8 :: _ => .ok (.alu8Imm op rm8 imm8) | _, _ => .error .udUnmapped
        else if op0 == 0x83#8 then
          match aluOpOfIdx reg3.toNat, tail with | some op, imm8 :: _ => .ok (.aluImm sz op rm (sext8To64 imm8)) | _, _ => .error .udUnmapped
        else if op0 == 0x81#8 then
          match aluOpOfIdx reg3.toNat with
          | none => .error .udUnmapped
          | some op =>
            if sz == .s16 then
              match readLe16? tail with | some (i16, _) => .ok (.aluImm .s16 op rm (i16.zeroExtend 64)) | none => .error .udUnmapped
            else
              match readLe32? tail with | some (i32, _) => .ok (.aluImm sz op rm (sext32To64 i32)) | none => .error .udUnmapped
        else if op0 == 0x6B#8 then
          match tail with | imm8 :: _ => .ok (.imul3 sz regG rm (sext8To64 imm8)) | [] => .error .udUnmapped
        else if op0 == 0x69#8 then
          if sz == .s16 then
            match readLe16? tail with | some (i16, _) => .ok (.imul3 .s16 regG rm (sext16To64 i16)) | none => .error .udUnmapped
          else
            match readLe32? tail with | some (i32, _) => .ok (.imul3 sz regG rm (sext32To64 i32)) | none => .error .udUnmapped
        else if op0 == 0xC0#8 || op0 == 0xC1#8 then
          match shiftOpOfIdx reg3.toNat, tail with
          | some sop, imm8 :: _ => if op0 == 0xC1#8 then .ok (.shiftImm sz sop rm imm8) else .error .udUnmapped
          | _, _ => .error .udUnmapped
        else if op0 == 0xD1#8 then
          match shiftOpOfIdx reg3.toNat with | some sop => .ok (.shiftImm sz sop rm 1#8) | none => .error .udUnmapped
        else if op0 == 0xF7#8 then
          if reg3.toNat == 2 then .ok (.unaryRm sz .not rm)
          else if reg3.toNat == 3 then .ok (.unaryRm sz .neg rm)
          else .error .udUnmapped
        else if op0 == 0xFF#8 then
          if reg3.toNat == 0 then .ok (.unaryRm sz .inc rm)
          else if reg3.toNat == 1 then .ok (.unaryRm sz .dec rm)
          else .error .udUnmapped
        else
          let hi5 := op0.toNat / 8
          let lo3 := op0.toNat % 8
          match aluOpOfIdx hi5 with
          | none => .error .udUnmapped
          | some aop =>
            if lo3 == 0 then .ok (.alu8RmReg aop rm8 r8)
            else if lo3 == 1 then .ok (.aluRmReg sz aop rm regG)
            else if lo3 == 2 then .ok (.alu8RegRm aop r8 rm8)
            else if lo3 == 3 then .ok (.aluRegRm sz aop regG rm)
            else .error .udUnmapped

/-- Variable-length (`1..15` byte) two-stage decoder `decodeX64`:
    decodes both standalone basic-block byte slices and 16-byte fetch windows. -/
def decodeX64 (bs : List (BitVec 8)) : DecodeOutcome :=
  let (ps, body) := scanPrefixes 16 {} bs
  if ps.count >= 15 && body.isEmpty then
    .fault .gp0LengthExceeds15
  else if ps.count > 14 then
    .fault .gp0LengthExceeds15
  else if body.isEmpty then
    .fault .truncated
  else
    match ildBodyLen ps body with
    | none => .fault .udUnmapped
    | some bLen =>
      if ps.count + bLen > 15 then
        .fault .gp0LengthExceeds15
      else if (body.take bLen).length < bLen then
        .fault .truncated
      else
        match parseExactBody ps (body.take bLen) with
        | .error fk => .fault fk
        | .ok ins   => .ok ins (ps.count + bLen)

/-! ### Universal Prefix-Invariance (`decodeX64_prefix_invariant`) -/

theorem stepPrefix_count {s s' : PrefixState} {b : BitVec 8}
    (h : stepPrefix s b = some s') : s'.count = s.count + 1 := by
  unfold stepPrefix at h
  split at h
  · injection h with h'; rw [← h']
  · split at h
    · injection h with h'; rw [← h']
    · split at h
      · injection h with h'; rw [← h']
      · split at h
        · injection h with h'; rw [← h']
        · split at h
          · injection h with h'; rw [← h']
          · split at h
            · injection h with h'; rw [← h']
            · nomatch h

theorem scanPrefixes_succ_cons (k : Nat) (st : PrefixState) (b : BitVec 8) (rest : List (BitVec 8)) :
    scanPrefixes (k + 1) st (b :: rest) =
      match stepPrefix st b with
      | some s' => scanPrefixes k s' rest
      | none    => (st, b :: rest) := rfl

theorem scanPrefixes_count_inv (fuel : Nat) :
    ∀ (st : PrefixState) (bs : List (BitVec 8)),
      let (ps, rem) := scanPrefixes fuel st bs
      ps.count + rem.length = st.count + bs.length := by
  induction fuel with
  | zero => intro st bs; rfl
  | succ k ih =>
    intro st bs
    cases bs with
    | nil => rfl
    | cons b rest =>
      rw [scanPrefixes_succ_cons]
      cases hstep : stepPrefix st b with
      | none => rfl
      | some s' =>
        have hc := stepPrefix_count hstep
        have h := ih s' rest
        dsimp at h ⊢
        omega

theorem scanPrefixes_append_nonempty (fuel : Nat) :
    ∀ (st : PrefixState) (pfx sfx : List (BitVec 8)) (ps : PrefixState)
      (op0 : BitVec 8) (rest0 : List (BitVec 8)),
      scanPrefixes fuel st pfx = (ps, op0 :: rest0) →
      scanPrefixes fuel st (pfx ++ sfx) = (ps, op0 :: (rest0 ++ sfx)) := by
  induction fuel with
  | zero =>
    intro st pfx sfx ps op0 rest0 h
    dsimp [scanPrefixes] at h ⊢
    injection h with hps hrem
    rw [hps, hrem]; rfl
  | succ k ih =>
    intro st pfx sfx ps op0 rest0 h
    cases pfx with
    | nil => dsimp [scanPrefixes] at h; injection h with _ hrem; nomatch hrem
    | cons b rest =>
      dsimp only [List.cons_append]
      rw [scanPrefixes_succ_cons] at h ⊢
      cases hstep : stepPrefix st b with
      | none =>
        rw [hstep] at h
        injection h with hps hrem
        injection hrem with hb hrest
        subst hps hb hrest; rfl
      | some s' =>
        rw [hstep] at h
        exact ih s' rest sfx ps op0 rest0 h

theorem modrmByteLen_append {xs sfx : List (BitVec 8)} {mLen : Nat}
    (hm : modrmByteLen xs = some mLen) (hle : mLen ≤ xs.length) :
    modrmByteLen (xs ++ sfx) = some mLen := by
  cases xs with
  | nil => nomatch hm
  | cons mrm rest =>
    dsimp only [modrmByteLen, List.cons_append] at hm ⊢
    by_cases hmod : (BitVec.extractLsb' 6 2 mrm).toNat == 3
    · simp only [hmod, ite_true] at hm ⊢; exact hm
    · simp only [hmod, Bool.false_eq_true, ite_false] at hm ⊢
      by_cases hrm4 : (BitVec.extractLsb' 0 3 mrm).toNat == 4
      · simp only [hrm4, ite_true] at hm ⊢
        cases rest with
        | nil => nomatch hm
        | cons sib _ => exact hm
      · simp only [hrm4, Bool.false_eq_true, ite_false] at hm ⊢; exact hm

theorem ildVexBodyLen_append {mapSel : Nat} {xs sfx : List (BitVec 8)} {vLen : Nat}
    (hv : ildVexBodyLen mapSel xs = some vLen) (hle : vLen ≤ xs.length) :
    ildVexBodyLen mapSel (xs ++ sfx) = some vLen := by
  cases xs with
  | nil => nomatch hv
  | cons opc afterOpc =>
    dsimp only [ildVexBodyLen, List.cons_append] at hv ⊢
    by_cases h77 : (mapSel == 1 && opc == 0x77#8) = true
    · simp only [h77, ite_true] at hv ⊢; exact hv
    · have h77f : (mapSel == 1 && opc == 0x77#8) = false := Bool.eq_false_iff.mpr h77
      simp only [h77f, Bool.false_eq_true, ite_false] at hv ⊢
      cases hm : modrmByteLen afterOpc with
      | none => rw [hm] at hv; nomatch hv
      | some mLen =>
        rw [hm] at hv
        dsimp only at hv
        injection hv with hvEq
        rw [← hvEq] at hle
        simp only [List.length_cons] at hle
        have hmle : mLen ≤ afterOpc.length := by omega
        rw [modrmByteLen_append hm hmle]
        dsimp only
        rw [hvEq]

theorem ildBodyLen_append (ps : PrefixState) {body sfx : List (BitVec 8)} {bLen : Nat}
    (hb : ildBodyLen ps body = some bLen) (hle : bLen ≤ body.length) :
    ildBodyLen ps (body ++ sfx) = some bLen := by
  cases body with
  | nil => nomatch hb
  | cons op0 rest0 =>
    dsimp only [ildBodyLen, List.cons_append] at hb ⊢
    by_cases hc5 : op0 == 0xC5#8
    · simp only [hc5, ite_true] at hb ⊢
      cases rest0 with
      | nil => nomatch hb
      | cons b1 afterHdr =>
        dsimp only [List.cons_append] at hb ⊢
        cases hv : ildVexBodyLen 1 afterHdr with
        | none => rw [hv] at hb; nomatch hb
        | some vLen =>
          rw [hv] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
          rw [← hbEq] at hle; simp only [List.length_cons] at hle
          have hvle : vLen ≤ afterHdr.length := by omega
          rw [ildVexBodyLen_append hv hvle]; dsimp only [Option.map]; rw [hbEq]
    · simp only [hc5, Bool.false_eq_true, ite_false] at hb ⊢
      by_cases hc4 : op0 == 0xC4#8
      · simp only [hc4, ite_true] at hb ⊢
        cases rest0 with
        | nil => nomatch hb
        | cons b1 r1 =>
          cases r1 with
          | nil => nomatch hb
          | cons b2 afterHdr =>
            dsimp only [List.cons_append] at hb ⊢
            cases hv : ildVexBodyLen (BitVec.extractLsb' 0 5 b1).toNat afterHdr with
            | none => rw [hv] at hb; nomatch hb
            | some vLen =>
              rw [hv] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
              rw [← hbEq] at hle; simp only [List.length_cons] at hle
              have hvle : vLen ≤ afterHdr.length := by omega
              rw [ildVexBodyLen_append hv hvle]; dsimp only [Option.map]; rw [hbEq]
      · simp only [hc4, Bool.false_eq_true, ite_false] at hb ⊢
        by_cases h1 : (op0 == 0x90#8 || op0 == 0xC3#8 || op0 == 0xC9#8 || op0 == 0xFA#8 || (op0.toNat >= 0x50 && op0.toNat <= 0x5F)) = true
        · simp only [h1, ite_true] at hb ⊢; exact hb
        · have h1f := Bool.eq_false_iff.mpr h1; simp only [h1f, Bool.false_eq_true, ite_false] at hb ⊢
          by_cases h2 : (op0 == 0xEB#8 || op0 == 0xA8#8 || (op0.toNat >= 0x70 && op0.toNat <= 0x7F) || (op0.toNat >= 0xB0 && op0.toNat <= 0xB7)) = true
          · simp only [h2, ite_true] at hb ⊢; exact hb
          · have h2f := Bool.eq_false_iff.mpr h2; simp only [h2f, Bool.false_eq_true, ite_false] at hb ⊢
            by_cases h3 : op0 == 0xE9#8
            · simp only [h3, ite_true] at hb ⊢; exact hb
            · simp only [h3, Bool.false_eq_true, ite_false] at hb ⊢
              by_cases h4 : (op0.toNat >= 0xB8 && op0.toNat <= 0xBF) = true
              · simp only [h4, ite_true] at hb ⊢; exact hb
              · have h4f := Bool.eq_false_iff.mpr h4; simp only [h4f, Bool.false_eq_true, ite_false] at hb ⊢
                by_cases h5 : (op0 == 0x80#8 || op0 == 0x83#8 || op0 == 0xC0#8 || op0 == 0xC1#8 || op0 == 0xC6#8 || op0 == 0x6B#8 || op0 == 0xF6#8) = true
                · simp only [h5, ite_true] at hb ⊢
                  cases hm : modrmByteLen rest0 with
                  | none => rw [hm] at hb; nomatch hb
                  | some mLen =>
                    rw [hm] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
                    rw [← hbEq] at hle; simp only [List.length_cons] at hle
                    rw [modrmByteLen_append hm (by omega)]; dsimp only [Option.map]; rw [hbEq]
                · have h5f := Bool.eq_false_iff.mpr h5; simp only [h5f, Bool.false_eq_true, ite_false] at hb ⊢
                  by_cases h6 : (op0 == 0x81#8 || op0 == 0xC7#8 || op0 == 0x69#8) = true
                  · simp only [h6, ite_true] at hb ⊢
                    cases hm : modrmByteLen rest0 with
                    | none => rw [hm] at hb; nomatch hb
                    | some mLen =>
                      rw [hm] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
                      rw [← hbEq] at hle; simp only [List.length_cons] at hle
                      have hmle : mLen ≤ rest0.length := by
                        by_cases h16 : (ps.has66 && !rexW ps.rex) = true
                        · rw [ifTrue h16] at hle; omega
                        · rw [ifFalse h16] at hle; omega
                      rw [modrmByteLen_append hm hmle]; dsimp only [Option.map]; rw [hbEq]
                  · have h6f := Bool.eq_false_iff.mpr h6; simp only [h6f, Bool.false_eq_true, ite_false] at hb ⊢
                    by_cases h7 : op0 == 0x0F#8
                    · simp only [h7, ite_true] at hb ⊢
                      cases rest0 with
                      | nil => nomatch hb
                      | cons op1 rest1 =>
                        dsimp only [List.cons_append] at hb ⊢
                        by_cases h0b : op1 == 0x0B#8
                        · simp only [h0b, ite_true] at hb ⊢; exact hb
                        · simp only [h0b, Bool.false_eq_true, ite_false] at hb ⊢
                          by_cases hjcc : (op1.toNat >= 0x80 && op1.toNat <= 0x8F) = true
                          · simp only [hjcc, ite_true] at hb ⊢; exact hb
                          · have hjccf := Bool.eq_false_iff.mpr hjcc; simp only [hjccf, Bool.false_eq_true, ite_false] at hb ⊢
                            by_cases h70 : (op1 == 0x70#8 || op1 == 0x71#8 || op1 == 0x72#8 || op1 == 0x73#8) = true
                            · simp only [h70, ite_true] at hb ⊢
                              cases hm : modrmByteLen rest1 with
                              | none => rw [hm] at hb; nomatch hb
                              | some mLen =>
                                rw [hm] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
                                rw [← hbEq] at hle; simp only [List.length_cons] at hle
                                rw [modrmByteLen_append hm (by omega)]; dsimp only [Option.map]; rw [hbEq]
                            · have h70f := Bool.eq_false_iff.mpr h70; simp only [h70f, Bool.false_eq_true, ite_false] at hb ⊢
                              cases hm : modrmByteLen rest1 with
                              | none => rw [hm] at hb; nomatch hb
                              | some mLen =>
                                rw [hm] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
                                rw [← hbEq] at hle; simp only [List.length_cons] at hle
                                rw [modrmByteLen_append hm (by omega)]; dsimp only [Option.map]; rw [hbEq]
                    · simp only [h7, Bool.false_eq_true, ite_false] at hb ⊢
                      cases hm : modrmByteLen rest0 with
                      | none => rw [hm] at hb; nomatch hb
                      | some mLen =>
                        rw [hm] at hb; dsimp only [Option.map] at hb; injection hb with hbEq
                        rw [← hbEq] at hle; simp only [List.length_cons] at hle
                        rw [modrmByteLen_append hm (by omega)]; dsimp only [Option.map]; rw [hbEq]

/-- **Universal Variable-Length Decode Prefix-Invariance (`decodeX64_prefix_invariant`):**
    Any finite byte slice `pfx` that decodes to `.ok ins len` decodes identically
    when followed by any trailing instruction stream `sfx`, proved **without
    unfolding `parseExactBody`**. -/
theorem decodeX64_prefix_invariant {pfx : List (BitVec 8)} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 pfx = .ok ins len) (sfx : List (BitVec 8)) :
    decodeX64 (pfx ++ sfx) = .ok ins len := by
  unfold decodeX64 at hok ⊢
  cases hscan : scanPrefixes 16 {} pfx with
  | mk ps body =>
    rw [hscan] at hok
    cases body with
    | nil =>
      by_cases hc15 : ps.count >= 15
      · simp [hc15] at hok
      · by_cases hc14 : ps.count > 14
        · simp [hc15, hc14] at hok
        · simp [hc15, hc14] at hok
    | cons op0 rest0 =>
      have happ := scanPrefixes_append_nonempty 16 {} pfx sfx ps op0 rest0 hscan
      rw [happ]
      dsimp only [List.isEmpty] at hok ⊢
      simp only [Bool.and_false, Bool.false_eq_true, ite_false] at hok ⊢
      by_cases hc14 : ps.count > 14
      · rw [ifTrue hc14] at hok; nomatch hok
      · rw [ifFalse hc14] at hok ⊢
        cases hild : ildBodyLen ps (op0 :: rest0) with
        | none => rw [hild] at hok; nomatch hok
        | some bLen =>
          rw [hild] at hok
          dsimp only at hok
          by_cases h15 : ps.count + bLen > 15
          · rw [ifTrue h15] at hok; nomatch hok
          · rw [ifFalse h15] at hok
            by_cases htrunc : ((op0 :: rest0).take bLen).length < bLen
            · rw [ifTrue htrunc] at hok; nomatch hok
            · have hle : bLen ≤ (op0 :: rest0).length := by
                rw [List.length_take] at htrunc; omega
              have hild2 := ildBodyLen_append ps (sfx := sfx) hild hle
              dsimp only [List.cons_append] at hild2
              rw [hild2]
              dsimp only
              rw [ifFalse h15]
              have htake : ((op0 :: (rest0 ++ sfx)).take bLen) = (op0 :: rest0).take bLen := by
                have hcons : op0 :: (rest0 ++ sfx) = (op0 :: rest0) ++ sfx := rfl
                rw [hcons, List.take_append_of_le_length hle]
              rw [htake]
              exact hok

/-! ## Section 3: Balanced `ByteCodeTree` & Operational Execution (`stepX64`, `runX64`) -/

inductive ByteCodeTree where
  | leaf (bytes : List (BitVec 8))
  | node (leftSz : Nat) (left right : ByteCodeTree)

/-- Non-recursive eliminator lookup (`0` `._unsafe_rec` helpers). -/
def listGetByteD (bs : List (BitVec 8)) (idx : Nat) : BitVec 8 :=
  (Nat.rec (motive := fun _ => List (BitVec 8) → BitVec 8)
    (fun rem => match rem with | b :: _ => b | [] => 0xCC#8)
    (fun _ ih rem => match rem with | _ :: rest => ih rest | [] => 0xCC#8)
    idx bs)

def treeGetByteFuel (fuel : Nat) (t : ByteCodeTree) (off : Nat) : BitVec 8 :=
  Nat.rec (motive := fun _ => ByteCodeTree → Nat → BitVec 8)
    (fun _ _ => 0xCC#8)
    (fun _ ih tr i =>
      match tr with
      | .leaf bs => listGetByteD bs i
      | .node lsz l r => if Nat.blt i lsz then ih l i else ih r (Nat.sub i lsz))
    fuel t off

def treeGetByte (t : ByteCodeTree) (off : Nat) : BitVec 8 :=
  treeGetByteFuel 16 t off

structure X64ObjImage where
  codeBase   : BitVec 64 := 0#64
  totalBytes : Nat
  code       : ByteCodeTree

def objCodeMap (img : X64ObjImage) : CodeMap :=
  fun addr =>
    let off := (addr - img.codeBase).toNat
    if Nat.blt off img.totalBytes then treeGetByte img.code off else 0xCC#8

def fetchWindow16 (code : CodeMap) (rip : BitVec 64) : List (BitVec 8) :=
  [ code (rip + 0#64),  code (rip + 1#64),  code (rip + 2#64),  code (rip + 3#64),
    code (rip + 4#64),  code (rip + 5#64),  code (rip + 6#64),  code (rip + 7#64),
    code (rip + 8#64),  code (rip + 9#64),  code (rip + 10#64), code (rip + 11#64),
    code (rip + 12#64), code (rip + 13#64), code (rip + 14#64), code (rip + 15#64) ]

structure X64State where
  rip    : BitVec 64 := 0#64
  regs   : Reg → BitVec 64 := fun _ => 0#64
  ymms   : YmmIdx → BitVec 256 := fun _ => 0#256
  flags  : RFlags := {}
  mem    : ByteMem := fun _ => 0#8
  halted : Bool := false
  fault  : Bool := false

def parity8 (lo : BitVec 8) : Bool :=
  !(lo.getLsbD 0 ^^ lo.getLsbD 1 ^^ lo.getLsbD 2 ^^ lo.getLsbD 3 ^^
    lo.getLsbD 4 ^^ lo.getLsbD 5 ^^ lo.getLsbD 6 ^^ lo.getLsbD 7)

def evalCond (cc : Cond) (f : RFlags) : Bool :=
  match cc with
  | .o  => f.of  | .no => !f.of | .b  => f.cf  | .ae => !f.cf
  | .e  => f.zf  | .ne => !f.zf | .be => f.cf || f.zf | .a => !f.cf && !f.zf
  | .s  => f.sf  | .ns => !f.sf | .p  => f.pf  | .np => !f.pf
  | .l  => f.sf != f.of | .ge => f.sf == f.of
  | .le => f.zf || (f.sf != f.of) | .g => !f.zf && (f.sf == f.of)

def evalByteAddr (s : X64State) (nextRip : BitVec 64) (a : X64Addr) : BitVec 64 :=
  let baseV := if a.ripRel then nextRip else match a.base with | some r => s.regs r | none => 0#64
  let idxV  := match a.index with | some (r, sc) => (s.regs r) <<< sc | none => 0#64
  baseV + idxV + a.disp

def readByteRm8 (s : X64State) (nextRip : BitVec 64) : X64Rm8 → BitVec 8
  | .reg8 r => readSubReg8 s.regs r
  | .mem8 a => readMem8 s.mem (evalByteAddr s nextRip a)

def writeByteRm8 (s : X64State) (nextRip : BitVec 64) (dst : X64Rm8) (v : BitVec 8) : X64State :=
  match dst with
  | .reg8 r => { s with regs := writeSubReg8 s.regs r v }
  | .mem8 a => { s with mem := memUpd8 s.mem (evalByteAddr s nextRip a) v }

def readByteRm (sz : OpSize) (s : X64State) (nextRip : BitVec 64) : X64Rm → BitVec 64
  | .reg r => readRegSz sz s.regs r
  | .mem a =>
    let ea := evalByteAddr s nextRip a
    match sz with
    | .s64 => readMem64 s.mem ea
    | .s32 => (readMem32 s.mem ea).zeroExtend 64
    | .s16 => (readMem16 s.mem ea).zeroExtend 64

def writeByteRm (sz : OpSize) (s : X64State) (nextRip : BitVec 64) (dst : X64Rm) (v : BitVec 64) : X64State :=
  match dst with
  | .reg r => { s with regs := writeRegSz sz s.regs r v }
  | .mem a =>
    let ea := evalByteAddr s nextRip a
    match sz with
    | .s64 => { s with mem := writeMem64 s.mem ea v }
    | .s32 => { s with mem := writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v) }
    | .s16 => { s with mem := writeMem16 s.mem ea (BitVec.extractLsb' 0 16 v) }

def readByteXmm128 (s : X64State) (nextRip : BitVec 64) : X64XmmRm → BitVec 128
  | .reg y => BitVec.extractLsb' 0 128 (s.ymms y)
  | .mem a => readMem128 s.mem (evalByteAddr s nextRip a)

def readByteYmm256 (s : X64State) (nextRip : BitVec 64) : X64XmmRm → BitVec 256
  | .reg y => s.ymms y
  | .mem a => readMem256 s.mem (evalByteAddr s nextRip a)

def evalAluN {w : Nat} (hw : 0 < w) (op : AluOp) (a b : BitVec w) (oldF undefF : RFlags) :
    BitVec w × RFlags :=
  let cin : Nat := if oldF.cf then 1 else 0
  let _ := hw
  match op with
  | .add =>
    let res := a + b
    let cf  := a.toNat + b.toNat >= (2 ^ w)
    let af  := (a.toNat % 16) + (b.toNat % 16) >= 16
    let of  := (a.msb == b.msb) && (res.msb != a.msb)
    (res, { cf, pf := parity8 (BitVec.extractLsb' 0 8 res), af, zf := res == 0#w, sf := res.msb, of })
  | .adc =>
    let sum := a.toNat + b.toNat + cin
    let res := BitVec.ofNat w sum
    let cf  := sum >= (2 ^ w)
    let af  := (a.toNat % 16) + (b.toNat % 16) + cin >= 16
    let of  := (a.msb == b.msb) && (res.msb != a.msb)
    (res, { cf, pf := parity8 (BitVec.extractLsb' 0 8 res), af, zf := res == 0#w, sf := res.msb, of })
  | .sub | .cmp =>
    let res := a - b
    let cf  := a.toNat < b.toNat
    let af  := (a.toNat % 16) < (b.toNat % 16)
    let of  := (a.msb != b.msb) && (res.msb != a.msb)
    (if op == .cmp then a else res,
     { cf, pf := parity8 (BitVec.extractLsb' 0 8 res), af, zf := res == 0#w, sf := res.msb, of })
  | .sbb =>
    let borrow := b.toNat + cin
    let res := a - BitVec.ofNat w borrow
    let cf  := a.toNat < borrow
    let af  := (a.toNat % 16) < (b.toNat % 16) + cin
    let of  := (a.msb != b.msb) && (res.msb != a.msb)
    (res, { cf, pf := parity8 (BitVec.extractLsb' 0 8 res), af, zf := res == 0#w, sf := res.msb, of })
  | .and | .test =>
    let res := a &&& b
    (if op == .test then a else res,
     { cf := false, pf := parity8 (BitVec.extractLsb' 0 8 res), af := undefF.af,
       zf := res == 0#w, sf := res.msb, of := false })
  | .or =>
    let res := a ||| b
    (res, { cf := false, pf := parity8 (BitVec.extractLsb' 0 8 res), af := undefF.af,
            zf := res == 0#w, sf := res.msb, of := false })
  | .xor =>
    let res := a ^^^ b
    (res, { cf := false, pf := parity8 (BitVec.extractLsb' 0 8 res), af := undefF.af,
            zf := res == 0#w, sf := res.msb, of := false })

def evalAluSz (sz : OpSize) (op : AluOp) (a b : BitVec 64) (oldF undefF : RFlags) :
    BitVec 64 × RFlags :=
  match sz with
  | .s64 => evalAluN (by decide) op a b oldF undefF
  | .s32 =>
    let (r32, fl) := evalAluN (by decide) op (BitVec.extractLsb' 0 32 a) (BitVec.extractLsb' 0 32 b) oldF undefF
    (r32.zeroExtend 64, fl)
  | .s16 =>
    let (r16, fl) := evalAluN (by decide) op (BitVec.extractLsb' 0 16 a) (BitVec.extractLsb' 0 16 b) oldF undefF
    (r16.zeroExtend 64, fl)

def evalUnarySz (sz : OpSize) (op : UnaryOp) (v : BitVec 64) (oldF : RFlags) :
    BitVec 64 × RFlags :=
  match op with
  | .not => (~~~v, oldF)
  | .neg => let (res, fl) := evalAluSz sz .sub 0#64 v oldF oldF; (res, { fl with cf := !fl.zf })
  | .inc => let (res, fl) := evalAluSz sz .add v 1#64 oldF oldF; (res, { fl with cf := oldF.cf })
  | .dec => let (res, fl) := evalAluSz sz .sub v 1#64 oldF oldF; (res, { fl with cf := oldF.cf })

def evalShiftSz (sz : OpSize) (op : ShiftOp) (v : BitVec 64) (rawCnt : BitVec 8)
    (oldF undefF : RFlags) : BitVec 64 × RFlags :=
  let mask := if sz == .s64 then 63 else 31
  let c := rawCnt.toNat &&& mask
  if c == 0 then (v, oldF)
  else
    match sz with
    | .s64 =>
      let r64 : BitVec 64 := match op with
        | .rol => BitVec.rotateLeft v c  | .ror => BitVec.rotateRight v c
        | .shl => v <<< c                | .shr => v >>> c
        | .sar => BitVec.sshiftRight v c
      let cf := match op with
        | .rol => r64.getLsbD 0 | .ror => r64.msb
        | .shl => v.getLsbD (64 - c) | .shr | .sar => v.getLsbD (c - 1)
      let fl : RFlags := match op with
        | .rol | .ror => { oldF with cf, of := undefF.of }
        | _ => { cf, pf := parity8 (BitVec.extractLsb' 0 8 r64), af := undefF.af,
                 zf := r64 == 0#64, sf := r64.msb, of := undefF.of }
      (r64, fl)
    | .s32 =>
      let v32 := BitVec.extractLsb' 0 32 v
      let r32 : BitVec 32 := match op with
        | .rol => BitVec.rotateLeft v32 c  | .ror => BitVec.rotateRight v32 c
        | .shl => v32 <<< c                | .shr => v32 >>> c
        | .sar => BitVec.sshiftRight v32 c
      let cf := match op with
        | .rol => r32.getLsbD 0 | .ror => r32.msb
        | .shl => v32.getLsbD (32 - c) | .shr | .sar => v32.getLsbD (c - 1)
      let fl : RFlags := match op with
        | .rol | .ror => { oldF with cf, of := undefF.of }
        | _ => { cf, pf := parity8 (BitVec.extractLsb' 0 8 r32), af := undefF.af,
                 zf := r32 == 0#32, sf := r32.msb, of := undefF.of }
      (r32.zeroExtend 64, fl)
    | .s16 =>
      let v16 := BitVec.extractLsb' 0 16 v
      let r16 : BitVec 16 := match op with
        | .rol => BitVec.rotateLeft v16 (c % 16) | .ror => BitVec.rotateRight v16 (c % 16)
        | .shl => v16 <<< c                      | .shr => v16 >>> c
        | .sar => BitVec.sshiftRight v16 c
      (r16.zeroExtend 64, { undefF with zf := r16 == 0#16, sf := r16.msb })

def evalImulSz (sz : OpSize) (a b : BitVec 64) (undefF : RFlags) : BitVec 64 × RFlags :=
  match sz with
  | .s64 =>
    let prod : Int := a.toInt * b.toInt; let lo64 : BitVec 64 := a * b
    let ov := decide (prod != lo64.toInt)
    (lo64, { undefF with cf := ov, of := ov })
  | .s32 =>
    let a32 := BitVec.extractLsb' 0 32 a; let b32 := BitVec.extractLsb' 0 32 b
    let prod : Int := a32.toInt * b32.toInt; let lo32 : BitVec 32 := a32 * b32
    let ov := decide (prod != lo32.toInt)
    (lo32.zeroExtend 64, { undefF with cf := ov, of := ov })
  | .s16 =>
    let a16 := BitVec.extractLsb' 0 16 a; let b16 := BitVec.extractLsb' 0 16 b
    let prod : Int := a16.toInt * b16.toInt; let lo16 : BitVec 16 := a16 * b16
    let ov := decide (prod != lo16.toInt)
    (lo16.zeroExtend 64, { undefF with cf := ov, of := ov })

def ctzLoop (n : Nat) (v : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat) 64 (fun k ih => if v.getLsbD (63 - k) then 63 - k else ih) n

def unpack128 (op : VecUnpackOp) (a b : BitVec 128) : BitVec 128 :=
  match op with
  | .lbw  => packBytes128 fun i => if i.val % 2 == 0 then getByte128 a ⟨i.val / 2, by omega⟩ else getByte128 b ⟨i.val / 2, by omega⟩
  | .hbw  => packBytes128 fun i => if i.val % 2 == 0 then getByte128 a ⟨8 + i.val / 2, by omega⟩ else getByte128 b ⟨8 + i.val / 2, by omega⟩
  | .lwd  => packWords128 fun i => if i.val % 2 == 0 then getWord128 a ⟨i.val / 2, by omega⟩ else getWord128 b ⟨i.val / 2, by omega⟩
  | .hwd  => packWords128 fun i => if i.val % 2 == 0 then getWord128 a ⟨4 + i.val / 2, by omega⟩ else getWord128 b ⟨4 + i.val / 2, by omega⟩
  | .ldq  => packDwords128 fun i => if i.val % 2 == 0 then getDword128 a ⟨i.val / 2, by omega⟩ else getDword128 b ⟨i.val / 2, by omega⟩
  | .hdq  => packDwords128 fun i => if i.val % 2 == 0 then getDword128 a ⟨2 + i.val / 2, by omega⟩ else getDword128 b ⟨2 + i.val / 2, by omega⟩
  | .lqdq => getQword128 b ⟨0, by decide⟩ ++ getQword128 a ⟨0, by decide⟩
  | .hqdq => getQword128 b ⟨1, by decide⟩ ++ getQword128 a ⟨1, by decide⟩

def pmullw128 (a b : BitVec 128) : BitVec 128 :=
  packWords128 fun i => getWord128 a i * getWord128 b i

def pmulhuw128 (a b : BitVec 128) : BitVec 128 :=
  packWords128 fun i => BitVec.ofNat 16 (((getWord128 a i).toNat * (getWord128 b i).toNat) / 65536)

def pmulld128 (a b : BitVec 128) : BitVec 128 :=
  packDwords128 fun i => getDword128 a i * getDword128 b i

def pmaddwd128 (a b : BitVec 128) : BitVec 128 :=
  packDwords128 fun i =>
    let w0a := (getWord128 a ⟨2 * i.val, by omega⟩).toInt
    let w0b := (getWord128 b ⟨2 * i.val, by omega⟩).toInt
    let w1a := (getWord128 a ⟨2 * i.val + 1, by omega⟩).toInt
    let w1b := (getWord128 b ⟨2 * i.val + 1, by omega⟩).toInt
    BitVec.ofInt 32 (w0a * w0b + w1a * w1b)

def pshufd128 (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  packDwords128 fun i =>
    let sel := (BitVec.extractLsb' (2 * i.val) 2 imm).toNat
    getDword128 a ⟨sel % 4, Nat.mod_lt _ (by decide)⟩

def pshuflw128 (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  let hi64 := BitVec.extractLsb' 64 64 a
  let w (k : Nat) : BitVec 16 :=
    let sel := (BitVec.extractLsb' (2 * k) 2 imm).toNat
    getWord128 a ⟨sel % 4, by omega⟩
  hi64 ++ (w 3 ++ (w 2 ++ (w 1 ++ w 0)))

def psrldq128 (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  let sh := imm.toNat
  if sh >= 16 then 0#128 else a >>> (sh * 8)

def psrlqImm128 (a : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  let sh := imm.toNat
  packQwords128 fun i => if sh >= 64 then 0#64 else (getQword128 a i) >>> sh

def perm2i128Eval (a b : BitVec 256) (imm : BitVec 8) : BitVec 256 :=
  let pick (ctrl : Nat) : BitVec 128 :=
    if (ctrl &&& 8) != 0 then 0#128
    else match ctrl &&& 3 with
      | 0 => BitVec.extractLsb' 0 128 a   | 1 => BitVec.extractLsb' 128 128 a
      | 2 => BitVec.extractLsb' 0 128 b   | _ => BitVec.extractLsb' 128 128 b
  pick ((BitVec.extractLsb' 4 4 imm).toNat) ++ pick ((BitVec.extractLsb' 0 4 imm).toNat)

def extendByte128 (op : VecExtendOp) (s : X64State) (nextRip : BitVec 64) (src : X64XmmRm) : BitVec 128 :=
  let raw64 : BitVec 64 := match src with
    | .reg y => BitVec.extractLsb' 0 64 (s.ymms y)
    | .mem a => readMem64 s.mem (evalByteAddr s nextRip a)
  match op with
  | .zxbw => packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 raw64).zeroExtend 16
  | .sxbw => packWords128 fun i => let b := BitVec.extractLsb' (i.val * 8) 8 raw64; (if b.msb then 0xFF#8 else 0#8) ++ b
  | .zxwd => packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 raw64).zeroExtend 32
  | .sxwd => packDwords128 fun i => let w := BitVec.extractLsb' (i.val * 16) 16 raw64; (if w.msb then 0xFFFF#16 else 0#16) ++ w
  | .zxdq => packQwords128 fun i => (BitVec.extractLsb' (i.val * 32) 32 raw64).zeroExtend 64
  | .sxdq => packQwords128 fun i => sext32To64 (BitVec.extractLsb' (i.val * 32) 32 raw64)

def extendByte256 (op : VecExtendOp) (s : X64State) (nextRip : BitVec 64) (src : X64XmmRm) : BitVec 256 :=
  let raw128 := readByteXmm128 s nextRip src
  match op with
  | .zxbw => packWords256 fun i => (getByte128 raw128 i).zeroExtend 16
  | .sxbw => packWords256 fun i => let b := getByte128 raw128 i; (if b.msb then 0xFF#8 else 0#8) ++ b
  | .zxwd => packDwords256 fun i => (getWord128 raw128 i).zeroExtend 32
  | .sxwd => packDwords256 fun i => let w := getWord128 raw128 i; (if w.msb then 0xFFFF#16 else 0#16) ++ w
  | .zxdq => packQwords256 fun i => (getDword128 raw128 i).zeroExtend 64
  | .sxdq => packQwords256 fun i => sext32To64 (getDword128 raw128 i)

def applyByte128Or256 (m : SimdMode) (ymms : YmmIdx → BitVec 256) (dst : YmmIdx)
    (f128 : BitVec 128 → BitVec 128 → BitVec 128) (a256 b256 : BitVec 256) :
    YmmIdx → BitVec 256 :=
  match m with
  | .legacy128 => writeXmm128 false ymms dst (f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256))
  | .vex128    => writeXmm128 true  ymms dst (f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256))
  | .vex256    =>
    let lo := f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256)
    let hi := f128 (BitVec.extractLsb' 128 128 a256) (BitVec.extractLsb' 128 128 b256)
    ymmUpd ymms dst (hi ++ lo)

def readByteModeRhs (m : SimdMode) (s : X64State) (nextRip : BitVec 64) (xrm : X64XmmRm) : BitVec 256 :=
  match m with
  | .vex256 => readByteYmm256 s nextRip xrm
  | _       => (readByteXmm128 s nextRip xrm).zeroExtend 256

def execByteInstr (ins : X64Instr) (nextRip : BitVec 64) (ch : UndefChoice) (s : X64State) : X64State :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .nop | .endbr64 => sRip
  | .vzeroupper     => { sRip with ymms := vzeroUpperAll s.ymms }
  | .ud2 | .cli     => { s with fault := true }
  | .mov8Load dst src => { sRip with regs := writeSubReg8 s.regs dst (readByteRm8 s nextRip src) }
  | .mov8Store dst src => writeByteRm8 sRip nextRip dst (readSubReg8 s.regs src)
  | .mov8Imm dst imm => writeByteRm8 sRip nextRip dst imm
  | .alu8RmReg op dst src =>
    let (res, fl) := evalAluN (by decide) op (readByteRm8 s nextRip dst) (readSubReg8 s.regs src) s.flags ch.flags
    let s1 := if op == .cmp || op == .test then sRip else writeByteRm8 sRip nextRip dst res
    { s1 with flags := fl }
  | .alu8RegRm op dst src =>
    let (res, fl) := evalAluN (by decide) op (readSubReg8 s.regs dst) (readByteRm8 s nextRip src) s.flags ch.flags
    let regs' := if op == .cmp || op == .test then s.regs else writeSubReg8 s.regs dst res
    { sRip with regs := regs', flags := fl }
  | .alu8Imm op dst imm =>
    let (res, fl) := evalAluN (by decide) op (readByteRm8 s nextRip dst) imm s.flags ch.flags
    let s1 := if op == .cmp || op == .test then sRip else writeByteRm8 sRip nextRip dst res
    { s1 with flags := fl }
  | .setcc8 cc dst =>
    writeByteRm8 sRip nextRip dst (if evalCond cc s.flags then 1#8 else 0#8)
  | .movzx8 sz dst src =>
    { sRip with regs := writeRegSz sz s.regs dst ((readByteRm8 s nextRip src).zeroExtend 64) }
  | .movzx16 sz dst src =>
    let v16 := BitVec.extractLsb' 0 16 (readByteRm .s16 s nextRip src)
    { sRip with regs := writeRegSz sz s.regs dst (v16.zeroExtend 64) }
  | .movsx8 sz dst src =>
    { sRip with regs := writeRegSz sz s.regs dst (sext8To64 (readByteRm8 s nextRip src)) }
  | .movsx16 sz dst src =>
    let v16 := BitVec.extractLsb' 0 16 (readByteRm .s16 s nextRip src)
    { sRip with regs := writeRegSz sz s.regs dst (sext16To64 v16) }
  | .movsxd dst src =>
    let v32 := BitVec.extractLsb' 0 32 (readByteRm .s32 s nextRip src)
    { sRip with regs := regUpd s.regs dst (sext32To64 v32) }
  | .movLoad sz dst src => { sRip with regs := writeRegSz sz s.regs dst (readByteRm sz s nextRip src) }
  | .movStore sz dst src => writeByteRm sz sRip nextRip dst (readRegSz sz s.regs src)
  | .movImm sz dst imm => { sRip with regs := writeRegSz sz s.regs dst imm }
  | .movRmImm32 sz dst imm => writeByteRm sz sRip nextRip dst imm
  | .lea sz dst addr => { sRip with regs := writeRegSz sz s.regs dst (evalByteAddr s nextRip addr) }
  | .xchg sz r1 rm =>
    let v1 := readRegSz sz s.regs r1
    let v2 := readByteRm sz s nextRip rm
    let s1 := writeByteRm sz sRip nextRip rm v1
    { s1 with regs := writeRegSz sz s1.regs r1 v2 }
  | .aluRmReg sz op dst src =>
    let (res, fl) := evalAluSz sz op (readByteRm sz s nextRip dst) (readRegSz sz s.regs src) s.flags ch.flags
    let s1 := if op == .cmp || op == .test then sRip else writeByteRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .aluRegRm sz op dst src =>
    let (res, fl) := evalAluSz sz op (readRegSz sz s.regs dst) (readByteRm sz s nextRip src) s.flags ch.flags
    let regs' := if op == .cmp || op == .test then s.regs else writeRegSz sz s.regs dst res
    { sRip with regs := regs', flags := fl }
  | .aluImm sz op dst imm =>
    let (res, fl) := evalAluSz sz op (readByteRm sz s nextRip dst) imm s.flags ch.flags
    let s1 := if op == .cmp || op == .test then sRip else writeByteRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .unaryRm sz op dst =>
    let (res, fl) := evalUnarySz sz op (readByteRm sz s nextRip dst) s.flags
    let s1 := writeByteRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .shiftImm sz op dst cnt =>
    let (res, fl) := evalShiftSz sz op (readByteRm sz s nextRip dst) cnt s.flags ch.flags
    let s1 := writeByteRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .imul2 sz dst src =>
    let (res, fl) := evalImulSz sz (readRegSz sz s.regs dst) (readByteRm sz s nextRip src) ch.flags
    { sRip with regs := writeRegSz sz s.regs dst res, flags := fl }
  | .imul3 sz dst src imm =>
    let (res, fl) := evalImulSz sz (readByteRm sz s nextRip src) imm ch.flags
    { sRip with regs := writeRegSz sz s.regs dst res, flags := fl }
  | .bsf sz dst src =>
    let v := readByteRm sz s nextRip src
    if v == 0#64 then
      { sRip with regs := writeRegSz sz s.regs dst ch.undefGpr, flags := { ch.flags with zf := true } }
    else
      { sRip with regs := writeRegSz sz s.regs dst (BitVec.ofNat 64 (ctzLoop 64 v)), flags := { ch.flags with zf := false } }
  | .push64 src =>
    let newRsp := s.regs .rsp - 8#64
    { sRip with regs := regUpd s.regs .rsp newRsp, mem := writeMem64 s.mem newRsp (s.regs src) }
  | .pop64 dst =>
    let oldRsp := s.regs .rsp
    let popped := readMem64 s.mem oldRsp
    { sRip with regs := regUpd (regUpd s.regs .rsp (oldRsp + 8#64)) dst popped }
  | .leave64 =>
    let fp := s.regs .rbp
    let savedRbp := readMem64 s.mem fp
    { sRip with regs := regUpd (regUpd s.regs .rsp (fp + 8#64)) .rbp savedRbp }
  | .ret64 => { s with halted := true }
  | .jmpRel rel => { s with rip := nextRip + rel }
  | .jccRel cc rel => { s with rip := if evalCond cc s.flags then nextRip + rel else nextRip }
  | .simdMovLoad m dst src =>
    match m with
    | .legacy128 => { sRip with ymms := writeXmm128 false s.ymms dst (readByteXmm128 s nextRip src) }
    | .vex128    => { sRip with ymms := writeXmm128 true  s.ymms dst (readByteXmm128 s nextRip src) }
    | .vex256    => { sRip with ymms := ymmUpd s.ymms dst (readByteYmm256 s nextRip src) }
  | .simdMovStore m dst src =>
    match dst with
    | .reg dstY =>
      match m with
      | .legacy128 => { sRip with ymms := writeXmm128 false s.ymms dstY (BitVec.extractLsb' 0 128 (s.ymms src)) }
      | .vex128    => { sRip with ymms := writeXmm128 true  s.ymms dstY (BitVec.extractLsb' 0 128 (s.ymms src)) }
      | .vex256    => { sRip with ymms := ymmUpd s.ymms dstY (s.ymms src) }
    | .mem a =>
      let ea := evalByteAddr s nextRip a
      match m with
      | .vex256 => { sRip with mem := writeMem256 s.mem ea (s.ymms src) }
      | _       => { sRip with mem := writeMem128 s.mem ea (BitVec.extractLsb' 0 128 (s.ymms src)) }
  | .simdMovqLoad isVex dst src =>
    let lo64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymms y)
      | .mem a => readMem64 s.mem (evalByteAddr s nextRip a)
    { sRip with ymms := writeXmm128 isVex s.ymms dst (lo64.zeroExtend 128) }
  | .simdMovqStore isVex dst src =>
    let lo64 := BitVec.extractLsb' 0 64 (s.ymms src)
    match dst with
    | .reg y => { sRip with ymms := writeXmm128 isVex s.ymms y (lo64.zeroExtend 128) }
    | .mem a => { sRip with mem := writeMem64 s.mem (evalByteAddr s nextRip a) lo64 }
  | .simdMovGprToX isVex is64 dst src =>
    let v64 := readByteRm (if is64 then .s64 else .s32) s nextRip src
    { sRip with ymms := writeXmm128 isVex s.ymms dst (v64.zeroExtend 128) }
  | .simdMovXToGpr _isVex is64 dst src =>
    writeByteRm (if is64 then .s64 else .s32) sRip nextRip dst (BitVec.extractLsb' 0 64 (s.ymms src))
  | .simdBitwise m op dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match op with
      | .and => (· &&& ·) | .or => (· ||| ·) | _ => (· ^^^ ·)
    { sRip with ymms := applyByte128Or256 m s.ymms dst f128 (s.ymms s1) rhs }
  | .simdAdd m ew dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => getByte128  a i + getByte128  b i
      | .e16 => fun a b => packWords128  fun i => getWord128  a i + getWord128  b i
      | .e32 => fun a b => packDwords128 fun i => getDword128 a i + getDword128 b i
      | .e64 => fun a b => packQwords128 fun i => getQword128 a i + getQword128 b i
    { sRip with ymms := applyByte128Or256 m s.ymms dst f128 (s.ymms s1) rhs }
  | .simdSub m ew dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => getByte128  a i - getByte128  b i
      | .e16 => fun a b => packWords128  fun i => getWord128  a i - getWord128  b i
      | .e32 => fun a b => packDwords128 fun i => getDword128 a i - getDword128 b i
      | .e64 => fun a b => packQwords128 fun i => getQword128 a i - getQword128 b i
    { sRip with ymms := applyByte128Or256 m s.ymms dst f128 (s.ymms s1) rhs }
  | .simdCmpeq m ew dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => if getByte128  a i == getByte128  b i then 0xFF#8 else 0#8
      | .e16 => fun a b => packWords128  fun i => if getWord128  a i == getWord128  b i then 0xFFFF#16 else 0#16
      | .e32 => fun a b => packDwords128 fun i => if getDword128 a i == getDword128 b i then 0xFFFFFFFF#32 else 0#32
      | .e64 => fun a b => packQwords128 fun i => if getQword128 a i == getQword128 b i then 0xFFFFFFFFFFFFFFFF#64 else 0#64
    { sRip with ymms := applyByte128Or256 m s.ymms dst f128 (s.ymms s1) rhs }
  | .simdCmpgt m ew dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => if (getByte128  b i).slt (getByte128  a i) then 0xFF#8 else 0#8
      | .e16 => fun a b => packWords128  fun i => if (getWord128  b i).slt (getWord128  a i) then 0xFFFF#16 else 0#16
      | .e32 => fun a b => packDwords128 fun i => if (getDword128 b i).slt (getDword128 a i) then 0xFFFFFFFF#32 else 0#32
      | .e64 => fun a b => packQwords128 fun i => if (getQword128 b i).slt (getQword128 a i) then 0xFFFFFFFFFFFFFFFF#64 else 0#64
    { sRip with ymms := applyByte128Or256 m s.ymms dst f128 (s.ymms s1) rhs }
  | .simdUnpack m op dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    { sRip with ymms := applyByte128Or256 m s.ymms dst (unpack128 op) (s.ymms s1) rhs }
  | .simdExtend m op dst src =>
    match m with
    | .vex256    => { sRip with ymms := ymmUpd s.ymms dst (extendByte256 op s nextRip src) }
    | .vex128    => { sRip with ymms := writeXmm128 true  s.ymms dst (extendByte128 op s nextRip src) }
    | .legacy128 => { sRip with ymms := writeXmm128 false s.ymms dst (extendByte128 op s nextRip src) }
  | .simdBroadcastB m dst src =>
    let b0 : BitVec 8 := match src with
      | .reg y => BitVec.extractLsb' 0 8 (s.ymms y)
      | .mem a => readMem8 s.mem (evalByteAddr s nextRip a)
    match m with
    | .vex256    => { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun _ => b0) }
    | .vex128    => { sRip with ymms := writeXmm128 true  s.ymms dst (packBytes128 fun _ => b0) }
    | .legacy128 => { sRip with ymms := writeXmm128 false s.ymms dst (packBytes128 fun _ => b0) }
  | .simdBroadcastQ m dst src =>
    let q0 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymms y)
      | .mem a => readMem64 s.mem (evalByteAddr s nextRip a)
    match m with
    | .vex256    => { sRip with ymms := ymmUpd s.ymms dst (packQwords256 fun _ => q0) }
    | .vex128    => { sRip with ymms := writeXmm128 true  s.ymms dst (packQwords128 fun _ => q0) }
    | .legacy128 => { sRip with ymms := writeXmm128 false s.ymms dst (packQwords128 fun _ => q0) }
  | .simdPmullw m dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    { sRip with ymms := applyByte128Or256 m s.ymms dst pmullw128 (s.ymms s1) rhs }
  | .simdPmulhuw m dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    { sRip with ymms := applyByte128Or256 m s.ymms dst pmulhuw128 (s.ymms s1) rhs }
  | .simdPmulld m dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    { sRip with ymms := applyByte128Or256 m s.ymms dst pmulld128 (s.ymms s1) rhs }
  | .simdPmaddwd m dst s1 s2 =>
    let rhs := readByteModeRhs m s nextRip s2
    { sRip with ymms := applyByte128Or256 m s.ymms dst pmaddwd128 (s.ymms s1) rhs }
  | .simdPsrldq m dst src imm =>
    { sRip with ymms := applyByte128Or256 m s.ymms dst (fun a _ => psrldq128 a imm) (s.ymms src) 0#256 }
  | .simdPsrlqImm m dst src imm =>
    { sRip with ymms := applyByte128Or256 m s.ymms dst (fun a _ => psrlqImm128 a imm) (s.ymms src) 0#256 }
  | .simdPshufd m dst src imm =>
    let rhs := readByteModeRhs m s nextRip src
    { sRip with ymms := applyByte128Or256 m s.ymms dst (fun a _ => pshufd128 a imm) rhs 0#256 }
  | .simdPshuflw m dst src imm =>
    let rhs := readByteModeRhs m s nextRip src
    { sRip with ymms := applyByte128Or256 m s.ymms dst (fun a _ => pshuflw128 a imm) rhs 0#256 }
  | .simdExtract128 dst src imm =>
    let lane := if (imm &&& 1#8) == 0#8 then BitVec.extractLsb' 0 128 (s.ymms src)
                else BitVec.extractLsb' 128 128 (s.ymms src)
    match dst with
    | .reg y => { sRip with ymms := writeXmm128 true s.ymms y lane }
    | .mem a => { sRip with mem := writeMem128 s.mem (evalByteAddr s nextRip a) lane }
  | .simdPerm2i128 dst s1 s2 imm =>
    let rhs := readByteYmm256 s nextRip s2
    { sRip with ymms := ymmUpd s.ymms dst (perm2i128Eval (s.ymms s1) rhs imm) }

def stepX64 (code : CodeMap) (ch : UndefChoice) (s : X64State) : X64State :=
  if s.halted || s.fault then s
  else
    match decodeX64 (fetchWindow16 code s.rip) with
    | .fault _    => { s with fault := true }
    | .ok ins len => execByteInstr ins (s.rip + BitVec.ofNat 64 len) ch s

def runX64 (img : X64ObjImage) (steps : Nat) (nd : Nat → UndefChoice) (s0 : X64State) : X64State :=
  let cmap := objCodeMap img
  Nat.rec (motive := fun _ => Nat → X64State → X64State)
    (fun _ s => s)
    (fun _ ih idx s => ih (idx + 1) (stepX64 cmap (nd idx) s))
    steps 0 s0

def Step (code : CodeMap) (s s' : X64State) : Prop :=
  ∃ ch : UndefChoice, stepX64 code ch s = s'

inductive StepsN (code : CodeMap) : Nat → X64State → X64State → Prop where
  | zero (s : X64State) : StepsN code 0 s s
  | succ {n : Nat} {s s1 s2 : X64State} :
      Step code s s1 → StepsN code n s1 s2 → StepsN code (n + 1) s s2

/-! ## Section 4: Constructive Sub-Register & Legacy-SSE-vs-VEX State-Transition Proofs -/

def codeFromBytes (bs : List (BitVec 8)) : CodeMap :=
  fun a => if a.toNat < bs.length then listGetByteD bs a.toNat else 0x90#8

/-- **REX Nullification Flips `DIL` Back to `BH` (`rex_nullified_by_cs_flips_dil_to_bh`):**
    1. `88 df` (`mov bh, bl`, no REX) updates `rbx[15:8]` and leaves `rdi` untouched.
    2. `40 88 df` (`mov dil, bl`, REX `0x40`) updates `rdi[7:0]` and leaves `rbx` untouched.
    3. `40 2e 88 df` (CS prefix `0x2E` after REX `0x40`) nullifies REX and reverts to `mov bh, bl`!
    4. `2e 40 88 df` (CS prefix `0x2E` before REX `0x40`) keeps REX active and executes `mov dil, bl`! -/
theorem rex_nullified_by_cs_flips_dil_to_bh (s : X64State) (ch : UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0#64) :
    let bl := BitVec.extractLsb' 0 8 (s.regs .rbx)
    let sNoRex  := stepX64 (codeFromBytes [0x88#8, 0xDF#8]) ch s
    let sRex40  := stepX64 (codeFromBytes [0x40#8, 0x88#8, 0xDF#8]) ch s
    let sNullif := stepX64 (codeFromBytes [0x40#8, 0x2E#8, 0x88#8, 0xDF#8]) ch s
    let sActive := stepX64 (codeFromBytes [0x2E#8, 0x40#8, 0x88#8, 0xDF#8]) ch s
    (BitVec.extractLsb' 8 8 (sNoRex.regs .rbx) = bl ∧ sNoRex.regs .rdi = s.regs .rdi) ∧
    (BitVec.extractLsb' 0 8 (sRex40.regs .rdi) = bl ∧ sRex40.regs .rbx = s.regs .rbx) ∧
    (sNullif.regs = sNoRex.regs ∧ sNullif.rip = 4#64) ∧
    (sActive.regs = sRex40.regs ∧ sActive.rip = 4#64) := by
  have hst : (s.halted || s.fault) = false := by simp [hrun, hnf]
  dsimp only
  have hdec1 : decodeX64 (fetchWindow16 (codeFromBytes [0x88#8, 0xDF#8]) 0#64) =
      .ok (.mov8Store (.reg8 (.hi8 .rbx)) (.lo8 .rbx)) 2 := rfl
  have hdec2 : decodeX64 (fetchWindow16 (codeFromBytes [0x40#8, 0x88#8, 0xDF#8]) 0#64) =
      .ok (.mov8Store (.reg8 (.lo8 .rdi)) (.lo8 .rbx)) 3 := rfl
  have hdec3 : decodeX64 (fetchWindow16 (codeFromBytes [0x40#8, 0x2E#8, 0x88#8, 0xDF#8]) 0#64) =
      .ok (.mov8Store (.reg8 (.hi8 .rbx)) (.lo8 .rbx)) 4 := rfl
  have hdec4 : decodeX64 (fetchWindow16 (codeFromBytes [0x2E#8, 0x40#8, 0x88#8, 0xDF#8]) 0#64) =
      .ok (.mov8Store (.reg8 (.lo8 .rdi)) (.lo8 .rbx)) 4 := rfl
  unfold stepX64
  rw [ifFalse (by simp [hst]), ifFalse (by simp [hst]), ifFalse (by simp [hst]), ifFalse (by simp [hst])]
  rw [hrip, hdec1, hdec2, hdec3, hdec4]
  dsimp only [execByteInstr, writeByteRm8, readSubReg8]
  have hhi := writeSubReg8_hi8_preserves_lo8_and_hi48 s.regs .rbx (BitVec.extractLsb' 0 8 (s.regs .rbx))
  have hlo := writeSubReg8_lo8_preserves_hi56 s.regs .rdi (BitVec.extractLsb' 0 8 (s.regs .rbx))
  exact ⟨⟨hhi.1, hhi.2.2.2 .rdi (by decide)⟩,
         ⟨hlo.1, hlo.2.2 .rbx (by decide)⟩,
         ⟨rfl, rfl⟩,
         ⟨rfl, rfl⟩⟩

def y0 : YmmIdx := ⟨0, by decide⟩
def y1 : YmmIdx := ⟨1, by decide⟩

/-- **Legacy Non-VEX SSE2 Preserves `YMM[255:128]` vs. VEX `L = 0` Zeroing:**
    Executing Legacy SSE2 `66 0f ef c0` (`pxor xmm0, xmm0`) clears `XMM0[127:0]`
    while **preserving `YMM0[255:128]`**, whereas VEX `c5 f9 ef c0`
    (`vpxor xmm0, xmm0, xmm0`) zeroes all `256` bits of `YMM0`. -/
theorem legacy_sse2_preserves_upper_ymm_vs_vex128_zeroes (s : X64State) (ch : UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0#64) :
    let sLeg := stepX64 (codeFromBytes [0x66#8, 0x0F#8, 0xEF#8, 0xC0#8]) ch s
    let sVex := stepX64 (codeFromBytes [0xC5#8, 0xF9#8, 0xEF#8, 0xC0#8]) ch s
    BitVec.extractLsb' 0 128 (sLeg.ymms y0) = 0#128 ∧
    BitVec.extractLsb' 128 128 (sLeg.ymms y0) = BitVec.extractLsb' 128 128 (s.ymms y0) ∧
    sVex.ymms y0 = 0#256 := by
  have hst : (s.halted || s.fault) = false := by simp [hrun, hnf]
  dsimp only
  have hdL : decodeX64 (fetchWindow16 (codeFromBytes [0x66#8, 0x0F#8, 0xEF#8, 0xC0#8]) 0#64) =
      .ok (.simdBitwise .legacy128 .xor y0 y0 (.reg y0)) 4 := rfl
  have hdV : decodeX64 (fetchWindow16 (codeFromBytes [0xC5#8, 0xF9#8, 0xEF#8, 0xC0#8]) 0#64) =
      .ok (.simdBitwise .vex128 .xor y0 y0 (.reg y0)) 4 := rfl
  unfold stepX64
  rw [ifFalse (by simp [hst]), ifFalse (by simp [hst]), hrip, hdL, hdV]
  dsimp [execByteInstr, readByteModeRhs, readByteXmm128, applyByte128Or256, writeXmm128]
  have hlo0 : BitVec.extractLsb' 0 128 (BitVec.setWidth 256 (BitVec.extractLsb' 0 128 (s.ymms y0))) =
      BitVec.extractLsb' 0 128 (s.ymms y0) := by
    rw [setWidth_eq_zero_append (m := 128), extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  have hxor : (BitVec.extractLsb' 0 128 (s.ymms y0) ^^^ BitVec.extractLsb' 0 128 (s.ymms y0)) = 0#128 :=
    BitVec.xor_self
  rw [ymmUpd_eq, ymmUpd_eq, hlo0, hxor]
  refine ⟨?_, ?_, rfl⟩
  · rw [extractLsb_append_right_off _ _ (by decide), extractLsb_self]
  · rw [extractLsb_append_left _ _ (by decide), extractLsb_self]

/-- **3-Band Bit Partition of `f3 0f 7e 07` (`movq`) vs. `c5 fa 7e 07` (`vmovq`):**
    Both load `bits[63:0] := Mem64[rdi]` and zero `bits[127:64] := 0#64`, while
    Legacy `movq` preserves `bits[255:128]` and VEX `vmovq` zeroes `bits[255:128]`. -/
theorem legacy_movq_vs_vex_vmovq_three_band_split (s : X64State) (ch : UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0#64) :
    let q := readMem64 s.mem (s.regs .rdi)
    let sLeg := stepX64 (codeFromBytes [0xF3#8, 0x0F#8, 0x7E#8, 0x07#8]) ch s
    let sVex := stepX64 (codeFromBytes [0xC5#8, 0xFA#8, 0x7E#8, 0x07#8]) ch s
    sLeg.ymms y0 = BitVec.extractLsb' 128 128 (s.ymms y0) ++ q.zeroExtend 128 ∧
    sVex.ymms y0 = (q.zeroExtend 128).zeroExtend 256 := by
  have hst : (s.halted || s.fault) = false := by simp [hrun, hnf]
  dsimp only
  have hdL : decodeX64 (fetchWindow16 (codeFromBytes [0xF3#8, 0x0F#8, 0x7E#8, 0x07#8]) 0#64) =
      .ok (.simdMovqLoad false y0 (.mem { base := some .rdi })) 4 := rfl
  have hdV : decodeX64 (fetchWindow16 (codeFromBytes [0xC5#8, 0xFA#8, 0x7E#8, 0x07#8]) 0#64) =
      .ok (.simdMovqLoad true y0 (.mem { base := some .rdi })) 4 := rfl
  unfold stepX64
  rw [ifFalse (by simp [hst]), ifFalse (by simp [hst]), hrip, hdL, hdV]
  dsimp only [execByteInstr, evalByteAddr, writeXmm128]
  simp [ymmUpd_eq]

/-- **SSE-After-`VZEROUPPER` Clean Transition (`sse_after_vzeroupper_clean_upper_ymm`):**
    Executing `c5 f8 77` (`vzeroupper`) followed by Legacy Non-VEX SSE2
    `66 0f fe c1` (`paddd xmm0, xmm1`) leaves `YMM[255:128] = 0#128` across every
    vector register `idx : YmmIdx`. -/
theorem sse_after_vzeroupper_clean_upper_ymm (s : X64State) (ch1 ch2 : UndefChoice)
    (hrun : s.halted = false) (hnf : s.fault = false) (hrip : s.rip = 0#64) (idx : YmmIdx) :
    let code := codeFromBytes [0xC5#8, 0xF8#8, 0x77#8, 0x66#8, 0x0F#8, 0xFE#8, 0xC1#8]
    let s1 := stepX64 code ch1 s
    let s2 := stepX64 code ch2 s1
    BitVec.extractLsb' 128 128 (s2.ymms idx) = 0#128 := by
  have hst1 : (s.halted || s.fault) = false := by simp [hrun, hnf]
  dsimp only
  have hd1 : decodeX64 (fetchWindow16 (codeFromBytes [0xC5#8, 0xF8#8, 0x77#8, 0x66#8, 0x0F#8, 0xFE#8, 0xC1#8]) 0#64) =
      .ok .vzeroupper 3 := rfl
  have hs1 : stepX64 (codeFromBytes [0xC5#8, 0xF8#8, 0x77#8, 0x66#8, 0x0F#8, 0xFE#8, 0xC1#8]) ch1 s =
      { s with rip := 3#64, ymms := vzeroUpperAll s.ymms } := by
    unfold stepX64
    rw [ifFalse (by simp [hst1]), hrip, hd1]
    rfl
  rw [hs1]
  have hd2 : decodeX64 (fetchWindow16 (codeFromBytes [0xC5#8, 0xF8#8, 0x77#8, 0x66#8, 0x0F#8, 0xFE#8, 0xC1#8]) 3#64) =
      .ok (.simdAdd .legacy128 .e32 y0 y0 (.reg y1)) 4 := rfl
  unfold stepX64
  rw [ifFalse (by simp [hst1]), hd2]
  dsimp only [execByteInstr, applyByte128Or256, writeXmm128]
  have hzeroHi : ∀ j : YmmIdx, BitVec.extractLsb' 128 128 (vzeroUpperAll s.ymms j) = 0#128 := by
    intro j; dsimp [vzeroUpperAll]
    rw [setWidth_eq_zero_append (m := 128), extractLsb_append_left _ _ (by decide), extractLsb_self]
  by_cases hij : idx = y0
  · subst hij
    rw [ymmUpd_eq, extractLsb_append_left _ _ (by decide), extractLsb_self]
    exact hzeroHi y0
  · rw [ymmUpd_ne _ hij]
    exact hzeroHi idx

end ByteX86Gcc
