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

/-!
# `VendorX86GccRef`

Pass-2 x86-64 byte-decoding reference specification (`prelude` + `Init.*` only,
`0` `sorry`, `0` `isPartial` via `Nat.rec`) extending pinned
`awslabs/s2n-bignum@d4518712d040485efe621caba1c723a07fbc549e`
(`x86/proofs/{instruction,decode,x86}.ml`) +
`intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` legality rules to close
the complete `gcc 15.2.0` `-O2` and `-O3 -mavx2` compiled C `.o` gap:

1. **8-bit and 16-bit GP sub-registers (`Reg8`, `OpSize16`):**
   - Non-orthogonal x86-64 REX 8-bit register selection (`reg8OfIdx`): without a
     REX prefix (`ps.rex = none`), indices `4..7` select high-byte `AH/CH/DH/BH`
     (`bits[15:8]` of `RAX/RCX/RDX/RBX`, preserving `bits[63:16]` and `bits[7:0]`);
     with *any* active REX prefix (`0x40..0x4F`), indices `4..7` (`extBit = false`)
     redirect to low-byte `SPL/BPL/SIL/DIL` (`bits[7:0]` of `RSP/RBP/RSI/RDI`,
     preserving `bits[63:8]`).
   - 16-bit operand size (`0x66` without `REX.W`) updates `bits[15:0]` while
     preserving `bits[63:16]`, contrasting with 32-bit zero-extension (`bits[63:32] := 0`).
   - Full `MOVZX` (`0F B6` byte, `0F B7` word), `MOVSX` (`0F BE` byte, `0F BF` word),
     and `MOVSXD` (`63` dword-to-qword).
2. **Multi-byte ModR/M `NOP` (`0F 1F /r` with arbitrary `0x66`/`0x2E` alignment
   prefixes up to 15 B, `#GP(0)` at `>= 16` B, `#UD` under `LOCK`), `MOV r64, imm64`
   (`48 B8+rd`), 16/32/64-bit `LEA` (`mod = 3 -> #UD`), 2/3-operand `IMUL`, `ROL`/`ROR`/`SHL`/`SHR`/`SAR`, and `LEAVE`.**
3. **Legacy Non-VEX SSE2 vs. VEX `L = 0` / `L = 1` Upper-`YMM[255:128]` Semantics:**
   - Legacy Non-VEX SSE2 (`0F 10`/`11`, `66 0F ...`, `F3 0F ...`, `F2 0F ...`) writes
     `XMM[127:0]` while **preserving `YMM[255:128]`** (`writeXmmResult false`).
   - VEX `L = 0` (`C5`/`C4`) writes `XMM[127:0]` while **zeroing `YMM[255:128]`**
     (`writeXmmResult true`), and `VZEROUPPER` (`C5 F8 77`) zeroes `YMM0..YMM15[255:128]`.
-/

namespace VendorX86GccRef

/-- 16 architectural 64-bit general-purpose registers (`RAX`..`R15`). -/
inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def gprOfNat (n : Nat) : Gpr :=
  match n % 16 with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

def gprUpd (regs : Gpr → BitVec 64) (r : Gpr) (v : BitVec 64) : Gpr → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

/-- 8-bit general-purpose sub-register: either `bits[7:0]` (`.lo8` = `AL..R15B`,
    including REX-gated `SPL/BPL/SIL/DIL`) or `bits[15:8]` (`.hi8` = `AH/CH/DH/BH`,
    addressable only when no REX prefix is active). -/
inductive Reg8 where
  | lo8 (g : Gpr)
  | hi8 (g : Gpr)
  deriving DecidableEq, Repr

/-- Non-orthogonal x86-64 8-bit register selector (Intel SDM Vol. 2A Table 2-2;
    `intelxed` `GPR8_R` / `GPR8_B`). -/
def reg8OfIdx (rexPresent extBit : Bool) (idx3 : BitVec 3) : Reg8 :=
  if !rexPresent then
    match idx3.toNat with
    | 0 => .lo8 .rax | 1 => .lo8 .rcx | 2 => .lo8 .rdx | 3 => .lo8 .rbx
    | 4 => .hi8 .rax | 5 => .hi8 .rcx | 6 => .hi8 .rdx | _ => .hi8 .rbx
  else
    .lo8 (gprOfNat ((if extBit then 8 else 0) + idx3.toNat))

def readReg8 (regs : Gpr → BitVec 64) : Reg8 → BitVec 8
  | .lo8 g => BitVec.extractLsb' 0 8 (regs g)
  | .hi8 g => BitVec.extractLsb' 8 8 (regs g)

def writeReg8 (regs : Gpr → BitVec 64) (r : Reg8) (v : BitVec 8) : Gpr → BitVec 64 :=
  match r with
  | .lo8 g =>
    let old := regs g
    gprUpd regs g (BitVec.extractLsb' 8 56 old ++ v)
  | .hi8 g =>
    let old := regs g
    gprUpd regs g (BitVec.extractLsb' 16 48 old ++ (v ++ BitVec.extractLsb' 0 8 old))

/-- Non-byte GP operand widths (`16`, `32`, `64` bits). -/
inductive OpSize where
  | s16 | s32 | s64
  deriving DecidableEq, Repr

def readGprSz (sz : OpSize) (regs : Gpr → BitVec 64) (g : Gpr) : BitVec 64 :=
  match sz with
  | .s64 => regs g
  | .s32 => (BitVec.extractLsb' 0 32 (regs g)).zeroExtend 64
  | .s16 => (BitVec.extractLsb' 0 16 (regs g)).zeroExtend 64

/-- Write `16`/`32`/`64`-bit GP result: `.s32` zero-extends to 64 bits, whereas
    `.s16` preserves `bits[63:16]` per Intel SDM Vol. 1 §3.4.1.1. -/
def writeGprSz (sz : OpSize) (regs : Gpr → BitVec 64) (g : Gpr) (v : BitVec 64) :
    Gpr → BitVec 64 :=
  match sz with
  | .s64 => gprUpd regs g v
  | .s32 => gprUpd regs g ((BitVec.extractLsb' 0 32 v).zeroExtend 64)
  | .s16 => gprUpd regs g (BitVec.extractLsb' 16 48 (regs g) ++ BitVec.extractLsb' 0 16 v)

/-- 16 architectural 256-bit YMM vector registers (`YMM0`..`YMM15`). -/
abbrev YmmIdx := Fin 16

def ymmIdxOfNat (n : Nat) : YmmIdx := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def ymmUpd (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v : BitVec 256) :
    YmmIdx → BitVec 256 :=
  fun idx' => if idx' = idx then v else ymms idx'

/-- Write a 128-bit vector result:
    - `isVex = true` (VEX `L = 0`): zeroes `YMM[255:128]` (Intel SDM Vol. 1 §14.5).
    - `isVex = false` (Legacy Non-VEX SSE2): preserves `YMM[255:128]`. -/
def writeXmmResult (isVex : Bool) (ymms : YmmIdx → BitVec 256) (idx : YmmIdx)
    (v128 : BitVec 128) : YmmIdx → BitVec 256 :=
  if isVex then
    ymmUpd ymms idx (v128.zeroExtend 256)
  else
    ymmUpd ymms idx (BitVec.extractLsb' 128 128 (ymms idx) ++ v128)

/-- `VZEROUPPER`: zeroes `bits[255:128]` of all 16 `YMM` registers while preserving
    `XMM0..XMM15` (`bits[127:0]`). -/
def vzeroUpperAll (ymms : YmmIdx → BitVec 256) : YmmIdx → BitVec 256 :=
  fun idx => (BitVec.extractLsb' 0 128 (ymms idx)).zeroExtend 256

/-- Six architectural status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  deriving DecidableEq, Repr

/-- Per-step demonic nondeterminism oracle (`UNDEFINED_VALUES[...]`). -/
structure UndefOracle where
  flags : RFlags := {}
  gpr   : BitVec 64 := 0#64
  deriving DecidableEq, Repr

abbrev ByteMem := BitVec 64 → BitVec 8
abbrev CodeMap := BitVec 64 → BitVec 8

def memUpd8 (m : ByteMem) (a : BitVec 64) (b : BitVec 8) : ByteMem :=
  fun a' => if a' = a then b else m a'

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

/-! ### Faults, Operands, and Instruction AST -/

inductive FaultKind where
  | gp0LengthExceeds15
  | gp0Privilege
  | udIllegalLock
  | udVexPrefix
  | udVexField
  | udRegisterOperand
  | udExplicit
  | udUnmapped
  deriving DecidableEq, Repr

structure MemAddr where
  base   : Option Gpr := none
  index  : Option (Gpr × Nat) := none
  disp   : BitVec 64 := 0#64
  ripRel : Bool := false
  deriving DecidableEq, Repr

inductive RmOp where
  | reg (r : Gpr)
  | mem (a : MemAddr)
  deriving DecidableEq, Repr

inductive Rm8Op where
  | reg8 (r : Reg8)
  | mem8 (a : MemAddr)
  deriving DecidableEq, Repr

inductive XmmRmOp where
  | reg (r : YmmIdx)
  | mem (a : MemAddr)
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

inductive Instr where
  | nop
  | endbr64
  | vzeroupper
  | ud2
  | cli
  -- 8-bit GP sub-register moves & ALU
  | mov8Load   (dst : Reg8) (src : Rm8Op)
  | mov8Store  (dst : Rm8Op) (src : Reg8)
  | mov8Imm    (dst : Rm8Op) (imm : BitVec 8)
  | alu8RmReg  (op : AluOp) (dst : Rm8Op) (src : Reg8)
  | alu8RegRm  (op : AluOp) (dst : Reg8) (src : Rm8Op)
  | alu8Imm    (op : AluOp) (dst : Rm8Op) (imm : BitVec 8)
  | setcc8     (cc : Cond) (dst : Rm8Op)
  -- Zero/sign-extending sub-word moves (`MOVZX`, `MOVSX`, `MOVSXD`)
  | movzx8     (sz : OpSize) (dst : Gpr) (src : Rm8Op)
  | movzx16    (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movsx8     (sz : OpSize) (dst : Gpr) (src : Rm8Op)
  | movsx16    (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movsxd     (dst : Gpr) (src : RmOp)
  -- 16/32/64-bit GP moves, LEA, XCHG, ALU, Shifts, Multiply, Bit-Scan
  | movLoad    (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movStore   (sz : OpSize) (dst : RmOp) (src : Gpr)
  | movImm     (sz : OpSize) (dst : Gpr) (imm : BitVec 64)
  | movRmImm32 (sz : OpSize) (dst : RmOp) (imm : BitVec 64)
  | lea        (sz : OpSize) (dst : Gpr) (addr : MemAddr)
  | xchg       (sz : OpSize) (r1 : Gpr) (rm : RmOp)
  | aluRmReg   (sz : OpSize) (op : AluOp) (dst : RmOp) (src : Gpr)
  | aluRegRm   (sz : OpSize) (op : AluOp) (dst : Gpr) (src : RmOp)
  | aluImm     (sz : OpSize) (op : AluOp) (dst : RmOp) (imm : BitVec 64)
  | unaryRm    (sz : OpSize) (op : UnaryOp) (dst : RmOp)
  | shiftImm   (sz : OpSize) (op : ShiftOp) (dst : RmOp) (cnt : BitVec 8)
  | imul2      (sz : OpSize) (dst : Gpr) (src : RmOp)
  | imul3      (sz : OpSize) (dst : Gpr) (src : RmOp) (imm : BitVec 64)
  | bsf        (sz : OpSize) (dst : Gpr) (src : RmOp)
  -- Stack & Control Flow
  | push64     (src : Gpr)
  | pop64      (dst : Gpr)
  | leave64
  | ret64
  | jmpRel     (rel : BitVec 64)
  | jccRel     (cc : Cond) (rel : BitVec 64)
  -- Legacy Non-VEX SSE2 & VEX 128/256-bit SIMD
  | simdMovLoad   (m : SimdMode) (dst : YmmIdx) (src : XmmRmOp)
  | simdMovStore  (m : SimdMode) (dst : XmmRmOp) (src : YmmIdx)
  | simdMovqLoad  (isVex : Bool) (dst : YmmIdx) (src : XmmRmOp)
  | simdMovqStore (isVex : Bool) (dst : XmmRmOp) (src : YmmIdx)
  | simdMovGprToX (isVex is64 : Bool) (dst : YmmIdx) (src : RmOp)
  | simdMovXToGpr (isVex is64 : Bool) (dst : RmOp) (src : YmmIdx)
  | simdBitwise   (m : SimdMode) (op : AluOp) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdAdd       (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdSub       (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdCmpeq     (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdCmpgt     (m : SimdMode) (ew : VecElem) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdUnpack    (m : SimdMode) (op : VecUnpackOp) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdExtend    (m : SimdMode) (op : VecExtendOp) (dst : YmmIdx) (src : XmmRmOp)
  | simdBroadcastB (m : SimdMode) (dst : YmmIdx) (src : XmmRmOp)
  | simdBroadcastQ (m : SimdMode) (dst : YmmIdx) (src : XmmRmOp)
  | simdPmullw    (m : SimdMode) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdPmulhuw   (m : SimdMode) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdPmulld    (m : SimdMode) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdPmaddwd   (m : SimdMode) (dst s1 : YmmIdx) (s2 : XmmRmOp)
  | simdPsrldq    (m : SimdMode) (dst src : YmmIdx) (imm : BitVec 8)
  | simdPsrlqImm  (m : SimdMode) (dst src : YmmIdx) (imm : BitVec 8)
  | simdPshufd    (m : SimdMode) (dst : YmmIdx) (src : XmmRmOp) (imm : BitVec 8)
  | simdPshuflw   (m : SimdMode) (dst : YmmIdx) (src : XmmRmOp) (imm : BitVec 8)
  | simdExtract128 (dst : XmmRmOp) (src : YmmIdx) (imm : BitVec 8)
  | simdPerm2i128  (dst s1 : YmmIdx) (s2 : XmmRmOp) (imm : BitVec 8)
  deriving DecidableEq, Repr

inductive DecodeResult where
  | ok    (ins : Instr) (len : Nat)
  | fault (fk : FaultKind)
  deriving DecidableEq, Repr

/-! ## Section 2: Prefix Scanner, ILD Length, and Exact-Slice Body Parser -/

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

def rexBit (rex : Option (BitVec 4)) (idx : Nat) : Bool :=
  match rex with
  | none => false
  | some r => r.getLsbD idx

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

/-- Bounded iterative prefix scanner via `Nat.rec` (`0` `._unsafe_rec` helpers).
    Enforces Intel SDM Vol. 2A §2.2.1: any legacy prefix after a REX byte resets
    `rex := none`! -/
def scanPrefixes (fuel : Nat) (st : PrefixState) (bs : List (BitVec 8)) :
    PrefixState × List (BitVec 8) :=
  Nat.rec (motive := fun _ => PrefixState → List (BitVec 8) → PrefixState × List (BitVec 8))
    (fun s rem => (s, rem))
    (fun _ ih s rem =>
      match rem with
      | [] => (s, [])
      | b :: rest =>
        if b == 0x66#8 then
          ih { s with has66 := true, rex := none, count := s.count + 1 } rest
        else if b == 0xF2#8 then
          ih { s with rep := .repnz, rex := none, count := s.count + 1 } rest
        else if b == 0xF3#8 then
          ih { s with rep := .repz, rex := none, count := s.count + 1 } rest
        else if b == 0xF0#8 then
          ih { s with hasLock := true, rex := none, count := s.count + 1 } rest
        else if b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 ||
                b == 0x64#8 || b == 0x65#8 || b == 0x67#8 then
          ih { s with hasSegOr67 := true, rex := none, count := s.count + 1 } rest
        else if (b &&& 0xF0#8) == 0x40#8 then
          ih { s with rex := some (BitVec.extractLsb' 0 4 b), count := s.count + 1 } rest
        else
          (s, b :: rest))
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

/-- Exact ModR/M (+ SIB + displacement) byte length from the ModR/M stream. -/
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

/-- Stage-1 Instruction Length Decoder (`ildBodyLen`): computes the exact non-prefix
    body byte count `bLen ≥ 1` required from `body` before opcode parsing. -/
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
      let immSz := if op0 == 0xC7#8 then (if ps.has66 && !rexW ps.rex then 2 else 4)
                   else (if ps.has66 && !rexW ps.rex then 2 else 4)
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
      -- Standard 1-byte ModR/M opcodes (`00..03`, `08..0B`, `20..23`, `28..2B`, `30..33`,
      -- `38..3B`, `63`, `84`, `85`, `87`, `88..8B`, `8D`, `D0..D3`, `F7`, `FF`, etc.)
      Option.map (· + 1) (modrmByteLen rest0)

/-- Parse ModR/M (+ SIB + displacement), returning `(regIdx, RmOp, mrmByte, rest)`. -/
def parseModRm (rBit xBit bBit : Bool) :
    List (BitVec 8) → Option (Nat × RmOp × BitVec 8 × List (BitVec 8))
  | [] => none
  | mrm :: rest =>
    let mod2 := (BitVec.extractLsb' 6 2 mrm).toNat
    let reg3 := BitVec.extractLsb' 3 3 mrm
    let rm3  := BitVec.extractLsb' 0 3 mrm
    let regIdx := mkRegIdx rBit reg3
    let rmIdx  := mkRegIdx bBit rm3
    if mod2 == 3 then
      some (regIdx, .reg (gprOfNat rmIdx), mrm, rest)
    else if rm3.toNat == 4 then
      match rest with
      | [] => none
      | sib :: restSib =>
        let scale2 := (BitVec.extractLsb' 6 2 sib).toNat
        let idx3   := BitVec.extractLsb' 3 3 sib
        let base3  := BitVec.extractLsb' 0 3 sib
        let idxFull := mkRegIdx xBit idx3
        let baseFull := mkRegIdx bBit base3
        let indexOpt : Option (Gpr × Nat) :=
          if idxFull == 4 then none else some (gprOfNat idxFull, scale2)
        if mod2 == 0 && base3.toNat == 5 then
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := none, index := indexOpt, disp := sext32To64 d32 }, mrm, restD)
        else if mod2 == 0 then
          some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := 0#64 }, mrm, restSib)
        else if mod2 == 1 then
          match restSib with
          | [] => none
          | d8 :: restD =>
            some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := sext8To64 d8 }, mrm, restD)
        else
          match readLe32? restSib with
          | none => none
          | some (d32, restD) =>
            some (regIdx, .mem { base := some (gprOfNat baseFull), index := indexOpt, disp := sext32To64 d32 }, mrm, restD)
    else if mod2 == 0 && rm3.toNat == 5 then
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := none, index := none, disp := sext32To64 d32, ripRel := true }, mrm, restD)
    else if mod2 == 0 then
      some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := 0#64 }, mrm, rest)
    else if mod2 == 1 then
      match rest with
      | [] => none
      | d8 :: restD =>
        some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := sext8To64 d8 }, mrm, restD)
    else
      match readLe32? rest with
      | none => none
      | some (d32, restD) =>
        some (regIdx, .mem { base := some (gprOfNat rmIdx), index := none, disp := sext32To64 d32 }, mrm, restD)

def rmToRm8 (rexPresent bBit : Bool) (mrmByte : BitVec 8) : RmOp → Rm8Op
  | .reg _ => .reg8 (reg8OfIdx rexPresent bBit (BitVec.extractLsb' 0 3 mrmByte))
  | .mem a => .mem8 a

def rmToXmm (bBit : Bool) (mrmByte : BitVec 8) : RmOp → XmmRmOp
  | .reg _ => .reg (ymmIdxOfNat (mkRegIdx bBit (BitVec.extractLsb' 0 3 mrmByte)))
  | .mem a => .mem a

/-- Shared SIMD opcode body parser used by BOTH VEX (`C5`/`C4`) and Legacy Non-VEX SSE2!
    - `isVex = false`: `s1 = dst = regY`, `lBit = false` (`SimdMode.legacy128`).
    - `isVex = true`:  `dst = regY`, `s1 = vvvvY` (or checked `vvvv == 0` for 2-op forms),
      `SimdMode.vex128` (`L = 0`) vs `SimdMode.vex256` (`L = 1`). -/
def parseSimdOpc (isVex rBit xBit bBit wBit lBit : Bool) (vvvv : Nat)
    (mapSel pp : Nat) (opc : BitVec 8) (afterOpc : List (BitVec 8)) :
    Except FaultKind Instr :=
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

/-- Stage-2 Exact-Slice Body Parser (`parseExactBody`): consumes only the exact
    `bLen`-byte body slice (`bodySlice = body.take bLen`). -/
def parseExactBody (ps : PrefixState) (bodySlice : List (BitVec 8)) : Except FaultKind Instr :=
  let rBit := rexR ps.rex
  let xBit := rexX ps.rex
  let bBit := rexB ps.rex
  let wBit := rexW ps.rex
  let rexP := ps.rex.isSome
  let sz   := opSizeOf ps
  match bodySlice with
  | [] => .error .udUnmapped
  | op0 :: rest0 =>
    -- VEX 2-byte (`0xC5`) and 3-byte (`0xC4`)
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
    -- Reject illegal `LOCK` (`0xF0`) on non-atomic opcodes in this slice
    else if ps.hasLock then
      .error .udIllegalLock
    -- 1-byte standalone opcodes
    else if op0 == 0x90#8 then
      if bBit then .ok (.xchg sz (gprOfNat 8) (.reg .rax)) else .ok .nop
    else if op0 == 0xC3#8 then .ok .ret64
    else if op0 == 0xC9#8 then .ok .leave64
    else if op0 == 0xFA#8 then .error .gp0Privilege
    else if op0.toNat >= 0x50 && op0.toNat <= 0x57 then
      .ok (.push64 (gprOfNat ((if bBit then 8 else 0) + (op0.toNat - 0x50))))
    else if op0.toNat >= 0x58 && op0.toNat <= 0x5F then
      .ok (.pop64 (gprOfNat ((if bBit then 8 else 0) + (op0.toNat - 0x58))))
    else if op0 == 0xEB#8 then
      match rest0 with
      | d8 :: _ => .ok (.jmpRel (sext8To64 d8))
      | [] => .error .udUnmapped
    else if op0 == 0xE9#8 then
      match readLe32? rest0 with
      | some (d32, _) => .ok (.jmpRel (sext32To64 d32))
      | none => .error .udUnmapped
    else if op0.toNat >= 0x70 && op0.toNat <= 0x7F then
      match rest0 with
      | d8 :: _ => .ok (.jccRel (condOfNib (op0.toNat - 0x70)) (sext8To64 d8))
      | [] => .error .udUnmapped
    else if op0 == 0xA8#8 then
      match rest0 with
      | imm8 :: _ => .ok (.alu8Imm .test (.reg8 (.lo8 .rax)) imm8)
      | [] => .error .udUnmapped
    else if op0.toNat >= 0xB0 && op0.toNat <= 0xB7 then
      match rest0 with
      | imm8 :: _ =>
        let r8 := reg8OfIdx rexP bBit (BitVec.ofNat 3 (op0.toNat - 0xB0))
        .ok (.mov8Imm (.reg8 r8) imm8)
      | [] => .error .udUnmapped
    else if op0.toNat >= 0xB8 && op0.toNat <= 0xBF then
      let dst := gprOfNat ((if bBit then 8 else 0) + (op0.toNat - 0xB8))
      if wBit then
        match readLe64? rest0 with
        | some (imm64, _) => .ok (.movImm .s64 dst imm64)
        | none => .error .udUnmapped
      else if ps.has66 then
        match readLe16? rest0 with
        | some (imm16, _) => .ok (.movImm .s16 dst (imm16.zeroExtend 64))
        | none => .error .udUnmapped
      else
        match readLe32? rest0 with
        | some (imm32, _) => .ok (.movImm .s32 dst (imm32.zeroExtend 64))
        | none => .error .udUnmapped
    -- `0x0F` two-byte escape (GP + Legacy Non-VEX SSE2!)
    else if op0 == 0x0F#8 then
      match rest0 with
      | [] => .error .udUnmapped
      | op1 :: rest1 =>
        if op1 == 0x0B#8 then .error .udExplicit
        else if op1.toNat >= 0x80 && op1.toNat <= 0x8F then
          match readLe32? rest1 with
          | some (d32, _) => .ok (.jccRel (condOfNib (op1.toNat - 0x80)) (sext32To64 d32))
          | none => .error .udUnmapped
        else if op1 == 0x1E#8 then
          match parseModRm rBit xBit bBit rest1 with
          | some (_, _, mrm, _) => if ps.rep == .repz && mrm == 0xFA#8 then .ok .endbr64 else .ok .nop
          | none => .error .udUnmapped
        else if op1 == 0x1F#8 then
          -- Multi-byte ModR/M `NOP` (`0F 1F /r` up to 15 bytes, zero memory access)
          match parseModRm rBit xBit bBit rest1 with
          | some _ => .ok .nop
          | none => .error .udUnmapped
        else if op1 == 0xB6#8 || op1 == 0xB7#8 || op1 == 0xBE#8 || op1 == 0xBF#8 ||
                op1 == 0xAF#8 || op1 == 0xBC#8 || (op1.toNat >= 0x90 && op1.toNat <= 0x9F) then
          match parseModRm rBit xBit bBit rest1 with
          | none => .error .udUnmapped
          | some (regIdx, rm, mrm, _) =>
            let dst := gprOfNat regIdx
            let rm8 := rmToRm8 rexP bBit mrm rm
            if op1 == 0xB6#8 then .ok (.movzx8 sz dst rm8)
            else if op1 == 0xB7#8 then .ok (.movzx16 sz dst rm)
            else if op1 == 0xBE#8 then .ok (.movsx8 sz dst rm8)
            else if op1 == 0xBF#8 then .ok (.movsx16 sz dst rm)
            else if op1 == 0xAF#8 then .ok (.imul2 sz dst rm)
            else if op1 == 0xBC#8 then .ok (.bsf sz dst rm)
            else .ok (.setcc8 (condOfNib (op1.toNat - 0x90)) rm8)
        else
          -- Legacy Non-VEX SSE2 (`0F 10`/`11` `pp=0`, `66 0F` `pp=1`, `F3 0F` `pp=2`, `F2 0F` `pp=3`)
          let pp := match ps.rep with
            | .repz  => 2
            | .repnz => 3
            | .none  => if ps.has66 then 1 else 0
          parseSimdOpc false rBit xBit bBit wBit false 0 1 pp op1 rest1
    -- Standard 1-byte ModR/M GP instructions
    else
      match parseModRm rBit xBit bBit rest0 with
      | none => .error .udUnmapped
      | some (regIdx, rm, mrm, tail) =>
        let regG := gprOfNat regIdx
        let reg3 := BitVec.extractLsb' 3 3 mrm
        let r8   := reg8OfIdx rexP rBit reg3
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
          match rm with
          | .mem a => .ok (.lea sz regG a)
          | .reg _ => .error .udRegisterOperand
        else if op0 == 0x63#8 then
          if wBit then .ok (.movsxd regG rm) else .ok (.movLoad .s32 regG rm)
        else if op0 == 0x87#8 then .ok (.xchg sz regG rm)
        else if op0 == 0x84#8 then .ok (.alu8RmReg .test rm8 r8)
        else if op0 == 0x85#8 then .ok (.aluRmReg sz .test rm regG)
        else if op0 == 0xF6#8 && reg3.toNat == 0 then
          match tail with | imm8 :: _ => .ok (.alu8Imm .test rm8 imm8) | [] => .error .udUnmapped
        else if op0 == 0x80#8 then
          match aluOpOfIdx reg3.toNat, tail with
          | some op, imm8 :: _ => .ok (.alu8Imm op rm8 imm8)
          | _, _ => .error .udUnmapped
        else if op0 == 0x83#8 then
          match aluOpOfIdx reg3.toNat, tail with
          | some op, imm8 :: _ => .ok (.aluImm sz op rm (sext8To64 imm8))
          | _, _ => .error .udUnmapped
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
          | some sop, imm8 :: _ =>
            if op0 == 0xC1#8 then .ok (.shiftImm sz sop rm imm8) else .error .udUnmapped
          | _, _ => .error .udUnmapped
        else if op0 == 0xD1#8 then
          match shiftOpOfIdx reg3.toNat with
          | some sop => .ok (.shiftImm sz sop rm 1#8)
          | none => .error .udUnmapped
        else if op0 == 0xF7#8 then
          if reg3.toNat == 2 then .ok (.unaryRm sz .not rm)
          else if reg3.toNat == 3 then .ok (.unaryRm sz .neg rm)
          else if reg3.toNat == 0 then
            -- `F7 /0`: has 16/32-bit immediate, not used here
            .error .udUnmapped
          else .error .udUnmapped
        else if op0 == 0xFF#8 then
          if reg3.toNat == 0 then .ok (.unaryRm sz .inc rm)
          else if reg3.toNat == 1 then .ok (.unaryRm sz .dec rm)
          else .error .udUnmapped
        else
          -- Binary ALU family (`00..03`, `08..0B`, `10..13`, `18..1B`, `20..23`, `28..2B`, `30..33`, `38..3B`)
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

/-- 16-byte fetch-window decoder of `VendorX86GccRef`. -/
def decodeRef (window16 : List (BitVec 8)) : DecodeResult :=
  let (ps, body) := scanPrefixes 16 {} window16
  if ps.count >= 15 && body.isEmpty then
    .fault .gp0LengthExceeds15
  else if ps.count > 14 then
    .fault .gp0LengthExceeds15
  else
    match ildBodyLen ps body with
    | none => .fault .udUnmapped
    | some bLen =>
      if ps.count + bLen > 15 then
        .fault .gp0LengthExceeds15
      else
        match parseExactBody ps (body.take bLen) with
        | .error fk => .fault fk
        | .ok ins   => .ok ins (ps.count + bLen)

/-! ## Section 3: Architectural Scalar & SIMD Operational Semantics -/

structure MachineState where
  rip    : BitVec 64 := 0#64
  gpr    : Gpr → BitVec 64 := fun _ => 0#64
  ymm    : YmmIdx → BitVec 256 := fun _ => 0#256
  flags  : RFlags := {}
  mem    : ByteMem := fun _ => 0#8
  halted : Bool := false
  fault  : Option FaultKind := none

def parity8 (lo : BitVec 8) : Bool :=
  !(lo.getLsbD 0 ^^ lo.getLsbD 1 ^^ lo.getLsbD 2 ^^ lo.getLsbD 3 ^^
    lo.getLsbD 4 ^^ lo.getLsbD 5 ^^ lo.getLsbD 6 ^^ lo.getLsbD 7)

def evalCond (cc : Cond) (f : RFlags) : Bool :=
  match cc with
  | .o  => f.of
  | .no => !f.of
  | .b  => f.cf
  | .ae => !f.cf
  | .e  => f.zf
  | .ne => !f.zf
  | .be => f.cf || f.zf
  | .a  => !f.cf && !f.zf
  | .s  => f.sf
  | .ns => !f.sf
  | .p  => f.pf
  | .np => !f.pf
  | .l  => f.sf != f.of
  | .ge => f.sf == f.of
  | .le => f.zf || (f.sf != f.of)
  | .g  => !f.zf && (f.sf == f.of)

def evalAddr (s : MachineState) (nextRip : BitVec 64) (a : MemAddr) : BitVec 64 :=
  let baseV := if a.ripRel then nextRip else match a.base with | some g => s.gpr g | none => 0#64
  let idxV  := match a.index with | some (g, sc) => (s.gpr g) <<< sc | none => 0#64
  baseV + idxV + a.disp

def readRm8 (s : MachineState) (nextRip : BitVec 64) : Rm8Op → BitVec 8
  | .reg8 r => readReg8 s.gpr r
  | .mem8 a => readMem8 s.mem (evalAddr s nextRip a)

def writeRm8 (s : MachineState) (nextRip : BitVec 64) (dst : Rm8Op) (v : BitVec 8) : MachineState :=
  match dst with
  | .reg8 r => { s with gpr := writeReg8 s.gpr r v }
  | .mem8 a => { s with mem := memUpd8 s.mem (evalAddr s nextRip a) v }

def readRm (sz : OpSize) (s : MachineState) (nextRip : BitVec 64) : RmOp → BitVec 64
  | .reg g => readGprSz sz s.gpr g
  | .mem a =>
    let ea := evalAddr s nextRip a
    match sz with
    | .s64 => readMem64 s.mem ea
    | .s32 => (readMem32 s.mem ea).zeroExtend 64
    | .s16 => (readMem16 s.mem ea).zeroExtend 64

def writeRm (sz : OpSize) (s : MachineState) (nextRip : BitVec 64) (dst : RmOp) (v : BitVec 64) :
    MachineState :=
  match dst with
  | .reg g => { s with gpr := writeGprSz sz s.gpr g v }
  | .mem a =>
    let ea := evalAddr s nextRip a
    match sz with
    | .s64 => { s with mem := writeMem64 s.mem ea v }
    | .s32 => { s with mem := writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v) }
    | .s16 => { s with mem := writeMem16 s.mem ea (BitVec.extractLsb' 0 16 v) }

def readXmm128 (s : MachineState) (nextRip : BitVec 64) : XmmRmOp → BitVec 128
  | .reg y => BitVec.extractLsb' 0 128 (s.ymm y)
  | .mem a => readMem128 s.mem (evalAddr s nextRip a)

def readYmm256 (s : MachineState) (nextRip : BitVec 64) : XmmRmOp → BitVec 256
  | .reg y => s.ymm y
  | .mem a => readMem256 s.mem (evalAddr s nextRip a)

def evalAluN {w : Nat} (hw : 0 < w) (op : AluOp) (a b : BitVec w) (oldF undefF : RFlags) :
    BitVec w × RFlags :=
  let cin : Nat := if oldF.cf then 1 else 0
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
    let _ := hw
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
  | .neg =>
    let (res, fl) := evalAluSz sz .sub 0#64 v oldF oldF
    (res, { fl with cf := !fl.zf })
  | .inc =>
    let (res, fl) := evalAluSz sz .add v 1#64 oldF oldF
    (res, { fl with cf := oldF.cf })
  | .dec =>
    let (res, fl) := evalAluSz sz .sub v 1#64 oldF oldF
    (res, { fl with cf := oldF.cf })

def evalShiftSz (sz : OpSize) (op : ShiftOp) (v : BitVec 64) (rawCnt : BitVec 8)
    (oldF undefF : RFlags) : BitVec 64 × RFlags :=
  let mask := if sz == .s64 then 63 else 31
  let c := rawCnt.toNat &&& mask
  if c == 0 then (v, oldF)
  else
    match sz with
    | .s64 =>
      let r64 : BitVec 64 := match op with
        | .rol => BitVec.rotateLeft v c
        | .ror => BitVec.rotateRight v c
        | .shl => v <<< c
        | .shr => v >>> c
        | .sar => BitVec.sshiftRight v c
      let cf := match op with
        | .rol => r64.getLsbD 0
        | .ror => r64.msb
        | .shl => v.getLsbD (64 - c)
        | .shr | .sar => v.getLsbD (c - 1)
      let fl : RFlags := match op with
        | .rol | .ror => { oldF with cf, of := undefF.of }
        | _ => { cf, pf := parity8 (BitVec.extractLsb' 0 8 r64), af := undefF.af,
                 zf := r64 == 0#64, sf := r64.msb, of := undefF.of }
      (r64, fl)
    | .s32 =>
      let v32 := BitVec.extractLsb' 0 32 v
      let r32 : BitVec 32 := match op with
        | .rol => BitVec.rotateLeft v32 c
        | .ror => BitVec.rotateRight v32 c
        | .shl => v32 <<< c
        | .shr => v32 >>> c
        | .sar => BitVec.sshiftRight v32 c
      let cf := match op with
        | .rol => r32.getLsbD 0
        | .ror => r32.msb
        | .shl => v32.getLsbD (32 - c)
        | .shr | .sar => v32.getLsbD (c - 1)
      let fl : RFlags := match op with
        | .rol | .ror => { oldF with cf, of := undefF.of }
        | _ => { cf, pf := parity8 (BitVec.extractLsb' 0 8 r32), af := undefF.af,
                 zf := r32 == 0#32, sf := r32.msb, of := undefF.of }
      (r32.zeroExtend 64, fl)
    | .s16 =>
      let v16 := BitVec.extractLsb' 0 16 v
      let r16 : BitVec 16 := match op with
        | .rol => BitVec.rotateLeft v16 (c % 16)
        | .ror => BitVec.rotateRight v16 (c % 16)
        | .shl => v16 <<< c
        | .shr => v16 >>> c
        | .sar => BitVec.sshiftRight v16 c
      (r16.zeroExtend 64, { undefF with zf := r16 == 0#16, sf := r16.msb })

def evalImulSz (sz : OpSize) (a b : BitVec 64) (undefF : RFlags) : BitVec 64 × RFlags :=
  match sz with
  | .s64 =>
    let prod : Int := a.toInt * b.toInt
    let lo64 : BitVec 64 := a * b
    let ov := decide (prod != lo64.toInt)
    (lo64, { undefF with cf := ov, of := ov })
  | .s32 =>
    let a32 := BitVec.extractLsb' 0 32 a
    let b32 := BitVec.extractLsb' 0 32 b
    let prod : Int := a32.toInt * b32.toInt
    let lo32 : BitVec 32 := a32 * b32
    let ov := decide (prod != lo32.toInt)
    (lo32.zeroExtend 64, { undefF with cf := ov, of := ov })
  | .s16 =>
    let a16 := BitVec.extractLsb' 0 16 a
    let b16 := BitVec.extractLsb' 0 16 b
    let prod : Int := a16.toInt * b16.toInt
    let lo16 : BitVec 16 := a16 * b16
    let ov := decide (prod != lo16.toInt)
    (lo16.zeroExtend 64, { undefF with cf := ov, of := ov })

def ctzLoop (n : Nat) (v : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    64
    (fun k ih => if v.getLsbD (63 - k) then 63 - k else ih)
    n

/-! ### 128-bit & 256-bit SIMD Pure Lane Helpers -/

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
  packWords128 fun i =>
    let prod : Nat := (getWord128 a i).toNat * (getWord128 b i).toNat
    BitVec.ofNat 16 (prod / 65536)

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
  let loWords : BitVec 64 :=
    let w (k : Nat) : BitVec 16 :=
      let sel := (BitVec.extractLsb' (2 * k) 2 imm).toNat
      getWord128 a ⟨sel % 4, by omega⟩
    w 3 ++ (w 2 ++ (w 1 ++ w 0))
  hi64 ++ loWords

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
      | 0 => BitVec.extractLsb' 0 128 a
      | 1 => BitVec.extractLsb' 128 128 a
      | 2 => BitVec.extractLsb' 0 128 b
      | _ => BitVec.extractLsb' 128 128 b
  pick ((BitVec.extractLsb' 4 4 imm).toNat) ++ pick ((BitVec.extractLsb' 0 4 imm).toNat)

def extend128 (op : VecExtendOp) (s : MachineState) (nextRip : BitVec 64) (src : XmmRmOp) : BitVec 128 :=
  match op with
  | .zxbw =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packWords128 fun i => (BitVec.extractLsb' (i.val * 8) 8 raw64).zeroExtend 16
  | .sxbw =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packWords128 fun i =>
      let b := BitVec.extractLsb' (i.val * 8) 8 raw64
      (if b.msb then 0xFF#8 else 0x00#8) ++ b
  | .zxwd =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packDwords128 fun i => (BitVec.extractLsb' (i.val * 16) 16 raw64).zeroExtend 32
  | .sxwd =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packDwords128 fun i =>
      let w := BitVec.extractLsb' (i.val * 16) 16 raw64
      (if w.msb then 0xFFFF#16 else 0x0000#16) ++ w
  | .zxdq =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packQwords128 fun i => (BitVec.extractLsb' (i.val * 32) 32 raw64).zeroExtend 64
  | .sxdq =>
    let raw64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    packQwords128 fun i => sext32To64 (BitVec.extractLsb' (i.val * 32) 32 raw64)

def extend256 (op : VecExtendOp) (s : MachineState) (nextRip : BitVec 64) (src : XmmRmOp) : BitVec 256 :=
  let raw128 := readXmm128 s nextRip src
  match op with
  | .zxbw => packWords256 fun i => (getByte128 raw128 i).zeroExtend 16
  | .sxbw => packWords256 fun i => let b := getByte128 raw128 i; (if b.msb then 0xFF#8 else 0x00#8) ++ b
  | .zxwd => packDwords256 fun i => (getWord128 raw128 i).zeroExtend 32
  | .sxwd => packDwords256 fun i => let w := getWord128 raw128 i; (if w.msb then 0xFFFF#16 else 0x0000#16) ++ w
  | .zxdq => packQwords256 fun i => (getDword128 raw128 i).zeroExtend 64
  | .sxdq => packQwords256 fun i => sext32To64 (getDword128 raw128 i)

def apply128Or256 (m : SimdMode) (ymms : YmmIdx → BitVec 256) (dst : YmmIdx)
    (f128 : BitVec 128 → BitVec 128 → BitVec 128) (a256 b256 : BitVec 256) :
    YmmIdx → BitVec 256 :=
  match m with
  | .legacy128 =>
    writeXmmResult false ymms dst (f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256))
  | .vex128 =>
    writeXmmResult true ymms dst (f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256))
  | .vex256 =>
    let lo := f128 (BitVec.extractLsb' 0 128 a256) (BitVec.extractLsb' 0 128 b256)
    let hi := f128 (BitVec.extractLsb' 128 128 a256) (BitVec.extractLsb' 128 128 b256)
    ymmUpd ymms dst (hi ++ lo)

def readModeRhs (m : SimdMode) (s : MachineState) (nextRip : BitVec 64) (xrm : XmmRmOp) : BitVec 256 :=
  match m with
  | .vex256 => readYmm256 s nextRip xrm
  | _       => (readXmm128 s nextRip xrm).zeroExtend 256

/-- Single-instruction execution of `VendorX86GccRef`. -/
def execInstr (ins : Instr) (nextRip : BitVec 64) (oracle : UndefOracle) (s : MachineState) :
    MachineState :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .nop | .endbr64 => sRip
  | .vzeroupper     => { sRip with ymm := vzeroUpperAll s.ymm }
  | .ud2            => { s with fault := some .udExplicit }
  | .cli            => { s with fault := some .gp0Privilege }
  -- 8-bit GP sub-register operations
  | .mov8Load dst src =>
    { sRip with gpr := writeReg8 s.gpr dst (readRm8 s nextRip src) }
  | .mov8Store dst src =>
    writeRm8 sRip nextRip dst (readReg8 s.gpr src)
  | .mov8Imm dst imm =>
    writeRm8 sRip nextRip dst imm
  | .alu8RmReg op dst src =>
    let (res, fl) := evalAluN (by decide) op (readRm8 s nextRip dst) (readReg8 s.gpr src) s.flags oracle.flags
    let s1 := if op == .cmp || op == .test then sRip else writeRm8 sRip nextRip dst res
    { s1 with flags := fl }
  | .alu8RegRm op dst src =>
    let (res, fl) := evalAluN (by decide) op (readReg8 s.gpr dst) (readRm8 s nextRip src) s.flags oracle.flags
    let gpr' := if op == .cmp || op == .test then s.gpr else writeReg8 s.gpr dst res
    { sRip with gpr := gpr', flags := fl }
  | .alu8Imm op dst imm =>
    let (res, fl) := evalAluN (by decide) op (readRm8 s nextRip dst) imm s.flags oracle.flags
    let s1 := if op == .cmp || op == .test then sRip else writeRm8 sRip nextRip dst res
    { s1 with flags := fl }
  | .setcc8 cc dst =>
    writeRm8 sRip nextRip dst (if evalCond cc s.flags then 1#8 else 0#8)
  -- Zero/sign-extending sub-word moves
  | .movzx8 sz dst src =>
    { sRip with gpr := writeGprSz sz s.gpr dst ((readRm8 s nextRip src).zeroExtend 64) }
  | .movzx16 sz dst src =>
    let v16 := BitVec.extractLsb' 0 16 (readRm .s16 s nextRip src)
    { sRip with gpr := writeGprSz sz s.gpr dst (v16.zeroExtend 64) }
  | .movsx8 sz dst src =>
    { sRip with gpr := writeGprSz sz s.gpr dst (sext8To64 (readRm8 s nextRip src)) }
  | .movsx16 sz dst src =>
    let v16 := BitVec.extractLsb' 0 16 (readRm .s16 s nextRip src)
    { sRip with gpr := writeGprSz sz s.gpr dst (sext16To64 v16) }
  | .movsxd dst src =>
    let v32 := BitVec.extractLsb' 0 32 (readRm .s32 s nextRip src)
    { sRip with gpr := gprUpd s.gpr dst (sext32To64 v32) }
  -- 16/32/64-bit GP operations
  | .movLoad sz dst src =>
    { sRip with gpr := writeGprSz sz s.gpr dst (readRm sz s nextRip src) }
  | .movStore sz dst src =>
    writeRm sz sRip nextRip dst (readGprSz sz s.gpr src)
  | .movImm sz dst imm =>
    { sRip with gpr := writeGprSz sz s.gpr dst imm }
  | .movRmImm32 sz dst imm =>
    writeRm sz sRip nextRip dst imm
  | .lea sz dst addr =>
    { sRip with gpr := writeGprSz sz s.gpr dst (evalAddr s nextRip addr) }
  | .xchg sz r1 rm =>
    let v1 := readGprSz sz s.gpr r1
    let v2 := readRm sz s nextRip rm
    let s1 := writeRm sz sRip nextRip rm v1
    { s1 with gpr := writeGprSz sz s1.gpr r1 v2 }
  | .aluRmReg sz op dst src =>
    let (res, fl) := evalAluSz sz op (readRm sz s nextRip dst) (readGprSz sz s.gpr src) s.flags oracle.flags
    let s1 := if op == .cmp || op == .test then sRip else writeRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .aluRegRm sz op dst src =>
    let (res, fl) := evalAluSz sz op (readGprSz sz s.gpr dst) (readRm sz s nextRip src) s.flags oracle.flags
    let gpr' := if op == .cmp || op == .test then s.gpr else writeGprSz sz s.gpr dst res
    { sRip with gpr := gpr', flags := fl }
  | .aluImm sz op dst imm =>
    let (res, fl) := evalAluSz sz op (readRm sz s nextRip dst) imm s.flags oracle.flags
    let s1 := if op == .cmp || op == .test then sRip else writeRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .unaryRm sz op dst =>
    let (res, fl) := evalUnarySz sz op (readRm sz s nextRip dst) s.flags
    let s1 := writeRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .shiftImm sz op dst cnt =>
    let (res, fl) := evalShiftSz sz op (readRm sz s nextRip dst) cnt s.flags oracle.flags
    let s1 := writeRm sz sRip nextRip dst res
    { s1 with flags := fl }
  | .imul2 sz dst src =>
    let (res, fl) := evalImulSz sz (readGprSz sz s.gpr dst) (readRm sz s nextRip src) oracle.flags
    { sRip with gpr := writeGprSz sz s.gpr dst res, flags := fl }
  | .imul3 sz dst src imm =>
    let (res, fl) := evalImulSz sz (readRm sz s nextRip src) imm oracle.flags
    { sRip with gpr := writeGprSz sz s.gpr dst res, flags := fl }
  | .bsf sz dst src =>
    let v := readRm sz s nextRip src
    if v == 0#64 then
      { sRip with gpr := writeGprSz sz s.gpr dst oracle.gpr, flags := { oracle.flags with zf := true } }
    else
      let idx := BitVec.ofNat 64 (ctzLoop 64 v)
      { sRip with gpr := writeGprSz sz s.gpr dst idx, flags := { oracle.flags with zf := false } }
  -- Stack & Control Flow
  | .push64 src =>
    let newRsp := s.gpr .rsp - 8#64
    { sRip with gpr := gprUpd s.gpr .rsp newRsp, mem := writeMem64 s.mem newRsp (s.gpr src) }
  | .pop64 dst =>
    let oldRsp := s.gpr .rsp
    let popped := readMem64 s.mem oldRsp
    { sRip with gpr := gprUpd (gprUpd s.gpr .rsp (oldRsp + 8#64)) dst popped }
  | .leave64 =>
    let fp := s.gpr .rbp
    let savedRbp := readMem64 s.mem fp
    { sRip with gpr := gprUpd (gprUpd s.gpr .rsp (fp + 8#64)) .rbp savedRbp }
  | .ret64 =>
    -- System V function-level return pops return address or halts at top-level FFI boundary
    { s with halted := true }
  | .jmpRel rel =>
    { s with rip := nextRip + rel }
  | .jccRel cc rel =>
    { s with rip := if evalCond cc s.flags then nextRip + rel else nextRip }
  -- Legacy Non-VEX SSE2 & VEX SIMD
  | .simdMovLoad m dst src =>
    match m with
    | .legacy128 => { sRip with ymm := writeXmmResult false s.ymm dst (readXmm128 s nextRip src) }
    | .vex128    => { sRip with ymm := writeXmmResult true  s.ymm dst (readXmm128 s nextRip src) }
    | .vex256    => { sRip with ymm := ymmUpd s.ymm dst (readYmm256 s nextRip src) }
  | .simdMovStore m dst src =>
    match dst with
    | .reg dstY =>
      match m with
      | .legacy128 => { sRip with ymm := writeXmmResult false s.ymm dstY (BitVec.extractLsb' 0 128 (s.ymm src)) }
      | .vex128    => { sRip with ymm := writeXmmResult true  s.ymm dstY (BitVec.extractLsb' 0 128 (s.ymm src)) }
      | .vex256    => { sRip with ymm := ymmUpd s.ymm dstY (s.ymm src) }
    | .mem a =>
      let ea := evalAddr s nextRip a
      match m with
      | .vex256 => { sRip with mem := writeMem256 s.mem ea (s.ymm src) }
      | _       => { sRip with mem := writeMem128 s.mem ea (BitVec.extractLsb' 0 128 (s.ymm src)) }
  | .simdMovqLoad isVex dst src =>
    let lo64 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    { sRip with ymm := writeXmmResult isVex s.ymm dst (lo64.zeroExtend 128) }
  | .simdMovqStore isVex dst src =>
    let lo64 := BitVec.extractLsb' 0 64 (s.ymm src)
    match dst with
    | .reg y => { sRip with ymm := writeXmmResult isVex s.ymm y (lo64.zeroExtend 128) }
    | .mem a => { sRip with mem := writeMem64 s.mem (evalAddr s nextRip a) lo64 }
  | .simdMovGprToX isVex is64 dst src =>
    let v64 := readRm (if is64 then .s64 else .s32) s nextRip src
    { sRip with ymm := writeXmmResult isVex s.ymm dst (v64.zeroExtend 128) }
  | .simdMovXToGpr _isVex is64 dst src =>
    let v64 := BitVec.extractLsb' 0 64 (s.ymm src)
    writeRm (if is64 then .s64 else .s32) sRip nextRip dst v64
  | .simdBitwise m op dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match op with
      | .and => (· &&& ·) | .or => (· ||| ·) | _ => (· ^^^ ·)
    { sRip with ymm := apply128Or256 m s.ymm dst f128 (s.ymm s1) rhs }
  | .simdAdd m ew dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => getByte128  a i + getByte128  b i
      | .e16 => fun a b => packWords128  fun i => getWord128  a i + getWord128  b i
      | .e32 => fun a b => packDwords128 fun i => getDword128 a i + getDword128 b i
      | .e64 => fun a b => packQwords128 fun i => getQword128 a i + getQword128 b i
    { sRip with ymm := apply128Or256 m s.ymm dst f128 (s.ymm s1) rhs }
  | .simdSub m ew dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => getByte128  a i - getByte128  b i
      | .e16 => fun a b => packWords128  fun i => getWord128  a i - getWord128  b i
      | .e32 => fun a b => packDwords128 fun i => getDword128 a i - getDword128 b i
      | .e64 => fun a b => packQwords128 fun i => getQword128 a i - getQword128 b i
    { sRip with ymm := apply128Or256 m s.ymm dst f128 (s.ymm s1) rhs }
  | .simdCmpeq m ew dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => if getByte128  a i == getByte128  b i then 0xFF#8 else 0#8
      | .e16 => fun a b => packWords128  fun i => if getWord128  a i == getWord128  b i then 0xFFFF#16 else 0#16
      | .e32 => fun a b => packDwords128 fun i => if getDword128 a i == getDword128 b i then 0xFFFFFFFF#32 else 0#32
      | .e64 => fun a b => packQwords128 fun i => if getQword128 a i == getQword128 b i then 0xFFFFFFFFFFFFFFFF#64 else 0#64
    { sRip with ymm := apply128Or256 m s.ymm dst f128 (s.ymm s1) rhs }
  | .simdCmpgt m ew dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    let f128 : BitVec 128 → BitVec 128 → BitVec 128 := match ew with
      | .e8  => fun a b => packBytes128  fun i => if (getByte128  b i).slt (getByte128  a i) then 0xFF#8 else 0#8
      | .e16 => fun a b => packWords128  fun i => if (getWord128  b i).slt (getWord128  a i) then 0xFFFF#16 else 0#16
      | .e32 => fun a b => packDwords128 fun i => if (getDword128 b i).slt (getDword128 a i) then 0xFFFFFFFF#32 else 0#32
      | .e64 => fun a b => packQwords128 fun i => if (getQword128 b i).slt (getQword128 a i) then 0xFFFFFFFFFFFFFFFF#64 else 0#64
    { sRip with ymm := apply128Or256 m s.ymm dst f128 (s.ymm s1) rhs }
  | .simdUnpack m op dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    { sRip with ymm := apply128Or256 m s.ymm dst (unpack128 op) (s.ymm s1) rhs }
  | .simdExtend m op dst src =>
    match m with
    | .vex256    => { sRip with ymm := ymmUpd s.ymm dst (extend256 op s nextRip src) }
    | .vex128    => { sRip with ymm := writeXmmResult true  s.ymm dst (extend128 op s nextRip src) }
    | .legacy128 => { sRip with ymm := writeXmmResult false s.ymm dst (extend128 op s nextRip src) }
  | .simdBroadcastB m dst src =>
    let b0 : BitVec 8 := match src with
      | .reg y => BitVec.extractLsb' 0 8 (s.ymm y)
      | .mem a => readMem8 s.mem (evalAddr s nextRip a)
    match m with
    | .vex256    => { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun _ => b0) }
    | .vex128    => { sRip with ymm := writeXmmResult true  s.ymm dst (packBytes128 fun _ => b0) }
    | .legacy128 => { sRip with ymm := writeXmmResult false s.ymm dst (packBytes128 fun _ => b0) }
  | .simdBroadcastQ m dst src =>
    let q0 : BitVec 64 := match src with
      | .reg y => BitVec.extractLsb' 0 64 (s.ymm y)
      | .mem a => readMem64 s.mem (evalAddr s nextRip a)
    match m with
    | .vex256    => { sRip with ymm := ymmUpd s.ymm dst (packQwords256 fun _ => q0) }
    | .vex128    => { sRip with ymm := writeXmmResult true  s.ymm dst (packQwords128 fun _ => q0) }
    | .legacy128 => { sRip with ymm := writeXmmResult false s.ymm dst (packQwords128 fun _ => q0) }
  | .simdPmullw m dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    { sRip with ymm := apply128Or256 m s.ymm dst pmullw128 (s.ymm s1) rhs }
  | .simdPmulhuw m dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    { sRip with ymm := apply128Or256 m s.ymm dst pmulhuw128 (s.ymm s1) rhs }
  | .simdPmulld m dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    { sRip with ymm := apply128Or256 m s.ymm dst pmulld128 (s.ymm s1) rhs }
  | .simdPmaddwd m dst s1 s2 =>
    let rhs := readModeRhs m s nextRip s2
    { sRip with ymm := apply128Or256 m s.ymm dst pmaddwd128 (s.ymm s1) rhs }
  | .simdPsrldq m dst src imm =>
    { sRip with ymm := apply128Or256 m s.ymm dst (fun a _ => psrldq128 a imm) (s.ymm src) 0#256 }
  | .simdPsrlqImm m dst src imm =>
    { sRip with ymm := apply128Or256 m s.ymm dst (fun a _ => psrlqImm128 a imm) (s.ymm src) 0#256 }
  | .simdPshufd m dst src imm =>
    let rhs := readModeRhs m s nextRip src
    { sRip with ymm := apply128Or256 m s.ymm dst (fun a _ => pshufd128 a imm) rhs 0#256 }
  | .simdPshuflw m dst src imm =>
    let rhs := readModeRhs m s nextRip src
    { sRip with ymm := apply128Or256 m s.ymm dst (fun a _ => pshuflw128 a imm) rhs 0#256 }
  | .simdExtract128 dst src imm =>
    let lane := if (imm &&& 1#8) == 0#8 then BitVec.extractLsb' 0 128 (s.ymm src)
                else BitVec.extractLsb' 128 128 (s.ymm src)
    match dst with
    | .reg y => { sRip with ymm := writeXmmResult true s.ymm y lane }
    | .mem a => { sRip with mem := writeMem128 s.mem (evalAddr s nextRip a) lane }
  | .simdPerm2i128 dst s1 s2 imm =>
    let rhs := readYmm256 s nextRip s2
    { sRip with ymm := ymmUpd s.ymm dst (perm2i128Eval (s.ymm s1) rhs imm) }

/-! ## Section 4: Top-Level Relational Machine (`Step`, `StepsN`, `execStepsN`) -/

def fetchWindow16 (code : CodeMap) (rip : BitVec 64) : List (BitVec 8) :=
  [ code (rip + 0#64),  code (rip + 1#64),  code (rip + 2#64),  code (rip + 3#64),
    code (rip + 4#64),  code (rip + 5#64),  code (rip + 6#64),  code (rip + 7#64),
    code (rip + 8#64),  code (rip + 9#64),  code (rip + 10#64), code (rip + 11#64),
    code (rip + 12#64), code (rip + 13#64), code (rip + 14#64), code (rip + 15#64) ]

def stepWithOracle (code : CodeMap) (oracle : UndefOracle) (s : MachineState) : MachineState :=
  if s.halted || s.fault.isSome then s
  else
    match decodeRef (fetchWindow16 code s.rip) with
    | .fault fk   => { s with fault := some fk }
    | .ok ins len => execInstr ins (s.rip + BitVec.ofNat 64 len) oracle s

def Step (code : CodeMap) (s s' : MachineState) : Prop :=
  ∃ oracle : UndefOracle, stepWithOracle code oracle s = s'

inductive StepsN (code : CodeMap) : Nat → MachineState → MachineState → Prop where
  | zero (s : MachineState) : StepsN code 0 s s
  | succ {n : Nat} {s s1 s2 : MachineState} :
      Step code s s1 → StepsN code n s1 s2 → StepsN code (n + 1) s s2

def execStepsN (code : CodeMap) (n : Nat) (oracle : UndefOracle) (s : MachineState) : MachineState :=
  Nat.rec (motive := fun _ => MachineState → MachineState)
    (fun s0 => s0)
    (fun _ ih s0 => ih (stepWithOracle code oracle s0))
    n s

theorem execStepsN_implies_stepsN (code : CodeMap) (n : Nat) (oracle : UndefOracle) (s : MachineState) :
    StepsN code n s (execStepsN code n oracle s) := by
  induction n generalizing s with
  | zero => exact .zero s
  | succ k ih => exact .succ ⟨oracle, rfl⟩ (ih (stepWithOracle code oracle s))

end VendorX86GccRef
