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
# `VendorX86RefV2.Types`

Repaired Pass-2 x86-64 architectural state, non-flat `FS`/`GS` segment base
registers (`fsBase`, `gsBase`), `0x67` 32-bit effective-address truncation
flag (`addr32`), `0x66` 16-bit operand-size (`OpSize.s16`), fault taxonomy,
demonic undefined-value oracle (`UNDEFINED_VALUES[...]`), and 77-form
instruction AST derived from pinned
`awslabs/s2n-bignum@d4518712d040485efe621caba1c723a07fbc549e` overlaid with
`intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` and Intel Xeon Ice
Lake-SP silicon prefix rules.
-/

namespace VendorX86RefV2

/-- Active 64-bit segment-base override (`0x64` `FS` or `0x65` `GS`). In 64-bit
    mode, `CS`/`DS`/`ES`/`SS` overrides (`0x2E`/`0x3E`/`0x26`/`0x36`) are null
    prefixes per Intel SDM Vol. 2A Section 2.1.1. -/
inductive SegReg where
  | fs
  | gs
  deriving DecidableEq, Repr

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

/-- Merge a 16-bit result into bits `15:0` of `old64`, preserving bits `63:16`
    per Intel SDM Vol. 1 Section 3.4.1.1. -/
def mergeLow16 (old64 : BitVec 64) (w16 : BitVec 16) : BitVec 64 :=
  (BitVec.extractLsb' 16 48 old64) ++ w16

/-- 16 architectural 256-bit YMM vector registers (`YMM0`..`YMM15`). -/
abbrev YmmIdx := Fin 16

def ymmIdxOfNat (n : Nat) : YmmIdx := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def ymmUpd (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v : BitVec 256) :
    YmmIdx → BitVec 256 :=
  fun idx' => if idx' = idx then v else ymms idx'

/-- Write a 128-bit VEX/EVEX result, zeroing bits `255:128` per Intel SDM Vol. 1
    Section 14.5 ("VEX-Encoded 128-Bit Instructions Zero Upper Bits"). -/
def writeVex128 (ymms : YmmIdx → BitVec 256) (idx : YmmIdx) (v128 : BitVec 128) :
    YmmIdx → BitVec 256 :=
  ymmUpd ymms idx (v128.zeroExtend 256)

/-- Six architectural status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  deriving DecidableEq, Repr

/-- Per-step demonic nondeterminism oracle representing `s2n-bignum`'s
    `UNDEFINED_VALUES[CF;OF;SF;PF;AF]` and `UNDEFINED_VALUES[destx]`. -/
structure UndefOracle where
  flags : RFlags := {}
  gpr   : BitVec 64 := 0#64
  deriving DecidableEq, Repr

/-- Byte-addressed 64-bit linear memory (`BitVec 64 → BitVec 8`). -/
abbrev ByteMem := BitVec 64 → BitVec 8

/-- Read-only executable code image (`BitVec 64 → BitVec 8`). -/
abbrev CodeMap := BitVec 64 → BitVec 8

def memUpd8 (m : ByteMem) (a : BitVec 64) (b : BitVec 8) : ByteMem :=
  fun a' => if a' = a then b else m a'

def byteOf64 (v : BitVec 64) (k : Nat) : BitVec 8 :=
  BitVec.extractLsb' (k * 8) 8 v

def sext8To64 (b : BitVec 8) : BitVec 64 :=
  (if b.msb then 0xFFFFFFFFFFFFFF#56 else 0#56) ++ b

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
  let m0 := memUpd8 m  (a + 0#64) (BitVec.extractLsb' 0 8 v)
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

/-! ### Fixed-Lane Vector Combinators (`Fin N`) -/

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

/-! ### Architectural Faults, Addressing Modes, and Instruction AST -/

/-- Normative Ring-3 trap taxonomy distinguishing `#GP(0)` from `#UD`. -/
inductive FaultKind where
  | gp0LengthExceeds15
  | gp0Privilege
  | udExplicit
  | udIllegalLock
  | udVexPrefix
  | udVexField
  | udEvexField
  | udUnmapped
  deriving DecidableEq, Repr

/-- Repaired machine state of `VendorX86RefV2`, carrying explicit `fsBase` and
    `gsBase` 64-bit segment base registers (`IA32_FS_BASE` / `IA32_GS_BASE`). -/
structure MachineState where
  rip    : BitVec 64 := 0#64
  gpr    : Gpr → BitVec 64 := fun _ => 0#64
  ymm    : YmmIdx → BitVec 256 := fun _ => 0#256
  flags  : RFlags := {}
  fsBase : BitVec 64 := 0#64
  gsBase : BitVec 64 := 0#64
  mem    : ByteMem := fun _ => 0#8
  halted : Bool := false
  fault  : Option FaultKind := none

inductive OpSize where
  | s16
  | s32
  | s64
  deriving DecidableEq, Repr

inductive SimdWidth where
  | v128
  | v256
  deriving DecidableEq, Repr

inductive AluOp where
  | add | adc | sub | sbb | and | or | xor | cmp | test
  deriving DecidableEq, Repr

inductive UnaryOp where
  | inc | dec | neg | not
  deriving DecidableEq, Repr

inductive ShiftOp where
  | shl | shr | sar | rol | ror
  deriving DecidableEq, Repr

inductive ShiftCnt where
  | imm (n : BitVec 8)
  | cl
  deriving DecidableEq, Repr

inductive Cond where
  | o | no | b | ae | e | ne | be | a
  | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

/-- ModR/M + SIB + displacement memory operand carrying `seg : Option SegReg`
    (`0x64` `FS` / `0x65` `GS`) and `addr32 : Bool` (`0x67`). -/
structure MemAddr where
  seg    : Option SegReg := none
  addr32 : Bool := false
  base   : Option Gpr := none
  index  : Option (Gpr × Nat) := none
  disp   : BitVec 64 := 0#64
  ripRel : Bool := false
  deriving DecidableEq, Repr

inductive RmOp where
  | reg (r : Gpr)
  | mem (a : MemAddr)
  deriving DecidableEq, Repr

inductive XmmRmOp where
  | reg (r : YmmIdx)
  | mem (a : MemAddr)
  deriving DecidableEq, Repr

inductive VecElemWidth where
  | e8 | e16 | e32 | e64
  deriving DecidableEq, Repr

inductive VecShiftKind where
  | sll | srl | sra
  deriving DecidableEq, Repr

/-- Repaired 77-form Pass-2 instruction AST covering scalar GP (`.s16`/`.s32`/`.s64`),
    `PUSH`/`POP`/`LEAVE` (`d64` `.s16`/`.s64`), `CMPXCHG` (both `LOCK` and non-`LOCK`),
    BMI1/2, ADX, CET `ENDBR64`, and VEX/EVEX 128/256-bit SIMD + AES-NI + PCLMULQDQ. -/
inductive Instr where
  | nop
  | endbr64
  | ud2
  | cli
  | aluRmReg    (sz : OpSize) (op : AluOp) (dst : RmOp) (src : Gpr)
  | aluRegRm    (sz : OpSize) (op : AluOp) (dst : Gpr) (src : RmOp)
  | aluRmImm    (sz : OpSize) (op : AluOp) (dst : RmOp) (imm : BitVec 64)
  | unaryRm     (sz : OpSize) (op : UnaryOp) (dst : RmOp)
  | bswap       (sz : OpSize) (dst : Gpr)
  | shiftRm     (sz : OpSize) (op : ShiftOp) (dst : RmOp) (cnt : ShiftCnt)
  | imul2       (sz : OpSize) (dst : Gpr) (src : RmOp)
  | imul3       (sz : OpSize) (dst : Gpr) (src : RmOp) (imm : BitVec 64)
  | mulUnsigned (sz : OpSize) (src : RmOp)
  | mulx        (sz : OpSize) (dstHi dstLo : Gpr) (src : RmOp)
  | adcx        (sz : OpSize) (dst : Gpr) (src : RmOp)
  | adox        (sz : OpSize) (dst : Gpr) (src : RmOp)
  | bsf         (sz : OpSize) (dst : Gpr) (src : RmOp)
  | bsr         (sz : OpSize) (dst : Gpr) (src : RmOp)
  | tzcnt       (sz : OpSize) (dst : Gpr) (src : RmOp)
  | lzcnt       (sz : OpSize) (dst : Gpr) (src : RmOp)
  | popcnt      (sz : OpSize) (dst : Gpr) (src : RmOp)
  | andn        (sz : OpSize) (dst src1 : Gpr) (src2 : RmOp)
  | shrx        (sz : OpSize) (dst : Gpr) (src : RmOp) (cnt : Gpr)
  | shlx        (sz : OpSize) (dst : Gpr) (src : RmOp) (cnt : Gpr)
  | sarx        (sz : OpSize) (dst : Gpr) (src : RmOp) (cnt : Gpr)
  | bzhi        (sz : OpSize) (dst : Gpr) (src : RmOp) (ctl : Gpr)
  | pdep        (sz : OpSize) (dst src1 : Gpr) (src2 : RmOp)
  | pext        (sz : OpSize) (dst src1 : Gpr) (src2 : RmOp)
  | cmovcc      (sz : OpSize) (cc : Cond) (dst : Gpr) (src : RmOp)
  | setcc       (cc : Cond) (dst : RmOp)
  | movRmReg    (sz : OpSize) (dst : RmOp) (src : Gpr)
  | movRegRm    (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movImm      (sz : OpSize) (dst : Gpr) (imm : BitVec 64)
  | movzxByte   (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movzxWord   (sz : OpSize) (dst : Gpr) (src : RmOp)
  | movsxd      (dst : Gpr) (src : RmOp)
  | lea         (sz : OpSize) (dst : Gpr) (addr : MemAddr)
  | xchgRegReg  (widthBits : Nat) (r1 r2 : Gpr)
  | pushReg     (sz : OpSize) (src : Gpr)
  | popReg      (sz : OpSize) (dst : Gpr)
  | leave       (sz : OpSize)
  | callRel32   (rel : BitVec 64)
  | ret
  | jmpRel      (rel : BitVec 64)
  | jccRel      (cc : Cond) (rel : BitVec 64)
  | cmpxchg     (sz : OpSize) (dst : RmOp) (src : Gpr)
  | lockAluReg  (sz : OpSize) (op : AluOp) (addr : MemAddr) (src : Gpr)
  | lockAluImm  (sz : OpSize) (op : AluOp) (addr : MemAddr) (imm : BitVec 64)
  | lockInc     (sz : OpSize) (addr : MemAddr)
  | lockXadd    (sz : OpSize) (addr : MemAddr) (src : Gpr)
  | lockCmpxchg (sz : OpSize) (addr : MemAddr) (src : Gpr)
  -- VEX 128/256-bit & EVEX SIMD / Crypto
  | vmovdqLoad  (w : SimdWidth) (dst : YmmIdx) (src : XmmRmOp)
  | vmovdqStore (w : SimdWidth) (dst : MemAddr) (src : YmmIdx)
  | vmovGprToXmm (is64 : Bool) (dst : YmmIdx) (src : RmOp)
  | vpadd       (w : SimdWidth) (ew : VecElemWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpsub       (w : SimdWidth) (ew : VecElemWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpaddsw     (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpsubusb    (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpand       (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpor        (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpxor       (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpandn      (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpcmpeq     (w : SimdWidth) (ew : VecElemWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpcmpgt     (w : SimdWidth) (ew : VecElemWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpmovmskb   (w : SimdWidth) (dst : Gpr) (src : YmmIdx)
  | vpextrq     (dst : Gpr) (src : YmmIdx) (imm : BitVec 8)
  | vpshufb     (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpshufd     (w : SimdWidth) (dst : YmmIdx) (src : XmmRmOp) (imm : BitVec 8)
  | vpmaddubsw  (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpmaddwd    (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpsadbw     (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpshiftImmD (w : SimdWidth) (kind : VecShiftKind) (dst src : YmmIdx) (imm : BitVec 8)
  | vpslldXmm   (w : SimdWidth) (dst src1 : YmmIdx) (cnt : XmmRmOp)
  | vpshiftVarD (w : SimdWidth) (kind : VecShiftKind) (dst src1 : YmmIdx) (cnt : XmmRmOp)
  | vpermd      (dst idx : YmmIdx) (tbl : XmmRmOp)
  | vpermq      (dst : YmmIdx) (src : XmmRmOp) (imm : BitVec 8)
  | vperm2x128  (dst src1 : YmmIdx) (src2 : XmmRmOp) (imm : BitVec 8)
  | vextract128 (dst : XmmRmOp) (src : YmmIdx) (imm : BitVec 8)
  | vpclmulqdq  (dst src1 : YmmIdx) (src2 : XmmRmOp) (imm : BitVec 8)
  | vaesenc     (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vptest      (w : SimdWidth) (src1 : YmmIdx) (src2 : XmmRmOp)
  | vprolvd     (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp)
  | vpternlogd  (w : SimdWidth) (dst src1 : YmmIdx) (src2 : XmmRmOp) (imm : BitVec 8)
  | vzeroupper
  deriving DecidableEq, Repr

inductive DecodeResult where
  | ok    (ins : Instr) (len : Nat)
  | fault (kind : FaultKind)
  deriving DecidableEq, Repr

end VendorX86RefV2
