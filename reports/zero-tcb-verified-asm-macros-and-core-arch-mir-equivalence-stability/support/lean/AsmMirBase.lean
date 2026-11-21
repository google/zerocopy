-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.UInt.Basic

/-!
Tactic-free trusted foundation (`AsmMirBase`) modeling:
1. Real byte-level x86-64 instruction decoding (`decodeX86At`) over the exact ELF64 `.text`
   machine bytes emitted by `rustc 1.99.1 -O --emit=obj` across all three assembly archetypes:
   - `mulxObjBytes` (100 B): 256-bit BMI2 `mulx` + ADX dual carry-chain (`adcx` / `adox`)
   - `dotObjBytes`  (125 B): 2x-unrolled AVX2 `vpmaddubsw` + `vpmaddwd` + `vzeroupper` loop
   - `ctObjBytes`   ( 98 B): 8-entry branchless `cmove` constant-time lookup
2. Operational x86-64 semantics (`X86State`, `step`, `run`) tracking independent `CF`/`OF`/`ZF`
   flags, AVX upper-lane dirtiness (`ymmDirty`, faulting on `ret` without `vzeroupper`),
   aligned 64-bit word memory (`mem64`), byte memory (`mem8`), and 2-safety leakage traces (`leak`).
3. `Runtime(PostCleanup)` MIR + `StdarchSemantics` twin evaluators and pure reference specs.
Zero tactics (`by`) and zero external dependencies beyond `Init.*`.
-/

namespace AsmMirBase

def W64 : Nat := 18446744073709551616
def M32 : Nat := 4294967296
def M16 : Nat := 65536

inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq

inductive Ymm where
  | ymm0 | ymm1 | ymm2 | ymm3 | ymm4 | ymm5 | ymm6 | ymm7
  deriving DecidableEq

structure Ymm256 where
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  d4 : Nat
  d5 : Nat
  d6 : Nat
  d7 : Nat
  deriving DecidableEq

def ymmZero : Ymm256 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
def ymmAllOnes : Ymm256 :=
  ⟨4294967295, 4294967295, 4294967295, 4294967295,
   4294967295, 4294967295, 4294967295, 4294967295⟩
def ymmOnes16 : Ymm256 := ⟨65537, 65537, 65537, 65537, 65537, 65537, 65537, 65537⟩

inductive LeakEvent where
  | load64  (addr : Nat)
  | store64 (addr : Nat)
  | load256 (addr : Nat)
  | branch  (taken : Bool) (target : Nat)
  deriving DecidableEq

structure X86State where
  rip      : Nat
  halted   : Bool
  fault    : Bool
  cf       : Bool
  of_      : Bool
  zf       : Bool
  ymmDirty : Bool
  gpr      : Gpr → Nat
  ymm      : Ymm → Ymm256
  mem64    : Nat → Nat
  mem8     : Nat → UInt8
  leak     : List LeakEvent

def gprUpd (f : Gpr → Nat) (r : Gpr) (v : Nat) : Gpr → Nat :=
  fun x => if x = r then v else f x

def ymmUpd (f : Ymm → Ymm256) (r : Ymm) (v : Ymm256) : Ymm → Ymm256 :=
  fun x => if x = r then v else f x

def mem64Upd (m : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  fun x => if x = addr then val % W64 else m x

def readMem64 (s : X86State) (addr : Nat) : Nat :=
  s.mem64 addr % W64

def b2n (b : Bool) : Nat :=
  match b with
  | true  => 1
  | false => 0

-- Exact signed byte & saturation arithmetic for `vpmaddubsw` + `vpmaddwd`
def u8ToInt (b : UInt8) : Int :=
  let n := b.toNat
  if n < 128 then Int.ofNat n else Int.ofNat n - 256

def clampI16 (x : Int) : Int :=
  if x < -32768 then -32768 else if 32767 < x then 32767 else x

def intToMod16 (x : Int) : Nat :=
  Int.toNat ((x % 65536 + 65536) % 65536)

def mod16ToInt (w : Nat) : Int :=
  let m := w % 65536
  if m < 32768 then Int.ofNat m else Int.ofNat m - 65536

def intToMod32 (x : Int) : Nat :=
  Int.toNat ((x % 4294967296 + 4294967296) % 4294967296)

def packDwordBytes (m : Nat → UInt8) (addr : Nat) : Nat :=
  (m addr).toNat +
  256 * ((m (addr + 1)).toNat +
  256 * ((m (addr + 2)).toNat +
  256 * (m (addr + 3)).toNat))

def loadYmm256 (m : Nat → UInt8) (addr : Nat) : Ymm256 :=
  { d0 := packDwordBytes m addr,
    d1 := packDwordBytes m (addr + 4),
    d2 := packDwordBytes m (addr + 8),
    d3 := packDwordBytes m (addr + 12),
    d4 := packDwordBytes m (addr + 16),
    d5 := packDwordBytes m (addr + 20),
    d6 := packDwordBytes m (addr + 24),
    d7 := packDwordBytes m (addr + 28) }

def srlwDword15 (dw : Nat) : Nat :=
  let w0 := (dw % 65536) / 32768
  let w1 := ((dw / 65536) % 65536) / 32768
  w0 + 65536 * w1

def vpsrlw15 (v : Ymm256) : Ymm256 :=
  ⟨srlwDword15 v.d0, srlwDword15 v.d1, srlwDword15 v.d2, srlwDword15 v.d3,
   srlwDword15 v.d4, srlwDword15 v.d5, srlwDword15 v.d6, srlwDword15 v.d7⟩

def maddubsDword (du ds : Nat) : Nat :=
  let u0 := du % 256
  let u1 := (du / 256) % 256
  let u2 := (du / 65536) % 256
  let u3 := (du / 16777216) % 256
  let s0 := u8ToInt (UInt8.ofNat (ds % 256))
  let s1 := u8ToInt (UInt8.ofNat ((ds / 256) % 256))
  let s2 := u8ToInt (UInt8.ofNat ((ds / 65536) % 256))
  let s3 := u8ToInt (UInt8.ofNat ((ds / 16777216) % 256))
  let p0 := clampI16 (Int.ofNat u0 * s0 + Int.ofNat u1 * s1)
  let p1 := clampI16 (Int.ofNat u2 * s2 + Int.ofNat u3 * s3)
  intToMod16 p0 + 65536 * intToMod16 p1

def evalVpmaddubsw (u s : Ymm256) : Ymm256 :=
  ⟨maddubsDword u.d0 s.d0, maddubsDword u.d1 s.d1,
   maddubsDword u.d2 s.d2, maddubsDword u.d3 s.d3,
   maddubsDword u.d4 s.d4, maddubsDword u.d5 s.d5,
   maddubsDword u.d6 s.d6, maddubsDword u.d7 s.d7⟩

def maddwdDword (da db : Nat) : Nat :=
  let a0 := mod16ToInt (da % 65536)
  let a1 := mod16ToInt ((da / 65536) % 65536)
  let b0 := mod16ToInt (db % 65536)
  let b1 := mod16ToInt ((db / 65536) % 65536)
  intToMod32 (a0 * b0 + a1 * b1)

def evalVpmaddwd (a b : Ymm256) : Ymm256 :=
  ⟨maddwdDword a.d0 b.d0, maddwdDword a.d1 b.d1,
   maddwdDword a.d2 b.d2, maddwdDword a.d3 b.d3,
   maddwdDword a.d4 b.d4, maddwdDword a.d5 b.d5,
   maddwdDword a.d6 b.d6, maddwdDword a.d7 b.d7⟩

def evalVpaddd256 (a b : Ymm256) : Ymm256 :=
  ⟨(a.d0 + b.d0) % M32, (a.d1 + b.d1) % M32,
   (a.d2 + b.d2) % M32, (a.d3 + b.d3) % M32,
   (a.d4 + b.d4) % M32, (a.d5 + b.d5) % M32,
   (a.d6 + b.d6) % M32, (a.d7 + b.d7) % M32⟩

def evalVpaddd128 (a b : Ymm256) : Ymm256 :=
  ⟨(a.d0 + b.d0) % M32, (a.d1 + b.d1) % M32,
   (a.d2 + b.d2) % M32, (a.d3 + b.d3) % M32,
   0, 0, 0, 0⟩

def evalVextracti128Hi (a : Ymm256) : Ymm256 :=
  ⟨a.d4, a.d5, a.d6, a.d7, 0, 0, 0, 0⟩

def selDword4 (v : Ymm256) (idx : Nat) : Nat :=
  match idx % 4 with
  | 0 => v.d0
  | 1 => v.d1
  | 2 => v.d2
  | _ => v.d3

def evalVpshufd128 (a : Ymm256) (imm : Nat) : Ymm256 :=
  ⟨selDword4 a (imm % 4),
   selDword4 a ((imm / 4) % 4),
   selDword4 a ((imm / 16) % 4),
   selDword4 a ((imm / 64) % 4),
   0, 0, 0, 0⟩

def zeroUpperAll (f : Ymm → Ymm256) : Ymm → Ymm256 :=
  fun r =>
    let v := f r
    ⟨v.d0, v.d1, v.d2, v.d3, 0, 0, 0, 0⟩

inductive X86Insn where
  | xorZero32    (dst : Gpr)
  | mulxMem      (hi lo base : Gpr) (disp : Nat)
  | adcxMem      (dst base : Gpr) (disp : Nat)
  | adcxReg      (dst src : Gpr)
  | adoxMem      (dst base : Gpr) (disp : Nat)
  | adoxReg      (dst src : Gpr)
  | movStore64   (base : Gpr) (disp : Nat) (src : Gpr)
  | movLoad64    (dst base : Gpr) (disp : Nat)
  | cmpImm64     (reg : Gpr) (imm : Nat)
  | cmove64      (dst src : Gpr)
  | testSelf64   (reg : Gpr)
  | jeTarget     (target : Nat)
  | jbTarget     (target : Nat)
  | shlImm64     (dst : Gpr) (sh : Nat)
  | addImm64     (dst : Gpr) (imm : Nat)
  | cmpReg64     (lhs rhs : Gpr)
  | vpxorZero256 (dst : Ymm)
  | vpcmpeqdAll1 (dst : Ymm)
  | vpsrlwImm256 (dst src : Ymm) (imm : Nat)
  | vmovdquLd256 (dst : Ymm) (base idx : Gpr) (disp : Nat)
  | vpmaddubsw   (dst u s : Ymm)
  | vpmaddwd     (dst a b : Ymm)
  | vpaddd256    (dst a b : Ymm)
  | vextracti128 (dst src : Ymm) (imm : Nat)
  | vpaddd128    (dst a b : Ymm)
  | vpshufd128   (dst src : Ymm) (imm : Nat)
  | vmovdToGpr32 (dst : Gpr) (src : Ymm)
  | vzeroupper
  | ret
  deriving DecidableEq

-- Byte-level x86-64 REX / VEX2 / VEX3 / ModRM / SIB decoder
def byteAt : List UInt8 → Nat → Option Nat
  | [], _ => none
  | b :: _, 0 => some b.toNat
  | _ :: bs, n + 1 => byteAt bs n

def decodeGpr4 : Nat → Gpr
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

def decodeYmm3 : Nat → Ymm
  | 0 => .ymm0 | 1 => .ymm1 | 2 => .ymm2 | 3 => .ymm3
  | 4 => .ymm4 | 5 => .ymm5 | 6 => .ymm6 | _ => .ymm7

def rel8Target (nextPc b : Nat) : Nat :=
  if b < 128 then nextPc + b else nextPc - (256 - b)

def decodeX86At (code : List UInt8) (pc : Nat) : Option (X86Insn × Nat) :=
  match byteAt code pc with
  | none => none
  | some b0 =>
    if b0 = 0xc3 then
      some (.ret, 1)
    else if b0 = 0x31 then
      match byteAt code (pc + 1) with
      | some modrm =>
        let md := modrm / 64
        let reg := (modrm / 8) % 8
        let rm := modrm % 8
        if md = 3 && reg = rm then some (.xorZero32 (decodeGpr4 rm), 2) else none
      | none => none
    else if b0 = 0x74 then
      match byteAt code (pc + 1) with
      | some rel => some (.jeTarget (rel8Target (pc + 2) rel), 2)
      | none => none
    else if b0 = 0x72 then
      match byteAt code (pc + 1) with
      | some rel => some (.jbTarget (rel8Target (pc + 2) rel), 2)
      | none => none
    else if b0 = 0x48 || b0 = 0x49 || b0 = 0x4c || b0 = 0x4d then
      let rexR := (b0 / 4) % 2
      let rexB := b0 % 2
      match byteAt code (pc + 1), byteAt code (pc + 2) with
      | some 0x89, some modrm =>
        let md := modrm / 64
        let reg := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let base := decodeGpr4 (rexB * 8 + modrm % 8)
        if md = 0 then some (.movStore64 base 0 reg, 3)
        else if md = 1 then
          match byteAt code (pc + 3) with
          | some disp => some (.movStore64 base disp reg, 4)
          | none => none
        else none
      | some 0x8b, some modrm =>
        let md := modrm / 64
        let dst := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let base := decodeGpr4 (rexB * 8 + modrm % 8)
        if md = 0 then some (.movLoad64 dst base 0, 3)
        else if md = 1 then
          match byteAt code (pc + 3) with
          | some disp => some (.movLoad64 dst base disp, 4)
          | none => none
        else none
      | some 0x83, some modrm =>
        let subop := (modrm / 8) % 8
        let reg := decodeGpr4 (rexB * 8 + modrm % 8)
        match byteAt code (pc + 3) with
        | some imm =>
          if subop = 7 then some (.cmpImm64 reg imm, 4)
          else if subop = 0 then some (.addImm64 reg imm, 4)
          else none
        | none => none
      | some 0x0f, some 0x44 =>
        match byteAt code (pc + 3) with
        | some modrm =>
          let dst := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
          let src := decodeGpr4 (rexB * 8 + modrm % 8)
          some (.cmove64 dst src, 4)
        | none => none
      | some 0x85, some modrm =>
        let r1 := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let r2 := decodeGpr4 (rexB * 8 + modrm % 8)
        if r1 = r2 then some (.testSelf64 r2, 3) else none
      | some 0xc1, some modrm =>
        let subop := (modrm / 8) % 8
        let dst := decodeGpr4 (rexB * 8 + modrm % 8)
        match byteAt code (pc + 3) with
        | some imm => if subop = 4 then some (.shlImm64 dst imm, 4) else none
        | none => none
      | some 0x39, some modrm =>
        let rhs := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let lhs := decodeGpr4 (rexB * 8 + modrm % 8)
        some (.cmpReg64 lhs rhs, 3)
      | _, _ => none
    else if b0 = 0x66 then
      match byteAt code (pc + 1), byteAt code (pc + 2), byteAt code (pc + 3), byteAt code (pc + 4), byteAt code (pc + 5) with
      | some rex, some 0x0f, some 0x38, some 0xf6, some modrm =>
        let rexR := (rex / 4) % 2
        let rexB := rex % 2
        let md := modrm / 64
        let dst := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let rm := decodeGpr4 (rexB * 8 + modrm % 8)
        if md = 3 then some (.adcxReg dst rm, 6)
        else if md = 0 then some (.adcxMem dst rm 0, 6)
        else if md = 1 then
          match byteAt code (pc + 6) with
          | some disp => some (.adcxMem dst rm disp, 7)
          | none => none
        else none
      | _, _, _, _, _ => none
    else if b0 = 0xf3 then
      match byteAt code (pc + 1), byteAt code (pc + 2), byteAt code (pc + 3), byteAt code (pc + 4), byteAt code (pc + 5) with
      | some rex, some 0x0f, some 0x38, some 0xf6, some modrm =>
        let rexR := (rex / 4) % 2
        let rexB := rex % 2
        let md := modrm / 64
        let dst := decodeGpr4 (rexR * 8 + (modrm / 8) % 8)
        let rm := decodeGpr4 (rexB * 8 + modrm % 8)
        if md = 3 then some (.adoxReg dst rm, 6)
        else if md = 0 then some (.adoxMem dst rm 0, 6)
        else if md = 1 then
          match byteAt code (pc + 6) with
          | some disp => some (.adoxMem dst rm disp, 7)
          | none => none
        else none
      | _, _, _, _, _ => none
    else if b0 = 0xc5 then
      -- 2-byte VEX: C5 [~R | ~vvvv(4) | L | pp(2)] opcode ...
      match byteAt code (pc + 1), byteAt code (pc + 2) with
      | some v1, some op =>
        let vvvv := 15 - ((v1 / 8) % 16)
        let vexL := (v1 / 4) % 2
        if op = 0x77 && vexL = 0 then
          some (.vzeroupper, 3)
        else
          match byteAt code (pc + 3) with
          | none => none
          | some modrm =>
            let md := modrm / 64
            let reg3 := (modrm / 8) % 8
            let rm3 := modrm % 8
            if op = 0xef && vexL = 1 && md = 3 && reg3 = rm3 && vvvv = reg3 then
              some (.vpxorZero256 (decodeYmm3 reg3), 4)
            else if op = 0x76 && vexL = 1 && md = 3 && reg3 = rm3 && vvvv = reg3 then
              some (.vpcmpeqdAll1 (decodeYmm3 reg3), 4)
            else if op = 0x71 && vexL = 1 && md = 3 && reg3 = 2 then
              match byteAt code (pc + 4) with
              | some imm => some (.vpsrlwImm256 (decodeYmm3 vvvv) (decodeYmm3 rm3) imm, 5)
              | none => none
            else if op = 0x6f && vexL = 1 && rm3 = 4 then
              match byteAt code (pc + 4) with
              | none => none
              | some sib =>
                let idxG := decodeGpr4 ((sib / 8) % 8)
                let baseG := decodeGpr4 (sib % 8)
                if md = 0 then
                  some (.vmovdquLd256 (decodeYmm3 reg3) baseG idxG 0, 5)
                else if md = 1 then
                  match byteAt code (pc + 5) with
                  | some disp => some (.vmovdquLd256 (decodeYmm3 reg3) baseG idxG disp, 6)
                  | none => none
                else none
            else if op = 0xf5 && vexL = 1 && md = 3 then
              some (.vpmaddwd (decodeYmm3 reg3) (decodeYmm3 vvvv) (decodeYmm3 rm3), 4)
            else if op = 0xfe && vexL = 1 && md = 3 then
              some (.vpaddd256 (decodeYmm3 reg3) (decodeYmm3 vvvv) (decodeYmm3 rm3), 4)
            else if op = 0xfe && vexL = 0 && md = 3 then
              some (.vpaddd128 (decodeYmm3 reg3) (decodeYmm3 vvvv) (decodeYmm3 rm3), 4)
            else if op = 0x70 && vexL = 0 && md = 3 then
              match byteAt code (pc + 4) with
              | some imm => some (.vpshufd128 (decodeYmm3 reg3) (decodeYmm3 rm3) imm, 5)
              | none => none
            else if op = 0x7e && vexL = 0 && md = 3 then
              some (.vmovdToGpr32 (decodeGpr4 rm3) (decodeYmm3 reg3), 4)
            else none
      | _, _ => none
    else if b0 = 0xc4 then
      -- 3-byte VEX: C4 [~R|~X|~B|mmmmm] [W|~vvvv|L|pp] opcode modrm ...
      match byteAt code (pc + 1), byteAt code (pc + 2), byteAt code (pc + 3), byteAt code (pc + 4) with
      | some v1, some v2, some op, some modrm =>
        let rBit := 1 - (v1 / 128)
        let bBit := 1 - ((v1 / 32) % 2)
        let mmmmm := v1 % 32
        let vvvv := 15 - ((v2 / 8) % 16)
        let vexL := (v2 / 4) % 2
        let md := modrm / 64
        let reg3 := (modrm / 8) % 8
        let rm3 := modrm % 8
        if mmmmm = 2 && op = 0xf6 && vexL = 0 then
          let hiG := decodeGpr4 (rBit * 8 + reg3)
          let loG := decodeGpr4 vvvv
          let baseG := decodeGpr4 (bBit * 8 + rm3)
          if md = 0 then some (.mulxMem hiG loG baseG 0, 5)
          else if md = 1 then
            match byteAt code (pc + 5) with
            | some disp => some (.mulxMem hiG loG baseG disp, 6)
            | none => none
          else none
        else if mmmmm = 2 && op = 0x04 && vexL = 1 && md = 3 then
          some (.vpmaddubsw (decodeYmm3 reg3) (decodeYmm3 vvvv) (decodeYmm3 rm3), 5)
        else if mmmmm = 3 && op = 0x39 && vexL = 1 && md = 3 then
          match byteAt code (pc + 5) with
          | some imm => some (.vextracti128 (decodeYmm3 rm3) (decodeYmm3 reg3) imm, 6)
          | none => none
        else none
      | _, _, _, _ => none
    else none

def execInsn (ins : X86Insn) (len : Nat) (s : X86State) : X86State :=
  let nextRip := s.rip + len
  match ins with
  | .xorZero32 dst =>
    { s with rip := nextRip, cf := false, of_ := false, zf := true, gpr := gprUpd s.gpr dst 0 }
  | .mulxMem hi lo base disp =>
    if hi = lo then { s with fault := true }
    else
      let addr := (s.gpr base + disp) % W64
      let src := readMem64 s addr
      let prod := (s.gpr .rdx % W64) * src
      let g1 := gprUpd s.gpr lo (prod % W64)
      let g2 := gprUpd g1 hi ((prod / W64) % W64)
      { s with rip := nextRip, gpr := g2, leak := s.leak ++ [.load64 addr] }
  | .adcxMem dst base disp =>
    let addr := (s.gpr base + disp) % W64
    let sum := (s.gpr dst % W64) + readMem64 s addr + b2n s.cf
    { s with rip := nextRip, cf := decide (sum ≥ W64),
             gpr := gprUpd s.gpr dst (sum % W64),
             leak := s.leak ++ [.load64 addr] }
  | .adcxReg dst src =>
    let sum := (s.gpr dst % W64) + (s.gpr src % W64) + b2n s.cf
    { s with rip := nextRip, cf := decide (sum ≥ W64),
             gpr := gprUpd s.gpr dst (sum % W64) }
  | .adoxMem dst base disp =>
    let addr := (s.gpr base + disp) % W64
    let sum := (s.gpr dst % W64) + readMem64 s addr + b2n s.of_
    { s with rip := nextRip, of_ := decide (sum ≥ W64),
             gpr := gprUpd s.gpr dst (sum % W64),
             leak := s.leak ++ [.load64 addr] }
  | .adoxReg dst src =>
    let sum := (s.gpr dst % W64) + (s.gpr src % W64) + b2n s.of_
    { s with rip := nextRip, of_ := decide (sum ≥ W64),
             gpr := gprUpd s.gpr dst (sum % W64) }
  | .movStore64 base disp src =>
    let addr := (s.gpr base + disp) % W64
    { s with rip := nextRip,
             mem64 := mem64Upd s.mem64 addr (s.gpr src % W64),
             leak := s.leak ++ [.store64 addr] }
  | .movLoad64 dst base disp =>
    let addr := (s.gpr base + disp) % W64
    { s with rip := nextRip,
             gpr := gprUpd s.gpr dst (readMem64 s addr),
             leak := s.leak ++ [.load64 addr] }
  | .cmpImm64 reg imm =>
    let lhs := s.gpr reg % W64
    { s with rip := nextRip, cf := decide (lhs < imm), zf := decide (lhs = imm), of_ := false }
  | .cmove64 dst src =>
    let v := if s.zf then s.gpr src % W64 else s.gpr dst % W64
    { s with rip := nextRip, gpr := gprUpd s.gpr dst v }
  | .testSelf64 reg =>
    let v := s.gpr reg % W64
    { s with rip := nextRip, cf := false, of_ := false, zf := decide (v = 0) }
  | .jeTarget target =>
    let taken := s.zf
    { s with rip := if taken then target else nextRip,
             leak := s.leak ++ [.branch taken target] }
  | .jbTarget target =>
    let taken := s.cf
    { s with rip := if taken then target else nextRip,
             leak := s.leak ++ [.branch taken target] }
  | .shlImm64 dst sh =>
    let v := ((s.gpr dst % W64) * (2 ^ sh)) % W64
    { s with rip := nextRip, gpr := gprUpd s.gpr dst v }
  | .addImm64 dst imm =>
    let sum := (s.gpr dst % W64) + imm
    { s with rip := nextRip, cf := decide (sum ≥ W64), zf := decide (sum % W64 = 0),
             gpr := gprUpd s.gpr dst (sum % W64) }
  | .cmpReg64 lhs rhs =>
    let l := s.gpr lhs % W64
    let r := s.gpr rhs % W64
    { s with rip := nextRip, cf := decide (l < r), zf := decide (l = r), of_ := false }
  | .vpxorZero256 dst =>
    { s with rip := nextRip, ymmDirty := true, ymm := ymmUpd s.ymm dst ymmZero }
  | .vpcmpeqdAll1 dst =>
    { s with rip := nextRip, ymmDirty := true, ymm := ymmUpd s.ymm dst ymmAllOnes }
  | .vpsrlwImm256 dst src imm =>
    let out := if imm = 15 then vpsrlw15 (s.ymm src) else ymmZero
    { s with rip := nextRip, ymmDirty := true, ymm := ymmUpd s.ymm dst out }
  | .vmovdquLd256 dst base idx disp =>
    let addr := (s.gpr base + s.gpr idx + disp) % W64
    { s with rip := nextRip, ymmDirty := true,
             ymm := ymmUpd s.ymm dst (loadYmm256 s.mem8 addr),
             leak := s.leak ++ [.load256 addr] }
  | .vpmaddubsw dst u sv =>
    { s with rip := nextRip, ymmDirty := true,
             ymm := ymmUpd s.ymm dst (evalVpmaddubsw (s.ymm u) (s.ymm sv)) }
  | .vpmaddwd dst a b =>
    { s with rip := nextRip, ymmDirty := true,
             ymm := ymmUpd s.ymm dst (evalVpmaddwd (s.ymm a) (s.ymm b)) }
  | .vpaddd256 dst a b =>
    { s with rip := nextRip, ymmDirty := true,
             ymm := ymmUpd s.ymm dst (evalVpaddd256 (s.ymm a) (s.ymm b)) }
  | .vextracti128 dst src imm =>
    let out := if imm = 1 then evalVextracti128Hi (s.ymm src) else ymmZero
    { s with rip := nextRip, ymmDirty := true, ymm := ymmUpd s.ymm dst out }
  | .vpaddd128 dst a b =>
    { s with rip := nextRip, ymm := ymmUpd s.ymm dst (evalVpaddd128 (s.ymm a) (s.ymm b)) }
  | .vpshufd128 dst src imm =>
    { s with rip := nextRip, ymm := ymmUpd s.ymm dst (evalVpshufd128 (s.ymm src) imm) }
  | .vmovdToGpr32 dst src =>
    { s with rip := nextRip, gpr := gprUpd s.gpr dst ((s.ymm src).d0 % M32) }
  | .vzeroupper =>
    { s with rip := nextRip, ymmDirty := false, ymm := zeroUpperAll s.ymm }
  | .ret =>
    -- Enforce AVX->SSE transition hygiene: returning with dirty upper YMM lanes faults!
    if s.ymmDirty then { s with fault := true } else { s with halted := true }

def step (code : List UInt8) (s : X86State) : X86State :=
  if s.halted || s.fault then s
  else
    match decodeX86At code s.rip with
    | none => { s with fault := true }
    | some (ins, len) => execInsn ins len s

def run (code : List UInt8) : Nat → X86State → X86State
  | 0, s => s
  | n + 1, s => run code n (step code s)

-- ============================================================================
-- Exact ELF64 `.text` machine bytes emitted by `rustc 1.99.1 -O --emit=obj`
-- ============================================================================

-- SHA-256: 69eb8ffe8219a54e880efe7b75befce2a63e525d66d00068f40c1e3da61668e3 (100 B, 20 insns)
def mulxObjBytes : List UInt8 :=
  [ 0x31, 0xc9, 0x31, 0xc0, 0xc4, 0x62, 0xbb, 0xf6, 0x0e, 0x66,
    0x4c, 0x0f, 0x38, 0xf6, 0x07, 0x4c, 0x89, 0x07, 0xc4, 0x62,
    0xbb, 0xf6, 0x56, 0x08, 0x66, 0x4d, 0x0f, 0x38, 0xf6, 0xc8,
    0xf3, 0x4c, 0x0f, 0x38, 0xf6, 0x4f, 0x08, 0x4c, 0x89, 0x4f,
    0x08, 0xc4, 0x62, 0xbb, 0xf6, 0x5e, 0x10, 0x66, 0x4d, 0x0f,
    0x38, 0xf6, 0xd0, 0xf3, 0x4c, 0x0f, 0x38, 0xf6, 0x57, 0x10,
    0x4c, 0x89, 0x57, 0x10, 0xc4, 0x62, 0xbb, 0xf6, 0x4e, 0x18,
    0x66, 0x4d, 0x0f, 0x38, 0xf6, 0xd8, 0xf3, 0x4c, 0x0f, 0x38,
    0xf6, 0x5f, 0x18, 0x4c, 0x89, 0x5f, 0x18, 0x66, 0x49, 0x0f,
    0x38, 0xf6, 0xc1, 0xf3, 0x48, 0x0f, 0x38, 0xf6, 0xc1, 0xc3 ]

-- SHA-256: 687c2b8c82cf7753114db508518dfd3be2cc599d3e593050155a5ce10b0742e6 (125 B, 31 insns)
def dotObjBytes : List UInt8 :=
  [ 0xc5, 0xfd, 0xef, 0xc0, 0xc5, 0xf5, 0xef, 0xc9, 0x48, 0x85,
    0xd2, 0x74, 0x48, 0xc5, 0xed, 0x76, 0xd2, 0xc5, 0xed, 0x71,
    0xd2, 0x0f, 0x48, 0xc1, 0xe2, 0x06, 0x31, 0xc9, 0xc5, 0xfe,
    0x6f, 0x1c, 0x0f, 0xc5, 0xfe, 0x6f, 0x24, 0x0e, 0xc4, 0xe2,
    0x65, 0x04, 0xdc, 0xc5, 0xe5, 0xf5, 0xda, 0xc5, 0xfd, 0xfe,
    0xc3, 0xc5, 0xfe, 0x6f, 0x6c, 0x0f, 0x20, 0xc5, 0xfe, 0x6f,
    0x74, 0x0e, 0x20, 0xc4, 0xe2, 0x55, 0x04, 0xee, 0xc5, 0xd5,
    0xf5, 0xea, 0xc5, 0xf5, 0xfe, 0xcd, 0x48, 0x83, 0xc1, 0x40,
    0x48, 0x39, 0xd1, 0x72, 0xc7, 0xc5, 0xfd, 0xfe, 0xc1, 0xc4,
    0xe3, 0x7d, 0x39, 0xc1, 0x01, 0xc5, 0xf9, 0xfe, 0xc1, 0xc5,
    0xf9, 0x70, 0xc8, 0x4e, 0xc5, 0xf9, 0xfe, 0xc1, 0xc5, 0xf9,
    0x70, 0xc8, 0xb1, 0xc5, 0xf9, 0xfe, 0xc1, 0xc5, 0xf9, 0x7e,
    0xc0, 0xc5, 0xf8, 0x77, 0xc3 ]

-- SHA-256: 878fff952e7a1f34d3d46f4fd60c750112f3fbb18f5ea9977b43469645a36dcf (98 B, 26 insns)
def ctObjBytes : List UInt8 :=
  [ 0x31, 0xc0, 0x4c, 0x8b, 0x07, 0x48, 0x83, 0xfe, 0x00, 0x49,
    0x0f, 0x44, 0xc0, 0x4c, 0x8b, 0x47, 0x08, 0x48, 0x83, 0xfe,
    0x01, 0x49, 0x0f, 0x44, 0xc0, 0x4c, 0x8b, 0x47, 0x10, 0x48,
    0x83, 0xfe, 0x02, 0x49, 0x0f, 0x44, 0xc0, 0x4c, 0x8b, 0x47,
    0x18, 0x48, 0x83, 0xfe, 0x03, 0x49, 0x0f, 0x44, 0xc0, 0x4c,
    0x8b, 0x47, 0x20, 0x48, 0x83, 0xfe, 0x04, 0x49, 0x0f, 0x44,
    0xc0, 0x4c, 0x8b, 0x47, 0x28, 0x48, 0x83, 0xfe, 0x05, 0x49,
    0x0f, 0x44, 0xc0, 0x4c, 0x8b, 0x47, 0x30, 0x48, 0x83, 0xfe,
    0x06, 0x49, 0x0f, 0x44, 0xc0, 0x4c, 0x8b, 0x47, 0x38, 0x48,
    0x83, 0xfe, 0x07, 0x49, 0x0f, 0x44, 0xc0, 0xc3 ]

-- ============================================================================
-- Pure Reference Specifications & `Runtime(PostCleanup)` MIR SafeTwin Models
-- ============================================================================

def val4Limbs (l0 l1 l2 l3 : Nat) : Nat :=
  l0 + W64 * (l1 + W64 * (l2 + W64 * l3))

def val5Limbs (l0 l1 l2 l3 l4 : Nat) : Nat :=
  l0 + W64 * (l1 + W64 * (l2 + W64 * (l3 + W64 * l4)))

def mac4RefVal (t0 t1 t2 t3 a0 a1 a2 a3 b : Nat) : Nat :=
  val4Limbs t0 t1 t2 t3 + b * val4Limbs a0 a1 a2 a3

-- `core::arch` MIR twin (`_mulx_u64` + `_addcarryx_u64`)
def mulxU64Prim (a b : Nat) : Nat × Nat :=
  let p := (a % W64) * (b % W64)
  (p % W64, (p / W64) % W64)

def addcarryxU64Prim (c : Nat) (x y : Nat) : Nat × Nat :=
  let s := (x % W64) + (y % W64) + (c % 2)
  (s % W64, s / W64)

def mulxMac4MirTwin (t0 t1 t2 t3 a0 a1 a2 a3 b : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let (lo0, hi0) := mulxU64Prim a0 b
  let (lo1, hi1) := mulxU64Prim a1 b
  let (lo2, hi2) := mulxU64Prim a2 b
  let (lo3, hi3) := mulxU64Prim a3 b
  let (out0, cf1) := addcarryxU64Prim 0 lo0 t0
  let (m1, cf2)   := addcarryxU64Prim cf1 hi0 lo1
  let (out1, of2) := addcarryxU64Prim 0 m1 t1
  let (m2, cf3)   := addcarryxU64Prim cf2 hi1 lo2
  let (out2, of3) := addcarryxU64Prim of2 m2 t2
  let (m3, cf4)   := addcarryxU64Prim cf3 hi2 lo3
  let (out3, of4) := addcarryxU64Prim of3 m3 t3
  let (top1, _)   := addcarryxU64Prim cf4 hi3 0
  let (out4, _)   := addcarryxU64Prim of4 top1 0
  (out0, out1, out2, out3, out4)

-- Reference & MIR twin for 64-byte block `vpmaddubsw` + `vpmaddwd` dot product
def ymmSum8Mod32 (v : Ymm256) : Nat :=
  (v.d0 + v.d1 + v.d2 + v.d3 + v.d4 + v.d5 + v.d6 + v.d7) % M32

def block32TermVec (mem8 : Nat → UInt8) (uBase sBase off : Nat) : Ymm256 :=
  evalVpmaddwd (evalVpmaddubsw (loadYmm256 mem8 ((uBase + off) % W64))
                               (loadYmm256 mem8 ((sBase + off) % W64)))
               ymmOnes16

def dotBlocks64Spec (mem8 : Nat → UInt8) (uBase sBase : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let prev := dotBlocks64Spec mem8 uBase sBase k
    let v0 := block32TermVec mem8 uBase sBase (64 * k)
    let v1 := block32TermVec mem8 uBase sBase (64 * k + 32)
    (prev + ymmSum8Mod32 v0 + ymmSum8Mod32 v1) % M32

def dotMirLoopAcc (mem8 : Nat → UInt8) (uBase sBase : Nat) : Nat → Ymm256
  | 0 => ymmZero
  | n + 1 => evalVpaddd256 (dotMirLoopAcc mem8 uBase sBase n) (block32TermVec mem8 uBase sBase (32 * n))

def dotAvx2MirTwin (mem8 : Nat → UInt8) (uBase sBase blocks64 : Nat) : Nat :=
  let vacc := dotMirLoopAcc mem8 uBase sBase (2 * blocks64)
  let sum128 := evalVpaddd128 vacc (evalVextracti128Hi vacc)
  let sum64  := evalVpaddd128 sum128 (evalVpshufd128 sum128 0x4e)
  let sum32  := evalVpaddd128 sum64  (evalVpshufd128 sum64  0xb1)
  sum32.d0 % M32

-- Reference & MIR twin for 8-entry constant-time lookup
def lookup8Spec (s : X86State) (base idx : Nat) : Nat :=
  if idx < 8 then readMem64 s ((base + 8 * idx) % W64) else 0

def ctSelectStep (s : X86State) (base idx acc k : Nat) : Nat :=
  let v := readMem64 s ((base + 8 * k) % W64)
  if idx = k then v else acc

def ctSelectMirTwin (s : X86State) (base idx : Nat) : Nat :=
  let a0 := ctSelectStep s base idx 0 0
  let a1 := ctSelectStep s base idx a0 1
  let a2 := ctSelectStep s base idx a1 2
  let a3 := ctSelectStep s base idx a2 3
  let a4 := ctSelectStep s base idx a3 4
  let a5 := ctSelectStep s base idx a4 5
  let a6 := ctSelectStep s base idx a5 6
  ctSelectStep s base idx a6 7

end AsmMirBase
