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
import Init.Data.Nat.Basic
import VendorX86RefV2.Types
import VendorX86RefV2.SemanticsScalar

/-!
# `VendorX86RefV2.SemanticsSimd`

Repaired VEX 128/256-bit and EVEX AVX-512VL SIMD, AES-NI (`VAESENC`), and
carryless multiplication (`VPCLMULQDQ`) operational semantics honoring non-flat
`FS`/`GS` segment overrides (`0x64`/`0x65`) and `0x67` `addr32` truncation via
`evalLinearAddr`.
-/

namespace VendorX86RefV2

def readXmm128 (s : MachineState) (nextRip : BitVec 64) (rm : XmmRmOp) : BitVec 128 :=
  match rm with
  | .reg r => BitVec.extractLsb' 0 128 (s.ymm r)
  | .mem a => readMem128 s.mem (evalLinearAddr s nextRip a)

def readYmm256 (s : MachineState) (nextRip : BitVec 64) (rm : XmmRmOp) : BitVec 256 :=
  match rm with
  | .reg r => s.ymm r
  | .mem a => readMem256 s.mem (evalLinearAddr s nextRip a)

def clampSigned16 (z : Int) : BitVec 16 :=
  let c : Int := if z > 32767 then 32767 else if z < -32768 then -32768 else z
  BitVec.ofInt 16 c

def satSubU8 (a b : BitVec 8) : BitVec 8 :=
  if a.toNat >= b.toNat then BitVec.ofNat 8 (a.toNat - b.toNat) else 0#8

def absDiffU8 (a b : BitVec 8) : Nat :=
  if a.toNat >= b.toNat then a.toNat - b.toNat else b.toNat - a.toNat

def pshufb128 (tbl ctl : BitVec 128) : BitVec 128 :=
  packBytes128 fun i =>
    let c := getByte128 ctl i
    if c.msb then 0#8
    else getByte128 tbl ⟨(c &&& 0x0F#8).toNat % 16, Nat.mod_lt _ (by decide)⟩

def pshufd128 (src : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  packDwords128 fun i =>
    let sel := (BitVec.extractLsb' (i.val * 2) 2 imm).toNat
    getDword128 src ⟨sel % 4, Nat.mod_lt _ (by decide)⟩

def pmaddubsw128 (ub sb : BitVec 128) : BitVec 128 :=
  packWords128 fun i =>
    let u0 : Int := Int.ofNat (getByte128 ub ⟨2 * i.val, by omega⟩).toNat
    let u1 : Int := Int.ofNat (getByte128 ub ⟨2 * i.val + 1, by omega⟩).toNat
    let s0 : Int := (getByte128 sb ⟨2 * i.val, by omega⟩).toInt
    let s1 : Int := (getByte128 sb ⟨2 * i.val + 1, by omega⟩).toInt
    clampSigned16 (u0 * s0 + u1 * s1)

def pmaddwd128 (a b : BitVec 128) : BitVec 128 :=
  packDwords128 fun i =>
    let a0 : Int := (getWord128 a ⟨2 * i.val, by omega⟩).toInt
    let a1 : Int := (getWord128 a ⟨2 * i.val + 1, by omega⟩).toInt
    let b0 : Int := (getWord128 b ⟨2 * i.val, by omega⟩).toInt
    let b1 : Int := (getWord128 b ⟨2 * i.val + 1, by omega⟩).toInt
    BitVec.ofInt 32 (a0 * b0 + a1 * b1)

def psadbw128 (a b : BitVec 128) : BitVec 128 :=
  let loSum :=
    absDiffU8 (getByte128 a ⟨0, by decide⟩) (getByte128 b ⟨0, by decide⟩) +
    absDiffU8 (getByte128 a ⟨1, by decide⟩) (getByte128 b ⟨1, by decide⟩) +
    absDiffU8 (getByte128 a ⟨2, by decide⟩) (getByte128 b ⟨2, by decide⟩) +
    absDiffU8 (getByte128 a ⟨3, by decide⟩) (getByte128 b ⟨3, by decide⟩) +
    absDiffU8 (getByte128 a ⟨4, by decide⟩) (getByte128 b ⟨4, by decide⟩) +
    absDiffU8 (getByte128 a ⟨5, by decide⟩) (getByte128 b ⟨5, by decide⟩) +
    absDiffU8 (getByte128 a ⟨6, by decide⟩) (getByte128 b ⟨6, by decide⟩) +
    absDiffU8 (getByte128 a ⟨7, by decide⟩) (getByte128 b ⟨7, by decide⟩)
  let hiSum :=
    absDiffU8 (getByte128 a ⟨8, by decide⟩)  (getByte128 b ⟨8, by decide⟩) +
    absDiffU8 (getByte128 a ⟨9, by decide⟩)  (getByte128 b ⟨9, by decide⟩) +
    absDiffU8 (getByte128 a ⟨10, by decide⟩) (getByte128 b ⟨10, by decide⟩) +
    absDiffU8 (getByte128 a ⟨11, by decide⟩) (getByte128 b ⟨11, by decide⟩) +
    absDiffU8 (getByte128 a ⟨12, by decide⟩) (getByte128 b ⟨12, by decide⟩) +
    absDiffU8 (getByte128 a ⟨13, by decide⟩) (getByte128 b ⟨13, by decide⟩) +
    absDiffU8 (getByte128 a ⟨14, by decide⟩) (getByte128 b ⟨14, by decide⟩) +
    absDiffU8 (getByte128 a ⟨15, by decide⟩) (getByte128 b ⟨15, by decide⟩)
  (BitVec.ofNat 64 hiSum) ++ (BitVec.ofNat 64 loSum)

def vshiftLane32 (kind : VecShiftKind) (x : BitVec 32) (cnt : Nat) : BitVec 32 :=
  match kind with
  | .sll => if cnt >= 32 then 0#32 else x <<< cnt
  | .srl => if cnt >= 32 then 0#32 else x >>> cnt
  | .sra => if cnt >= 32 then BitVec.sshiftRight x 31 else BitVec.sshiftRight x cnt

def pmovmskb128Loop (n : Nat) (v : BitVec 128) (acc : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 64)
    (fun a => a)
    (fun k ih a =>
      let b := BitVec.extractLsb' (k * 8) 8 v
      let a' := if b.msb then a ||| (1#64 <<< k) else a
      ih a')
    n acc

def pmovmskb256Loop (n : Nat) (v : BitVec 256) (acc : BitVec 64) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64 → BitVec 64)
    (fun a => a)
    (fun k ih a =>
      let b := BitVec.extractLsb' (k * 8) 8 v
      let a' := if b.msb then a ||| (1#64 <<< k) else a
      ih a')
    n acc

def vpmovmskb128 (v : BitVec 128) : BitVec 64 := pmovmskb128Loop 16 v 0#64
def vpmovmskb256 (v : BitVec 256) : BitVec 64 := pmovmskb256Loop 32 v 0#64

def selectPerm128Lane (a b : BitVec 256) (ctlNib : BitVec 4) : BitVec 128 :=
  if ctlNib.getLsbD 3 then 0#128
  else
    match (BitVec.extractLsb' 0 2 ctlNib).toNat with
    | 0 => BitVec.extractLsb' 0 128 a
    | 1 => BitVec.extractLsb' 128 128 a
    | 2 => BitVec.extractLsb' 0 128 b
    | _ => BitVec.extractLsb' 128 128 b

def vperm2x128Eval (a b : BitVec 256) (imm : BitVec 8) : BitVec 256 :=
  let lo := selectPerm128Lane a b (BitVec.extractLsb' 0 4 imm)
  let hi := selectPerm128Lane a b (BitVec.extractLsb' 4 4 imm)
  hi ++ lo

def ternlogBit (imm : BitVec 8) (a b c : Bool) : Bool :=
  let idx := (if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)
  imm.getLsbD idx

def ternlogDwordLoop (n : Nat) (imm : BitVec 8) (x y z acc : BitVec 32) : BitVec 32 :=
  Nat.rec (motive := fun _ => BitVec 32 → BitVec 32)
    (fun a => a)
    (fun k ih a =>
      let bit := ternlogBit imm (x.getLsbD k) (y.getLsbD k) (z.getLsbD k)
      let a' := if bit then a ||| (1#32 <<< k) else a
      ih a')
    n acc

def ternlogDword (imm : BitVec 8) (x y z : BitVec 32) : BitVec 32 :=
  ternlogDwordLoop 32 imm x y z 0#32

/-! ### Carryless Multiplication (`VPCLMULQDQ`) and AES-NI (`VAESENC`) -/

def clmulLoop (n : Nat) (aExt : BitVec 128) (b : BitVec 64) (acc : BitVec 128) : BitVec 128 :=
  Nat.rec (motive := fun _ => BitVec 128 → BitVec 128)
    (fun a => a)
    (fun k ih a =>
      let idx := 63 - k
      let a' := if b.getLsbD idx then a ^^^ (aExt <<< idx) else a
      ih a')
    n acc

def carrylessMul64 (a b : BitVec 64) : BitVec 128 :=
  clmulLoop 64 (a.zeroExtend 128) b 0#128

def aesXtime (b : BitVec 8) : BitVec 8 :=
  (b <<< 1) ^^^ (if b.msb then 0x1B#8 else 0x00#8)

def aesSboxRow0  (lo : Nat) : BitVec 8 := match lo with | 0=>0x63#8|1=>0x7c#8|2=>0x77#8|3=>0x7b#8|4=>0xf2#8|5=>0x6b#8|6=>0x6f#8|7=>0xc5#8|8=>0x30#8|9=>0x01#8|10=>0x67#8|11=>0x2b#8|12=>0xfe#8|13=>0xd7#8|14=>0xab#8|_=>0x76#8
def aesSboxRow1  (lo : Nat) : BitVec 8 := match lo with | 0=>0xca#8|1=>0x82#8|2=>0xc9#8|3=>0x7d#8|4=>0xfa#8|5=>0x59#8|6=>0x47#8|7=>0xf0#8|8=>0xad#8|9=>0xd4#8|10=>0xa2#8|11=>0xaf#8|12=>0x9c#8|13=>0xa4#8|14=>0x72#8|_=>0xc0#8
def aesSboxRow2  (lo : Nat) : BitVec 8 := match lo with | 0=>0xb7#8|1=>0xfd#8|2=>0x93#8|3=>0x26#8|4=>0x36#8|5=>0x3f#8|6=>0xf7#8|7=>0xcc#8|8=>0x34#8|9=>0xa5#8|10=>0xe5#8|11=>0xf1#8|12=>0x71#8|13=>0xd8#8|14=>0x31#8|_=>0x15#8
def aesSboxRow3  (lo : Nat) : BitVec 8 := match lo with | 0=>0x04#8|1=>0xc7#8|2=>0x23#8|3=>0xc3#8|4=>0x18#8|5=>0x96#8|6=>0x05#8|7=>0x9a#8|8=>0x07#8|9=>0x12#8|10=>0x80#8|11=>0xe2#8|12=>0xeb#8|13=>0x27#8|14=>0xb2#8|_=>0x75#8
def aesSboxRow4  (lo : Nat) : BitVec 8 := match lo with | 0=>0x09#8|1=>0x83#8|2=>0x2c#8|3=>0x1a#8|4=>0x1b#8|5=>0x6e#8|6=>0x5a#8|7=>0xa0#8|8=>0x52#8|9=>0x3b#8|10=>0xd6#8|11=>0xb3#8|12=>0x29#8|13=>0xe3#8|14=>0x2f#8|_=>0x84#8
def aesSboxRow5  (lo : Nat) : BitVec 8 := match lo with | 0=>0x53#8|1=>0xd1#8|2=>0x00#8|3=>0xed#8|4=>0x20#8|5=>0xfc#8|6=>0xb1#8|7=>0x5b#8|8=>0x6a#8|9=>0xcb#8|10=>0xbe#8|11=>0x39#8|12=>0x4a#8|13=>0x4c#8|14=>0x58#8|_=>0xcf#8
def aesSboxRow6  (lo : Nat) : BitVec 8 := match lo with | 0=>0xd0#8|1=>0xef#8|2=>0xaa#8|3=>0xfb#8|4=>0x43#8|5=>0x4d#8|6=>0x33#8|7=>0x85#8|8=>0x45#8|9=>0xf9#8|10=>0x02#8|11=>0x7f#8|12=>0x50#8|13=>0x3c#8|14=>0x9f#8|_=>0xa8#8
def aesSboxRow7  (lo : Nat) : BitVec 8 := match lo with | 0=>0x51#8|1=>0xa3#8|2=>0x40#8|3=>0x8f#8|4=>0x92#8|5=>0x9d#8|6=>0x38#8|7=>0xf5#8|8=>0xbc#8|9=>0xb6#8|10=>0xda#8|11=>0x21#8|12=>0x10#8|13=>0xff#8|14=>0xf3#8|_=>0xd2#8
def aesSboxRow8  (lo : Nat) : BitVec 8 := match lo with | 0=>0xcd#8|1=>0x0c#8|2=>0x13#8|3=>0xec#8|4=>0x5f#8|5=>0x97#8|6=>0x44#8|7=>0x17#8|8=>0xc4#8|9=>0xa7#8|10=>0x7e#8|11=>0x3d#8|12=>0x64#8|13=>0x5d#8|14=>0x19#8|_=>0x73#8
def aesSboxRow9  (lo : Nat) : BitVec 8 := match lo with | 0=>0x60#8|1=>0x81#8|2=>0x4f#8|3=>0xdc#8|4=>0x22#8|5=>0x2a#8|6=>0x90#8|7=>0x88#8|8=>0x46#8|9=>0xee#8|10=>0xb8#8|11=>0x14#8|12=>0xde#8|13=>0x5e#8|14=>0x0b#8|_=>0xdb#8
def aesSboxRow10 (lo : Nat) : BitVec 8 := match lo with | 0=>0xe0#8|1=>0x32#8|2=>0x3a#8|3=>0x0a#8|4=>0x49#8|5=>0x06#8|6=>0x24#8|7=>0x5c#8|8=>0xc2#8|9=>0xd3#8|10=>0xac#8|11=>0x62#8|12=>0x91#8|13=>0x95#8|14=>0xe4#8|_=>0x79#8
def aesSboxRow11 (lo : Nat) : BitVec 8 := match lo with | 0=>0xe7#8|1=>0xc8#8|2=>0x37#8|3=>0x6d#8|4=>0x8d#8|5=>0xd5#8|6=>0x4e#8|7=>0xa9#8|8=>0x6c#8|9=>0x56#8|10=>0xf4#8|11=>0xea#8|12=>0x65#8|13=>0x7a#8|14=>0xae#8|_=>0x08#8
def aesSboxRow12 (lo : Nat) : BitVec 8 := match lo with | 0=>0xba#8|1=>0x78#8|2=>0x25#8|3=>0x2e#8|4=>0x1c#8|5=>0xa6#8|6=>0xb4#8|7=>0xc6#8|8=>0xe8#8|9=>0xdd#8|10=>0x74#8|11=>0x1f#8|12=>0x4b#8|13=>0xbd#8|14=>0x8b#8|_=>0x8a#8
def aesSboxRow13 (lo : Nat) : BitVec 8 := match lo with | 0=>0x70#8|1=>0x3e#8|2=>0xb5#8|3=>0x66#8|4=>0x48#8|5=>0x03#8|6=>0xf6#8|7=>0x0e#8|8=>0x61#8|9=>0x35#8|10=>0x57#8|11=>0xb9#8|12=>0x86#8|13=>0xc1#8|14=>0x1d#8|_=>0x9e#8
def aesSboxRow14 (lo : Nat) : BitVec 8 := match lo with | 0=>0xe1#8|1=>0xf8#8|2=>0x98#8|3=>0x11#8|4=>0x69#8|5=>0xd9#8|6=>0x8e#8|7=>0x94#8|8=>0x9b#8|9=>0x1e#8|10=>0x87#8|11=>0xe9#8|12=>0xce#8|13=>0x55#8|14=>0x28#8|_=>0xdf#8
def aesSboxRow15 (lo : Nat) : BitVec 8 := match lo with | 0=>0x8c#8|1=>0xa1#8|2=>0x89#8|3=>0x0d#8|4=>0xbf#8|5=>0xe6#8|6=>0x42#8|7=>0x68#8|8=>0x41#8|9=>0x99#8|10=>0x2d#8|11=>0x0f#8|12=>0xb0#8|13=>0x54#8|14=>0xbb#8|_=>0x16#8

def aesSbox (b : BitVec 8) : BitVec 8 :=
  let lo := b.toNat % 16
  match b.toNat / 16 with
  | 0  => aesSboxRow0  lo | 1  => aesSboxRow1  lo | 2  => aesSboxRow2  lo | 3  => aesSboxRow3  lo
  | 4  => aesSboxRow4  lo | 5  => aesSboxRow5  lo | 6  => aesSboxRow6  lo | 7  => aesSboxRow7  lo
  | 8  => aesSboxRow8  lo | 9  => aesSboxRow9  lo | 10 => aesSboxRow10 lo | 11 => aesSboxRow11 lo
  | 12 => aesSboxRow12 lo | 13 => aesSboxRow13 lo | 14 => aesSboxRow14 lo | _  => aesSboxRow15 lo

def aesShiftPerm (i : Fin 16) : Fin 16 :=
  match i.val with
  | 0  => ⟨0,  by decide⟩ | 1  => ⟨5,  by decide⟩ | 2  => ⟨10, by decide⟩ | 3  => ⟨15, by decide⟩
  | 4  => ⟨4,  by decide⟩ | 5  => ⟨9,  by decide⟩ | 6  => ⟨14, by decide⟩ | 7  => ⟨3,  by decide⟩
  | 8  => ⟨8,  by decide⟩ | 9  => ⟨13, by decide⟩ | 10 => ⟨2,  by decide⟩ | 11 => ⟨7,  by decide⟩
  | 12 => ⟨12, by decide⟩ | 13 => ⟨1,  by decide⟩ | 14 => ⟨6,  by decide⟩ | _  => ⟨11, by decide⟩

def aesMixCol (s0 s1 s2 s3 : BitVec 8) : BitVec 32 :=
  let t := s0 ^^^ s1 ^^^ s2 ^^^ s3
  let r0 := s0 ^^^ t ^^^ aesXtime (s0 ^^^ s1)
  let r1 := s1 ^^^ t ^^^ aesXtime (s1 ^^^ s2)
  let r2 := s2 ^^^ t ^^^ aesXtime (s2 ^^^ s3)
  let r3 := s3 ^^^ t ^^^ aesXtime (s3 ^^^ s0)
  r3 ++ (r2 ++ (r1 ++ r0))

def vaesenc128 (state rkey : BitVec 128) : BitVec 128 :=
  let sb : Fin 16 → BitVec 8 := fun i => aesSbox (getByte128 state (aesShiftPerm i))
  let c0 := aesMixCol (sb ⟨0, by decide⟩)  (sb ⟨1, by decide⟩)  (sb ⟨2, by decide⟩)  (sb ⟨3, by decide⟩)
  let c1 := aesMixCol (sb ⟨4, by decide⟩)  (sb ⟨5, by decide⟩)  (sb ⟨6, by decide⟩)  (sb ⟨7, by decide⟩)
  let c2 := aesMixCol (sb ⟨8, by decide⟩)  (sb ⟨9, by decide⟩)  (sb ⟨10, by decide⟩) (sb ⟨11, by decide⟩)
  let c3 := aesMixCol (sb ⟨12, by decide⟩) (sb ⟨13, by decide⟩) (sb ⟨14, by decide⟩) (sb ⟨15, by decide⟩)
  (c3 ++ (c2 ++ (c1 ++ c0))) ^^^ rkey

/-- Execute VEX/EVEX SIMD instruction honoring `FS:`/`GS:` and `0x67` `addr32`. -/
def execSimd (ins : Instr) (nextRip : BitVec 64) (s : MachineState) : Option MachineState :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .vmovdqLoad .v128 dst src =>
    some { sRip with ymm := writeVex128 s.ymm dst (readXmm128 s nextRip src) }
  | .vmovdqLoad .v256 dst src =>
    some { sRip with ymm := ymmUpd s.ymm dst (readYmm256 s nextRip src) }
  | .vmovdqStore .v128 addr src =>
    some { sRip with mem := writeMem128 s.mem (evalLinearAddr s nextRip addr) (BitVec.extractLsb' 0 128 (s.ymm src)) }
  | .vmovdqStore .v256 addr src =>
    some { sRip with mem := writeMem256 s.mem (evalLinearAddr s nextRip addr) (s.ymm src) }
  | .vmovGprToXmm is64 dst src =>
    let v64 := readRm (if is64 then .s64 else .s32) s nextRip src
    some { sRip with ymm := writeVex128 s.ymm dst (v64.zeroExtend 128) }
  | .vpadd .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1)
    let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packBytes128 fun i => getByte128 a i + getByte128 b i) }
  | .vpadd .v256 .e8 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun i => getByte256 a i + getByte256 b i) }
  | .vpadd .v256 .e16 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packWords256 fun i => getWord256 a i + getWord256 b i) }
  | .vpadd .v256 .e32 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => getDword256 a i + getDword256 b i) }
  | .vpadd .v256 .e64 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packQwords256 fun i => getQword256 a i + getQword256 b i) }
  | .vpsub .v256 .e8 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun i => getByte256 a i - getByte256 b i) }
  | .vpsub .v256 .e16 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packWords256 fun i => getWord256 a i - getWord256 b i) }
  | .vpsub .v256 .e32 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => getDword256 a i - getDword256 b i) }
  | .vpsub .v256 .e64 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packQwords256 fun i => getQword256 a i - getQword256 b i) }
  | .vpaddsw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packWords128 fun i => clampSigned16 ((getWord128 a i).toInt + (getWord128 b i).toInt)) }
  | .vpaddsw .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packWords256 fun i => clampSigned16 ((getWord256 a i).toInt + (getWord256 b i).toInt)) }
  | .vpsubusb .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packBytes128 fun i => satSubU8 (getByte128 a i) (getByte128 b i)) }
  | .vpsubusb .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun i => satSubU8 (getByte256 a i) (getByte256 b i)) }
  | .vpand .v128 dst s1 s2 =>
    some { sRip with ymm := writeVex128 s.ymm dst (BitVec.extractLsb' 0 128 (s.ymm s1) &&& readXmm128 s nextRip s2) }
  | .vpand .v256 dst s1 s2 =>
    some { sRip with ymm := ymmUpd s.ymm dst (s.ymm s1 &&& readYmm256 s nextRip s2) }
  | .vpor .v128 dst s1 s2 =>
    some { sRip with ymm := writeVex128 s.ymm dst (BitVec.extractLsb' 0 128 (s.ymm s1) ||| readXmm128 s nextRip s2) }
  | .vpor .v256 dst s1 s2 =>
    some { sRip with ymm := ymmUpd s.ymm dst (s.ymm s1 ||| readYmm256 s nextRip s2) }
  | .vpxor .v128 dst s1 s2 =>
    some { sRip with ymm := writeVex128 s.ymm dst (BitVec.extractLsb' 0 128 (s.ymm s1) ^^^ readXmm128 s nextRip s2) }
  | .vpxor .v256 dst s1 s2 =>
    some { sRip with ymm := ymmUpd s.ymm dst (s.ymm s1 ^^^ readYmm256 s nextRip s2) }
  | .vpandn .v128 dst s1 s2 =>
    some { sRip with ymm := writeVex128 s.ymm dst ((~~~BitVec.extractLsb' 0 128 (s.ymm s1)) &&& readXmm128 s nextRip s2) }
  | .vpandn .v256 dst s1 s2 =>
    some { sRip with ymm := ymmUpd s.ymm dst ((~~~(s.ymm s1)) &&& readYmm256 s nextRip s2) }
  | .vpcmpeq .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packBytes128 fun i => if getByte128 a i == getByte128 b i then 0xFF#8 else 0x00#8) }
  | .vpcmpeq .v256 .e8 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun i => if getByte256 a i == getByte256 b i then 0xFF#8 else 0x00#8) }
  | .vpcmpeq .v256 .e16 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packWords256 fun i => if getWord256 a i == getWord256 b i then 0xFFFF#16 else 0x0000#16) }
  | .vpcmpgt .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packBytes128 fun i => if (getByte128 b i).slt (getByte128 a i) then 0xFF#8 else 0x00#8) }
  | .vpcmpgt .v256 .e8 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packBytes256 fun i => if (getByte256 b i).slt (getByte256 a i) then 0xFF#8 else 0x00#8) }
  | .vpcmpgt .v256 .e32 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => if (getDword256 b i).slt (getDword256 a i) then 0xFFFFFFFF#32 else 0x00000000#32) }
  | .vpmovmskb .v128 dst src =>
    some { sRip with gpr := gprUpd s.gpr dst (vpmovmskb128 (BitVec.extractLsb' 0 128 (s.ymm src))) }
  | .vpmovmskb .v256 dst src =>
    some { sRip with gpr := gprUpd s.gpr dst (vpmovmskb256 (s.ymm src)) }
  | .vpextrq dst src imm =>
    let lane := getQword128 (BitVec.extractLsb' 0 128 (s.ymm src)) ⟨(imm &&& 1#8).toNat % 2, Nat.mod_lt _ (by decide)⟩
    some { sRip with gpr := gprUpd s.gpr dst lane }
  | .vpshufb .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (pshufb128 a b) }
  | .vpshufb .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    let lo := pshufb128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pshufb128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymm := ymmUpd s.ymm dst (hi ++ lo) }
  | .vpshufd .v128 dst src imm =>
    let a := readXmm128 s nextRip src
    some { sRip with ymm := writeVex128 s.ymm dst (pshufd128 a imm) }
  | .vpshufd .v256 dst src imm =>
    let a := readYmm256 s nextRip src
    let lo := pshufd128 (BitVec.extractLsb' 0 128 a) imm
    let hi := pshufd128 (BitVec.extractLsb' 128 128 a) imm
    some { sRip with ymm := ymmUpd s.ymm dst (hi ++ lo) }
  | .vpmaddubsw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (pmaddubsw128 a b) }
  | .vpmaddubsw .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    let lo := pmaddubsw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pmaddubsw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymm := ymmUpd s.ymm dst (hi ++ lo) }
  | .vpmaddwd .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (pmaddwd128 a b) }
  | .vpmaddwd .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    let lo := pmaddwd128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pmaddwd128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymm := ymmUpd s.ymm dst (hi ++ lo) }
  | .vpsadbw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (psadbw128 a b) }
  | .vpsadbw .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    let lo := psadbw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := psadbw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymm := ymmUpd s.ymm dst (hi ++ lo) }
  | .vpshiftImmD .v128 kind dst src imm =>
    let a := BitVec.extractLsb' 0 128 (s.ymm src)
    some { sRip with ymm := writeVex128 s.ymm dst (packDwords128 fun i => vshiftLane32 kind (getDword128 a i) imm.toNat) }
  | .vpshiftImmD .v256 kind dst src imm =>
    let a := s.ymm src
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) imm.toNat) }
  | .vpslldXmm .v256 dst s1 cnt =>
    let a := s.ymm s1
    let count64 := (BitVec.extractLsb' 0 64 (readXmm128 s nextRip cnt)).toNat
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => vshiftLane32 .sll (getDword256 a i) count64) }
  | .vpshiftVarD .v256 kind dst s1 cnt =>
    let a := s.ymm s1; let c := readYmm256 s nextRip cnt
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) (getDword256 c i).toNat) }
  | .vpermd dst idx tbl =>
    let idxV := s.ymm idx; let tblV := readYmm256 s nextRip tbl
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i =>
      let sel := ((getDword256 idxV i) &&& 7#32).toNat
      getDword256 tblV ⟨sel % 8, Nat.mod_lt _ (by decide)⟩) }
  | .vpermq dst src imm =>
    let a := readYmm256 s nextRip src
    some { sRip with ymm := ymmUpd s.ymm dst (packQwords256 fun i =>
      let sel := (BitVec.extractLsb' (i.val * 2) 2 imm).toNat
      getQword256 a ⟨sel % 4, Nat.mod_lt _ (by decide)⟩) }
  | .vperm2x128 dst s1 s2 imm =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (vperm2x128Eval a b imm) }
  | .vextract128 dst src imm =>
    let lane128 := if imm.getLsbD 0 then BitVec.extractLsb' 128 128 (s.ymm src) else BitVec.extractLsb' 0 128 (s.ymm src)
    match dst with
    | .reg r => some { sRip with ymm := writeVex128 s.ymm r lane128 }
    | .mem a => some { sRip with mem := writeMem128 s.mem (evalLinearAddr s nextRip a) lane128 }
  | .vpclmulqdq dst s1 s2 imm =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1)
    let b := readXmm128 s nextRip s2
    let qa := if imm.getLsbD 0 then BitVec.extractLsb' 64 64 a else BitVec.extractLsb' 0 64 a
    let qb := if imm.getLsbD 4 then BitVec.extractLsb' 64 64 b else BitVec.extractLsb' 0 64 b
    some { sRip with ymm := writeVex128 s.ymm dst (carrylessMul64 qa qb) }
  | .vaesenc dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1)
    let rk := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (vaesenc128 a rk) }
  | .vptest .v128 s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with flags := { cf := ((~~~a) &&& b) == 0#128, pf := false, af := false, zf := (a &&& b) == 0#128, sf := false, of := false } }
  | .vptest .v256 s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with flags := { cf := ((~~~a) &&& b) == 0#256, pf := false, af := false, zf := (a &&& b) == 0#256, sf := false, of := false } }
  | .vprolvd .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymm s1); let b := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packDwords128 fun i =>
      BitVec.rotateLeft (getDword128 a i) ((getDword128 b i).toNat % 32)) }
  | .vprolvd .v256 dst s1 s2 =>
    let a := s.ymm s1; let b := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i =>
      BitVec.rotateLeft (getDword256 a i) ((getDword256 b i).toNat % 32)) }
  | .vpternlogd .v128 dst s1 s2 imm =>
    let d := BitVec.extractLsb' 0 128 (s.ymm dst)
    let b := BitVec.extractLsb' 0 128 (s.ymm s1)
    let c := readXmm128 s nextRip s2
    some { sRip with ymm := writeVex128 s.ymm dst (packDwords128 fun i =>
      ternlogDword imm (getDword128 d i) (getDword128 b i) (getDword128 c i)) }
  | .vpternlogd .v256 dst s1 s2 imm =>
    let d := s.ymm dst; let b := s.ymm s1; let c := readYmm256 s nextRip s2
    some { sRip with ymm := ymmUpd s.ymm dst (packDwords256 fun i =>
      ternlogDword imm (getDword256 d i) (getDword256 b i) (getDword256 c i)) }
  | .vzeroupper =>
    let ymms' : YmmIdx → BitVec 256 := fun idx => (BitVec.extractLsb' 0 128 (s.ymm idx)).zeroExtend 256
    some { sRip with ymm := ymms' }
  | _ => none

end VendorX86RefV2
