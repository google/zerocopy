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
import VendorArm64Ref.Types
import VendorArm64Ref.SemanticsScalar

/-!
# `VendorArm64Ref.SemanticsNeon`

Pure, `Nat.rec`-total (`0` `isPartial`) Advanced SIMD (`NEON`) + Armv8/v8.2
Cryptographic (`AES`, `PMUL`/`PMULL`, `SHA-256`, `SHA-512`) operational semantics
with 64-bit `D`-register upper-64 zeroing (`V[127:64] = 0`) and scalar reduction
zero-extension (`UADDLV`, `ADDV`, `UMAXV`, `UMINV`).
-/

namespace VendorArm64Ref

def getByte128 (v : BitVec 128) (i : Nat) : BitVec 8 :=
  BitVec.extractLsb' (i * 8) 8 v

def getHalf128 (v : BitVec 128) (i : Nat) : BitVec 16 :=
  BitVec.extractLsb' (i * 16) 16 v

def getWord128 (v : BitVec 128) (i : Nat) : BitVec 32 :=
  BitVec.extractLsb' (i * 32) 32 v

def getDword128 (v : BitVec 128) (i : Nat) : BitVec 64 :=
  BitVec.extractLsb' (i * 64) 64 v

def packBytes128 (f : Nat → BitVec 8) : BitVec 128 :=
  ((f 15 ++ (f 14 ++ (f 13 ++ f 12))) ++ (f 11 ++ (f 10 ++ (f 9 ++ f 8)))) ++
  ((f 7  ++ (f 6  ++ (f 5  ++ f 4)))  ++ (f 3  ++ (f 2  ++ (f 1 ++ f 0))))

def packHalfs128 (f : Nat → BitVec 16) : BitVec 128 :=
  ((f 7 ++ f 6) ++ (f 5 ++ f 4)) ++ ((f 3 ++ f 2) ++ (f 1 ++ f 0))

def packWords128 (f : Nat → BitVec 32) : BitVec 128 :=
  (f 3 ++ f 2) ++ (f 1 ++ f 0)

def packDwords128 (hi lo : BitVec 64) : BitVec 128 :=
  hi ++ lo

def uqaddW (w : Nat) (a b : BitVec w) : BitVec w :=
  let s := a.toNat + b.toNat
  let mx := (2 ^ w) - 1
  BitVec.ofNat w (if s > mx then mx else s)

def uqsubW (w : Nat) (a b : BitVec w) : BitVec w :=
  if a.toNat >= b.toNat then BitVec.ofNat w (a.toNat - b.toNat) else 0#w

def sqaddW (w : Nat) (a b : BitVec w) : BitVec w :=
  let s := a.toInt + b.toInt
  let hi : Int := Int.ofNat (2 ^ (w - 1)) - 1
  let lo : Int := -(Int.ofNat (2 ^ (w - 1)))
  BitVec.ofInt w (if s > hi then hi else if s < lo then lo else s)

def sqsubW (w : Nat) (a b : BitVec w) : BitVec w :=
  let d := a.toInt - b.toInt
  let hi : Int := Int.ofNat (2 ^ (w - 1)) - 1
  let lo : Int := -(Int.ofNat (2 ^ (w - 1)))
  BitVec.ofInt w (if d > hi then hi else if d < lo then lo else d)

def neonUshlLane (w : Nat) (x : BitVec w) (shByte : BitVec 8) : BitVec w :=
  if shByte.msb then
    let rsh := (0#8 - shByte).toNat
    if rsh >= w then 0#w else x >>> rsh
  else
    let lsh := shByte.toNat
    if lsh >= w then 0#w else x <<< lsh

def neonSshlLane (w : Nat) (x : BitVec w) (shByte : BitVec 8) : BitVec w :=
  if shByte.msb then
    let rsh := (0#8 - shByte).toNat
    let clamped := if rsh >= w then w - 1 else rsh
    BitVec.sshiftRight x clamped
  else
    let lsh := shByte.toNat
    if lsh >= w then 0#w else x <<< lsh

def popcntByte (b : BitVec 8) : BitVec 8 :=
  Nat.rec (motive := fun _ => BitVec 8)
    0#8
    (fun k acc => if b.getLsbD k then acc + 1#8 else acc)
    8

def pmullByte (a b : BitVec 8) : BitVec 16 :=
  let b16 := b.zeroExtend 16
  Nat.rec (motive := fun _ => BitVec 16)
    0#16
    (fun k acc => if a.getLsbD k then acc ^^^ (b16 <<< k) else acc)
    8

def pmulByte (a b : BitVec 8) : BitVec 8 :=
  BitVec.extractLsb' 0 8 (pmullByte a b)

def pmull64 (a b : BitVec 64) : BitVec 128 :=
  let b128 := b.zeroExtend 128
  Nat.rec (motive := fun _ => BitVec 128)
    0#128
    (fun k acc => if a.getLsbD k then acc ^^^ (b128 <<< k) else acc)
    64

def uaddlvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun k acc => acc + (BitVec.extractLsb' (k * esize) esize v).toNat)
    lanes

def umaxvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun k acc =>
      let cur := (BitVec.extractLsb' (k * esize) esize v).toNat
      if cur > acc then cur else acc)
    lanes

def uminvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    ((2 ^ esize) - 1)
    (fun k acc =>
      let cur := (BitVec.extractLsb' (k * esize) esize v).toNat
      if cur < acc then cur else acc)
    lanes

/-- AES forward/inverse S-box & MixColumns matching Armv8 Cryptography Extension. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  match hi with
  | 0 => match lo with
    | 0 => 0x63#8 | 1 => 0x7c#8 | 2 => 0x77#8 | 3 => 0x7b#8
    | 4 => 0xf2#8 | 5 => 0x6b#8 | 6 => 0x6f#8 | 7 => 0xc5#8
    | 8 => 0x30#8 | 9 => 0x01#8 | 10 => 0x67#8 | 11 => 0x2b#8
    | 12 => 0xfe#8 | 13 => 0xd7#8 | 14 => 0xab#8 | _ => 0x76#8
  | 1 => match lo with
    | 0 => 0xca#8 | 1 => 0x82#8 | 2 => 0xc9#8 | 3 => 0x7d#8
    | 4 => 0xfa#8 | 5 => 0x59#8 | 6 => 0x47#8 | 7 => 0xf0#8
    | 8 => 0xad#8 | 9 => 0xd4#8 | 10 => 0xa2#8 | 11 => 0xaf#8
    | 12 => 0x9c#8 | 13 => 0xa4#8 | 14 => 0x72#8 | _ => 0xc0#8
  | 2 => match lo with
    | 0 => 0xb7#8 | 1 => 0xfd#8 | 2 => 0x93#8 | 3 => 0x26#8
    | 4 => 0x36#8 | 5 => 0x3f#8 | 6 => 0xf7#8 | 7 => 0xcc#8
    | 8 => 0x34#8 | 9 => 0xa5#8 | 10 => 0xe5#8 | 11 => 0xf1#8
    | 12 => 0x71#8 | 13 => 0xd8#8 | 14 => 0x31#8 | _ => 0x15#8
  | 3 => match lo with
    | 0 => 0x04#8 | 1 => 0xc7#8 | 2 => 0x23#8 | 3 => 0xc3#8
    | 4 => 0x18#8 | 5 => 0x96#8 | 6 => 0x05#8 | 7 => 0x9a#8
    | 8 => 0x07#8 | 9 => 0x12#8 | 10 => 0x80#8 | 11 => 0xe2#8
    | 12 => 0xeb#8 | 13 => 0x27#8 | 14 => 0xb2#8 | _ => 0x75#8
  | 4 => match lo with
    | 0 => 0x09#8 | 1 => 0x83#8 | 2 => 0x2c#8 | 3 => 0x1a#8
    | 4 => 0x1b#8 | 5 => 0x6e#8 | 6 => 0x5a#8 | 7 => 0xa0#8
    | 8 => 0x52#8 | 9 => 0x3b#8 | 10 => 0xd6#8 | 11 => 0xb3#8
    | 12 => 0x29#8 | 13 => 0xe3#8 | 14 => 0x2f#8 | _ => 0x84#8
  | 5 => match lo with
    | 0 => 0x53#8 | 1 => 0xd1#8 | 2 => 0x00#8 | 3 => 0xed#8
    | 4 => 0x20#8 | 5 => 0xfc#8 | 6 => 0xb1#8 | 7 => 0x5b#8
    | 8 => 0x6a#8 | 9 => 0xcb#8 | 10 => 0xbe#8 | 11 => 0x39#8
    | 12 => 0x4a#8 | 13 => 0x4c#8 | 14 => 0x58#8 | _ => 0xcf#8
  | 6 => match lo with
    | 0 => 0xd0#8 | 1 => 0xef#8 | 2 => 0xaa#8 | 3 => 0xfb#8
    | 4 => 0x43#8 | 5 => 0x4d#8 | 6 => 0x33#8 | 7 => 0x85#8
    | 8 => 0x45#8 | 9 => 0xf9#8 | 10 => 0x02#8 | 11 => 0x7f#8
    | 12 => 0x50#8 | 13 => 0x3c#8 | 14 => 0x9f#8 | _ => 0xa8#8
  | 7 => match lo with
    | 0 => 0x51#8 | 1 => 0xa3#8 | 2 => 0x40#8 | 3 => 0x8f#8
    | 4 => 0x92#8 | 5 => 0x9d#8 | 6 => 0x38#8 | 7 => 0xf5#8
    | 8 => 0xbc#8 | 9 => 0xb6#8 | 10 => 0xda#8 | 11 => 0x21#8
    | 12 => 0x10#8 | 13 => 0xff#8 | 14 => 0xf3#8 | _ => 0xd2#8
  | 8 => match lo with
    | 0 => 0xcd#8 | 1 => 0x0c#8 | 2 => 0x13#8 | 3 => 0xec#8
    | 4 => 0x5f#8 | 5 => 0x97#8 | 6 => 0x44#8 | 7 => 0x17#8
    | 8 => 0xc4#8 | 9 => 0xa7#8 | 10 => 0x7e#8 | 11 => 0x3d#8
    | 12 => 0x64#8 | 13 => 0x5d#8 | 14 => 0x19#8 | _ => 0x73#8
  | 9 => match lo with
    | 0 => 0x60#8 | 1 => 0x81#8 | 2 => 0x4f#8 | 3 => 0xdc#8
    | 4 => 0x22#8 | 5 => 0x2a#8 | 6 => 0x90#8 | 7 => 0x88#8
    | 8 => 0x46#8 | 9 => 0xee#8 | 10 => 0xb8#8 | 11 => 0x14#8
    | 12 => 0xde#8 | 13 => 0x5e#8 | 14 => 0x0b#8 | _ => 0xdb#8
  | 10 => match lo with
    | 0 => 0xe0#8 | 1 => 0x32#8 | 2 => 0x3a#8 | 3 => 0x0a#8
    | 4 => 0x49#8 | 5 => 0x06#8 | 6 => 0x24#8 | 7 => 0x5c#8
    | 8 => 0xc2#8 | 9 => 0xd3#8 | 10 => 0xac#8 | 11 => 0x62#8
    | 12 => 0x91#8 | 13 => 0x95#8 | 14 => 0xe4#8 | _ => 0x79#8
  | 11 => match lo with
    | 0 => 0xe7#8 | 1 => 0xc8#8 | 2 => 0x37#8 | 3 => 0x6d#8
    | 4 => 0x8d#8 | 5 => 0xd5#8 | 6 => 0x4e#8 | 7 => 0xa9#8
    | 8 => 0x6c#8 | 9 => 0x56#8 | 10 => 0xf4#8 | 11 => 0xea#8
    | 12 => 0x65#8 | 13 => 0x7a#8 | 14 => 0xae#8 | _ => 0x08#8
  | 12 => match lo with
    | 0 => 0xba#8 | 1 => 0x78#8 | 2 => 0x25#8 | 3 => 0x2e#8
    | 4 => 0x1c#8 | 5 => 0xa6#8 | 6 => 0xb4#8 | 7 => 0xc6#8
    | 8 => 0xe8#8 | 9 => 0xdd#8 | 10 => 0x74#8 | 11 => 0x1f#8
    | 12 => 0x4b#8 | 13 => 0xbd#8 | 14 => 0x8b#8 | _ => 0x8a#8
  | 13 => match lo with
    | 0 => 0x70#8 | 1 => 0x3e#8 | 2 => 0xb5#8 | 3 => 0x66#8
    | 4 => 0x48#8 | 5 => 0x03#8 | 6 => 0xf6#8 | 7 => 0x0e#8
    | 8 => 0x61#8 | 9 => 0x35#8 | 10 => 0x57#8 | 11 => 0xb9#8
    | 12 => 0x86#8 | 13 => 0xc1#8 | 14 => 0x1d#8 | _ => 0x9e#8
  | 14 => match lo with
    | 0 => 0xe1#8 | 1 => 0xf8#8 | 2 => 0x98#8 | 3 => 0x11#8
    | 4 => 0x69#8 | 5 => 0xd9#8 | 6 => 0x8e#8 | 7 => 0x94#8
    | 8 => 0x9b#8 | 9 => 0x1e#8 | 10 => 0x87#8 | 11 => 0xe9#8
    | 12 => 0xce#8 | 13 => 0x55#8 | 14 => 0x28#8 | _ => 0xdf#8
  | _ => match lo with
    | 0 => 0x8c#8 | 1 => 0xa1#8 | 2 => 0x89#8 | 3 => 0x0d#8
    | 4 => 0xbf#8 | 5 => 0xe6#8 | 6 => 0x42#8 | 7 => 0x68#8
    | 8 => 0x41#8 | 9 => 0x99#8 | 10 => 0x2d#8 | 11 => 0x0f#8
    | 12 => 0xb0#8 | 13 => 0x54#8 | 14 => 0xbb#8 | _ => 0x16#8

def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  match hi with
  | 0 => match lo with
    | 0 => 0x52#8 | 1 => 0x09#8 | 2 => 0x6a#8 | 3 => 0xd5#8
    | 4 => 0x30#8 | 5 => 0x36#8 | 6 => 0xa5#8 | 7 => 0x38#8
    | 8 => 0xbf#8 | 9 => 0x40#8 | 10 => 0xa3#8 | 11 => 0x9e#8
    | 12 => 0x81#8 | 13 => 0xf3#8 | 14 => 0xd7#8 | _ => 0xfb#8
  | 1 => match lo with
    | 0 => 0x7c#8 | 1 => 0xe3#8 | 2 => 0x39#8 | 3 => 0x82#8
    | 4 => 0x9b#8 | 5 => 0x2f#8 | 6 => 0xff#8 | 7 => 0x87#8
    | 8 => 0x34#8 | 9 => 0x8e#8 | 10 => 0x43#8 | 11 => 0x44#8
    | 12 => 0xc4#8 | 13 => 0xde#8 | 14 => 0xe9#8 | _ => 0xcb#8
  | 2 => match lo with
    | 0 => 0x54#8 | 1 => 0x7b#8 | 2 => 0x94#8 | 3 => 0x32#8
    | 4 => 0xa6#8 | 5 => 0xc2#8 | 6 => 0x23#8 | 7 => 0x3d#8
    | 8 => 0xee#8 | 9 => 0x4c#8 | 10 => 0x95#8 | 11 => 0x0b#8
    | 12 => 0x42#8 | 13 => 0xfa#8 | 14 => 0xc3#8 | _ => 0x4e#8
  | 3 => match lo with
    | 0 => 0x08#8 | 1 => 0x2e#8 | 2 => 0xa1#8 | 3 => 0x66#8
    | 4 => 0x28#8 | 5 => 0xd9#8 | 6 => 0x24#8 | 7 => 0xb2#8
    | 8 => 0x76#8 | 9 => 0x5b#8 | 10 => 0xa2#8 | 11 => 0x49#8
    | 12 => 0x6d#8 | 13 => 0x8b#8 | 14 => 0xd1#8 | _ => 0x25#8
  | 4 => match lo with
    | 0 => 0x72#8 | 1 => 0xf8#8 | 2 => 0xf6#8 | 3 => 0x64#8
    | 4 => 0x86#8 | 5 => 0x68#8 | 6 => 0x98#8 | 7 => 0x16#8
    | 8 => 0xd4#8 | 9 => 0xa4#8 | 10 => 0x5c#8 | 11 => 0xcc#8
    | 12 => 0x5d#8 | 13 => 0x65#8 | 14 => 0xb6#8 | _ => 0x92#8
  | 5 => match lo with
    | 0 => 0x6c#8 | 1 => 0x70#8 | 2 => 0x48#8 | 3 => 0x50#8
    | 4 => 0xfd#8 | 5 => 0xed#8 | 6 => 0xb9#8 | 7 => 0xda#8
    | 8 => 0x5e#8 | 9 => 0x15#8 | 10 => 0x46#8 | 11 => 0x57#8
    | 12 => 0xa7#8 | 13 => 0x8d#8 | 14 => 0x9d#8 | _ => 0x84#8
  | 6 => match lo with
    | 0 => 0x90#8 | 1 => 0xd8#8 | 2 => 0xab#8 | 3 => 0x00#8
    | 4 => 0x8c#8 | 5 => 0xbc#8 | 6 => 0xd3#8 | 7 => 0x0a#8
    | 8 => 0xf7#8 | 9 => 0xe4#8 | 10 => 0x58#8 | 11 => 0x05#8
    | 12 => 0xb8#8 | 13 => 0xb3#8 | 14 => 0x45#8 | _ => 0x06#8
  | 7 => match lo with
    | 0 => 0xd0#8 | 1 => 0x2c#8 | 2 => 0x1e#8 | 3 => 0x8f#8
    | 4 => 0xca#8 | 5 => 0x3f#8 | 6 => 0x0f#8 | 7 => 0x02#8
    | 8 => 0xc1#8 | 9 => 0xaf#8 | 10 => 0xbd#8 | 11 => 0x03#8
    | 12 => 0x01#8 | 13 => 0x13#8 | 14 => 0x8a#8 | _ => 0x6b#8
  | 8 => match lo with
    | 0 => 0x3a#8 | 1 => 0x91#8 | 2 => 0x11#8 | 3 => 0x41#8
    | 4 => 0x4f#8 | 5 => 0x67#8 | 6 => 0xdc#8 | 7 => 0xea#8
    | 8 => 0x97#8 | 9 => 0xf2#8 | 10 => 0xcf#8 | 11 => 0xce#8
    | 12 => 0xf0#8 | 13 => 0xb4#8 | 14 => 0xe6#8 | _ => 0x73#8
  | 9 => match lo with
    | 0 => 0x96#8 | 1 => 0xac#8 | 2 => 0x74#8 | 3 => 0x22#8
    | 4 => 0xe7#8 | 5 => 0xad#8 | 6 => 0x35#8 | 7 => 0x85#8
    | 8 => 0xe2#8 | 9 => 0xf9#8 | 10 => 0x37#8 | 11 => 0xe8#8
    | 12 => 0x1c#8 | 13 => 0x75#8 | 14 => 0xdf#8 | _ => 0x6e#8
  | 10 => match lo with
    | 0 => 0x47#8 | 1 => 0xf1#8 | 2 => 0x1a#8 | 3 => 0x71#8
    | 4 => 0x1d#8 | 5 => 0x29#8 | 6 => 0xc5#8 | 7 => 0x89#8
    | 8 => 0x6f#8 | 9 => 0xb7#8 | 10 => 0x62#8 | 11 => 0x0e#8
    | 12 => 0xaa#8 | 13 => 0x18#8 | 14 => 0xbe#8 | _ => 0x1b#8
  | 11 => match lo with
    | 0 => 0xfc#8 | 1 => 0x56#8 | 2 => 0x3e#8 | 3 => 0x4b#8
    | 4 => 0xc6#8 | 5 => 0xd2#8 | 6 => 0x79#8 | 7 => 0x20#8
    | 8 => 0x9a#8 | 9 => 0xdb#8 | 10 => 0xc0#8 | 11 => 0xfe#8
    | 12 => 0x78#8 | 13 => 0xcd#8 | 14 => 0x5a#8 | _ => 0xf4#8
  | 12 => match lo with
    | 0 => 0x1f#8 | 1 => 0xdd#8 | 2 => 0xa8#8 | 3 => 0x33#8
    | 4 => 0x88#8 | 5 => 0x07#8 | 6 => 0xc7#8 | 7 => 0x31#8
    | 8 => 0xb1#8 | 9 => 0x12#8 | 10 => 0x10#8 | 11 => 0x59#8
    | 12 => 0x27#8 | 13 => 0x80#8 | 14 => 0xec#8 | _ => 0x5f#8
  | 13 => match lo with
    | 0 => 0x60#8 | 1 => 0x51#8 | 2 => 0x7f#8 | 3 => 0xa9#8
    | 4 => 0x19#8 | 5 => 0xb5#8 | 6 => 0x4a#8 | 7 => 0x0d#8
    | 8 => 0x2d#8 | 9 => 0xe5#8 | 10 => 0x7a#8 | 11 => 0x9f#8
    | 12 => 0x93#8 | 13 => 0xc9#8 | 14 => 0x9c#8 | _ => 0xef#8
  | 14 => match lo with
    | 0 => 0xa0#8 | 1 => 0xe0#8 | 2 => 0x3b#8 | 3 => 0x4d#8
    | 4 => 0xae#8 | 5 => 0x2a#8 | 6 => 0xf5#8 | 7 => 0xb0#8
    | 8 => 0xc8#8 | 9 => 0xeb#8 | 10 => 0xbb#8 | 11 => 0x3c#8
    | 12 => 0x83#8 | 13 => 0x53#8 | 14 => 0x99#8 | _ => 0x61#8
  | _ => match lo with
    | 0 => 0x17#8 | 1 => 0x2b#8 | 2 => 0x04#8 | 3 => 0x7e#8
    | 4 => 0xba#8 | 5 => 0x77#8 | 6 => 0xd6#8 | 7 => 0x26#8
    | 8 => 0xe1#8 | 9 => 0x69#8 | 10 => 0x14#8 | 11 => 0x63#8
    | 12 => 0x55#8 | 13 => 0x21#8 | 14 => 0x0c#8 | _ => 0x7d#8

def gfMul2 (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if b.msb then shifted ^^^ 0x1b#8 else shifted

def gfMul3  (b : BitVec 8) : BitVec 8 := gfMul2 b ^^^ b

def gfXtimeNat (n : Nat) : Nat :=
  let s := Nat.land (n * 2) 0xff
  if Nat.ble 128 n then Nat.xor s 0x1b else s

def gfMul9  (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  BitVec.ofNat 8 (Nat.xor (gfXtimeNat (gfXtimeNat (gfXtimeNat n))) n)
def gfMul11 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n2 := gfXtimeNat n
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat (gfXtimeNat n2)) n2) n)
def gfMul13 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n4 := gfXtimeNat (gfXtimeNat n)
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat n4) n4) n)
def gfMul14 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n2 := gfXtimeNat n
  let n4 := gfXtimeNat n2
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat n4) n4) n2)

def aesShiftRows128 (s : BitVec 128) : BitVec 128 :=
  let b := getByte128 s
  ((b 11 ++ (b 6  ++ (b 1  ++ b 12))) ++ (b 7  ++ (b 2  ++ (b 13 ++ b 8)))) ++
  ((b 3  ++ (b 14 ++ (b 9  ++ b 4)))  ++ (b 15 ++ (b 10 ++ (b 5  ++ b 0))))

def aesInvShiftRows128 (s : BitVec 128) : BitVec 128 :=
  let b := getByte128 s
  ((b 3  ++ (b 6  ++ (b 9  ++ b 12))) ++ (b 15 ++ (b 2  ++ (b 5  ++ b 8)))) ++
  ((b 11 ++ (b 14 ++ (b 1  ++ b 4)))  ++ (b 7  ++ (b 10 ++ (b 13 ++ b 0))))

def aesSubBytes128 (s : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => aesSbox (getByte128 s i)

def aesInvSubBytes128 (s : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => aesInvSbox (getByte128 s i)

def aesMixCol32 (col : BitVec 32) : BitVec 32 :=
  let s0 := BitVec.extractLsb' 0  8 col
  let s1 := BitVec.extractLsb' 8  8 col
  let s2 := BitVec.extractLsb' 16 8 col
  let s3 := BitVec.extractLsb' 24 8 col
  let r0 := gfMul2 s0 ^^^ gfMul3 s1 ^^^ s2 ^^^ s3
  let r1 := s0 ^^^ gfMul2 s1 ^^^ gfMul3 s2 ^^^ s3
  let r2 := s0 ^^^ s1 ^^^ gfMul2 s2 ^^^ gfMul3 s3
  let r3 := gfMul3 s0 ^^^ s1 ^^^ s2 ^^^ gfMul2 s3
  (r3 ++ r2) ++ (r1 ++ r0)

def aesInvMixCol32 (col : BitVec 32) : BitVec 32 :=
  let s0 := BitVec.extractLsb' 0  8 col
  let s1 := BitVec.extractLsb' 8  8 col
  let s2 := BitVec.extractLsb' 16 8 col
  let s3 := BitVec.extractLsb' 24 8 col
  let r0 := gfMul14 s0 ^^^ gfMul11 s1 ^^^ gfMul13 s2 ^^^ gfMul9  s3
  let r1 := gfMul9  s0 ^^^ gfMul14 s1 ^^^ gfMul11 s2 ^^^ gfMul13 s3
  let r2 := gfMul13 s0 ^^^ gfMul9  s1 ^^^ gfMul14 s2 ^^^ gfMul11 s3
  let r3 := gfMul11 s0 ^^^ gfMul13 s1 ^^^ gfMul9  s2 ^^^ gfMul14 s3
  (r3 ++ r2) ++ (r1 ++ r0)

def aeseVec (data key : BitVec 128) : BitVec 128 :=
  aesSubBytes128 (aesShiftRows128 (data ^^^ key))

def aesmcVec (data : BitVec 128) : BitVec 128 :=
  packWords128 fun c => aesMixCol32 (getWord128 data c)

def aesdVec (data key : BitVec 128) : BitVec 128 :=
  aesInvSubBytes128 (aesInvShiftRows128 (data ^^^ key))

def aesimcVec (data : BitVec 128) : BitVec 128 :=
  packWords128 fun c => aesInvMixCol32 (getWord128 data c)

/-- SHA-256 (`sha256.ml:62-215`) & SHA-512 (`sha512.ml:41-210`) Crypto Extensions. -/
def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

def sha256HashStep (x y : BitVec 128) (wk : BitVec 32) : BitVec 128 × BitVec 128 :=
  let x0 := getWord128 x 0; let x1 := getWord128 x 1; let x2 := getWord128 x 2; let x3 := getWord128 x 3
  let y0 := getWord128 y 0; let y1 := getWord128 y 1; let y2 := getWord128 y 2; let y3 := getWord128 y 3
  let chs := ((y1 ^^^ y2) &&& y0) ^^^ y2
  let maj := (x0 &&& x1) ||| ((x0 ||| x1) &&& x2)
  let sig1 := rotr32 y0 6 ^^^ rotr32 y0 11 ^^^ rotr32 y0 25
  let sig0 := rotr32 x0 2 ^^^ rotr32 x0 13 ^^^ rotr32 x0 22
  let t := y3 + sig1 + chs + wk
  let xUp := t + x3
  let yUp := t + sig0 + maj
  -- `<Y, X> = ROL(Y : X, 32)` (`sha256.ml:75-78`)
  let x' := ((x2 ++ x1) ++ (x0 ++ yUp))
  let y' := ((y2 ++ y1) ++ (y0 ++ xUp))
  (x', y')

def sha256Hash4 (x y w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let (x1, y1) := sha256HashStep x  y  (getWord128 w 0)
  let (x2, y2) := sha256HashStep x1 y1 (getWord128 w 1)
  let (x3, y3) := sha256HashStep x2 y2 (getWord128 w 2)
  let (x4, y4) := sha256HashStep x3 y3 (getWord128 w 3)
  if part1 then x4 else y4

def sha256su0Vec (d n : BitVec 128) : BitVec 128 :=
  let t : BitVec 128 := (getWord128 n 0) ++ (BitVec.extractLsb' 32 96 d)
  packWords128 fun e =>
    let elt := getWord128 t e
    let s0 := rotr32 elt 7 ^^^ rotr32 elt 18 ^^^ (elt >>> 3)
    s0 + getWord128 d e

def sha256su1Vec (d n m : BitVec 128) : BitVec 128 :=
  let t0 : BitVec 128 := (getWord128 m 0) ++ (BitVec.extractLsb' 32 96 n)
  let s1 (elt : BitVec 32) : BitVec 32 := rotr32 elt 17 ^^^ rotr32 elt 19 ^^^ (elt >>> 10)
  let r0 := s1 (getWord128 m 2) + getWord128 d 0 + getWord128 t0 0
  let r1 := s1 (getWord128 m 3) + getWord128 d 1 + getWord128 t0 1
  let r2 := s1 r0               + getWord128 d 2 + getWord128 t0 2
  let r3 := s1 r1               + getWord128 d 3 + getWord128 t0 3
  ((r3 ++ r2) ++ (r1 ++ r0))

def rotr64 (x : BitVec 64) (n : Nat) : BitVec 64 :=
  (x >>> n) ||| (x <<< (64 - n))

def sha512SumSigma0 (x : BitVec 64) : BitVec 64 := rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39
def sha512SumSigma1 (x : BitVec 64) : BitVec 64 := rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41
def sha512SchedSigma0 (x : BitVec 64) : BitVec 64 := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)
def sha512SchedSigma1 (x : BitVec 64) : BitVec 64 := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

def sha512hVec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0; let x1 := getDword128 x 1
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  let vtmp1 := ((y1 &&& x0) ^^^ ((~~~y1) &&& x1)) + sha512SumSigma1 y1 + w1
  let tmp   := vtmp1 + y0
  let vtmp0 := ((tmp &&& y1) ^^^ ((~~~tmp) &&& x0)) + sha512SumSigma1 tmp + w0
  packDwords128 vtmp1 vtmp0

def sha512h2Vec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  let vtmp1 := ((x0 &&& y1) ^^^ (x0 &&& y0) ^^^ (y1 &&& y0)) + sha512SumSigma0 y0 + w1
  let vtmp0 := ((vtmp1 &&& y0) ^^^ (vtmp1 &&& y1) ^^^ (y1 &&& y0)) + sha512SumSigma0 vtmp1 + w0
  packDwords128 vtmp1 vtmp0

def sha512su0Vec (w x : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1; let x0 := getDword128 x 0
  packDwords128 (w1 + sha512SchedSigma0 x0) (w0 + sha512SchedSigma0 w1)

def sha512su1Vec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0; let x1 := getDword128 x 1
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  packDwords128 (w1 + sha512SchedSigma1 x1 + y1) (w0 + sha512SchedSigma1 x0 + y0)

def execNeonInstr (ins : Instr) (s : MachineState) : Option MachineState :=
  let nextPc := s.pc + 4#64
  match ins with
  | .ldstSimd load vw vt rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let sAfterMem : MachineState :=
        if load then
          let val := match vw with
            | .q128 => readMem128 s.mem ea
            | .d64  => (readMem64 s.mem ea).zeroExtend 128
          writeVec vw s vt val
        else
          let v := readVec s vt
          let m' := match vw with
            | .q128 => writeMem128 s.mem ea v
            | .d64  => writeMem64  s.mem ea (BitVec.extractLsb' 0 64 v)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldstPairSimd load vw vt1 vt2 rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let stepBytes : BitVec 64 := match vw with | .q128 => 16#64 | .d64 => 8#64
      let sAfterMem : MachineState :=
        if load then
          let v1 := match vw with
            | .q128 => readMem128 s.mem ea
            | .d64  => (readMem64  s.mem ea).zeroExtend 128
          let v2 := match vw with
            | .q128 => readMem128 s.mem (ea + stepBytes)
            | .d64  => (readMem64  s.mem (ea + stepBytes)).zeroExtend 128
          let s1 := writeVec vw s vt1 v1
          writeVec vw s1 vt2 v2
        else
          let v1 := readVec s vt1
          let v2 := readVec s vt2
          let m' := match vw with
            | .q128 => writeMem128 (writeMem128 s.mem ea v1) (ea + stepBytes) v2
            | .d64  => writeMem64  (writeMem64  s.mem ea (BitVec.extractLsb' 0 64 v1))
                                   (ea + stepBytes) (BitVec.extractLsb' 0 64 v2)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .neonMovi vw vd imm64 =>
    let val128 : BitVec 128 := imm64 ++ imm64
    let s1 := writeVec vw s vd val128
    some { s1 with pc := nextPc }

  | .neonDupGp vw es vd rn =>
    let g := readXzr .x64 s rn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun _ => BitVec.extractLsb' 0 8  g
      | .e16 => packHalfs128 fun _ => BitVec.extractLsb' 0 16 g
      | .e32 => packWords128 fun _ => BitVec.extractLsb' 0 32 g
      | .e64 => g ++ g
    let s1 := writeVec vw s vd val128
    some { s1 with pc := nextPc }

  -- `FMOV Sd, Wn` / `FMOV Dd, Xn`: zeroes upper `[127:32]` or `[127:64]`!
  | .fmovGpToVec w vd rn =>
    let g := readXzr w s rn
    let val128 : BitVec 128 := match w with
      | .w32 => (BitVec.extractLsb' 0 32 g).zeroExtend 128
      | .x64 => g.zeroExtend 128
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  -- `FMOV Wd, Sn` / `FMOV Xd, Dn`: zeroes `X[d][63:32]` on 32-bit `Wd`!
  | .fmovVecToGp w rd vn =>
    let v := readVec s vn
    let val64 : BitVec 64 := match w with
      | .w32 => (BitVec.extractLsb' 0 32 v).zeroExtend 64
      | .x64 => BitVec.extractLsb' 0 64 v
    let s1 := writeXzr w s rd val64
    some { s1 with pc := nextPc }

  | .neonUmov es rd vn idx =>
    let v := readVec s vn
    let (gpw, val64) : GpWidth × BitVec 64 := match es with
      | .e8  => (.w32, (getByte128  v (idx % 16)).zeroExtend 64)
      | .e16 => (.w32, (getHalf128  v (idx % 8)).zeroExtend 64)
      | .e32 => (.w32, (getWord128  v (idx % 4)).zeroExtend 64)
      | .e64 => (.x64, getDword128 v (idx % 2))
    let s1 := writeXzr gpw s rd val64
    some { s1 with pc := nextPc }

  | .neonInsGp es vd rn idx =>
    let cur := readVec s vd
    let g   := readXzr .x64 s rn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => if i == (idx % 16) then BitVec.extractLsb' 0 8  g else getByte128 cur i
      | .e16 => packHalfs128 fun i => if i == (idx % 8)  then BitVec.extractLsb' 0 16 g else getHalf128 cur i
      | .e32 => packWords128 fun i => if i == (idx % 4)  then BitVec.extractLsb' 0 32 g else getWord128 cur i
      | .e64 =>
        if (idx % 2) == 0 then packDwords128 (getDword128 cur 1) g
        else packDwords128 g (getDword128 cur 0)
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  | .neonInsElt es vd vn dstIdx srcIdx =>
    let cur := readVec s vd
    let src := readVec s vn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => if i == (dstIdx % 16) then getByte128 src (srcIdx % 16) else getByte128 cur i
      | .e16 => packHalfs128 fun i => if i == (dstIdx % 8)  then getHalf128 src (srcIdx % 8)  else getHalf128 cur i
      | .e32 => packWords128 fun i => if i == (dstIdx % 4)  then getWord128 src (srcIdx % 4)  else getWord128 cur i
      | .e64 =>
        let el := getDword128 src (srcIdx % 2)
        if (dstIdx % 2) == 0 then packDwords128 (getDword128 cur 1) el
        else packDwords128 el (getDword128 cur 0)
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  | .neonLogic vw op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match op with
      | .and_ => n &&& m
      | .bic  => n &&& (~~~m)
      | .orr  => n ||| m
      | .eor  => n ^^^ m
      | .bsl  => (n &&& d) ||| (m &&& (~~~d))
      | .bit_ => (n &&& m) ||| (d &&& (~~~m))
      | .bif_ => (d &&& m) ||| (n &&& (~~~m))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonArith vw es op vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match op, es with
      | .add,   .e8  => packBytes128 fun i => getByte128 n i + getByte128 m i
      | .add,   .e16 => packHalfs128 fun i => getHalf128 n i + getHalf128 m i
      | .add,   .e32 => packWords128 fun i => getWord128 n i + getWord128 m i
      | .add,   .e64 => packDwords128 (getDword128 n 1 + getDword128 m 1) (getDword128 n 0 + getDword128 m 0)
      | .sub,   .e8  => packBytes128 fun i => getByte128 n i - getByte128 m i
      | .sub,   .e16 => packHalfs128 fun i => getHalf128 n i - getHalf128 m i
      | .sub,   .e32 => packWords128 fun i => getWord128 n i - getWord128 m i
      | .sub,   .e64 => packDwords128 (getDword128 n 1 - getDword128 m 1) (getDword128 n 0 - getDword128 m 0)
      | .uqadd, .e8  => packBytes128 fun i => uqaddW 8  (getByte128 n i) (getByte128 m i)
      | .uqadd, .e16 => packHalfs128 fun i => uqaddW 16 (getHalf128 n i) (getHalf128 m i)
      | .uqadd, .e32 => packWords128 fun i => uqaddW 32 (getWord128 n i) (getWord128 m i)
      | .uqadd, .e64 => packDwords128 (uqaddW 64 (getDword128 n 1) (getDword128 m 1)) (uqaddW 64 (getDword128 n 0) (getDword128 m 0))
      | .uqsub, .e8  => packBytes128 fun i => uqsubW 8  (getByte128 n i) (getByte128 m i)
      | .uqsub, .e16 => packHalfs128 fun i => uqsubW 16 (getHalf128 n i) (getHalf128 m i)
      | .uqsub, .e32 => packWords128 fun i => uqsubW 32 (getWord128 n i) (getWord128 m i)
      | .uqsub, .e64 => packDwords128 (uqsubW 64 (getDword128 n 1) (getDword128 m 1)) (uqsubW 64 (getDword128 n 0) (getDword128 m 0))
      | .sqadd, .e8  => packBytes128 fun i => sqaddW 8  (getByte128 n i) (getByte128 m i)
      | .sqadd, .e16 => packHalfs128 fun i => sqaddW 16 (getHalf128 n i) (getHalf128 m i)
      | .sqadd, .e32 => packWords128 fun i => sqaddW 32 (getWord128 n i) (getWord128 m i)
      | .sqadd, .e64 => packDwords128 (sqaddW 64 (getDword128 n 1) (getDword128 m 1)) (sqaddW 64 (getDword128 n 0) (getDword128 m 0))
      | .sqsub, .e8  => packBytes128 fun i => sqsubW 8  (getByte128 n i) (getByte128 m i)
      | .sqsub, .e16 => packHalfs128 fun i => sqsubW 16 (getHalf128 n i) (getHalf128 m i)
      | .sqsub, .e32 => packWords128 fun i => sqsubW 32 (getWord128 n i) (getWord128 m i)
      | .sqsub, .e64 => packDwords128 (sqsubW 64 (getDword128 n 1) (getDword128 m 1)) (sqsubW 64 (getDword128 n 0) (getDword128 m 0))
      | .addp,  .e8  =>
        match vw with
        | .q128 => packBytes128 fun i =>
          if i < 8 then getByte128 n (2 * i) + getByte128 n (2 * i + 1)
          else getByte128 m (2 * (i - 8)) + getByte128 m (2 * (i - 8) + 1)
        | .d64  => packBytes128 fun i =>
          if i < 4 then getByte128 n (2 * i) + getByte128 n (2 * i + 1)
          else if i < 8 then getByte128 m (2 * (i - 4)) + getByte128 m (2 * (i - 4) + 1)
          else 0#8
      | .addp,  .e16 =>
        match vw with
        | .q128 => packHalfs128 fun i =>
          if i < 4 then getHalf128 n (2 * i) + getHalf128 n (2 * i + 1)
          else getHalf128 m (2 * (i - 4)) + getHalf128 m (2 * (i - 4) + 1)
        | .d64  => packHalfs128 fun i =>
          if i < 2 then getHalf128 n (2 * i) + getHalf128 n (2 * i + 1)
          else if i < 4 then getHalf128 m (2 * (i - 2)) + getHalf128 m (2 * (i - 2) + 1)
          else 0#16
      | .addp,  .e32 =>
        match vw with
        | .q128 => packWords128 fun i =>
          if i < 2 then getWord128 n (2 * i) + getWord128 n (2 * i + 1)
          else getWord128 m (2 * (i - 2)) + getWord128 m (2 * (i - 2) + 1)
        | .d64  => packWords128 fun i =>
          if i == 0 then getWord128 n 0 + getWord128 n 1
          else if i == 1 then getWord128 m 0 + getWord128 m 1
          else 0#32
      | .addp,  .e64 =>
        packDwords128 (getDword128 m 0 + getDword128 m 1) (getDword128 n 0 + getDword128 n 1)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonCmp vw es op vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let mask8  (p : Bool) : BitVec 8  := if p then 0xff#8 else 0#8
    let mask16 (p : Bool) : BitVec 16 := if p then 0xffff#16 else 0#16
    let mask32 (p : Bool) : BitVec 32 := if p then 0xffffffff#32 else 0#32
    let mask64 (p : Bool) : BitVec 64 := if p then 0xffffffffffffffff#64 else 0#64
    let cmpW {k : Nat} (x y : BitVec k) : Bool :=
      match op with
      | .cmeq     => x == y
      | .cmgt     => decide (x.toInt > y.toInt)
      | .cmhi     => decide (x.toNat > y.toNat)
      | .cmge     => decide (x.toInt >= y.toInt)
      | .cmeqZero => x == 0#k
      | .cmltZero => x.msb
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => mask8  (cmpW (getByte128 n i) (getByte128 m i))
      | .e16 => packHalfs128 fun i => mask16 (cmpW (getHalf128 n i) (getHalf128 m i))
      | .e32 => packWords128 fun i => mask32 (cmpW (getWord128 n i) (getWord128 m i))
      | .e64 => packDwords128 (mask64 (cmpW (getDword128 n 1) (getDword128 m 1)))
                              (mask64 (cmpW (getDword128 n 0) (getDword128 m 0)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonShiftImm vw es op vd vn amt =>
    let n := readVec s vn
    let shW (k : Nat) (x : BitVec k) : BitVec k :=
      match op with
      | .shl  => if amt >= k then 0#k else x <<< amt
      | .ushr => if amt >= k then 0#k else x >>> amt
      | .sshr => BitVec.sshiftRight x (if amt >= k then k - 1 else amt)
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => shW 8  (getByte128 n i)
      | .e16 => packHalfs128 fun i => shW 16 (getHalf128 n i)
      | .e32 => packWords128 fun i => shW 32 (getWord128 n i)
      | .e64 => packDwords128 (shW 64 (getDword128 n 1)) (shW 64 (getDword128 n 0))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonShiftVar vw es signed vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let fnW (k : Nat) (x : BitVec k) (sh : BitVec 8) : BitVec k :=
      if signed then neonSshlLane k x sh else neonUshlLane k x sh
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => fnW 8  (getByte128 n i) (getByte128 m i)
      | .e16 => packHalfs128 fun i => fnW 16 (getHalf128 n i) (BitVec.extractLsb' 0 8 (getHalf128 m i))
      | .e32 => packWords128 fun i => fnW 32 (getWord128 n i) (BitVec.extractLsb' 0 8 (getWord128 m i))
      | .e64 => packDwords128 (fnW 64 (getDword128 n 1) (BitVec.extractLsb' 0 8 (getDword128 m 1)))
                              (fnW 64 (getDword128 n 0) (BitVec.extractLsb' 0 8 (getDword128 m 0)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonUaddlp vw es vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := match es with
      | .e8  => packHalfs128 fun i => (getByte128 n (2 * i)).zeroExtend 16 + (getByte128 n (2 * i + 1)).zeroExtend 16
      | .e16 => packWords128 fun i => (getHalf128 n (2 * i)).zeroExtend 32 + (getHalf128 n (2 * i + 1)).zeroExtend 32
      | _    => packDwords128 ((getWord128 n 2).zeroExtend 64 + (getWord128 n 3).zeroExtend 64)
                              ((getWord128 n 0).zeroExtend 64 + (getWord128 n 1).zeroExtend 64)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  -- Across-vector scalar reductions (`instruction.ml:1872, 1922, 2625`):
  -- writes zero-extended result into `V[Rd][127:0]`, zeroing all upper bits!
  | .neonReduce vw es op vd vn =>
    let n := readVec s vn
    let datasize := match vw with | .q128 => 128 | .d64 => 64
    let esBits := es.bits
    let lanes := datasize / esBits
    let res128 : BitVec 128 := match op with
      | .uaddlv => (BitVec.ofNat (2 * esBits) (uaddlvLoop lanes esBits n)).zeroExtend 128
      | .addv   => (BitVec.ofNat esBits       (uaddlvLoop lanes esBits n)).zeroExtend 128
      | .umaxv  => (BitVec.ofNat esBits       (umaxvLoop  lanes esBits n)).zeroExtend 128
      | .uminv  => (BitVec.ofNat esBits       (uminvLoop  lanes esBits n)).zeroExtend 128
    let s1 := writeVec .q128 s vd res128
    some { s1 with pc := nextPc }

  | .neonRev64 vw es vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => getByte128 n ((i / 8) * 8 + (7 - (i % 8)))
      | .e16 => packHalfs128 fun i => getHalf128 n ((i / 4) * 4 + (3 - (i % 4)))
      | _    => packWords128 fun i => getWord128 n ((i / 2) * 2 + (1 - (i % 2)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonExt vw vd vn vm imm4 =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match vw with
      | .q128 => packBytes128 fun i =>
        let k := i + imm4
        if k < 16 then getByte128 n k else getByte128 m (k - 16)
      | .d64  => packBytes128 fun i =>
        if i >= 8 then 0#8
        else
          let k := i + imm4
          if k < 8 then getByte128 n k else getByte128 m (k - 8)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonTbl1 vw vd vn vm =>
    let tbl := readVec s vn
    let idx := readVec s vm
    let res : BitVec 128 := packBytes128 fun i =>
      let b := (getByte128 idx i).toNat
      if b < 16 then getByte128 tbl b else 0#8
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonCnt vw vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := packBytes128 fun i => popcntByte (getByte128 n i)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonPmul vw vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := packBytes128 fun i => pmulByte (getByte128 n i) (getByte128 m i)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonPmull high es vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match es with
      | .e8  =>
        let off := if high then 8 else 0
        packHalfs128 fun i => pmullByte (getByte128 n (off + i)) (getByte128 m (off + i))
      | _    =>
        let lane := if high then 1 else 0
        pmull64 (getDword128 n lane) (getDword128 m lane)
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoAes op vd vn =>
    let d := readVec s vd
    let n := readVec s vn
    let res := match op with
      | .aese   => aeseVec d n
      | .aesmc  => aesmcVec n
      | .aesd   => aesdVec d n
      | .aesimc => aesimcVec n
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoSha256 op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res := match op with
      | .h   => sha256Hash4 d n m true
      | .h2  => sha256Hash4 n d m false
      | .su0 => sha256su0Vec d n
      | .su1 => sha256su1Vec d n m
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoSha512 op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res := match op with
      | .h   => sha512hVec d n m
      | .h2  => sha512h2Vec d n m
      | .su0 => sha512su0Vec d n
      | .su1 => sha512su1Vec d n m
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | _ => none

end VendorArm64Ref
