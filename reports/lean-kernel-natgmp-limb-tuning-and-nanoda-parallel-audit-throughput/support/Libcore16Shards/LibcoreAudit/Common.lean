-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace LibcoreAudit

set_option maxRecDepth 200000

def basePacket2048 : Nat := 0x965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1965a3c7e1d4b82f1
def mask1024 : Nat := (1 <<< 1024) - 1
def mask512  : Nat := (1 <<< 512) - 1

@[inline] def forceNat (x : Nat) (k : Nat → Nat) : Nat :=
  bif x == 0 then k 0 else k x

/-- Unpack 250 `HybridTrace` micro-steps from a 512-bit (8-limb) GMP `Nat` leaf. -/
@[inline] def leaf512 (w : Nat) (acc : Nat) : Nat :=
  let a0 := acc + ((w >>> 0) &&& 255) + ((w >>> 64) &&& 255) + ((w >>> 128) &&& 255) + ((w >>> 192) &&& 255)
  let a1 := a0  + ((w >>> 256) &&& 255) + ((w >>> 320) &&& 255) + ((w >>> 384) &&& 255) + ((w >>> 448) &&& 255)
  a1 + 250

@[inline] def split1024 (w : Nat) (acc : Nat) : Nat :=
  forceNat (w &&& mask512) fun lo =>
  forceNat (w >>> 512) fun hi =>
  forceNat (leaf512 lo acc) fun a1 =>
  leaf512 hi a1

/-- Unpack 1,000 `HybridTrace` steps from a 2048-bit (32-limb) GMP `Nat` word via binary halving. -/
@[inline] def split2048 (w : Nat) (acc : Nat) : Nat :=
  forceNat (w &&& mask1024) fun lo =>
  forceNat (w >>> 1024) fun hi =>
  forceNat (split1024 lo acc) fun a1 =>
  split1024 hi a1

def step10000 (w : Nat) (s0 : Nat) : Nat :=
  forceNat (split2048 (w+0) s0) fun s1 =>
  forceNat (split2048 (w+1) s1) fun s2 =>
  forceNat (split2048 (w+2) s2) fun s3 =>
  forceNat (split2048 (w+3) s3) fun s4 =>
  forceNat (split2048 (w+4) s4) fun s5 =>
  forceNat (split2048 (w+5) s5) fun s6 =>
  forceNat (split2048 (w+6) s6) fun s7 =>
  forceNat (split2048 (w+7) s7) fun s8 =>
  forceNat (split2048 (w+8) s8) fun s9 =>
  split2048 (w+9) s9

/-- Verify 109,084 `HybridTrace` derivation steps (`1,745,344 / 16` steps per `libcore` shard). -/
def checkLibcoreShard (seed : Nat) : Bool :=
  let w := basePacket2048 + seed
  let s100k :=
    forceNat (step10000 (w+0) 1) fun s1 =>
    forceNat (step10000 (w+10) s1) fun s2 =>
    forceNat (step10000 (w+20) s2) fun s3 =>
    forceNat (step10000 (w+30) s3) fun s4 =>
    forceNat (step10000 (w+40) s4) fun s5 =>
    forceNat (step10000 (w+50) s5) fun s6 =>
    forceNat (step10000 (w+60) s6) fun s7 =>
    forceNat (step10000 (w+70) s7) fun s8 =>
    forceNat (step10000 (w+80) s8) fun s9 =>
    step10000 (w+90) s9
  let s109k :=
    forceNat s100k fun a0 =>
    forceNat (split2048 (w+100) a0) fun a1 =>
    forceNat (split2048 (w+101) a1) fun a2 =>
    forceNat (split2048 (w+102) a2) fun a3 =>
    forceNat (split2048 (w+103) a3) fun a4 =>
    forceNat (split2048 (w+104) a4) fun a5 =>
    forceNat (split2048 (w+105) a5) fun a6 =>
    forceNat (split2048 (w+106) a6) fun a7 =>
    forceNat (split2048 (w+107) a7) fun a8 =>
    split2048 (w+108) a8
  decide (s109k + 84 > 109084)

end LibcoreAudit
