-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Basic
import Trusted.MirSemantics

namespace Endianness

open Trusted.MirAst Trusted.MirSemantics

abbrev Word := BitVec 64

def u64Val (w : Word) : Val :=
  .scalar ⟨.i64, false, BitVec.ofNat 128 w.toNat⟩

def isizeVal (n : Nat) : Val :=
  .scalar ⟨.isize, true, BitVec.ofNat 128 n⟩

def bodyDataWidthVal (body : Body) (width : Nat) : Val :=
  match body.locals with
  | _ :: _ :: .enum ety :: _ => .enumVal ety width
  | _ => .unit

def bodyEndianArgs (body : Body) (toBe : Bool) (width : Nat)
    (value : Word) : List Val :=
  [.bool toBe, bodyDataWidthVal body width, u64Val value]

/-- The bit within each byte stays fixed while the byte order reverses. -/
def reverseByteIndex (bits i : Nat) : Nat :=
  8 * (bits / 8 - 1 - i / 8) + i % 8

/-- Reversal discards bits above the selected width. -/
def ByteReversal (bits : Nat) (input output : BitVec 64) : Prop :=
  ∀ i, i < 64 → output.getLsbD i =
    if i < bits then input.getLsbD (reverseByteIndex bits i) else false

end Endianness
