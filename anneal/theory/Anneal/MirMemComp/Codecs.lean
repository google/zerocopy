-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Data.UInt.BasicAux
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.PureLift.Lens
public import Anneal.PureLift.MirBridge
public import Anneal.PureLift.SpatialMem.MirMemMirror
public import Anneal.MirMemComp.Memory

public section

/-!
# Computable MIR Layout, Byte-Codec, & Indirect Access Mirrors (`Codecs`)

Thin re-export and simplification layer over the computable
`Trusted.MirSemantics.{Layout, Bytes}` mirrors in
`Anneal.PureLift.SpatialMem.MirMemMirror` (`execProfileTargetEndian`,
`execByteSize`, `execIntLayout`, `execOverflowPairLayout`, `execLayoutOfTy`,
`execLeBytesOfNat`, `execEncodeUInt`, `execNatOfLeBytes`, `execDecodeUInt`,
`execInitBytes?`, `execEncodeVal`, `execDecodeValFallback`, `execDecodeVal`,
`execLoadIndirect`, `execStoreIndirect`, and `execDeinitIndirect`).

Re-exports all shared computable definitions, equational bridges, and endian
length/round-trip laws via `export Anneal.PureLift (...)` so opening both
`Anneal.PureLift` and `Anneal.MirMemComp` resolves every shared name to the
same kernel constant without ambiguity, and adds `execProfileTargetEndian_eq`,
little-endian specialization corollaries (`execLeBytesOfNat_length`,
`leBytes_roundtrip_of_lt`), and `execDecodeVal_int`.

`execProfileTargetEndian_eq`, `execLeBytesOfNat_length`, and
`leBytes_roundtrip_of_lt` compile with zero axioms (`[]`); `execDecodeVal_int`
uses at most `[propext]` (inherited from `Anneal.PureLift.MirBridge`), with `0`
`Classical.choice` and `0` `Quot.sound`.
-/

namespace Anneal.MirMemComp

open Trusted.MirAst Trusted.MirSemantics

/-! ## Re-exported Computable Mirrors and Bridges from `Anneal.PureLift` -/

export Anneal.PureLift (
  execProfileTargetEndian
  execByteSize
  execIntLayout
  execOverflowPairLayout
  execLayoutOfTy
  execLeBytesOfNat
  execEncodeUInt
  execNatOfLeBytes
  execDecodeUInt
  execInitBytes?
  execEncodeVal
  execDecodeValFallback
  execDecodeVal
  execLoadIndirect
  execStoreIndirect
  execDeinitIndirect
  execByteSize_eq
  execIntLayout_eq
  execOverflowPairLayout_eq
  execLayoutOfTy_eq
  execLeBytesOfNat_eq
  execEncodeUInt_eq
  execNatOfLeBytes_eq
  execDecodeUInt_eq
  execInitBytes?_eq
  execEncodeVal_eq
  execDecodeVal_eq
  execLoadIndirect_eq
  execStoreIndirect_eq
  execDeinitIndirect_eq
  execEncodeUInt_length
  decodeUInt_encodeUInt_of_lt
)

/-! ## Additional Equational, Byte-Length, and Integer-Decoding Laws -/

/-- `execProfileTargetEndian` equals `Trusted.MirSemantics.profileTargetEndian`
(`[]` zero axioms). -/
theorem execProfileTargetEndian_eq :
    execProfileTargetEndian = profileTargetEndian := rfl

/-- `execLeBytesOfNat k val` always emits exactly `k` bytes (`[]`). -/
theorem execLeBytesOfNat_length (k val : Nat) :
    (execLeBytesOfNat k val).length = k :=
  execEncodeUInt_length .little k val

/-- Little-endian byte decoding inverts `execLeBytesOfNat` for all
`val < 256 ^ k` (`[]`). -/
theorem leBytes_roundtrip_of_lt (k val : Nat) (hLt : val < Nat.pow 256 k) :
    execNatOfLeBytes (execLeBytesOfNat k val) = val :=
  decodeUInt_encodeUInt_of_lt .little k val hLt

/-- `execDecodeVal` on any integer type `.int w s` with
`bytes.length = execByteSize w` simplifies directly to `execInitBytes?` +
`mirEvalConstLit` (`[propext]`). -/
theorem execDecodeVal_int (endian : TargetEndian) (w : IntWidth) (s : Bool)
    (bytes : List AllocByte) (hLen : bytes.length = execByteSize w) :
    execDecodeVal endian (.int w s) bytes =
      match execInitBytes? bytes with
      | none => .ok none
      | some raw =>
        match Anneal.PureLift.mirEvalConstLit (.int w s)
            (.scalar (BitVec.ofNat 128 (execDecodeUInt endian raw))) with
        | .ok v => .ok (some v)
        | .error k => .error k := by
  have hSizeEq : (execIntLayout w).size = execByteSize w := by
    cases w <;> rfl
  have hSizePos : Nat.beq (execIntLayout w).size 0 = false := by
    cases w <;> rfl
  have hBeqSelf : Nat.beq (execByteSize w) (execByteSize w) = true := by
    cases w <;> rfl
  unfold execDecodeVal execDecodeValFallback
  dsimp only [execLayoutOfTy]
  rw [hLen, hSizeEq, hBeqSelf, Bool.not_true,
    Anneal.PureLift.ite_bool_false rfl, ← hSizeEq, hSizePos,
    Anneal.PureLift.ite_bool_false rfl]
  rfl

end Anneal.MirMemComp

end
