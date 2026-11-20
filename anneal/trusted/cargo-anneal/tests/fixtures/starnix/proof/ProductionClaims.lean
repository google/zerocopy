-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import ProductionEndpoints

namespace ProductionClaims

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction ProductionSteps

theorem wellFormed :
    BodyStaticAdmitted Captured.program sourceBody = true := rfl

theorem behavior_of_sourceReturns {flag : Bool} {width : Fin 4} {value : Word}
    {ret : Val}
    (h_ret : Returns sourceBody (endianArgs flag width.val value) ret) :
    Behavior (entryProgForBody Captured.program 0)
      { args := endianArgs flag width.val value }
      (.returned ⟨ret, ⟨[]⟩⟩) :=
  behavior_of_returns rfl wellFormed
    (validEntryArgs_bodyEndianArgs sourceBody _ rfl rfl rfl flag width value) h_ret

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output := by
  intro flag
  cases flag with
  | false =>
    exact fin4_cases
      (fun v => ⟨(le8 v).1, _, (le8 v).2⟩)
      (fun v => ⟨(le16 v).1, _, (le16 v).2⟩)
      (fun v => ⟨(le32 v).1, _, (le32 v).2⟩)
      (fun v => ⟨(le64 v).1, _, (le64 v).2⟩)
  | true =>
    exact fin4_cases
      (fun v => ⟨(be8 v).1, _, (be8 v).2⟩)
      (fun v => ⟨(be16 v).1, _, (be16 v).2⟩)
      (fun v => ⟨(be32 v).1, _, (be32 v).2⟩)
      (fun v => ⟨(be64 v).1, _, (be64 v).2⟩)

theorem baseline (safetyPre : List Val → Prop) :
    BodyVerified Captured.program 0 sourceBody safetyPre := by
  refine bodyVerified_of_safe rfl wellFormed (fun args valid _ => ?_)
  apply validArgs3_elim sourceBody _ rfl rfl (Safe sourceBody) _ args valid
  intro flag width value
  exact (completed flag width value).1

theorem bigEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      ByteReversal (8 * 2 ^ width.val) value output := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 0) (be8 value).2,
      swap8_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 1) (be16 value).2,
      swap16_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 2) (be32 value).2,
      swap32_exact value⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 3) (be64 value).2,
      swap64_exact value⟩

theorem littleEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs false width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 0) (le8 value).2, rfl⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 1) (le16 value).2, rfl⟩
  · intro value
    exact ⟨_, behavior_of_sourceReturns (width := 2) (le32 value).2, rfl⟩
  · intro value
    refine ⟨_, behavior_of_sourceReturns (width := 3) (le64 value).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change value = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]

theorem bigEndian_involutive :
    ∀ width : Fin 4, ∀ value : Word, ∃ first second : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val first, ⟨[]⟩⟩) ∧
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val first }
        (.returned ⟨u64Val second, ⟨[]⟩⟩) ∧
      second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  refine fin4_cases ?_ ?_ ?_ ?_
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (width := 0) (be8 value).2,
      behavior_of_sourceReturns (width := 0) (be8 (swap8 value)).2,
      swap8_involutive value⟩
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (width := 1) (be16 value).2,
      behavior_of_sourceReturns (width := 1) (be16 (swap16 value)).2,
      swap16_involutive value⟩
  · intro value
    exact ⟨_, _, behavior_of_sourceReturns (width := 2) (be32 value).2,
      behavior_of_sourceReturns (width := 2) (be32 (swap32 value)).2,
      swap32_involutive value⟩
  · intro value
    refine ⟨_, _, behavior_of_sourceReturns (width := 3) (be64 value).2,
      behavior_of_sourceReturns (width := 3) (be64 (swap64 value)).2, ?_⟩
    have mask : BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1) =
        BitVec.allOnes 64 := rfl
    change swap64 (swap64 value) =
      value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ (3 : Nat)) - 1)
    rw [mask, BitVec.and_allOnes]
    exact swap64_involutive value

end ProductionClaims
