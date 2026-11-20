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
  ProductionReduction SymExec ProductionPaths ProductionEndpoints

theorem wellFormed :
    BodyStaticAdmitted Captured.program sourceBody = true := rfl

theorem behavior_of_sourceReturns {flag : Bool} {width : Fin 4} {value : Word}
    {ret : Val}
    (h_ret : Returns sourceBody (endianArgs flag width.val value) ret) :
    Behavior (entryProgForBody Captured.program 0)
      { args := endianArgs flag width.val value }
      (.returned ⟨ret, ⟨[]⟩⟩) :=
  behavior_of_returns rfl wellFormed
    (validEntryArgs_bodyEndianArgs sourceBody _ rfl rfl rfl rfl rfl flag width
      value)
    h_ret

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output := by
  intro flag width value
  cases flag with
  | false =>
    let ⟨_, hp, _⟩ := littleEndian width
    exact ⟨(path_sound hp value).1, _, (path_sound hp value).2⟩
  | true =>
    let ⟨_, hp, _⟩ := bigEndian width
    exact ⟨(path_sound hp value).1, _, (path_sound hp value).2⟩

theorem baseline (safetyPre : List Val → Prop) :
    BodyVerified Captured.program 0 sourceBody safetyPre := by
  refine bodyVerified_of_safe rfl wellFormed (fun args valid _ => ?_)
  apply validArgs3_elim sourceBody _ rfl rfl rfl rfl (Safe sourceBody) _ args
    valid
  intro flag width value
  exact (completed flag width value).1

theorem bigEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      ByteReversal (8 * 2 ^ width.val) value output := by
  intro width value
  let ⟨s, hp, hrev⟩ := bigEndian width
  exact ⟨s.eval value, behavior_of_sourceReturns (path_sound hp value).2,
    hrev value⟩

theorem littleEndian_exact :
    ∀ width : Fin 4, ∀ value : Word, ∃ output : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs false width.val value }
        (.returned ⟨u64Val output, ⟨[]⟩⟩) ∧
      output = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  intro width value
  let ⟨s, hp, hmask⟩ := littleEndian width
  exact ⟨s.eval value, behavior_of_sourceReturns (path_sound hp value).2,
    hmask value⟩

theorem bigEndian_involutive :
    ∀ width : Fin 4, ∀ value : Word, ∃ first second : Word,
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val value }
        (.returned ⟨u64Val first, ⟨[]⟩⟩) ∧
      Behavior (entryProgForBody Captured.program 0)
        { args := endianArgs true width.val first }
        (.returned ⟨u64Val second, ⟨[]⟩⟩) ∧
      second = value &&& BitVec.ofNat 64 (2 ^ (8 * 2 ^ width.val) - 1) := by
  intro width value
  let ⟨s, hp, hrev⟩ := bigEndian width
  exact ⟨s.eval value, s.eval (s.eval value),
    behavior_of_sourceReturns (path_sound hp value).2,
    behavior_of_sourceReturns (path_sound hp (s.eval value)).2,
    reverse_involutive width (hrev value) (hrev (s.eval value))⟩

end ProductionClaims
