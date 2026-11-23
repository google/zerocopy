-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import ProductionPaths

namespace ExecutionProof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction SymExec ProductionPaths

/-!
Every control path must prove a real source execution before a negative test
can credit rejection of the fixed byte-reversal property. This proof runs the
same symbolic paths as that check, with no expected endpoints, so it applies
unchanged to any implementation the symbolic evaluator supports.
-/

/-- Every control path returns some supported word. -/
theorem paths_some : ∀ flag : Bool, ∀ width : Fin 4,
    (pathWord flag width.val).isSome = true := by
  intro flag
  cases flag <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> decide +kernel

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output := by
  intro flag width value
  let ⟨_, hp⟩ := Option.isSome_iff_exists.mp (paths_some flag width)
  exact ⟨(path_sound hp value).1, _, (path_sound hp value).2⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      have same : sourceBody = body := Option.some.inj found
      subst body
      refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
      apply validArgs3_elim sourceBody _ rfl rfl
        (Safe sourceBody) _ args valid
      intro flag width value
      exact (completed flag width value).1
    | succ id => cases found
  · refine ⟨sourceBody, rfl, ?_⟩
    apply validArgs3_elim sourceBody _ rfl rfl
      (fun args => ∃ output,
        Behavior (entryProgForBody Captured.program 0) { args := args }
          (.returned ⟨output, ⟨[]⟩⟩))
    intro flag width value
    let ⟨output, h_ret⟩ := (completed flag width value).2
    exact ⟨output, behavior_of_returns rfl rfl
      (validEntryArgs_bodyEndianArgs sourceBody _ rfl rfl rfl flag width value)
      h_ret⟩

end ExecutionProof
