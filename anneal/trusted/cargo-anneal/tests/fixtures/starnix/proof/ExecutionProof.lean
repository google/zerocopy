-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import ProductionSteps

namespace ExecutionProof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness
  ProductionReduction ProductionSteps

/-!
All generated paths must prove real source executions before a negative test
can credit rejection of the fixed byte-reversal property. This proof uses the
same generated witness module as that later check, with no expected endpoints.
-/

theorem completed :
    ∀ flag : Bool, ∀ width : Fin 4, ∀ value : Word,
      Safe sourceBody (endianArgs flag width.val value) ∧
      ∃ output, Returns sourceBody (endianArgs flag width.val value) output := by
  intro flag
  cases flag with
  | false =>
    exact fin4_cases
      (fun v => ⟨(le8_actual v).1, _, (le8_actual v).2⟩)
      (fun v => ⟨(le16_actual v).1, _, (le16_actual v).2⟩)
      (fun v => ⟨(le32_actual v).1, _, (le32_actual v).2⟩)
      (fun v => ⟨(le64_actual v).1, _, (le64_actual v).2⟩)
  | true =>
    exact fin4_cases
      (fun v => ⟨(be8_actual v).1, _, (be8_actual v).2⟩)
      (fun v => ⟨(be16_actual v).1, _, (be16_actual v).2⟩)
      (fun v => ⟨(be32_actual v).1, _, (be32_actual v).2⟩)
      (fun v => ⟨(be64_actual v).1, _, (be64_actual v).2⟩)

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
