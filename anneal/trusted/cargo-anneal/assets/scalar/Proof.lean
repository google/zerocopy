-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem execution :
    execProg (entryProgForBody Captured.program 0) 2 { args := [] }
      (fun outcome => outcome = Spec.expectedReturn) := rfl

theorem totalCorrectness : Spec.returnsZero Captured.program := by
  have ⟨post, terminates, out, returned, result⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [] } 2 (fun outcome => outcome = Spec.expectedReturn)
      (wpProg_of_execProg execution)
  exact ⟨post, terminates, result ▸ returned⟩

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩
  intro id body found
  cases id with
  | zero =>
      have same : Captured.program.bodies[0] = body := Option.some.inj found
      subst body
      refine ⟨found, rfl, ?_⟩
      intro args valid _
      cases args with
      | nil => exact totalCorrectness.1.1
      | cons _ _ => cases valid
  | succ id => cases found

end Proof
