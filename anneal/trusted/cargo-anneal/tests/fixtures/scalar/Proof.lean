-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

def body : Body := Captured.program.bodies[0]

-- The execution certificate uses the captured body. Changing the Rust result
-- invalidates this equation and the stated property.
theorem runs :
    Runs body 2 [] (.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩) := rfl

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
        have same : body = selected := Option.some.inj found
        subst selected
        refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
        cases args with
        | nil => exact (run_initial_success runs).1
        | cons _ _ => cases valid
    | succ id => cases found
  · constructor
    · exact behavior_of_returns (body := body) rfl rfl rfl
        (run_initial_success runs).2
    · intro args value beh
      let ⟨valid, returned⟩ := returns_of_behavior (body := body) rfl beh
      cases args with
      | nil => exact ⟨rfl, (run_result_unique runs returned).symm⟩
      | cons _ _ => cases valid

end Proof
