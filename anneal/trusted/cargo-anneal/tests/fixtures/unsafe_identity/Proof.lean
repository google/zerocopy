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

-- Inventory positions retrieve the operational bodies for this fixture. The
-- canonical safety duty still selects the reviewed predicate by body identity.
def faulting : Body := Captured.program.bodies[0]
def returning : Body := Captured.program.bodies[1]

theorem returning_runs :
    Runs returning 2 [] (.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩) := rfl

theorem faulting_step0 :
    evalStep (bodyProg faulting) 0
      (mkState 0 0 (initLocalsLoop faulting [] 0 faulting.locals)) =
      .step (mkState 0 1 [.immediate none, .immediate none]) := rfl

theorem faulting_really_faults :
    evalStep (bodyProg faulting) 0
      (mkState 0 1 [.immediate none, .immediate none]) =
      .fault .undefined := rfl

theorem faulting_not_safe : ¬Safe faulting [] := by
  intro safe
  exact safe _ .undefined (.next .refl faulting_step0) faulting_really_faults

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, True.intro⟩
  intro id selected found
  cases id with
  | zero =>
      have same : faulting = selected := Option.some.inj found
      subst selected
      exact bodyVerified_of_safe found rfl (fun _ _ required =>
        -- This elimination is valid only for the uncallable locked item.
        -- Moving the same faulting body to open changes its authenticated
        -- key, so its caller requirement no longer supplies False here.
        False.elim (required rfl))
  | succ id =>
      cases id with
      | zero =>
          have same : returning = selected := Option.some.inj found
          subst selected
          refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
          cases args with
          | nil => exact (run_initial_success returning_runs).1
          | cons _ _ => cases valid
      | succ id => cases found

end Proof
