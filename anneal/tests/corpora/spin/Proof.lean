-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Captured
import Spec
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

def body : Body := Captured.program.bodies[0]

noncomputable def s0 : State := mkState 0 0 [.immediate none, .dead, .immediate (some .unit)]
noncomputable def s1 : State := mkState 0 1 [.immediate none, .immediate none, .immediate (some .unit)]
noncomputable def s2 : State := mkState 1 0 [.immediate none, .immediate none, .immediate (some .unit)]
noncomputable def s3 : State := mkState 1 1 [.immediate none, .immediate none, .immediate (some .unit)]
noncomputable def s4 : State := mkState 1 0 [.immediate none, .immediate none, .immediate (some .unit)]

theorem step0 : evalStep (bodyProg body) 0 s0 = .step s1 := rfl
theorem step1 : evalStep (bodyProg body) 0 s1 = .step s2 := rfl
theorem step2 : evalStep (bodyProg body) 0 s2 = .step s3 := rfl
theorem step3 : evalStep (bodyProg body) 0 s3 = .step s4 := rfl
theorem step4 : evalStep (bodyProg body) 0 s4 = .step s3 := rfl

def invariant (state : State) : Prop :=
  state = s0 ∨ state = s1 ∨ state = s2 ∨ state = s3 ∨ state = s4

theorem closed (before after : State) (inv : invariant before)
    (transition : evalStep (bodyProg body) 0 before = .step after) :
    invariant after := by
  cases inv with
  | inl same =>
      subst before
      have equal := StepResult.step.inj (step0.symm.trans transition)
      subst after
      exact .inr (.inl rfl)
  | inr inv => cases inv with
    | inl same =>
        subst before
        have equal := StepResult.step.inj (step1.symm.trans transition)
        subst after
        exact .inr (.inr (.inl rfl))
    | inr inv => cases inv with
      | inl same =>
          subst before
          have equal := StepResult.step.inj (step2.symm.trans transition)
          subst after
          exact .inr (.inr (.inr (.inl rfl)))
      | inr inv => cases inv with
        | inl same =>
            subst before
            have equal := StepResult.step.inj (step3.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inr rfl)))
        | inr same =>
            subst before
            have equal := StepResult.step.inj (step4.symm.trans transition)
            subst after
            exact .inr (.inr (.inr (.inl rfl)))

theorem stepExists (state : State) (inv : invariant state) :
    ∃ next, evalStep (bodyProg body) 0 state = .step next := by
  cases inv with
  | inl same => subst state; exact ⟨s1, step0⟩
  | inr inv => cases inv with
    | inl same => subst state; exact ⟨s2, step1⟩
    | inr inv => cases inv with
      | inl same => subst state; exact ⟨s3, step2⟩
      | inr inv => cases inv with
        | inl same => subst state; exact ⟨s4, step3⟩
        | inr same => subst state; exact ⟨s3, step4⟩

theorem productive :
    ProductiveInvariant .little body
      (mkState 0 0 (initLocalsLoop body [] 0 body.locals)) invariant :=
  ⟨.inl rfl, closed, stepExists⟩

theorem safe : Safe .little body [] :=
  (safeFrom_and_no_done_of_productiveInvariant productive).1

theorem diverges_and_no_behavior :
    Diverges (entryProgForBody Captured.program 0) { args := [] } ∧
    ∀ out, ¬ Behavior (entryProgForBody Captured.program 0) { args := [] } out :=
  diverges_of_productiveInvariant (p := Captured.program) (defId := 0)
    (body := body) rfl rfl rfl productive

theorem verify : CrateTheorem ⟨Captured.program, Spec.specs⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id selected found
    cases id with
    | zero =>
        have same : body = selected := Option.some.inj found
        subst selected
        refine bodyVerified_of_safe found rfl (fun args valid _ => ?_)
        cases args with
        | nil => exact safe
        | cons _ _ => cases valid
    | succ id => cases found
  · intro args out
    cases args with
    | nil => exact diverges_and_no_behavior.2 out
    | cons _ _ =>
        intro h
        cases h

end Proof
