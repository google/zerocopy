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

-- Comparing the long tuple-marker identities by `rfl` reduces strings of up
-- to about 200 characters.
set_option maxRecDepth 16384

/-! ## Shared Plumbing -/

private theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec : Executes body
      (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    Spec.ReturnsTotal Captured.program defId args ret := by
  let ⟨fuel, h_execState⟩ := executes_iff_wpState.mp h_exec
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body
      (isSingleFrame0_mkState 0 0 _)).mpr h_execState
  have h_all := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_execProg)
  exact ⟨h_all.2.2.2 _ rfl, h_all.2.2.1, h_all.2.1⟩

/-- A safe, parameterless body that runs to a return of `ret` in two steps
satisfies `BodyVerified` and `returnsPost`. -/
private theorem ret0_verified {defId : DefId} {body : Body}
    {identity : String} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_id : body.identity = identity)
    (h_safe : body.isUnsafe = false)
    (h_argc : body.argumentCount = 0)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_runs : Runs body 2 [] ret) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.returnsPost Captured.program defId identity ret := by
  have h_args : ValidEntryArgs body [] := by
    unfold ValidEntryArgs
    rw [h_tys]
    rfl
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_), ?_⟩
  · have hMatch : checkArgsMatch args [] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
    subst hNil
    exact (run_initial_success h_runs).1
  · unfold Spec.returnsPost
    rw [h_body]
    exact ⟨h_id, h_safe, h_argc,
      total_of_executes h_body h_adm h_args (run_executes h_runs)⟩

/-! ## Tuple Sealing Markers (Bodies 0-95) -/

/-- Body 0: the `FromBytes` marker for arity 3. -/
private theorem b0 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.returnsPost Captured.program 0
      (Spec.tupleMarkerId "FromBytes" 3) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 1: the `FromBytes` marker for arity 4. -/
private theorem b1 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.returnsPost Captured.program 1
      (Spec.tupleMarkerId "FromBytes" 4) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 2: the `FromBytes` marker for arity 5. -/
private theorem b2 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.returnsPost Captured.program 2
      (Spec.tupleMarkerId "FromBytes" 5) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 3: the `FromBytes` marker for arity 6. -/
private theorem b3 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.returnsPost Captured.program 3
      (Spec.tupleMarkerId "FromBytes" 6) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 4: the `FromBytes` marker for arity 7. -/
private theorem b4 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.returnsPost Captured.program 4
      (Spec.tupleMarkerId "FromBytes" 7) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 5: the `FromBytes` marker for arity 8. -/
private theorem b5 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.returnsPost Captured.program 5
      (Spec.tupleMarkerId "FromBytes" 8) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 6: the `FromBytes` marker for arity 9. -/
private theorem b6 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.returnsPost Captured.program 6
      (Spec.tupleMarkerId "FromBytes" 9) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 7: the `FromBytes` marker for arity 10. -/
private theorem b7 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.returnsPost Captured.program 7
      (Spec.tupleMarkerId "FromBytes" 10) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 8: the `FromBytes` marker for arity 11. -/
private theorem b8 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.returnsPost Captured.program 8
      (Spec.tupleMarkerId "FromBytes" 11) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 9: the `FromBytes` marker for arity 12. -/
private theorem b9 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.returnsPost Captured.program 9
      (Spec.tupleMarkerId "FromBytes" 12) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 10: the `FromBytes` marker for arity 13. -/
private theorem b10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.returnsPost Captured.program 10
      (Spec.tupleMarkerId "FromBytes" 13) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 11: the `FromBytes` marker for arity 14. -/
private theorem b11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.returnsPost Captured.program 11
      (Spec.tupleMarkerId "FromBytes" 14) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 12: the `FromBytes` marker for arity 15. -/
private theorem b12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.returnsPost Captured.program 12
      (Spec.tupleMarkerId "FromBytes" 15) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 13: the `FromBytes` marker for arity 16. -/
private theorem b13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.returnsPost Captured.program 13
      (Spec.tupleMarkerId "FromBytes" 16) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 14: the `FromBytes` marker for arity 17. -/
private theorem b14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.returnsPost Captured.program 14
      (Spec.tupleMarkerId "FromBytes" 17) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 15: the `FromBytes` marker for arity 18. -/
private theorem b15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.returnsPost Captured.program 15
      (Spec.tupleMarkerId "FromBytes" 18) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 16: the `FromBytes` marker for arity 19. -/
private theorem b16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.returnsPost Captured.program 16
      (Spec.tupleMarkerId "FromBytes" 19) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 17: the `FromBytes` marker for arity 20. -/
private theorem b17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.returnsPost Captured.program 17
      (Spec.tupleMarkerId "FromBytes" 20) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 18: the `FromBytes` marker for arity 21. -/
private theorem b18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.returnsPost Captured.program 18
      (Spec.tupleMarkerId "FromBytes" 21) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 19: the `FromBytes` marker for arity 22. -/
private theorem b19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.returnsPost Captured.program 19
      (Spec.tupleMarkerId "FromBytes" 22) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 20: the `FromBytes` marker for arity 23. -/
private theorem b20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.returnsPost Captured.program 20
      (Spec.tupleMarkerId "FromBytes" 23) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 21: the `FromBytes` marker for arity 24. -/
private theorem b21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.returnsPost Captured.program 21
      (Spec.tupleMarkerId "FromBytes" 24) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 22: the `FromBytes` marker for arity 25. -/
private theorem b22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.returnsPost Captured.program 22
      (Spec.tupleMarkerId "FromBytes" 25) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 23: the `FromBytes` marker for arity 26. -/
private theorem b23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.returnsPost Captured.program 23
      (Spec.tupleMarkerId "FromBytes" 26) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 24: the `FromZeros` marker for arity 3. -/
private theorem b24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.returnsPost Captured.program 24
      (Spec.tupleMarkerId "FromZeros" 3) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 25: the `FromZeros` marker for arity 4. -/
private theorem b25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.returnsPost Captured.program 25
      (Spec.tupleMarkerId "FromZeros" 4) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 26: the `FromZeros` marker for arity 5. -/
private theorem b26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.returnsPost Captured.program 26
      (Spec.tupleMarkerId "FromZeros" 5) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 27: the `FromZeros` marker for arity 6. -/
private theorem b27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.returnsPost Captured.program 27
      (Spec.tupleMarkerId "FromZeros" 6) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 28: the `FromZeros` marker for arity 7. -/
private theorem b28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.returnsPost Captured.program 28
      (Spec.tupleMarkerId "FromZeros" 7) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 29: the `FromZeros` marker for arity 8. -/
private theorem b29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.returnsPost Captured.program 29
      (Spec.tupleMarkerId "FromZeros" 8) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 30: the `FromZeros` marker for arity 9. -/
private theorem b30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.returnsPost Captured.program 30
      (Spec.tupleMarkerId "FromZeros" 9) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 31: the `FromZeros` marker for arity 10. -/
private theorem b31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.returnsPost Captured.program 31
      (Spec.tupleMarkerId "FromZeros" 10) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 32: the `FromZeros` marker for arity 11. -/
private theorem b32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.returnsPost Captured.program 32
      (Spec.tupleMarkerId "FromZeros" 11) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 33: the `FromZeros` marker for arity 12. -/
private theorem b33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.returnsPost Captured.program 33
      (Spec.tupleMarkerId "FromZeros" 12) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 34: the `FromZeros` marker for arity 13. -/
private theorem b34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.returnsPost Captured.program 34
      (Spec.tupleMarkerId "FromZeros" 13) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 35: the `FromZeros` marker for arity 14. -/
private theorem b35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.returnsPost Captured.program 35
      (Spec.tupleMarkerId "FromZeros" 14) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 36: the `FromZeros` marker for arity 15. -/
private theorem b36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.returnsPost Captured.program 36
      (Spec.tupleMarkerId "FromZeros" 15) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 37: the `FromZeros` marker for arity 16. -/
private theorem b37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.returnsPost Captured.program 37
      (Spec.tupleMarkerId "FromZeros" 16) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 38: the `FromZeros` marker for arity 17. -/
private theorem b38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.returnsPost Captured.program 38
      (Spec.tupleMarkerId "FromZeros" 17) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 39: the `FromZeros` marker for arity 18. -/
private theorem b39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.returnsPost Captured.program 39
      (Spec.tupleMarkerId "FromZeros" 18) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 40: the `FromZeros` marker for arity 19. -/
private theorem b40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.returnsPost Captured.program 40
      (Spec.tupleMarkerId "FromZeros" 19) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 41: the `FromZeros` marker for arity 20. -/
private theorem b41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.returnsPost Captured.program 41
      (Spec.tupleMarkerId "FromZeros" 20) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 42: the `FromZeros` marker for arity 21. -/
private theorem b42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.returnsPost Captured.program 42
      (Spec.tupleMarkerId "FromZeros" 21) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 43: the `FromZeros` marker for arity 22. -/
private theorem b43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.returnsPost Captured.program 43
      (Spec.tupleMarkerId "FromZeros" 22) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 44: the `FromZeros` marker for arity 23. -/
private theorem b44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.returnsPost Captured.program 44
      (Spec.tupleMarkerId "FromZeros" 23) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 45: the `FromZeros` marker for arity 24. -/
private theorem b45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.returnsPost Captured.program 45
      (Spec.tupleMarkerId "FromZeros" 24) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 46: the `FromZeros` marker for arity 25. -/
private theorem b46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.returnsPost Captured.program 46
      (Spec.tupleMarkerId "FromZeros" 25) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 47: the `FromZeros` marker for arity 26. -/
private theorem b47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.returnsPost Captured.program 47
      (Spec.tupleMarkerId "FromZeros" 26) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 48: the `Immutable` marker for arity 3. -/
private theorem b48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.returnsPost Captured.program 48
      (Spec.tupleMarkerId "Immutable" 3) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 49: the `Immutable` marker for arity 4. -/
private theorem b49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.returnsPost Captured.program 49
      (Spec.tupleMarkerId "Immutable" 4) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 50: the `Immutable` marker for arity 5. -/
private theorem b50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.returnsPost Captured.program 50
      (Spec.tupleMarkerId "Immutable" 5) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 51: the `Immutable` marker for arity 6. -/
private theorem b51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.returnsPost Captured.program 51
      (Spec.tupleMarkerId "Immutable" 6) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 52: the `Immutable` marker for arity 7. -/
private theorem b52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.returnsPost Captured.program 52
      (Spec.tupleMarkerId "Immutable" 7) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 53: the `Immutable` marker for arity 8. -/
private theorem b53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.returnsPost Captured.program 53
      (Spec.tupleMarkerId "Immutable" 8) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 54: the `Immutable` marker for arity 9. -/
private theorem b54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.returnsPost Captured.program 54
      (Spec.tupleMarkerId "Immutable" 9) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 55: the `Immutable` marker for arity 10. -/
private theorem b55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.returnsPost Captured.program 55
      (Spec.tupleMarkerId "Immutable" 10) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 56: the `Immutable` marker for arity 11. -/
private theorem b56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.returnsPost Captured.program 56
      (Spec.tupleMarkerId "Immutable" 11) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 57: the `Immutable` marker for arity 12. -/
private theorem b57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.returnsPost Captured.program 57
      (Spec.tupleMarkerId "Immutable" 12) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 58: the `Immutable` marker for arity 13. -/
private theorem b58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.returnsPost Captured.program 58
      (Spec.tupleMarkerId "Immutable" 13) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 59: the `Immutable` marker for arity 14. -/
private theorem b59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.returnsPost Captured.program 59
      (Spec.tupleMarkerId "Immutable" 14) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 60: the `Immutable` marker for arity 15. -/
private theorem b60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.returnsPost Captured.program 60
      (Spec.tupleMarkerId "Immutable" 15) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 61: the `Immutable` marker for arity 16. -/
private theorem b61 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.returnsPost Captured.program 61
      (Spec.tupleMarkerId "Immutable" 16) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 62: the `Immutable` marker for arity 17. -/
private theorem b62 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.returnsPost Captured.program 62
      (Spec.tupleMarkerId "Immutable" 17) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 63: the `Immutable` marker for arity 18. -/
private theorem b63 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.returnsPost Captured.program 63
      (Spec.tupleMarkerId "Immutable" 18) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 64: the `Immutable` marker for arity 19. -/
private theorem b64 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.returnsPost Captured.program 64
      (Spec.tupleMarkerId "Immutable" 19) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 65: the `Immutable` marker for arity 20. -/
private theorem b65 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.returnsPost Captured.program 65
      (Spec.tupleMarkerId "Immutable" 20) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 66: the `Immutable` marker for arity 21. -/
private theorem b66 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.returnsPost Captured.program 66
      (Spec.tupleMarkerId "Immutable" 21) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 67: the `Immutable` marker for arity 22. -/
private theorem b67 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.returnsPost Captured.program 67
      (Spec.tupleMarkerId "Immutable" 22) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 68: the `Immutable` marker for arity 23. -/
private theorem b68 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.returnsPost Captured.program 68
      (Spec.tupleMarkerId "Immutable" 23) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 69: the `Immutable` marker for arity 24. -/
private theorem b69 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.returnsPost Captured.program 69
      (Spec.tupleMarkerId "Immutable" 24) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 70: the `Immutable` marker for arity 25. -/
private theorem b70 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.returnsPost Captured.program 70
      (Spec.tupleMarkerId "Immutable" 25) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 71: the `Immutable` marker for arity 26. -/
private theorem b71 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.returnsPost Captured.program 71
      (Spec.tupleMarkerId "Immutable" 26) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 72: the `TryFromBytes` marker for arity 3. -/
private theorem b72 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.returnsPost Captured.program 72
      (Spec.tupleMarkerId "TryFromBytes" 3) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 73: the `TryFromBytes` marker for arity 4. -/
private theorem b73 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.returnsPost Captured.program 73
      (Spec.tupleMarkerId "TryFromBytes" 4) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 74: the `TryFromBytes` marker for arity 5. -/
private theorem b74 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.returnsPost Captured.program 74
      (Spec.tupleMarkerId "TryFromBytes" 5) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 75: the `TryFromBytes` marker for arity 6. -/
private theorem b75 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.returnsPost Captured.program 75
      (Spec.tupleMarkerId "TryFromBytes" 6) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 76: the `TryFromBytes` marker for arity 7. -/
private theorem b76 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.returnsPost Captured.program 76
      (Spec.tupleMarkerId "TryFromBytes" 7) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 77: the `TryFromBytes` marker for arity 8. -/
private theorem b77 :
    BodyVerified Captured.program 77 Captured.body_77
      (Spec.specs.safety Captured.body_77.identity) ∧
    Spec.returnsPost Captured.program 77
      (Spec.tupleMarkerId "TryFromBytes" 8) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 78: the `TryFromBytes` marker for arity 9. -/
private theorem b78 :
    BodyVerified Captured.program 78 Captured.body_78
      (Spec.specs.safety Captured.body_78.identity) ∧
    Spec.returnsPost Captured.program 78
      (Spec.tupleMarkerId "TryFromBytes" 9) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 79: the `TryFromBytes` marker for arity 10. -/
private theorem b79 :
    BodyVerified Captured.program 79 Captured.body_79
      (Spec.specs.safety Captured.body_79.identity) ∧
    Spec.returnsPost Captured.program 79
      (Spec.tupleMarkerId "TryFromBytes" 10) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 80: the `TryFromBytes` marker for arity 11. -/
private theorem b80 :
    BodyVerified Captured.program 80 Captured.body_80
      (Spec.specs.safety Captured.body_80.identity) ∧
    Spec.returnsPost Captured.program 80
      (Spec.tupleMarkerId "TryFromBytes" 11) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 81: the `TryFromBytes` marker for arity 12. -/
private theorem b81 :
    BodyVerified Captured.program 81 Captured.body_81
      (Spec.specs.safety Captured.body_81.identity) ∧
    Spec.returnsPost Captured.program 81
      (Spec.tupleMarkerId "TryFromBytes" 12) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 82: the `TryFromBytes` marker for arity 13. -/
private theorem b82 :
    BodyVerified Captured.program 82 Captured.body_82
      (Spec.specs.safety Captured.body_82.identity) ∧
    Spec.returnsPost Captured.program 82
      (Spec.tupleMarkerId "TryFromBytes" 13) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 83: the `TryFromBytes` marker for arity 14. -/
private theorem b83 :
    BodyVerified Captured.program 83 Captured.body_83
      (Spec.specs.safety Captured.body_83.identity) ∧
    Spec.returnsPost Captured.program 83
      (Spec.tupleMarkerId "TryFromBytes" 14) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 84: the `TryFromBytes` marker for arity 15. -/
private theorem b84 :
    BodyVerified Captured.program 84 Captured.body_84
      (Spec.specs.safety Captured.body_84.identity) ∧
    Spec.returnsPost Captured.program 84
      (Spec.tupleMarkerId "TryFromBytes" 15) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 85: the `TryFromBytes` marker for arity 16. -/
private theorem b85 :
    BodyVerified Captured.program 85 Captured.body_85
      (Spec.specs.safety Captured.body_85.identity) ∧
    Spec.returnsPost Captured.program 85
      (Spec.tupleMarkerId "TryFromBytes" 16) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 86: the `TryFromBytes` marker for arity 17. -/
private theorem b86 :
    BodyVerified Captured.program 86 Captured.body_86
      (Spec.specs.safety Captured.body_86.identity) ∧
    Spec.returnsPost Captured.program 86
      (Spec.tupleMarkerId "TryFromBytes" 17) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 87: the `TryFromBytes` marker for arity 18. -/
private theorem b87 :
    BodyVerified Captured.program 87 Captured.body_87
      (Spec.specs.safety Captured.body_87.identity) ∧
    Spec.returnsPost Captured.program 87
      (Spec.tupleMarkerId "TryFromBytes" 18) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 88: the `TryFromBytes` marker for arity 19. -/
private theorem b88 :
    BodyVerified Captured.program 88 Captured.body_88
      (Spec.specs.safety Captured.body_88.identity) ∧
    Spec.returnsPost Captured.program 88
      (Spec.tupleMarkerId "TryFromBytes" 19) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 89: the `TryFromBytes` marker for arity 20. -/
private theorem b89 :
    BodyVerified Captured.program 89 Captured.body_89
      (Spec.specs.safety Captured.body_89.identity) ∧
    Spec.returnsPost Captured.program 89
      (Spec.tupleMarkerId "TryFromBytes" 20) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 90: the `TryFromBytes` marker for arity 21. -/
private theorem b90 :
    BodyVerified Captured.program 90 Captured.body_90
      (Spec.specs.safety Captured.body_90.identity) ∧
    Spec.returnsPost Captured.program 90
      (Spec.tupleMarkerId "TryFromBytes" 21) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 91: the `TryFromBytes` marker for arity 22. -/
private theorem b91 :
    BodyVerified Captured.program 91 Captured.body_91
      (Spec.specs.safety Captured.body_91.identity) ∧
    Spec.returnsPost Captured.program 91
      (Spec.tupleMarkerId "TryFromBytes" 22) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 92: the `TryFromBytes` marker for arity 23. -/
private theorem b92 :
    BodyVerified Captured.program 92 Captured.body_92
      (Spec.specs.safety Captured.body_92.identity) ∧
    Spec.returnsPost Captured.program 92
      (Spec.tupleMarkerId "TryFromBytes" 23) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 93: the `TryFromBytes` marker for arity 24. -/
private theorem b93 :
    BodyVerified Captured.program 93 Captured.body_93
      (Spec.specs.safety Captured.body_93.identity) ∧
    Spec.returnsPost Captured.program 93
      (Spec.tupleMarkerId "TryFromBytes" 24) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 94: the `TryFromBytes` marker for arity 25. -/
private theorem b94 :
    BodyVerified Captured.program 94 Captured.body_94
      (Spec.specs.safety Captured.body_94.identity) ∧
    Spec.returnsPost Captured.program 94
      (Spec.tupleMarkerId "TryFromBytes" 25) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 95: the `TryFromBytes` marker for arity 26. -/
private theorem b95 :
    BodyVerified Captured.program 95 Captured.body_95
      (Spec.specs.safety Captured.body_95.identity) ∧
    Spec.returnsPost Captured.program 95
      (Spec.tupleMarkerId "TryFromBytes" 26) .unit :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-! ## `maximum_trailing_slice_len` Bodies (Bodies 96-107) -/

/-- Body 96: `maximum_trailing_slice_len::<[((), u8)]>`. -/
private theorem b96 :
    BodyVerified Captured.program 96 Captured.body_96
      (Spec.specs.safety Captured.body_96.identity) ∧
    Spec.returnsPost Captured.program 96 (Spec.maxLenId "[((), u8)]")
      (Spec.usizeVal (Spec.maxSliceLen 1)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 97: `maximum_trailing_slice_len::<[(u16, u8)]>`. -/
private theorem b97 :
    BodyVerified Captured.program 97 Captured.body_97
      (Spec.specs.safety Captured.body_97.identity) ∧
    Spec.returnsPost Captured.program 97 (Spec.maxLenId "[(u16, u8)]")
      (Spec.usizeVal (Spec.maxSliceLen 4)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 98: `maximum_trailing_slice_len::<[(u32, u8, u16)]>`. -/
private theorem b98 :
    BodyVerified Captured.program 98 Captured.body_98
      (Spec.specs.safety Captured.body_98.identity) ∧
    Spec.returnsPost Captured.program 98 (Spec.maxLenId "[(u32, u8, u16)]")
      (Spec.usizeVal (Spec.maxSliceLen 8)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 99: `maximum_trailing_slice_len::<[(u64, u8)]>`. -/
private theorem b99 :
    BodyVerified Captured.program 99 Captured.body_99
      (Spec.specs.safety Captured.body_99.identity) ∧
    Spec.returnsPost Captured.program 99 (Spec.maxLenId "[(u64, u8)]")
      (Spec.usizeVal (Spec.maxSliceLen 16)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 100: `maximum_trailing_slice_len::<[(u8, u16, u32)]>`. -/
private theorem b100 :
    BodyVerified Captured.program 100 Captured.body_100
      (Spec.specs.safety Captured.body_100.identity) ∧
    Spec.returnsPost Captured.program 100 (Spec.maxLenId "[(u8, u16, u32)]")
      (Spec.usizeVal (Spec.maxSliceLen 8)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 101: `maximum_trailing_slice_len::<[(u8, u32)]>`. -/
private theorem b101 :
    BodyVerified Captured.program 101 Captured.body_101
      (Spec.specs.safety Captured.body_101.identity) ∧
    Spec.returnsPost Captured.program 101 (Spec.maxLenId "[(u8, u32)]")
      (Spec.usizeVal (Spec.maxSliceLen 8)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 102: `maximum_trailing_slice_len::<[(u8, u8, u8)]>`. -/
private theorem b102 :
    BodyVerified Captured.program 102 Captured.body_102
      (Spec.specs.safety Captured.body_102.identity) ∧
    Spec.returnsPost Captured.program 102 (Spec.maxLenId "[(u8, u8, u8)]")
      (Spec.usizeVal (Spec.maxSliceLen 3)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 103: `maximum_trailing_slice_len::<[(u8,)]>`. -/
private theorem b103 :
    BodyVerified Captured.program 103 Captured.body_103
      (Spec.specs.safety Captured.body_103.identity) ∧
    Spec.returnsPost Captured.program 103 (Spec.maxLenId "[(u8,)]")
      (Spec.usizeVal (Spec.maxSliceLen 1)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 104: `maximum_trailing_slice_len::<[[u16; 3]]>`. -/
private theorem b104 :
    BodyVerified Captured.program 104 Captured.body_104
      (Spec.specs.safety Captured.body_104.identity) ∧
    Spec.returnsPost Captured.program 104 (Spec.maxLenId "[[u16; 3]]")
      (Spec.usizeVal (Spec.maxSliceLen 6)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 105: `maximum_trailing_slice_len::<[bool]>`. -/
private theorem b105 :
    BodyVerified Captured.program 105 Captured.body_105
      (Spec.specs.safety Captured.body_105.identity) ∧
    Spec.returnsPost Captured.program 105 (Spec.maxLenId "[bool]")
      (Spec.usizeVal (Spec.maxSliceLen 1)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 106: `maximum_trailing_slice_len::<[char]>`. -/
private theorem b106 :
    BodyVerified Captured.program 106 Captured.body_106
      (Spec.specs.safety Captured.body_106.identity) ∧
    Spec.returnsPost Captured.program 106 (Spec.maxLenId "[char]")
      (Spec.usizeVal (Spec.maxSliceLen 4)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 107: `maximum_trailing_slice_len::<[i128]>`. -/
private theorem b107 :
    BodyVerified Captured.program 107 Captured.body_107
      (Spec.specs.safety Captured.body_107.identity) ∧
    Spec.returnsPost Captured.program 107 (Spec.maxLenId "[i128]")
      (Spec.usizeVal (Spec.maxSliceLen 16)) :=
  ret0_verified rfl rfl rfl rfl rfl rfl rfl

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
      ⟨b0.1, b1.1, b2.1, b3.1, b4.1, b5.1, b6.1, b7.1, b8.1, b9.1, b10.1,
       b11.1, b12.1, b13.1, b14.1, b15.1, b16.1, b17.1, b18.1, b19.1,
       b20.1, b21.1, b22.1, b23.1, b24.1, b25.1, b26.1, b27.1, b28.1,
       b29.1, b30.1, b31.1, b32.1, b33.1, b34.1, b35.1, b36.1, b37.1,
       b38.1, b39.1, b40.1, b41.1, b42.1, b43.1, b44.1, b45.1, b46.1,
       b47.1, b48.1, b49.1, b50.1, b51.1, b52.1, b53.1, b54.1, b55.1,
       b56.1, b57.1, b58.1, b59.1, b60.1, b61.1, b62.1, b63.1, b64.1,
       b65.1, b66.1, b67.1, b68.1, b69.1, b70.1, b71.1, b72.1, b73.1,
       b74.1, b75.1, b76.1, b77.1, b78.1, b79.1, b80.1, b81.1, b82.1,
       b83.1, b84.1, b85.1, b86.1, b87.1, b88.1, b89.1, b90.1, b91.1,
       b92.1, b93.1, b94.1, b95.1, b96.1, b97.1, b98.1, b99.1, b100.1,
       b101.1, b102.1, b103.1, b104.1, b105.1, b106.1, b107.1, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨b0.2, b1.2, b2.2, b3.2, b4.2, b5.2, b6.2, b7.2, b8.2, b9.2, b10.2,
        b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2,
        b19.2, b20.2, b21.2, b22.2, b23.2, trivial⟩
    · exact ⟨b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2,
        b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2,
        b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2, trivial⟩
    · exact ⟨b48.2, b49.2, b50.2, b51.2, b52.2, b53.2, b54.2, b55.2, b56.2,
        b57.2, b58.2, b59.2, b60.2, b61.2, b62.2, b63.2, b64.2,
        b65.2, b66.2, b67.2, b68.2, b69.2, b70.2, b71.2, trivial⟩
    · exact ⟨b72.2, b73.2, b74.2, b75.2, b76.2, b77.2, b78.2, b79.2, b80.2,
        b81.2, b82.2, b83.2, b84.2, b85.2, b86.2, b87.2, b88.2,
        b89.2, b90.2, b91.2, b92.2, b93.2, b94.2, b95.2, trivial⟩
    · exact ⟨b96.2, b97.2, b98.2, b99.2, b100.2, b101.2, b102.2, b103.2, b104.2,
        b105.2, b106.2, b107.2, trivial⟩

end Proof
