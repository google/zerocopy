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

-- Comparing the marker identities by `rfl` reduces strings of up to about
-- 190 characters.
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

/-- A safe, parameterless body that runs to a return of `()` in two steps
satisfies `BodyVerified` and `returnsUnitPost`. -/
private theorem unit0_verified {defId : DefId} {body : Body}
    {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_id : body.identity = identity)
    (h_safe : body.isUnsafe = false)
    (h_argc : body.argumentCount = 0)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_runs : Runs body 2 [] .unit) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.returnsUnitPost Captured.program defId identity := by
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
  · unfold Spec.returnsUnitPost
    rw [h_body]
    exact ⟨h_id, h_safe, h_argc,
      total_of_executes h_body h_adm h_args (run_executes h_runs)⟩

/-! ## Markers (Bodies 0-155) -/

/-- Body 0: `FromZeros`, `Option<extern "C" fn>`, arity 0. -/
private theorem b0 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.returnsUnitPost Captured.program 0
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 1: `FromZeros`, `Option<extern "C" fn>`, arity 1. -/
private theorem b1 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.returnsUnitPost Captured.program 1
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 2: `FromZeros`, `Option<extern "C" fn>`, arity 2. -/
private theorem b2 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.returnsUnitPost Captured.program 2
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 3: `FromZeros`, `Option<extern "C" fn>`, arity 3. -/
private theorem b3 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.returnsUnitPost Captured.program 3
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 4: `FromZeros`, `Option<extern "C" fn>`, arity 4. -/
private theorem b4 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.returnsUnitPost Captured.program 4
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 5: `FromZeros`, `Option<extern "C" fn>`, arity 5. -/
private theorem b5 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.returnsUnitPost Captured.program 5
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 6: `FromZeros`, `Option<extern "C" fn>`, arity 6. -/
private theorem b6 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.returnsUnitPost Captured.program 6
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 7: `FromZeros`, `Option<extern "C" fn>`, arity 7. -/
private theorem b7 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.returnsUnitPost Captured.program 7
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 8: `FromZeros`, `Option<extern "C" fn>`, arity 8. -/
private theorem b8 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.returnsUnitPost Captured.program 8
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 9: `FromZeros`, `Option<extern "C" fn>`, arity 9. -/
private theorem b9 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.returnsUnitPost Captured.program 9
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 10: `FromZeros`, `Option<extern "C" fn>`, arity 10. -/
private theorem b10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.returnsUnitPost Captured.program 10
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 11: `FromZeros`, `Option<extern "C" fn>`, arity 11. -/
private theorem b11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.returnsUnitPost Captured.program 11
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 12: `FromZeros`, `Option<extern "C" fn>`, arity 12. -/
private theorem b12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.returnsUnitPost Captured.program 12
      (Spec.optFnMarkerId "FromZeros" "extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 13: `FromZeros`, `Option<fn>`, arity 0. -/
private theorem b13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.returnsUnitPost Captured.program 13
      (Spec.optFnMarkerId "FromZeros" "" 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 14: `FromZeros`, `Option<fn>`, arity 1. -/
private theorem b14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.returnsUnitPost Captured.program 14
      (Spec.optFnMarkerId "FromZeros" "" 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 15: `FromZeros`, `Option<fn>`, arity 2. -/
private theorem b15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.returnsUnitPost Captured.program 15
      (Spec.optFnMarkerId "FromZeros" "" 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 16: `FromZeros`, `Option<fn>`, arity 3. -/
private theorem b16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.returnsUnitPost Captured.program 16
      (Spec.optFnMarkerId "FromZeros" "" 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 17: `FromZeros`, `Option<fn>`, arity 4. -/
private theorem b17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.returnsUnitPost Captured.program 17
      (Spec.optFnMarkerId "FromZeros" "" 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 18: `FromZeros`, `Option<fn>`, arity 5. -/
private theorem b18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.returnsUnitPost Captured.program 18
      (Spec.optFnMarkerId "FromZeros" "" 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 19: `FromZeros`, `Option<fn>`, arity 6. -/
private theorem b19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.returnsUnitPost Captured.program 19
      (Spec.optFnMarkerId "FromZeros" "" 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 20: `FromZeros`, `Option<fn>`, arity 7. -/
private theorem b20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.returnsUnitPost Captured.program 20
      (Spec.optFnMarkerId "FromZeros" "" 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 21: `FromZeros`, `Option<fn>`, arity 8. -/
private theorem b21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.returnsUnitPost Captured.program 21
      (Spec.optFnMarkerId "FromZeros" "" 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 22: `FromZeros`, `Option<fn>`, arity 9. -/
private theorem b22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.returnsUnitPost Captured.program 22
      (Spec.optFnMarkerId "FromZeros" "" 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 23: `FromZeros`, `Option<fn>`, arity 10. -/
private theorem b23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.returnsUnitPost Captured.program 23
      (Spec.optFnMarkerId "FromZeros" "" 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 24: `FromZeros`, `Option<fn>`, arity 11. -/
private theorem b24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.returnsUnitPost Captured.program 24
      (Spec.optFnMarkerId "FromZeros" "" 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 25: `FromZeros`, `Option<fn>`, arity 12. -/
private theorem b25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.returnsUnitPost Captured.program 25
      (Spec.optFnMarkerId "FromZeros" "" 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 26: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 0. -/
private theorem b26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.returnsUnitPost Captured.program 26
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 27: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 1. -/
private theorem b27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.returnsUnitPost Captured.program 27
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 28: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 2. -/
private theorem b28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.returnsUnitPost Captured.program 28
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 29: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 3. -/
private theorem b29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.returnsUnitPost Captured.program 29
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 30: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 4. -/
private theorem b30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.returnsUnitPost Captured.program 30
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 31: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 5. -/
private theorem b31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.returnsUnitPost Captured.program 31
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 32: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 6. -/
private theorem b32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.returnsUnitPost Captured.program 32
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 33: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 7. -/
private theorem b33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.returnsUnitPost Captured.program 33
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 34: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 8. -/
private theorem b34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.returnsUnitPost Captured.program 34
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 35: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 9. -/
private theorem b35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.returnsUnitPost Captured.program 35
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 36: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 10. -/
private theorem b36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.returnsUnitPost Captured.program 36
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 37: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 11. -/
private theorem b37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.returnsUnitPost Captured.program 37
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 38: `FromZeros`, `Option<unsafe extern "C" fn>`, arity 12. -/
private theorem b38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.returnsUnitPost Captured.program 38
      (Spec.optFnMarkerId "FromZeros" "unsafe extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 39: `FromZeros`, `Option<unsafe fn>`, arity 0. -/
private theorem b39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.returnsUnitPost Captured.program 39
      (Spec.optFnMarkerId "FromZeros" "unsafe " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 40: `FromZeros`, `Option<unsafe fn>`, arity 1. -/
private theorem b40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.returnsUnitPost Captured.program 40
      (Spec.optFnMarkerId "FromZeros" "unsafe " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 41: `FromZeros`, `Option<unsafe fn>`, arity 2. -/
private theorem b41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.returnsUnitPost Captured.program 41
      (Spec.optFnMarkerId "FromZeros" "unsafe " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 42: `FromZeros`, `Option<unsafe fn>`, arity 3. -/
private theorem b42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.returnsUnitPost Captured.program 42
      (Spec.optFnMarkerId "FromZeros" "unsafe " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 43: `FromZeros`, `Option<unsafe fn>`, arity 4. -/
private theorem b43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.returnsUnitPost Captured.program 43
      (Spec.optFnMarkerId "FromZeros" "unsafe " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 44: `FromZeros`, `Option<unsafe fn>`, arity 5. -/
private theorem b44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.returnsUnitPost Captured.program 44
      (Spec.optFnMarkerId "FromZeros" "unsafe " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 45: `FromZeros`, `Option<unsafe fn>`, arity 6. -/
private theorem b45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.returnsUnitPost Captured.program 45
      (Spec.optFnMarkerId "FromZeros" "unsafe " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 46: `FromZeros`, `Option<unsafe fn>`, arity 7. -/
private theorem b46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.returnsUnitPost Captured.program 46
      (Spec.optFnMarkerId "FromZeros" "unsafe " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 47: `FromZeros`, `Option<unsafe fn>`, arity 8. -/
private theorem b47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.returnsUnitPost Captured.program 47
      (Spec.optFnMarkerId "FromZeros" "unsafe " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 48: `FromZeros`, `Option<unsafe fn>`, arity 9. -/
private theorem b48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.returnsUnitPost Captured.program 48
      (Spec.optFnMarkerId "FromZeros" "unsafe " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 49: `FromZeros`, `Option<unsafe fn>`, arity 10. -/
private theorem b49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.returnsUnitPost Captured.program 49
      (Spec.optFnMarkerId "FromZeros" "unsafe " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 50: `FromZeros`, `Option<unsafe fn>`, arity 11. -/
private theorem b50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.returnsUnitPost Captured.program 50
      (Spec.optFnMarkerId "FromZeros" "unsafe " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 51: `FromZeros`, `Option<unsafe fn>`, arity 12. -/
private theorem b51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.returnsUnitPost Captured.program 51
      (Spec.optFnMarkerId "FromZeros" "unsafe " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 52: `Immutable`, `Option<extern "C" fn>`, arity 0. -/
private theorem b52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.returnsUnitPost Captured.program 52
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 53: `Immutable`, `Option<extern "C" fn>`, arity 1. -/
private theorem b53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.returnsUnitPost Captured.program 53
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 54: `Immutable`, `Option<extern "C" fn>`, arity 2. -/
private theorem b54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.returnsUnitPost Captured.program 54
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 55: `Immutable`, `Option<extern "C" fn>`, arity 3. -/
private theorem b55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.returnsUnitPost Captured.program 55
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 56: `Immutable`, `Option<extern "C" fn>`, arity 4. -/
private theorem b56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.returnsUnitPost Captured.program 56
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 57: `Immutable`, `Option<extern "C" fn>`, arity 5. -/
private theorem b57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.returnsUnitPost Captured.program 57
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 58: `Immutable`, `Option<extern "C" fn>`, arity 6. -/
private theorem b58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.returnsUnitPost Captured.program 58
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 59: `Immutable`, `Option<extern "C" fn>`, arity 7. -/
private theorem b59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.returnsUnitPost Captured.program 59
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 60: `Immutable`, `Option<extern "C" fn>`, arity 8. -/
private theorem b60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.returnsUnitPost Captured.program 60
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 61: `Immutable`, `Option<extern "C" fn>`, arity 9. -/
private theorem b61 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.returnsUnitPost Captured.program 61
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 62: `Immutable`, `Option<extern "C" fn>`, arity 10. -/
private theorem b62 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.returnsUnitPost Captured.program 62
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 63: `Immutable`, `Option<extern "C" fn>`, arity 11. -/
private theorem b63 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.returnsUnitPost Captured.program 63
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 64: `Immutable`, `Option<extern "C" fn>`, arity 12. -/
private theorem b64 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.returnsUnitPost Captured.program 64
      (Spec.optFnMarkerId "Immutable" "extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 65: `Immutable`, `Option<fn>`, arity 0. -/
private theorem b65 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.returnsUnitPost Captured.program 65
      (Spec.optFnMarkerId "Immutable" "" 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 66: `Immutable`, `Option<fn>`, arity 1. -/
private theorem b66 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.returnsUnitPost Captured.program 66
      (Spec.optFnMarkerId "Immutable" "" 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 67: `Immutable`, `Option<fn>`, arity 2. -/
private theorem b67 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.returnsUnitPost Captured.program 67
      (Spec.optFnMarkerId "Immutable" "" 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 68: `Immutable`, `Option<fn>`, arity 3. -/
private theorem b68 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.returnsUnitPost Captured.program 68
      (Spec.optFnMarkerId "Immutable" "" 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 69: `Immutable`, `Option<fn>`, arity 4. -/
private theorem b69 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.returnsUnitPost Captured.program 69
      (Spec.optFnMarkerId "Immutable" "" 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 70: `Immutable`, `Option<fn>`, arity 5. -/
private theorem b70 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.returnsUnitPost Captured.program 70
      (Spec.optFnMarkerId "Immutable" "" 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 71: `Immutable`, `Option<fn>`, arity 6. -/
private theorem b71 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.returnsUnitPost Captured.program 71
      (Spec.optFnMarkerId "Immutable" "" 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 72: `Immutable`, `Option<fn>`, arity 7. -/
private theorem b72 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.returnsUnitPost Captured.program 72
      (Spec.optFnMarkerId "Immutable" "" 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 73: `Immutable`, `Option<fn>`, arity 8. -/
private theorem b73 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.returnsUnitPost Captured.program 73
      (Spec.optFnMarkerId "Immutable" "" 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 74: `Immutable`, `Option<fn>`, arity 9. -/
private theorem b74 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.returnsUnitPost Captured.program 74
      (Spec.optFnMarkerId "Immutable" "" 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 75: `Immutable`, `Option<fn>`, arity 10. -/
private theorem b75 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.returnsUnitPost Captured.program 75
      (Spec.optFnMarkerId "Immutable" "" 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 76: `Immutable`, `Option<fn>`, arity 11. -/
private theorem b76 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.returnsUnitPost Captured.program 76
      (Spec.optFnMarkerId "Immutable" "" 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 77: `Immutable`, `Option<fn>`, arity 12. -/
private theorem b77 :
    BodyVerified Captured.program 77 Captured.body_77
      (Spec.specs.safety Captured.body_77.identity) ∧
    Spec.returnsUnitPost Captured.program 77
      (Spec.optFnMarkerId "Immutable" "" 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 78: `Immutable`, `Option<unsafe extern "C" fn>`, arity 0. -/
private theorem b78 :
    BodyVerified Captured.program 78 Captured.body_78
      (Spec.specs.safety Captured.body_78.identity) ∧
    Spec.returnsUnitPost Captured.program 78
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 79: `Immutable`, `Option<unsafe extern "C" fn>`, arity 1. -/
private theorem b79 :
    BodyVerified Captured.program 79 Captured.body_79
      (Spec.specs.safety Captured.body_79.identity) ∧
    Spec.returnsUnitPost Captured.program 79
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 80: `Immutable`, `Option<unsafe extern "C" fn>`, arity 2. -/
private theorem b80 :
    BodyVerified Captured.program 80 Captured.body_80
      (Spec.specs.safety Captured.body_80.identity) ∧
    Spec.returnsUnitPost Captured.program 80
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 81: `Immutable`, `Option<unsafe extern "C" fn>`, arity 3. -/
private theorem b81 :
    BodyVerified Captured.program 81 Captured.body_81
      (Spec.specs.safety Captured.body_81.identity) ∧
    Spec.returnsUnitPost Captured.program 81
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 82: `Immutable`, `Option<unsafe extern "C" fn>`, arity 4. -/
private theorem b82 :
    BodyVerified Captured.program 82 Captured.body_82
      (Spec.specs.safety Captured.body_82.identity) ∧
    Spec.returnsUnitPost Captured.program 82
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 83: `Immutable`, `Option<unsafe extern "C" fn>`, arity 5. -/
private theorem b83 :
    BodyVerified Captured.program 83 Captured.body_83
      (Spec.specs.safety Captured.body_83.identity) ∧
    Spec.returnsUnitPost Captured.program 83
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 84: `Immutable`, `Option<unsafe extern "C" fn>`, arity 6. -/
private theorem b84 :
    BodyVerified Captured.program 84 Captured.body_84
      (Spec.specs.safety Captured.body_84.identity) ∧
    Spec.returnsUnitPost Captured.program 84
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 85: `Immutable`, `Option<unsafe extern "C" fn>`, arity 7. -/
private theorem b85 :
    BodyVerified Captured.program 85 Captured.body_85
      (Spec.specs.safety Captured.body_85.identity) ∧
    Spec.returnsUnitPost Captured.program 85
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 86: `Immutable`, `Option<unsafe extern "C" fn>`, arity 8. -/
private theorem b86 :
    BodyVerified Captured.program 86 Captured.body_86
      (Spec.specs.safety Captured.body_86.identity) ∧
    Spec.returnsUnitPost Captured.program 86
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 87: `Immutable`, `Option<unsafe extern "C" fn>`, arity 9. -/
private theorem b87 :
    BodyVerified Captured.program 87 Captured.body_87
      (Spec.specs.safety Captured.body_87.identity) ∧
    Spec.returnsUnitPost Captured.program 87
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 88: `Immutable`, `Option<unsafe extern "C" fn>`, arity 10. -/
private theorem b88 :
    BodyVerified Captured.program 88 Captured.body_88
      (Spec.specs.safety Captured.body_88.identity) ∧
    Spec.returnsUnitPost Captured.program 88
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 89: `Immutable`, `Option<unsafe extern "C" fn>`, arity 11. -/
private theorem b89 :
    BodyVerified Captured.program 89 Captured.body_89
      (Spec.specs.safety Captured.body_89.identity) ∧
    Spec.returnsUnitPost Captured.program 89
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 90: `Immutable`, `Option<unsafe extern "C" fn>`, arity 12. -/
private theorem b90 :
    BodyVerified Captured.program 90 Captured.body_90
      (Spec.specs.safety Captured.body_90.identity) ∧
    Spec.returnsUnitPost Captured.program 90
      (Spec.optFnMarkerId "Immutable" "unsafe extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 91: `Immutable`, `Option<unsafe fn>`, arity 0. -/
private theorem b91 :
    BodyVerified Captured.program 91 Captured.body_91
      (Spec.specs.safety Captured.body_91.identity) ∧
    Spec.returnsUnitPost Captured.program 91
      (Spec.optFnMarkerId "Immutable" "unsafe " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 92: `Immutable`, `Option<unsafe fn>`, arity 1. -/
private theorem b92 :
    BodyVerified Captured.program 92 Captured.body_92
      (Spec.specs.safety Captured.body_92.identity) ∧
    Spec.returnsUnitPost Captured.program 92
      (Spec.optFnMarkerId "Immutable" "unsafe " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 93: `Immutable`, `Option<unsafe fn>`, arity 2. -/
private theorem b93 :
    BodyVerified Captured.program 93 Captured.body_93
      (Spec.specs.safety Captured.body_93.identity) ∧
    Spec.returnsUnitPost Captured.program 93
      (Spec.optFnMarkerId "Immutable" "unsafe " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 94: `Immutable`, `Option<unsafe fn>`, arity 3. -/
private theorem b94 :
    BodyVerified Captured.program 94 Captured.body_94
      (Spec.specs.safety Captured.body_94.identity) ∧
    Spec.returnsUnitPost Captured.program 94
      (Spec.optFnMarkerId "Immutable" "unsafe " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 95: `Immutable`, `Option<unsafe fn>`, arity 4. -/
private theorem b95 :
    BodyVerified Captured.program 95 Captured.body_95
      (Spec.specs.safety Captured.body_95.identity) ∧
    Spec.returnsUnitPost Captured.program 95
      (Spec.optFnMarkerId "Immutable" "unsafe " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 96: `Immutable`, `Option<unsafe fn>`, arity 5. -/
private theorem b96 :
    BodyVerified Captured.program 96 Captured.body_96
      (Spec.specs.safety Captured.body_96.identity) ∧
    Spec.returnsUnitPost Captured.program 96
      (Spec.optFnMarkerId "Immutable" "unsafe " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 97: `Immutable`, `Option<unsafe fn>`, arity 6. -/
private theorem b97 :
    BodyVerified Captured.program 97 Captured.body_97
      (Spec.specs.safety Captured.body_97.identity) ∧
    Spec.returnsUnitPost Captured.program 97
      (Spec.optFnMarkerId "Immutable" "unsafe " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 98: `Immutable`, `Option<unsafe fn>`, arity 7. -/
private theorem b98 :
    BodyVerified Captured.program 98 Captured.body_98
      (Spec.specs.safety Captured.body_98.identity) ∧
    Spec.returnsUnitPost Captured.program 98
      (Spec.optFnMarkerId "Immutable" "unsafe " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 99: `Immutable`, `Option<unsafe fn>`, arity 8. -/
private theorem b99 :
    BodyVerified Captured.program 99 Captured.body_99
      (Spec.specs.safety Captured.body_99.identity) ∧
    Spec.returnsUnitPost Captured.program 99
      (Spec.optFnMarkerId "Immutable" "unsafe " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 100: `Immutable`, `Option<unsafe fn>`, arity 9. -/
private theorem b100 :
    BodyVerified Captured.program 100 Captured.body_100
      (Spec.specs.safety Captured.body_100.identity) ∧
    Spec.returnsUnitPost Captured.program 100
      (Spec.optFnMarkerId "Immutable" "unsafe " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 101: `Immutable`, `Option<unsafe fn>`, arity 10. -/
private theorem b101 :
    BodyVerified Captured.program 101 Captured.body_101
      (Spec.specs.safety Captured.body_101.identity) ∧
    Spec.returnsUnitPost Captured.program 101
      (Spec.optFnMarkerId "Immutable" "unsafe " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 102: `Immutable`, `Option<unsafe fn>`, arity 11. -/
private theorem b102 :
    BodyVerified Captured.program 102 Captured.body_102
      (Spec.specs.safety Captured.body_102.identity) ∧
    Spec.returnsUnitPost Captured.program 102
      (Spec.optFnMarkerId "Immutable" "unsafe " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 103: `Immutable`, `Option<unsafe fn>`, arity 12. -/
private theorem b103 :
    BodyVerified Captured.program 103 Captured.body_103
      (Spec.specs.safety Captured.body_103.identity) ∧
    Spec.returnsUnitPost Captured.program 103
      (Spec.optFnMarkerId "Immutable" "unsafe " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 104: `TryFromBytes`, `Option<extern "C" fn>`, arity 0. -/
private theorem b104 :
    BodyVerified Captured.program 104 Captured.body_104
      (Spec.specs.safety Captured.body_104.identity) ∧
    Spec.returnsUnitPost Captured.program 104
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 105: `TryFromBytes`, `Option<extern "C" fn>`, arity 1. -/
private theorem b105 :
    BodyVerified Captured.program 105 Captured.body_105
      (Spec.specs.safety Captured.body_105.identity) ∧
    Spec.returnsUnitPost Captured.program 105
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 106: `TryFromBytes`, `Option<extern "C" fn>`, arity 2. -/
private theorem b106 :
    BodyVerified Captured.program 106 Captured.body_106
      (Spec.specs.safety Captured.body_106.identity) ∧
    Spec.returnsUnitPost Captured.program 106
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 107: `TryFromBytes`, `Option<extern "C" fn>`, arity 3. -/
private theorem b107 :
    BodyVerified Captured.program 107 Captured.body_107
      (Spec.specs.safety Captured.body_107.identity) ∧
    Spec.returnsUnitPost Captured.program 107
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 108: `TryFromBytes`, `Option<extern "C" fn>`, arity 4. -/
private theorem b108 :
    BodyVerified Captured.program 108 Captured.body_108
      (Spec.specs.safety Captured.body_108.identity) ∧
    Spec.returnsUnitPost Captured.program 108
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 109: `TryFromBytes`, `Option<extern "C" fn>`, arity 5. -/
private theorem b109 :
    BodyVerified Captured.program 109 Captured.body_109
      (Spec.specs.safety Captured.body_109.identity) ∧
    Spec.returnsUnitPost Captured.program 109
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 110: `TryFromBytes`, `Option<extern "C" fn>`, arity 6. -/
private theorem b110 :
    BodyVerified Captured.program 110 Captured.body_110
      (Spec.specs.safety Captured.body_110.identity) ∧
    Spec.returnsUnitPost Captured.program 110
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 111: `TryFromBytes`, `Option<extern "C" fn>`, arity 7. -/
private theorem b111 :
    BodyVerified Captured.program 111 Captured.body_111
      (Spec.specs.safety Captured.body_111.identity) ∧
    Spec.returnsUnitPost Captured.program 111
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 112: `TryFromBytes`, `Option<extern "C" fn>`, arity 8. -/
private theorem b112 :
    BodyVerified Captured.program 112 Captured.body_112
      (Spec.specs.safety Captured.body_112.identity) ∧
    Spec.returnsUnitPost Captured.program 112
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 113: `TryFromBytes`, `Option<extern "C" fn>`, arity 9. -/
private theorem b113 :
    BodyVerified Captured.program 113 Captured.body_113
      (Spec.specs.safety Captured.body_113.identity) ∧
    Spec.returnsUnitPost Captured.program 113
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 114: `TryFromBytes`, `Option<extern "C" fn>`, arity 10. -/
private theorem b114 :
    BodyVerified Captured.program 114 Captured.body_114
      (Spec.specs.safety Captured.body_114.identity) ∧
    Spec.returnsUnitPost Captured.program 114
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 115: `TryFromBytes`, `Option<extern "C" fn>`, arity 11. -/
private theorem b115 :
    BodyVerified Captured.program 115 Captured.body_115
      (Spec.specs.safety Captured.body_115.identity) ∧
    Spec.returnsUnitPost Captured.program 115
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 116: `TryFromBytes`, `Option<extern "C" fn>`, arity 12. -/
private theorem b116 :
    BodyVerified Captured.program 116 Captured.body_116
      (Spec.specs.safety Captured.body_116.identity) ∧
    Spec.returnsUnitPost Captured.program 116
      (Spec.optFnMarkerId "TryFromBytes" "extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 117: `TryFromBytes`, `Option<fn>`, arity 0. -/
private theorem b117 :
    BodyVerified Captured.program 117 Captured.body_117
      (Spec.specs.safety Captured.body_117.identity) ∧
    Spec.returnsUnitPost Captured.program 117
      (Spec.optFnMarkerId "TryFromBytes" "" 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 118: `TryFromBytes`, `Option<fn>`, arity 1. -/
private theorem b118 :
    BodyVerified Captured.program 118 Captured.body_118
      (Spec.specs.safety Captured.body_118.identity) ∧
    Spec.returnsUnitPost Captured.program 118
      (Spec.optFnMarkerId "TryFromBytes" "" 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 119: `TryFromBytes`, `Option<fn>`, arity 2. -/
private theorem b119 :
    BodyVerified Captured.program 119 Captured.body_119
      (Spec.specs.safety Captured.body_119.identity) ∧
    Spec.returnsUnitPost Captured.program 119
      (Spec.optFnMarkerId "TryFromBytes" "" 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 120: `TryFromBytes`, `Option<fn>`, arity 3. -/
private theorem b120 :
    BodyVerified Captured.program 120 Captured.body_120
      (Spec.specs.safety Captured.body_120.identity) ∧
    Spec.returnsUnitPost Captured.program 120
      (Spec.optFnMarkerId "TryFromBytes" "" 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 121: `TryFromBytes`, `Option<fn>`, arity 4. -/
private theorem b121 :
    BodyVerified Captured.program 121 Captured.body_121
      (Spec.specs.safety Captured.body_121.identity) ∧
    Spec.returnsUnitPost Captured.program 121
      (Spec.optFnMarkerId "TryFromBytes" "" 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 122: `TryFromBytes`, `Option<fn>`, arity 5. -/
private theorem b122 :
    BodyVerified Captured.program 122 Captured.body_122
      (Spec.specs.safety Captured.body_122.identity) ∧
    Spec.returnsUnitPost Captured.program 122
      (Spec.optFnMarkerId "TryFromBytes" "" 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 123: `TryFromBytes`, `Option<fn>`, arity 6. -/
private theorem b123 :
    BodyVerified Captured.program 123 Captured.body_123
      (Spec.specs.safety Captured.body_123.identity) ∧
    Spec.returnsUnitPost Captured.program 123
      (Spec.optFnMarkerId "TryFromBytes" "" 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 124: `TryFromBytes`, `Option<fn>`, arity 7. -/
private theorem b124 :
    BodyVerified Captured.program 124 Captured.body_124
      (Spec.specs.safety Captured.body_124.identity) ∧
    Spec.returnsUnitPost Captured.program 124
      (Spec.optFnMarkerId "TryFromBytes" "" 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 125: `TryFromBytes`, `Option<fn>`, arity 8. -/
private theorem b125 :
    BodyVerified Captured.program 125 Captured.body_125
      (Spec.specs.safety Captured.body_125.identity) ∧
    Spec.returnsUnitPost Captured.program 125
      (Spec.optFnMarkerId "TryFromBytes" "" 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 126: `TryFromBytes`, `Option<fn>`, arity 9. -/
private theorem b126 :
    BodyVerified Captured.program 126 Captured.body_126
      (Spec.specs.safety Captured.body_126.identity) ∧
    Spec.returnsUnitPost Captured.program 126
      (Spec.optFnMarkerId "TryFromBytes" "" 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 127: `TryFromBytes`, `Option<fn>`, arity 10. -/
private theorem b127 :
    BodyVerified Captured.program 127 Captured.body_127
      (Spec.specs.safety Captured.body_127.identity) ∧
    Spec.returnsUnitPost Captured.program 127
      (Spec.optFnMarkerId "TryFromBytes" "" 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 128: `TryFromBytes`, `Option<fn>`, arity 11. -/
private theorem b128 :
    BodyVerified Captured.program 128 Captured.body_128
      (Spec.specs.safety Captured.body_128.identity) ∧
    Spec.returnsUnitPost Captured.program 128
      (Spec.optFnMarkerId "TryFromBytes" "" 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 129: `TryFromBytes`, `Option<fn>`, arity 12. -/
private theorem b129 :
    BodyVerified Captured.program 129 Captured.body_129
      (Spec.specs.safety Captured.body_129.identity) ∧
    Spec.returnsUnitPost Captured.program 129
      (Spec.optFnMarkerId "TryFromBytes" "" 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 130: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 0. -/
private theorem b130 :
    BodyVerified Captured.program 130 Captured.body_130
      (Spec.specs.safety Captured.body_130.identity) ∧
    Spec.returnsUnitPost Captured.program 130
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 131: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 1. -/
private theorem b131 :
    BodyVerified Captured.program 131 Captured.body_131
      (Spec.specs.safety Captured.body_131.identity) ∧
    Spec.returnsUnitPost Captured.program 131
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 132: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 2. -/
private theorem b132 :
    BodyVerified Captured.program 132 Captured.body_132
      (Spec.specs.safety Captured.body_132.identity) ∧
    Spec.returnsUnitPost Captured.program 132
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 133: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 3. -/
private theorem b133 :
    BodyVerified Captured.program 133 Captured.body_133
      (Spec.specs.safety Captured.body_133.identity) ∧
    Spec.returnsUnitPost Captured.program 133
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 134: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 4. -/
private theorem b134 :
    BodyVerified Captured.program 134 Captured.body_134
      (Spec.specs.safety Captured.body_134.identity) ∧
    Spec.returnsUnitPost Captured.program 134
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 135: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 5. -/
private theorem b135 :
    BodyVerified Captured.program 135 Captured.body_135
      (Spec.specs.safety Captured.body_135.identity) ∧
    Spec.returnsUnitPost Captured.program 135
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 136: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 6. -/
private theorem b136 :
    BodyVerified Captured.program 136 Captured.body_136
      (Spec.specs.safety Captured.body_136.identity) ∧
    Spec.returnsUnitPost Captured.program 136
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 137: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 7. -/
private theorem b137 :
    BodyVerified Captured.program 137 Captured.body_137
      (Spec.specs.safety Captured.body_137.identity) ∧
    Spec.returnsUnitPost Captured.program 137
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 138: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 8. -/
private theorem b138 :
    BodyVerified Captured.program 138 Captured.body_138
      (Spec.specs.safety Captured.body_138.identity) ∧
    Spec.returnsUnitPost Captured.program 138
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 139: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 9. -/
private theorem b139 :
    BodyVerified Captured.program 139 Captured.body_139
      (Spec.specs.safety Captured.body_139.identity) ∧
    Spec.returnsUnitPost Captured.program 139
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 140: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 10. -/
private theorem b140 :
    BodyVerified Captured.program 140 Captured.body_140
      (Spec.specs.safety Captured.body_140.identity) ∧
    Spec.returnsUnitPost Captured.program 140
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 141: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 11. -/
private theorem b141 :
    BodyVerified Captured.program 141 Captured.body_141
      (Spec.specs.safety Captured.body_141.identity) ∧
    Spec.returnsUnitPost Captured.program 141
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 142: `TryFromBytes`, `Option<unsafe extern "C" fn>`, arity 12. -/
private theorem b142 :
    BodyVerified Captured.program 142 Captured.body_142
      (Spec.specs.safety Captured.body_142.identity) ∧
    Spec.returnsUnitPost Captured.program 142
      (Spec.optFnMarkerId "TryFromBytes" "unsafe extern \"C\" " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 143: `TryFromBytes`, `Option<unsafe fn>`, arity 0. -/
private theorem b143 :
    BodyVerified Captured.program 143 Captured.body_143
      (Spec.specs.safety Captured.body_143.identity) ∧
    Spec.returnsUnitPost Captured.program 143
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 0) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 144: `TryFromBytes`, `Option<unsafe fn>`, arity 1. -/
private theorem b144 :
    BodyVerified Captured.program 144 Captured.body_144
      (Spec.specs.safety Captured.body_144.identity) ∧
    Spec.returnsUnitPost Captured.program 144
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 1) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 145: `TryFromBytes`, `Option<unsafe fn>`, arity 2. -/
private theorem b145 :
    BodyVerified Captured.program 145 Captured.body_145
      (Spec.specs.safety Captured.body_145.identity) ∧
    Spec.returnsUnitPost Captured.program 145
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 2) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 146: `TryFromBytes`, `Option<unsafe fn>`, arity 3. -/
private theorem b146 :
    BodyVerified Captured.program 146 Captured.body_146
      (Spec.specs.safety Captured.body_146.identity) ∧
    Spec.returnsUnitPost Captured.program 146
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 3) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 147: `TryFromBytes`, `Option<unsafe fn>`, arity 4. -/
private theorem b147 :
    BodyVerified Captured.program 147 Captured.body_147
      (Spec.specs.safety Captured.body_147.identity) ∧
    Spec.returnsUnitPost Captured.program 147
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 4) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 148: `TryFromBytes`, `Option<unsafe fn>`, arity 5. -/
private theorem b148 :
    BodyVerified Captured.program 148 Captured.body_148
      (Spec.specs.safety Captured.body_148.identity) ∧
    Spec.returnsUnitPost Captured.program 148
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 5) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 149: `TryFromBytes`, `Option<unsafe fn>`, arity 6. -/
private theorem b149 :
    BodyVerified Captured.program 149 Captured.body_149
      (Spec.specs.safety Captured.body_149.identity) ∧
    Spec.returnsUnitPost Captured.program 149
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 6) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 150: `TryFromBytes`, `Option<unsafe fn>`, arity 7. -/
private theorem b150 :
    BodyVerified Captured.program 150 Captured.body_150
      (Spec.specs.safety Captured.body_150.identity) ∧
    Spec.returnsUnitPost Captured.program 150
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 7) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 151: `TryFromBytes`, `Option<unsafe fn>`, arity 8. -/
private theorem b151 :
    BodyVerified Captured.program 151 Captured.body_151
      (Spec.specs.safety Captured.body_151.identity) ∧
    Spec.returnsUnitPost Captured.program 151
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 8) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 152: `TryFromBytes`, `Option<unsafe fn>`, arity 9. -/
private theorem b152 :
    BodyVerified Captured.program 152 Captured.body_152
      (Spec.specs.safety Captured.body_152.identity) ∧
    Spec.returnsUnitPost Captured.program 152
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 9) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 153: `TryFromBytes`, `Option<unsafe fn>`, arity 10. -/
private theorem b153 :
    BodyVerified Captured.program 153 Captured.body_153
      (Spec.specs.safety Captured.body_153.identity) ∧
    Spec.returnsUnitPost Captured.program 153
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 10) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 154: `TryFromBytes`, `Option<unsafe fn>`, arity 11. -/
private theorem b154 :
    BodyVerified Captured.program 154 Captured.body_154
      (Spec.specs.safety Captured.body_154.identity) ∧
    Spec.returnsUnitPost Captured.program 154
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 11) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 155: `TryFromBytes`, `Option<unsafe fn>`, arity 12. -/
private theorem b155 :
    BodyVerified Captured.program 155 Captured.body_155
      (Spec.specs.safety Captured.body_155.identity) ∧
    Spec.returnsUnitPost Captured.program 155
      (Spec.optFnMarkerId "TryFromBytes" "unsafe " 12) :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · have hAll : BodiesVerified Captured.program Spec.specs 0
        Captured.program.bodies :=
      ⟨b0.1, b1.1, b2.1, b3.1, b4.1, b5.1, b6.1, b7.1, b8.1, b9.1, b10.1,
       b11.1, b12.1, b13.1, b14.1, b15.1, b16.1, b17.1, b18.1, b19.1, b20.1,
       b21.1, b22.1, b23.1, b24.1, b25.1, b26.1, b27.1, b28.1, b29.1, b30.1,
       b31.1, b32.1, b33.1, b34.1, b35.1, b36.1, b37.1, b38.1, b39.1, b40.1,
       b41.1, b42.1, b43.1, b44.1, b45.1, b46.1, b47.1, b48.1, b49.1, b50.1,
       b51.1, b52.1, b53.1, b54.1, b55.1, b56.1, b57.1, b58.1, b59.1, b60.1,
       b61.1, b62.1, b63.1, b64.1, b65.1, b66.1, b67.1, b68.1, b69.1, b70.1,
       b71.1, b72.1, b73.1, b74.1, b75.1, b76.1, b77.1, b78.1, b79.1, b80.1,
       b81.1, b82.1, b83.1, b84.1, b85.1, b86.1, b87.1, b88.1, b89.1, b90.1,
       b91.1, b92.1, b93.1, b94.1, b95.1, b96.1, b97.1, b98.1, b99.1, b100.1,
       b101.1, b102.1, b103.1, b104.1, b105.1, b106.1, b107.1, b108.1, b109.1,
       b110.1, b111.1, b112.1, b113.1, b114.1, b115.1, b116.1, b117.1, b118.1,
       b119.1, b120.1, b121.1, b122.1, b123.1, b124.1, b125.1, b126.1, b127.1,
       b128.1, b129.1, b130.1, b131.1, b132.1, b133.1, b134.1, b135.1, b136.1,
       b137.1, b138.1, b139.1, b140.1, b141.1, b142.1, b143.1, b144.1, b145.1,
       b146.1, b147.1, b148.1, b149.1, b150.1, b151.1, b152.1, b153.1, b154.1,
       b155.1, True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨b0.2, b1.2, b2.2, b3.2, b4.2, b5.2, b6.2, b7.2, b8.2, b9.2, b10.2,
        b11.2, b12.2, trivial⟩
    · exact ⟨b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2,
        b22.2, b23.2, b24.2, b25.2, trivial⟩
    · exact ⟨b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2,
        b35.2, b36.2, b37.2, b38.2, trivial⟩
    · exact ⟨b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2,
        b48.2, b49.2, b50.2, b51.2, trivial⟩
    · exact ⟨b52.2, b53.2, b54.2, b55.2, b56.2, b57.2, b58.2, b59.2, b60.2,
        b61.2, b62.2, b63.2, b64.2, trivial⟩
    · exact ⟨b65.2, b66.2, b67.2, b68.2, b69.2, b70.2, b71.2, b72.2, b73.2,
        b74.2, b75.2, b76.2, b77.2, trivial⟩
    · exact ⟨b78.2, b79.2, b80.2, b81.2, b82.2, b83.2, b84.2, b85.2, b86.2,
        b87.2, b88.2, b89.2, b90.2, trivial⟩
    · exact ⟨b91.2, b92.2, b93.2, b94.2, b95.2, b96.2, b97.2, b98.2, b99.2,
        b100.2, b101.2, b102.2, b103.2, trivial⟩
    · exact ⟨b104.2, b105.2, b106.2, b107.2, b108.2, b109.2, b110.2, b111.2,
        b112.2, b113.2, b114.2, b115.2, b116.2, trivial⟩
    · exact ⟨b117.2, b118.2, b119.2, b120.2, b121.2, b122.2, b123.2, b124.2,
        b125.2, b126.2, b127.2, b128.2, b129.2, trivial⟩
    · exact ⟨b130.2, b131.2, b132.2, b133.2, b134.2, b135.2, b136.2, b137.2,
        b138.2, b139.2, b140.2, b141.2, b142.2, trivial⟩
    · exact ⟨b143.2, b144.2, b145.2, b146.2, b147.2, b148.2, b149.2, b150.2,
        b151.2, b152.2, b153.2, b154.2, b155.2, trivial⟩

end Proof
