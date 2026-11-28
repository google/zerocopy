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

-- Comparing the witness identities by `rfl` reduces strings of up to about
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

/-! ## Witnesses (Bodies 0-59) -/

/-- Body 0: `FromBytes` for `Cell<T>`, with `T = u16`. -/
private theorem b0 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.returnsUnitPost Captured.program 0
      (Spec.wrapperWitnessId "FromBytes" "core::cell::Cell" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 1: `FromBytes` for `UnsafeCell<T>`, with `T = i64`. -/
private theorem b1 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.returnsUnitPost Captured.program 1
      (Spec.wrapperWitnessId "FromBytes" "core::cell::UnsafeCell" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 2: `FromBytes` for `ManuallyDrop<T>`, with `T = [u8]`. -/
private theorem b2 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.returnsUnitPost Captured.program 2
      (Spec.wrapperWitnessId
        "FromBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 3: `FromBytes` for `Wrapping<T>`, with `T = u32`. -/
private theorem b3 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.returnsUnitPost Captured.program 3
      (Spec.wrapperWitnessId
        "FromBytes" "core::num::wrapping::Wrapping" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 4: `FromZeros` for `Cell<T>`, with `T = u16`. -/
private theorem b4 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.returnsUnitPost Captured.program 4
      (Spec.wrapperWitnessId "FromZeros" "core::cell::Cell" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 5: `FromZeros` for `UnsafeCell<T>`, with `T = i64`. -/
private theorem b5 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.returnsUnitPost Captured.program 5
      (Spec.wrapperWitnessId "FromZeros" "core::cell::UnsafeCell" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 6: `FromZeros` for `ManuallyDrop<T>`, with `T = [u8]`. -/
private theorem b6 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.returnsUnitPost Captured.program 6
      (Spec.wrapperWitnessId
        "FromZeros" "core::mem::manually_drop::ManuallyDrop" "[u8]") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 7: `FromZeros` for `Wrapping<T>`, with `T = u32`. -/
private theorem b7 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.returnsUnitPost Captured.program 7
      (Spec.wrapperWitnessId
        "FromZeros" "core::num::wrapping::Wrapping" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 8: `IntoBytes` for `Cell<T>`, with `T = u16`. -/
private theorem b8 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.returnsUnitPost Captured.program 8
      (Spec.wrapperWitnessId "IntoBytes" "core::cell::Cell" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 9: `IntoBytes` for `UnsafeCell<T>`, with `T = i64`. -/
private theorem b9 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.returnsUnitPost Captured.program 9
      (Spec.wrapperWitnessId "IntoBytes" "core::cell::UnsafeCell" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 10: `IntoBytes` for `ManuallyDrop<T>`, with `T = [u8]`. -/
private theorem b10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.returnsUnitPost Captured.program 10
      (Spec.wrapperWitnessId
        "IntoBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 11: `IntoBytes` for `Wrapping<T>`, with `T = u32`. -/
private theorem b11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.returnsUnitPost Captured.program 11
      (Spec.wrapperWitnessId
        "IntoBytes" "core::num::wrapping::Wrapping" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 12: `TryFromBytes` for `Cell<T>`, with `T = u16`. -/
private theorem b12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.returnsUnitPost Captured.program 12
      (Spec.wrapperWitnessId "TryFromBytes" "core::cell::Cell" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 13: `TryFromBytes` for `ManuallyDrop<T>`, with `T = [u8]`. -/
private theorem b13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.returnsUnitPost Captured.program 13
      (Spec.wrapperWitnessId
        "TryFromBytes" "core::mem::manually_drop::ManuallyDrop" "[u8]") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 14: `TryFromBytes` for `Wrapping<T>`, with `T = u32`. -/
private theorem b14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.returnsUnitPost Captured.program 14
      (Spec.wrapperWitnessId
        "TryFromBytes" "core::num::wrapping::Wrapping" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 15: `FromBytes` for `Atomic<i16>`. -/
private theorem b15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.returnsUnitPost Captured.program 15
      (Spec.atomicWitnessId "16" "FromBytes" "i16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 16: `FromBytes` for `Atomic<u16>`. -/
private theorem b16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.returnsUnitPost Captured.program 16
      (Spec.atomicWitnessId "16" "FromBytes" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 17: `FromZeros` for `Atomic<i16>`. -/
private theorem b17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.returnsUnitPost Captured.program 17
      (Spec.atomicWitnessId "16" "FromZeros" "i16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 18: `FromZeros` for `Atomic<u16>`. -/
private theorem b18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.returnsUnitPost Captured.program 18
      (Spec.atomicWitnessId "16" "FromZeros" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 19: `IntoBytes` for `Atomic<i16>`. -/
private theorem b19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.returnsUnitPost Captured.program 19
      (Spec.atomicWitnessId "16" "IntoBytes" "i16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 20: `IntoBytes` for `Atomic<u16>`. -/
private theorem b20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.returnsUnitPost Captured.program 20
      (Spec.atomicWitnessId "16" "IntoBytes" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 21: `TryFromBytes` for `Atomic<i16>`. -/
private theorem b21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.returnsUnitPost Captured.program 21
      (Spec.atomicWitnessId "16" "TryFromBytes" "i16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 22: `TryFromBytes` for `Atomic<u16>`. -/
private theorem b22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.returnsUnitPost Captured.program 22
      (Spec.atomicWitnessId "16" "TryFromBytes" "u16") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 23: `FromBytes` for `Atomic<i32>`. -/
private theorem b23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.returnsUnitPost Captured.program 23
      (Spec.atomicWitnessId "32" "FromBytes" "i32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 24: `FromBytes` for `Atomic<u32>`. -/
private theorem b24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.returnsUnitPost Captured.program 24
      (Spec.atomicWitnessId "32" "FromBytes" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 25: `FromZeros` for `Atomic<i32>`. -/
private theorem b25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.returnsUnitPost Captured.program 25
      (Spec.atomicWitnessId "32" "FromZeros" "i32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 26: `FromZeros` for `Atomic<u32>`. -/
private theorem b26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.returnsUnitPost Captured.program 26
      (Spec.atomicWitnessId "32" "FromZeros" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 27: `IntoBytes` for `Atomic<i32>`. -/
private theorem b27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.returnsUnitPost Captured.program 27
      (Spec.atomicWitnessId "32" "IntoBytes" "i32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 28: `IntoBytes` for `Atomic<u32>`. -/
private theorem b28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.returnsUnitPost Captured.program 28
      (Spec.atomicWitnessId "32" "IntoBytes" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 29: `TryFromBytes` for `Atomic<i32>`. -/
private theorem b29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.returnsUnitPost Captured.program 29
      (Spec.atomicWitnessId "32" "TryFromBytes" "i32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 30: `TryFromBytes` for `Atomic<u32>`. -/
private theorem b30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.returnsUnitPost Captured.program 30
      (Spec.atomicWitnessId "32" "TryFromBytes" "u32") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 31: `FromBytes` for `Atomic<i64>`. -/
private theorem b31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.returnsUnitPost Captured.program 31
      (Spec.atomicWitnessId "64" "FromBytes" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 32: `FromBytes` for `Atomic<u64>`. -/
private theorem b32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.returnsUnitPost Captured.program 32
      (Spec.atomicWitnessId "64" "FromBytes" "u64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 33: `FromZeros` for `Atomic<i64>`. -/
private theorem b33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.returnsUnitPost Captured.program 33
      (Spec.atomicWitnessId "64" "FromZeros" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 34: `FromZeros` for `Atomic<u64>`. -/
private theorem b34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.returnsUnitPost Captured.program 34
      (Spec.atomicWitnessId "64" "FromZeros" "u64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 35: `IntoBytes` for `Atomic<i64>`. -/
private theorem b35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.returnsUnitPost Captured.program 35
      (Spec.atomicWitnessId "64" "IntoBytes" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 36: `IntoBytes` for `Atomic<u64>`. -/
private theorem b36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.returnsUnitPost Captured.program 36
      (Spec.atomicWitnessId "64" "IntoBytes" "u64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 37: `TryFromBytes` for `Atomic<i64>`. -/
private theorem b37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.returnsUnitPost Captured.program 37
      (Spec.atomicWitnessId "64" "TryFromBytes" "i64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 38: `TryFromBytes` for `Atomic<u64>`. -/
private theorem b38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.returnsUnitPost Captured.program 38
      (Spec.atomicWitnessId "64" "TryFromBytes" "u64") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 39: `FromBytes` for `Atomic<i8>`. -/
private theorem b39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.returnsUnitPost Captured.program 39
      (Spec.atomicWitnessId "8" "FromBytes" "i8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 40: `FromBytes` for `Atomic<u8>`. -/
private theorem b40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.returnsUnitPost Captured.program 40
      (Spec.atomicWitnessId "8" "FromBytes" "u8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 41: `FromZeros` for `Atomic<bool>`. -/
private theorem b41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.returnsUnitPost Captured.program 41
      (Spec.atomicWitnessId "8" "FromZeros" "bool") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 42: `FromZeros` for `Atomic<i8>`. -/
private theorem b42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.returnsUnitPost Captured.program 42
      (Spec.atomicWitnessId "8" "FromZeros" "i8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 43: `FromZeros` for `Atomic<u8>`. -/
private theorem b43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.returnsUnitPost Captured.program 43
      (Spec.atomicWitnessId "8" "FromZeros" "u8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 44: `IntoBytes` for `Atomic<bool>`. -/
private theorem b44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.returnsUnitPost Captured.program 44
      (Spec.atomicWitnessId "8" "IntoBytes" "bool") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 45: `IntoBytes` for `Atomic<i8>`. -/
private theorem b45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.returnsUnitPost Captured.program 45
      (Spec.atomicWitnessId "8" "IntoBytes" "i8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 46: `IntoBytes` for `Atomic<u8>`. -/
private theorem b46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.returnsUnitPost Captured.program 46
      (Spec.atomicWitnessId "8" "IntoBytes" "u8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 47: `TryFromBytes` for `Atomic<bool>`. -/
private theorem b47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.returnsUnitPost Captured.program 47
      (Spec.atomicWitnessId "8" "TryFromBytes" "bool") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 48: `TryFromBytes` for `Atomic<i8>`. -/
private theorem b48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.returnsUnitPost Captured.program 48
      (Spec.atomicWitnessId "8" "TryFromBytes" "i8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 49: `TryFromBytes` for `Atomic<u8>`. -/
private theorem b49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.returnsUnitPost Captured.program 49
      (Spec.atomicWitnessId "8" "TryFromBytes" "u8") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 50: `FromBytes` for `Atomic<isize>`. -/
private theorem b50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.returnsUnitPost Captured.program 50
      (Spec.atomicWitnessId "ptr" "FromBytes" "isize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 51: `FromBytes` for `Atomic<usize>`. -/
private theorem b51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.returnsUnitPost Captured.program 51
      (Spec.atomicWitnessId "ptr" "FromBytes" "usize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 52: `FromZeros` for `AtomicPtr<T>`, with `T = u8`. -/
private theorem b52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.returnsUnitPost Captured.program 52
      (Spec.atomicPtrWitnessId "FromZeros") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 53: `FromZeros` for `Atomic<isize>`. -/
private theorem b53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.returnsUnitPost Captured.program 53
      (Spec.atomicWitnessId "ptr" "FromZeros" "isize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 54: `FromZeros` for `Atomic<usize>`. -/
private theorem b54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.returnsUnitPost Captured.program 54
      (Spec.atomicWitnessId "ptr" "FromZeros" "usize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 55: `IntoBytes` for `Atomic<isize>`. -/
private theorem b55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.returnsUnitPost Captured.program 55
      (Spec.atomicWitnessId "ptr" "IntoBytes" "isize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 56: `IntoBytes` for `Atomic<usize>`. -/
private theorem b56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.returnsUnitPost Captured.program 56
      (Spec.atomicWitnessId "ptr" "IntoBytes" "usize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 57: `TryFromBytes` for `AtomicPtr<T>`, with `T = u8`. -/
private theorem b57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.returnsUnitPost Captured.program 57
      (Spec.atomicPtrWitnessId "TryFromBytes") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 58: `TryFromBytes` for `Atomic<isize>`. -/
private theorem b58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.returnsUnitPost Captured.program 58
      (Spec.atomicWitnessId "ptr" "TryFromBytes" "isize") :=
  unit0_verified rfl rfl rfl rfl rfl rfl rfl

/-- Body 59: `TryFromBytes` for `Atomic<usize>`. -/
private theorem b59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.returnsUnitPost Captured.program 59
      (Spec.atomicWitnessId "ptr" "TryFromBytes" "usize") :=
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
       b51.1, b52.1, b53.1, b54.1, b55.1, b56.1, b57.1, b58.1, b59.1,
       True.intro⟩
    intro defId body found
    have hSub := bodiesVerified_getElem hAll defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨rfl, ?_⟩
    exact ⟨b0.2, b1.2, b2.2, b3.2, b4.2, b5.2, b6.2, b7.2, b8.2, b9.2, b10.2,
        b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2,
        b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2,
        b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2,
        b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2, b48.2, b49.2, b50.2,
        b51.2, b52.2, b53.2, b54.2, b55.2, b56.2, b57.2, b58.2, b59.2, trivial⟩

end Proof
