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
import Anneal.InitLemmas

set_option maxRecDepth 16384

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Part 1: Selected MIR Sealing-Marker Verification -/

private theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    Spec.ReturnsTotal Captured.program defId args ret := by
  let ⟨fuel', h_execState⟩ := executes_iff_wpState.mp (run_executes h_runs)
  have h_execProg :
      execProg (entryProgForBody Captured.program defId) fuel' { args := args }
        (fun outcome => outcome = .returned ⟨ret, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody h_body h_adm h_args]
    exact (execOutcomeState_entryProg_iff h_body
      (isSingleFrame0_mkState 0 0 _)).mpr h_execState
  have h_all := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_execProg)
  exact ⟨h_all.2.2.2 _ rfl, h_all.2.2.1, h_all.2.1⟩

private theorem marker_safe_and_at {defId : DefId} {body : Body}
    {identity : String}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_id : body.identity = identity)
    (h_safe : body.isUnsafe = false)
    (h_argc : body.argumentCount = 0)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_args : ValidEntryArgs body [])
    (h_runs : Runs body 2 [] .unit)
    (h_step1 : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 0, [.immediate none], none, none, none⟩],
           callerMem := ⟨[]⟩, mem := mem } =
      .step
        { frames := [⟨defId, 0, 1, [.immediate (some .unit)], none, none, none⟩],
           callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames := [⟨defId, 0, 1, [.immediate (some .unit)], none, none, none⟩],
           callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨.unit, ⟨[]⟩⟩)) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.UnitMarkerAt Captured.program defId identity := by
  refine ⟨?_, ⟨body, h_body, h_id, h_safe, h_argc,
    total_of_runs h_body h_adm h_args h_runs, fun mem =>
      ⟨{ frames := [⟨defId, 0, 1, [.immediate (some .unit)], none, none, none⟩],
          callerMem := ⟨[]⟩, mem := mem },
       ⟨0, rfl, h_step1 mem⟩, rfl, ⟨0, rfl, h_step2 mem⟩⟩⟩⟩
  refine bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_)
  have hMatch : checkArgsMatch args [] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
  subst hNil
  exact (run_initial_success h_runs).1

private theorem string_mk_eq :
    ∀ {b1 b2 : ByteArray} {h1 : ByteArray.IsValidUTF8 b1}
      {h2 : ByteArray.IsValidUTF8 b2},
      b1 = b2 → (⟨b1, h1⟩ : String) = ⟨b2, h2⟩
  | _, _, _, _, rfl => rfl

private theorem stringAppend_ofList (a b : List Char) :
    stringAppend (String.ofList a) (String.ofList b) =
      String.ofList (a ++ b) := by
  refine string_mk_eq ?_
  change (List.toByteArray (a.flatMap String.utf8EncodeChar)).append
      (List.toByteArray (b.flatMap String.utf8EncodeChar)) =
    List.toByteArray ((a ++ b).flatMap String.utf8EncodeChar)
  rw [@List.flatMap_append _ _ a b String.utf8EncodeChar]
  exact Eq.symm (@List.toByteArray_append'
    (a.flatMap String.utf8EncodeChar) (b.flatMap String.utf8EncodeChar))

private def idAt : Nat → List String → String
  | _, [] => ""
  | 0, s :: _ => s
  | n + 1, _ :: rest => idAt n rest

private theorem m00 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.UnitMarkerAt Captured.program 0
      (idAt 0 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_0, Captured.Shard_000.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m01 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.UnitMarkerAt Captured.program 1
      (idAt 1 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_1, Captured.Shard_000.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m02 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.UnitMarkerAt Captured.program 2
      (idAt 2 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_2, Captured.Shard_000.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m03 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.UnitMarkerAt Captured.program 3
      (idAt 3 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_3, Captured.Shard_000.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m04 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.UnitMarkerAt Captured.program 4
      (idAt 4 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_4, Captured.Shard_000.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m05 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.UnitMarkerAt Captured.program 5
      (idAt 5 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_5, Captured.Shard_000.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m06 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.UnitMarkerAt Captured.program 6
      (idAt 6 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_6, Captured.Shard_000.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m07 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.UnitMarkerAt Captured.program 7
      (idAt 7 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_7, Captured.Shard_001.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m08 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.UnitMarkerAt Captured.program 8
      (idAt 8 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_8, Captured.Shard_001.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m09 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.UnitMarkerAt Captured.program 9
      (idAt 9 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_9, Captured.Shard_001.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.UnitMarkerAt Captured.program 10
      (idAt 10 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_10, Captured.Shard_001.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.UnitMarkerAt Captured.program 11
      (idAt 11 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_11, Captured.Shard_001.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.UnitMarkerAt Captured.program 12
      (idAt 12 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_12, Captured.Shard_001.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.UnitMarkerAt Captured.program 13
      (idAt 13 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_13, Captured.Shard_001.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.UnitMarkerAt Captured.program 14
      (idAt 14 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_14, Captured.Shard_002.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.UnitMarkerAt Captured.program 15
      (idAt 15 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_15, Captured.Shard_002.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.UnitMarkerAt Captured.program 16
      (idAt 16 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_16, Captured.Shard_002.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.UnitMarkerAt Captured.program 17
      (idAt 17 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_17, Captured.Shard_002.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.UnitMarkerAt Captured.program 18
      (idAt 18 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_18, Captured.Shard_002.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.UnitMarkerAt Captured.program 19
      (idAt 19 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_19, Captured.Shard_002.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.UnitMarkerAt Captured.program 20
      (idAt 20 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_20, Captured.Shard_002.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.UnitMarkerAt Captured.program 21
      (idAt 21 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_21, Captured.Shard_003.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.UnitMarkerAt Captured.program 22
      (idAt 22 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_22, Captured.Shard_003.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.UnitMarkerAt Captured.program 23
      (idAt 23 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_23, Captured.Shard_003.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.UnitMarkerAt Captured.program 24
      (idAt 24 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_24, Captured.Shard_003.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.UnitMarkerAt Captured.program 25
      (idAt 25 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_25, Captured.Shard_003.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.UnitMarkerAt Captured.program 26
      (idAt 26 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_26, Captured.Shard_003.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.UnitMarkerAt Captured.program 27
      (idAt 27 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_27, Captured.Shard_003.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.UnitMarkerAt Captured.program 28
      (idAt 28 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_28, Captured.Shard_003.body_7, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.UnitMarkerAt Captured.program 29
      (idAt 29 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_29, Captured.Shard_004.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.UnitMarkerAt Captured.program 30
      (idAt 30 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_30, Captured.Shard_004.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.UnitMarkerAt Captured.program 31
      (idAt 31 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_31, Captured.Shard_004.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.UnitMarkerAt Captured.program 32
      (idAt 32 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_32, Captured.Shard_004.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.UnitMarkerAt Captured.program 33
      (idAt 33 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_33, Captured.Shard_004.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.UnitMarkerAt Captured.program 34
      (idAt 34 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_34, Captured.Shard_004.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.UnitMarkerAt Captured.program 35
      (idAt 35 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_35, Captured.Shard_004.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.UnitMarkerAt Captured.program 36
      (idAt 36 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_36, Captured.Shard_004.body_7, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.UnitMarkerAt Captured.program 37
      (idAt 37 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_37, Captured.Shard_004.body_8, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.UnitMarkerAt Captured.program 38
      (idAt 38 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_38, Captured.Shard_005.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.UnitMarkerAt Captured.program 39
      (idAt 39 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_39, Captured.Shard_005.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.UnitMarkerAt Captured.program 40
      (idAt 40 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_40, Captured.Shard_005.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.UnitMarkerAt Captured.program 41
      (idAt 41 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_41, Captured.Shard_005.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.UnitMarkerAt Captured.program 42
      (idAt 42 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_42, Captured.Shard_005.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.UnitMarkerAt Captured.program 43
      (idAt 43 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_43, Captured.Shard_005.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.UnitMarkerAt Captured.program 44
      (idAt 44 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_44, Captured.Shard_005.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.UnitMarkerAt Captured.program 45
      (idAt 45 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_45, Captured.Shard_005.body_7, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.UnitMarkerAt Captured.program 46
      (idAt 46 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_46, Captured.Shard_005.body_8, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.UnitMarkerAt Captured.program 47
      (idAt 47 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_47, Captured.Shard_006.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.UnitMarkerAt Captured.program 48
      (idAt 48 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_48, Captured.Shard_006.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.UnitMarkerAt Captured.program 49
      (idAt 49 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_49, Captured.Shard_006.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.UnitMarkerAt Captured.program 50
      (idAt 50 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_50, Captured.Shard_006.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.UnitMarkerAt Captured.program 51
      (idAt 51 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_51, Captured.Shard_006.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.UnitMarkerAt Captured.program 52
      (idAt 52 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_52, Captured.Shard_006.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.UnitMarkerAt Captured.program 53
      (idAt 53 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_53, Captured.Shard_006.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.UnitMarkerAt Captured.program 54
      (idAt 54 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_54, Captured.Shard_007.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.UnitMarkerAt Captured.program 55
      (idAt 55 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_55, Captured.Shard_007.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.UnitMarkerAt Captured.program 56
      (idAt 56 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_56, Captured.Shard_007.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.UnitMarkerAt Captured.program 57
      (idAt 57 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_57, Captured.Shard_007.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.UnitMarkerAt Captured.program 58
      (idAt 58 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_58, Captured.Shard_007.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.UnitMarkerAt Captured.program 59
      (idAt 59 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_59, Captured.Shard_007.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.UnitMarkerAt Captured.program 60
      (idAt 60 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_60, Captured.Shard_007.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m61 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.UnitMarkerAt Captured.program 61
      (idAt 61 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_61, Captured.Shard_007.body_7, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m62 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.UnitMarkerAt Captured.program 62
      (idAt 62 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_62, Captured.Shard_008.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m63 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.UnitMarkerAt Captured.program 63
      (idAt 63 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_63, Captured.Shard_008.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m64 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.UnitMarkerAt Captured.program 64
      (idAt 64 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_64, Captured.Shard_008.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m65 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.UnitMarkerAt Captured.program 65
      (idAt 65 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_65, Captured.Shard_008.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m66 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.UnitMarkerAt Captured.program 66
      (idAt 66 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_66, Captured.Shard_008.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m67 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.UnitMarkerAt Captured.program 67
      (idAt 67 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_67, Captured.Shard_008.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m68 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.UnitMarkerAt Captured.program 68
      (idAt 68 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_68, Captured.Shard_008.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m69 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.UnitMarkerAt Captured.program 69
      (idAt 69 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_69, Captured.Shard_008.body_7, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m70 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.UnitMarkerAt Captured.program 70
      (idAt 70 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_70, Captured.Shard_009.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m71 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.UnitMarkerAt Captured.program 71
      (idAt 71 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_71, Captured.Shard_009.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m72 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.UnitMarkerAt Captured.program 72
      (idAt 72 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_72, Captured.Shard_009.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m73 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.UnitMarkerAt Captured.program 73
      (idAt 73 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_73, Captured.Shard_009.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m74 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.UnitMarkerAt Captured.program 74
      (idAt 74 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_74, Captured.Shard_009.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m75 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.UnitMarkerAt Captured.program 75
      (idAt 75 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_75, Captured.Shard_009.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m76 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.UnitMarkerAt Captured.program 76
      (idAt 76 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_76, Captured.Shard_009.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m77 :
    BodyVerified Captured.program 77 Captured.body_77
      (Spec.specs.safety Captured.body_77.identity) ∧
    Spec.UnitMarkerAt Captured.program 77
      (idAt 77 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_77, Captured.Shard_010.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m78 :
    BodyVerified Captured.program 78 Captured.body_78
      (Spec.specs.safety Captured.body_78.identity) ∧
    Spec.UnitMarkerAt Captured.program 78
      (idAt 78 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_78, Captured.Shard_010.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m79 :
    BodyVerified Captured.program 79 Captured.body_79
      (Spec.specs.safety Captured.body_79.identity) ∧
    Spec.UnitMarkerAt Captured.program 79
      (idAt 79 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_79, Captured.Shard_010.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m80 :
    BodyVerified Captured.program 80 Captured.body_80
      (Spec.specs.safety Captured.body_80.identity) ∧
    Spec.UnitMarkerAt Captured.program 80
      (idAt 80 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_80, Captured.Shard_010.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m81 :
    BodyVerified Captured.program 81 Captured.body_81
      (Spec.specs.safety Captured.body_81.identity) ∧
    Spec.UnitMarkerAt Captured.program 81
      (idAt 81 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_81, Captured.Shard_010.body_4, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m82 :
    BodyVerified Captured.program 82 Captured.body_82
      (Spec.specs.safety Captured.body_82.identity) ∧
    Spec.UnitMarkerAt Captured.program 82
      (idAt 82 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_82, Captured.Shard_010.body_5, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m83 :
    BodyVerified Captured.program 83 Captured.body_83
      (Spec.specs.safety Captured.body_83.identity) ∧
    Spec.UnitMarkerAt Captured.program 83
      (idAt 83 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_83, Captured.Shard_010.body_6, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m84 :
    BodyVerified Captured.program 84 Captured.body_84
      (Spec.specs.safety Captured.body_84.identity) ∧
    Spec.UnitMarkerAt Captured.program 84
      (idAt 84 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_84, Captured.Shard_011.body_0, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m85 :
    BodyVerified Captured.program 85 Captured.body_85
      (Spec.specs.safety Captured.body_85.identity) ∧
    Spec.UnitMarkerAt Captured.program 85
      (idAt 85 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_85, Captured.Shard_011.body_1, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m86 :
    BodyVerified Captured.program 86 Captured.body_86
      (Spec.specs.safety Captured.body_86.identity) ∧
    Spec.UnitMarkerAt Captured.program 86
      (idAt 86 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_86, Captured.Shard_011.body_2, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m87 :
    BodyVerified Captured.program 87 Captured.body_87
      (Spec.specs.safety Captured.body_87.identity) ∧
    Spec.UnitMarkerAt Captured.program 87
      (idAt 87 Spec.nonzeroMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_87, Captured.Shard_011.body_3, Spec.nonzeroMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem all_bodies_verified :
    BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
    ⟨m00.1, m01.1, m02.1, m03.1, m04.1, m05.1, m06.1, m07.1, m08.1, m09.1,
     m10.1, m11.1, m12.1, m13.1, m14.1, m15.1, m16.1, m17.1, m18.1, m19.1,
     m20.1, m21.1, m22.1, m23.1, m24.1, m25.1, m26.1, m27.1, m28.1, m29.1,
     m30.1, m31.1, m32.1, m33.1, m34.1, m35.1, m36.1, m37.1, m38.1, m39.1,
     m40.1, m41.1, m42.1, m43.1, m44.1, m45.1, m46.1, m47.1, m48.1, m49.1,
     m50.1, m51.1, m52.1, m53.1, m54.1, m55.1, m56.1, m57.1, m58.1, m59.1,
     m60.1, m61.1, m62.1, m63.1, m64.1, m65.1, m66.1, m67.1, m68.1, m69.1,
     m70.1, m71.1, m72.1, m73.1, m74.1, m75.1, m76.1, m77.1, m78.1, m79.1,
     m80.1, m81.1, m82.1, m83.1, m84.1, m85.1, m86.1, m87.1, True.intro⟩

private noncomputable def AllMarkersAt (program : Program) (startIdx : Nat)
    (identities : List String) : Prop :=
  identities.foldr
    (fun identity ih curIdx =>
      Spec.UnitMarkerAt program curIdx identity ∧ ih (curIdx + 1))
    (fun _ => True)
    startIdx

private theorem allMarkersAt_getElem {p : Program} :
    ∀ {idx : Nat} {ids : List String},
      AllMarkersAt p idx ids →
      ∀ (k : Nat) (identity : String),
        Trusted.MirSemantics.getElem? ids k = some identity →
        Spec.UnitMarkerAt p (idx + k) identity
  | _, [], _, _, _, hGet => by cases hGet
  | idx, _ :: _, hIds, 0, _, hGet => by
    injection hGet with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hIds.1
  | idx, _ :: _, hIds, k + 1, identity, hGet => by
    have hSub := allMarkersAt_getElem hIds.2 k identity hGet
    have hIdx : idx + 1 + k = idx + (k + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 k]
    rw [← hIdx]
    exact hSub

private theorem all_markers_at :
    AllMarkersAt Captured.program 0 Spec.nonzeroMarkerIdentities :=
    ⟨m00.2, m01.2, m02.2, m03.2, m04.2, m05.2, m06.2, m07.2, m08.2, m09.2,
     m10.2, m11.2, m12.2, m13.2, m14.2, m15.2, m16.2, m17.2, m18.2, m19.2,
     m20.2, m21.2, m22.2, m23.2, m24.2, m25.2, m26.2, m27.2, m28.2, m29.2,
     m30.2, m31.2, m32.2, m33.2, m34.2, m35.2, m36.2, m37.2, m38.2, m39.2,
     m40.2, m41.2, m42.2, m43.2, m44.2, m45.2, m46.2, m47.2, m48.2, m49.2,
     m50.2, m51.2, m52.2, m53.2, m54.2, m55.2, m56.2, m57.2, m58.2, m59.2,
     m60.2, m61.2, m62.2, m63.2, m64.2, m65.2, m66.2, m67.2, m68.2, m69.2,
     m70.2, m71.2, m72.2, m73.2, m74.2, m75.2, m76.2, m77.2, m78.2, m79.2,
     m80.2, m81.2, m82.2, m83.2, m84.2, m85.2, m86.2, m87.2, True.intro⟩

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: Model-Side `Trusted.MirSemantics.Bytes` Niche Proofs -/

private theorem bne_self_eq_false (x : BitVec 128) : (x != x) = false := by
  unfold bne
  rw [beq_self_eq_true x]
  rfl

private theorem list_length_reverseAux {α : Type} (xs acc : List α) :
    (List.reverseAux xs acc).length = xs.length + acc.length := by
  induction xs generalizing acc with
  | nil =>
    unfold List.reverseAux
    exact (Nat.zero_add acc.length).symm
  | cons _ rest ih =>
    unfold List.reverseAux
    rw [ih]
    change rest.length + (acc.length + 1) = (rest.length + 1) + acc.length
    rw [Nat.add_assoc, Nat.add_comm 1 acc.length, ← Nat.add_assoc]

private theorem list_length_reverse {α : Type} (xs : List α) :
    xs.reverse.length = xs.length := by
  unfold List.reverse
  rw [list_length_reverseAux]
  exact Nat.add_zero xs.length

private theorem reverseAux_reverseAux {α : Type} :
    ∀ (xs acc : List α),
      List.reverseAux (List.reverseAux xs acc) [] = List.reverseAux acc xs
  | [], _ => rfl
  | x :: rest, acc => reverseAux_reverseAux rest (x :: acc)

private theorem reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs :=
  reverseAux_reverseAux xs []

private theorem reverseAux_replicate {α : Type} :
    ∀ (m k : Nat) (a : α),
      List.reverseAux (List.replicate m a) (List.replicate k a) =
        List.replicate (m + k) a
  | 0, k, a => by
    dsimp only [List.replicate, List.reverseAux]
    rw [Nat.zero_add]
  | m + 1, k, a => by
    dsimp only [List.replicate, List.reverseAux]
    have hStep : a :: List.replicate k a = List.replicate (k + 1) a := rfl
    rw [hStep, reverseAux_replicate m (k + 1) a]
    have hAdd : m + (k + 1) = (m + 1) + k := by
      rw [Nat.add_succ, Nat.succ_add]
    rw [hAdd]

private theorem reverse_replicate {α : Type} (n : Nat) (a : α) :
    (List.replicate n a).reverse = List.replicate n a := by
  unfold List.reverse
  change List.reverseAux (List.replicate n a) (List.replicate 0 a) =
    List.replicate n a
  rw [reverseAux_replicate n 0 a, Nat.add_zero]

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).length = xs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (list_length_map f rest)

private theorem list_length_replicate {α : Type} :
    ∀ (n : Nat) (a : α), (List.replicate n a).length = n
  | 0, _ => rfl
  | n + 1, a => congrArg Nat.succ (list_length_replicate n a)

private theorem initBytes?_length :
    ∀ {bs : List AllocByte} {raw : List UInt8},
      initBytes? bs = some raw → raw.length = bs.length
  | [], _, h => by
    injection h with hEq
    subst hEq
    rfl
  | .uninit :: _, _, h => by cases h
  | .init _ _ :: rest, _, h => by
    unfold initBytes? at h
    cases hRest : initBytes? rest with
    | none => rw [hRest] at h; cases h
    | some rs =>
      rw [hRest] at h
      injection h with hEq
      subst hEq
      exact congrArg Nat.succ (initBytes?_length hRest)

private theorem initBytes?_map_init :
    ∀ (raw : List UInt8),
      initBytes? (raw.map (fun b => AllocByte.init b none)) = some raw
  | [] => rfl
  | _ :: rest => by
    unfold List.map initBytes?
    rw [initBytes?_map_init rest]

private theorem initBytes?_replicate_zero :
    ∀ (n : Nat),
      initBytes? (List.replicate n (AllocByte.init 0 none)) =
        some (List.replicate n 0)
  | 0 => rfl
  | n + 1 => by
    unfold List.replicate initBytes?
    rw [initBytes?_replicate_zero n]

private theorem map_init_replicate_zero :
    ∀ (n : Nat),
      (List.replicate n (0 : UInt8)).map (fun b => AllocByte.init b none) =
        Spec.zeroAllocBytes n
  | 0 => rfl
  | n + 1 => congrArg (List.cons (AllocByte.init 0 none))
      (map_init_replicate_zero n)

private theorem not_mem_uninit_of_initBytes? :
    ∀ {bs : List AllocByte} {raw : List UInt8},
      initBytes? bs = some raw → AllocByte.uninit ∉ bs
  | [], _, _, hMem => by cases hMem
  | .uninit :: _, _, h, _ => by cases h
  | .init _ _ :: rest, _, h, hMem => by
    unfold initBytes? at h
    cases hRest : initBytes? rest with
    | none => rw [hRest] at h; cases h
    | some rs =>
      cases hMem with
      | tail _ hTail => exact not_mem_uninit_of_initBytes? hRest hTail

private theorem nat_pow_add (a m : Nat) :
    ∀ (n : Nat), Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n
  | 0 => by
    rw [Nat.add_zero]
    change Nat.pow a m = Nat.pow a m * 1
    rw [Nat.mul_one]
  | n + 1 => by
    change Nat.pow a (m + n) * a = Nat.pow a m * (Nat.pow a n * a)
    rw [nat_pow_add a m n, Nat.mul_assoc]

private theorem natOfLeBytes_lt :
    ∀ (raw : List UInt8), natOfLeBytes raw < Nat.pow 2 (8 * raw.length)
  | [] => Nat.zero_lt_one
  | b :: rest => by
    unfold natOfLeBytes
    change b.toNat + 256 * natOfLeBytes rest <
      Nat.pow 2 (8 * (rest.length + 1))
    have hPow : Nat.pow 2 (8 * (rest.length + 1)) =
        256 * Nat.pow 2 (8 * rest.length) := by
      rw [Nat.mul_succ, nat_pow_add 2 (8 * rest.length) 8,
        Nat.mul_comm (Nat.pow 2 (8 * rest.length)) (Nat.pow 2 8)]
    rw [hPow]
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have ih := natOfLeBytes_lt rest
    have h1 : b.toNat + 256 * natOfLeBytes rest <
        256 + 256 * natOfLeBytes rest :=
      Nat.add_lt_add_right hb (256 * natOfLeBytes rest)
    have h2 : 256 + 256 * natOfLeBytes rest =
        256 * (natOfLeBytes rest + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 256 ih)

private theorem decodeUInt_lt (endian : TargetEndian) (raw : List UInt8) :
    decodeUInt endian raw < Nat.pow 2 (8 * raw.length) := by
  cases endian with
  | little => exact natOfLeBytes_lt raw
  | big =>
    unfold decodeUInt
    have h := natOfLeBytes_lt raw.reverse
    rw [list_length_reverse] at h
    exact h

private theorem natOfLeBytes_replicate_zero :
    ∀ (n : Nat), natOfLeBytes (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by
    unfold List.replicate natOfLeBytes
    rw [natOfLeBytes_replicate_zero n]
    rfl

private theorem eq_replicate_zero_of_natOfLeBytes_zero :
    ∀ (raw : List UInt8),
      natOfLeBytes raw = 0 → raw = List.replicate raw.length 0
  | [], _ => rfl
  | b :: rest, h => by
    unfold natOfLeBytes at h
    have hb0 : b.toNat = 0 := by
      cases hbn : b.toNat with
      | zero => rfl
      | succ k =>
        rw [hbn] at h
        have hPos : 0 < (k + 1) + 256 * natOfLeBytes rest := by
          rw [Nat.add_comm (k + 1), ← Nat.add_assoc]
          exact Nat.zero_lt_succ _
        rw [h] at hPos
        cases hPos
    have hRest0 : natOfLeBytes rest = 0 := by
      rw [hb0, Nat.zero_add] at h
      cases hr : natOfLeBytes rest with
      | zero => rfl
      | succ m =>
        rw [hr] at h
        have hPos : 0 < 256 * (m + 1) := by
          change 0 < 256 * m + 256
          exact Nat.zero_lt_succ _
        rw [h] at hPos
        cases hPos
    have hbEq : b = 0 := by
      cases b with
      | ofBitVec bv =>
        cases bv with
        | ofFin f =>
          exact congrArg UInt8.ofBitVec
            (congrArg BitVec.ofFin (Fin.eq_of_val_eq hb0))
    rw [hbEq]
    exact congrArg (List.cons 0)
      (eq_replicate_zero_of_natOfLeBytes_zero rest hRest0)

private theorem decodeUInt_replicate_zero (endian : TargetEndian) (n : Nat) :
    decodeUInt endian (List.replicate n 0) = 0 := by
  cases endian with
  | little => exact natOfLeBytes_replicate_zero n
  | big =>
    unfold decodeUInt
    rw [reverse_replicate n 0]
    exact natOfLeBytes_replicate_zero n

private theorem eq_replicate_zero_of_decodeUInt_zero (endian : TargetEndian)
    {raw : List UInt8} (h : decodeUInt endian raw = 0) :
    raw = List.replicate raw.length 0 := by
  cases endian with
  | little => exact eq_replicate_zero_of_natOfLeBytes_zero raw h
  | big =>
    unfold decodeUInt at h
    have hRev := eq_replicate_zero_of_natOfLeBytes_zero raw.reverse h
    rw [list_length_reverse] at hRev
    have hRR := congrArg List.reverse hRev
    rw [reverse_reverse, reverse_replicate raw.length 0] at hRR
    exact hRR

/-! ### Unsigned & Two's-Complement Zero Equivalence for `decodeScalar` -/

private theorem int_sub_ofNat_succ (a pm : Nat) :
    Int.ofNat a - Int.ofNat (pm + 1) = Int.subNatNat a (pm + 1) := rfl

private theorem nat_mod_eq_hmod (a b : Nat) : Nat.mod a b = a % b := rfl

private theorem toNat_zero_of_bvToInt_zero {v : Nat} (hvPos : 0 < Nat.pow 2 v)
    {z : BitVec v} (h : bvToInt z = 0) : z.toNat = 0 := by
  unfold bvToInt at h
  cases Nat.lt_or_ge (2 * z.toNat) (Nat.pow 2 v) with
  | inl hCmp =>
    rw [ite_prop_true hCmp] at h
    injection h
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)] at h
    cases hPv : Nat.pow 2 v with
    | zero => rw [hPv] at hvPos; cases hvPos
    | succ pv =>
      rw [hPv, int_sub_ofNat_succ] at h
      unfold Int.subNatNat at h
      have hLt : z.toNat < pv + 1 := by rw [← hPv]; exact z.isLt
      cases hD : (pv + 1) - z.toNat with
      | zero =>
        exact False.elim (Nat.not_le_of_gt hLt (Nat.le_of_sub_eq_zero hD))
      | succ _ => rw [hD] at h; cases h

private theorem low_toNat_zero_of_bvSignExtend_zero {m v : Nat}
    (hmLe : Nat.pow 2 m ≤ Nat.pow 2 v) (hmPos : 1 < Nat.pow 2 m)
    {low : BitVec m} (h : bvToInt (bvSignExtend v low) = 0) :
    low.toNat = 0 := by
  have hvPos : 0 < Nat.pow 2 v :=
    Nat.lt_of_lt_of_le (Nat.lt_trans Nat.zero_lt_one hmPos) hmLe
  have hz0 : (bvSignExtend v low).toNat = 0 :=
    toNat_zero_of_bvToInt_zero hvPos h
  unfold bvSignExtend bvOfInt bvToInt at hz0
  cases Nat.lt_or_ge (2 * low.toNat) (Nat.pow 2 m) with
  | inl hCmp =>
    rw [ite_prop_true hCmp] at hz0
    dsimp only [intEmod, Int.natAbs, Int.toNat] at hz0
    have hLtV : low.toNat < Nat.pow 2 v := Nat.lt_of_lt_of_le low.isLt hmLe
    rw [nat_mod_eq_hmod, Nat.mod_eq_of_lt hLtV] at hz0
    have hBv : (BitVec.ofNat v low.toNat).toNat = low.toNat :=
      Nat.mod_eq_of_lt hLtV
    rw [hBv] at hz0
    exact hz0
  | inr hCmp =>
    rw [ite_prop_false (Nat.not_lt_of_ge hCmp)] at hz0
    cases hPm : Nat.pow 2 m with
    | zero => rw [hPm] at hmPos; cases hmPos
    | succ pm =>
      rw [hPm, int_sub_ofNat_succ] at hz0
      unfold Int.subNatNat at hz0
      have hLowLt : low.toNat < pm + 1 := by rw [← hPm]; exact low.isLt
      cases hDm : (pm + 1) - low.toNat with
      | zero =>
        exact False.elim (Nat.not_le_of_gt hLowLt (Nat.le_of_sub_eq_zero hDm))
      | succ k =>
        rw [hDm] at hz0
        dsimp only [intEmod, Int.natAbs] at hz0
        have hLowPos : 0 < low.toNat := by
          cases hL0 : low.toNat with
          | zero =>
            rw [hL0, Nat.mul_zero] at hCmp
            exact False.elim
              (Nat.not_le_of_gt (Nat.lt_trans Nat.zero_lt_one hmPos) hCmp)
          | succ _ => exact Nat.zero_lt_succ _
        have hSuccKLtM : k + 1 < Nat.pow 2 m := by
          have hEq : k + 1 = Nat.pow 2 m - low.toNat := by rw [hPm, hDm]
          rw [hEq]
          exact Nat.sub_lt (Nat.lt_trans Nat.zero_lt_one hmPos) hLowPos
        have hSuccKLtV : k + 1 < Nat.pow 2 v :=
          Nat.lt_of_lt_of_le hSuccKLtM hmLe
        have hKLtV : k < Nat.pow 2 v :=
          Nat.lt_trans (Nat.lt_succ_self k) hSuccKLtV
        rw [nat_mod_eq_hmod, Nat.mod_eq_of_lt hKLtV] at hz0
        have hSubV :
            Int.subNatNat (Nat.pow 2 v) (Nat.succ k) =
              Int.ofNat (Nat.pow 2 v - (k + 1)) := by
          unfold Int.subNatNat
          rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hSuccKLtV)]
        rw [hSubV] at hz0
        dsimp only [Int.toNat] at hz0
        have hRemLtV : Nat.pow 2 v - (k + 1) < Nat.pow 2 v :=
          Nat.sub_lt hvPos (Nat.zero_lt_succ k)
        have hBv :
            (BitVec.ofNat v (Nat.pow 2 v - (k + 1))).toNat =
              Nat.pow 2 v - (k + 1) :=
          Nat.mod_eq_of_lt hRemLtV
        rw [hBv] at hz0
        have hRemPos : 0 < Nat.pow 2 v - (k + 1) :=
          Nat.sub_pos_of_lt hSuccKLtV
        rw [hz0] at hRemPos
        cases hRemPos

private theorem nat_shiftRight_zero (x : Nat) : Nat.shiftRight x 0 = x := rfl

private theorem signExtendBits_zero_to_toNat_zero (w : IntWidth)
    {bits : BitVec 128} (hLt : bits.toNat < intWidthModulus w)
    (hZero : signExtendBits w bits = 0) : bits.toNat = 0 := by
  unfold signExtendBits bvExtractLsb bvExtractLsb' at hZero
  rw [nat_shiftRight_zero] at hZero
  cases w with
  | i8 =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 8 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 8 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow
  | i16 =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 16 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 16 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow
  | i32 =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 32 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 32 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow
  | i64 =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 64 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 64 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow
  | i128 =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 128 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 128 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow
  | isize =>
    have hLow := low_toNat_zero_of_bvSignExtend_zero (by decide) (by decide)
      hZero
    change (BitVec.ofNat 64 bits.toNat).toNat = 0 at hLow
    have hMod : (BitVec.ofNat 64 bits.toNat).toNat = bits.toNat :=
      Nat.mod_eq_of_lt hLt
    rw [hMod] at hLow
    exact hLow

private theorem decodeScalar_zero_of_bits_zero (w : IntWidth) (signed : Bool) :
    decodeScalar ⟨w, signed, BitVec.ofNat 128 0⟩ = 0 := by
  cases signed <;> cases w <;> rfl

private theorem toNat_zero_of_decodeScalar_zero (w : IntWidth) (signed : Bool)
    {bits : BitVec 128} (hLt : bits.toNat < intWidthModulus w)
    (hDec : decodeScalar ⟨w, signed, bits⟩ = 0) :
    bits.toNat = 0 := by
  unfold decodeScalar at hDec
  dsimp only at hDec
  rw [truncateBits_of_toNat_lt hLt] at hDec
  cases signed with
  | false => injection hDec
  | true => exact signExtendBits_zero_to_toNat_zero w hLt hDec

/-! ### Layout, `decodeVal` Bridge, and Niche Partition Proofs -/

private theorem intLayout_size_eq_byteSize (w : IntWidth) :
    (intLayout w).size = w.byteSize := by
  cases w <;> rfl

private theorem intLayout_size_beq_zero (w : IntWidth) :
    Nat.beq (intLayout w).size 0 = false := by
  cases w <;> rfl

private theorem two_pow_eight_mul_byteSize (w : IntWidth) :
    Nat.pow 2 (8 * w.byteSize) = intWidthModulus w := by
  cases w <;> rfl

private theorem intWidthModulus_le_128 (w : IntWidth) :
    intWidthModulus w ≤ Nat.pow 2 128 := by
  cases w <;> decide

private theorem decodeVal_bridge (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) {bs : List AllocByte}
    (hInit : Spec.AllInitBytes w.byteSize bs) :
    ∃ sv : ScalarVal,
      decodeVal endian (.int w signed) bs = .ok (some (.scalar sv)) ∧
      checkVal (.scalar sv) (.int w signed) = true ∧
      Spec.decodeIntBytes endian signed w bs = some (decodeScalar sv) := by
  let ⟨hbs, raw, hraw⟩ := hInit
  have hrawLen : raw.length = w.byteSize := (initBytes?_length hraw).trans hbs
  have hDecLt : decodeUInt endian raw < intWidthModulus w := by
    have h := decodeUInt_lt endian raw
    rw [hrawLen, two_pow_eight_mul_byteSize w] at h
    exact h
  have hDecLt128 : decodeUInt endian raw < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hDecLt (intWidthModulus_le_128 w)
  let bits : BitVec 128 := BitVec.ofNat 128 (decodeUInt endian raw)
  have hBitsNat : bits.toNat = decodeUInt endian raw :=
    Nat.mod_eq_of_lt hDecLt128
  have hBitsLt : bits.toNat < intWidthModulus w := by
    rw [hBitsNat]; exact hDecLt
  have hTrunc : truncateBits w bits = bits :=
    truncateBits_of_toNat_lt hBitsLt
  have hLenBeq : (!Nat.beq bs.length (intLayout w).size) = false := by
    rw [hbs, intLayout_size_eq_byteSize w, Anneal.InitLemmas.nat_beq_refl]
    rfl
  have hLenEqTrue : Nat.beq bs.length w.byteSize = true := by
    rw [hbs, Anneal.InitLemmas.nat_beq_refl]
  refine ⟨⟨w, signed, bits⟩, ?_, checkVal_scalar_of_toNat_lt hBitsLt, ?_⟩
  · unfold decodeVal
    dsimp only [layoutOfTy]
    rw [ite_bool_false hLenBeq, ite_bool_false (intLayout_size_beq_zero w),
      hraw]
    dsimp only [evalConstLit]
    rw [show BitVec.ofNat 128 (decodeUInt endian raw) = bits from rfl,
      hTrunc, ite_bool_false (bne_self_eq_false bits)]
  · unfold Spec.decodeIntBytes
    rw [ite_bool_true hLenEqTrue, hraw]

private theorem decodeIntBytes_zero_iff (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) {bs : List AllocByte}
    (hInit : Spec.AllInitBytes w.byteSize bs) :
    Spec.decodeIntBytes endian signed w bs = some 0 ↔
      Spec.ZeroNicheBytes w.byteSize bs := by
  let ⟨hbs, raw, hraw⟩ := hInit
  have hrawLen : raw.length = w.byteSize := (initBytes?_length hraw).trans hbs
  have hLenEqTrue : Nat.beq bs.length w.byteSize = true := by
    rw [hbs, Anneal.InitLemmas.nat_beq_refl]
  constructor
  · intro hDec0
    unfold Spec.decodeIntBytes at hDec0
    rw [ite_bool_true hLenEqTrue, hraw] at hDec0
    dsimp only at hDec0
    injection hDec0 with hSc0
    have hDecLt : decodeUInt endian raw < intWidthModulus w := by
      have h := decodeUInt_lt endian raw
      rw [hrawLen, two_pow_eight_mul_byteSize w] at h
      exact h
    have hDecLt128 : decodeUInt endian raw < Nat.pow 2 128 :=
      Nat.lt_of_lt_of_le hDecLt (intWidthModulus_le_128 w)
    have hBitsNat :
        (BitVec.ofNat 128 (decodeUInt endian raw)).toNat =
          decodeUInt endian raw :=
      Nat.mod_eq_of_lt hDecLt128
    have hBitsLt :
        (BitVec.ofNat 128 (decodeUInt endian raw)).toNat <
          intWidthModulus w := by
      rw [hBitsNat]; exact hDecLt
    have hToNat0 := toNat_zero_of_decodeScalar_zero w signed hBitsLt hSc0
    rw [hBitsNat] at hToNat0
    have hRawEq := eq_replicate_zero_of_decodeUInt_zero endian hToNat0
    rw [hrawLen] at hRawEq
    refine ⟨hbs, ?_⟩
    rw [hraw, hRawEq]
  · intro ⟨_, hNiche⟩
    unfold Spec.decodeIntBytes
    rw [ite_bool_true hLenEqTrue, hNiche]
    dsimp only
    rw [decodeUInt_replicate_zero endian w.byteSize,
      decodeScalar_zero_of_bits_zero w signed]

private theorem nonZeroValid_iff_not_niche (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) (bs : List AllocByte) :
    Spec.NonZeroValidBytes endian signed w bs ↔
      (Spec.AllInitBytes w.byteSize bs ∧
        ¬ Spec.ZeroNicheBytes w.byteSize bs) := by
  constructor
  · intro ⟨hInit, z, hDec, hzNe⟩
    refine ⟨hInit, fun hNiche => ?_⟩
    have hDec0 := (decodeIntBytes_zero_iff endian signed w hInit).mpr hNiche
    rw [hDec] at hDec0
    injection hDec0 with hzEq
    exact hzNe hzEq
  · intro ⟨hInit, hNotNiche⟩
    let ⟨hbs, raw, hraw⟩ := hInit
    have hLenEqTrue : Nat.beq bs.length w.byteSize = true := by
      rw [hbs, Anneal.InitLemmas.nat_beq_refl]
    let z := decodeScalar ⟨w, signed, BitVec.ofNat 128 (decodeUInt endian raw)⟩
    have hDecZ : Spec.decodeIntBytes endian signed w bs = some z := by
      unfold Spec.decodeIntBytes
      rw [ite_bool_true hLenEqTrue, hraw]
    refine ⟨hInit, z, hDecZ, fun hz0 => ?_⟩
    rw [hz0] at hDecZ
    exact hNotNiche ((decodeIntBytes_zero_iff endian signed w hInit).mp hDecZ)

private theorem nonZeroValid_plain_iff (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) {raw : List UInt8} (hLen : raw.length = w.byteSize) :
    Spec.NonZeroValidBytes endian signed w
        (raw.map (fun b => AllocByte.init b none)) ↔
      raw.map (fun b => AllocByte.init b none) ≠
        Spec.zeroAllocBytes w.byteSize := by
  have hBsLen :
      (raw.map (fun b => AllocByte.init b none)).length = w.byteSize := by
    rw [list_length_map, hLen]
  have hInit :
      Spec.AllInitBytes w.byteSize
        (raw.map (fun b => AllocByte.init b none)) :=
    ⟨hBsLen, raw, initBytes?_map_init raw⟩
  rw [nonZeroValid_iff_not_niche endian signed w]
  constructor
  · intro ⟨_, hNotNiche⟩ hEqZero
    apply hNotNiche
    rw [hEqZero]
    exact ⟨list_length_replicate w.byteSize (AllocByte.init 0 none),
      initBytes?_replicate_zero w.byteSize⟩
  · intro hNeZero
    refine ⟨hInit, fun ⟨_, hNiche⟩ => hNeZero ?_⟩
    rw [initBytes?_map_init raw] at hNiche
    injection hNiche with hRawRep
    rw [hRawRep, map_init_replicate_zero w.byteSize]

private theorem nonZeroValid_unit_one (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) :
    Spec.NonZeroValidBytes endian signed w
      ((encodeUInt endian w.byteSize 1).map
        (fun b => AllocByte.init b none)) := by
  cases endian <;> cases signed <;> cases w <;>
    exact ⟨⟨rfl, _, rfl⟩, 1, rfl, fun h => nomatch h⟩

private theorem zeroAllocBytes_allInit (n : Nat) :
    Spec.AllInitBytes n (Spec.zeroAllocBytes n) :=
  ⟨list_length_replicate n (AllocByte.init 0 none),
    List.replicate n 0, initBytes?_replicate_zero n⟩

private theorem zeroAllocBytes_isNiche (n : Nat) :
    Spec.ZeroNicheBytes n (Spec.zeroAllocBytes n) :=
  ⟨list_length_replicate n (AllocByte.init 0 none),
    initBytes?_replicate_zero n⟩

private theorem zeroAllocBytes_not_nonZeroValid (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) :
    ¬ Spec.NonZeroValidBytes endian signed w
        (Spec.zeroAllocBytes w.byteSize) := by
  rw [nonZeroValid_iff_not_niche]
  intro ⟨_, hNot⟩
  exact hNot (zeroAllocBytes_isNiche w.byteSize)

private theorem leBytesOfNat_length :
    ∀ (n value : Nat), (leBytesOfNat n value).length = n
  | 0, _ => rfl
  | n + 1, value =>
    congrArg Nat.succ (leBytesOfNat_length n (Nat.div value 256))

private theorem encodeUInt_length (endian : TargetEndian) (n value : Nat) :
    (encodeUInt endian n value).length = n := by
  cases endian with
  | little => exact leBytesOfNat_length n value
  | big =>
    unfold encodeUInt
    rw [list_length_reverse]
    exact leBytesOfNat_length n value

private theorem uint8_ofNat_toNat_mod (x : Nat) :
    (UInt8.ofNat (x % 256)).toNat = x % 256 := by
  change ((x % 256) % 256) = x % 256
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))

private theorem mod_256_add_mul_mod (v M : Nat) (hM : 0 < M) :
    v % 256 + 256 * ((v / 256) % M) = v % (256 * M) := by
  let q := (v / 256) / M
  let r := (v / 256) % M
  have hDiv : M * q + r = v / 256 := Nat.div_add_mod (v / 256) M
  have hV : 256 * (M * q + r) + v % 256 = v := by
    rw [hDiv]
    exact Nat.div_add_mod v 256
  have hDecomp : v = (v % 256 + 256 * r) + (256 * M) * q := by
    refine Eq.trans hV.symm ?_
    rw [Nat.mul_add 256 (M * q) r, ← Nat.mul_assoc 256 M q,
      Nat.add_assoc ((256 * M) * q) (256 * r) (v % 256),
      Nat.add_comm ((256 * M) * q) (256 * r + v % 256),
      Nat.add_comm (256 * r) (v % 256)]
  have hrLt : r < M := Nat.mod_lt (v / 256) hM
  have hvLt : v % 256 < 256 := Nat.mod_lt v (by decide)
  have hRemLt : v % 256 + 256 * r < 256 * M := by
    have h1 : v % 256 + 256 * r < 256 + 256 * r :=
      Nat.add_lt_add_right hvLt (256 * r)
    have h2 : 256 + 256 * r = 256 * (r + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [h2] at h1
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left 256 hrLt)
  have hMod : v % (256 * M) = v % 256 + 256 * r := by
    have hModEq :
        ((v % 256 + 256 * r) + (256 * M) * q) % (256 * M) =
          v % 256 + 256 * r := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hRemLt
    exact (congrArg (fun x => x % (256 * M)) hDecomp).trans hModEq
  exact hMod.symm

private theorem natOfLeBytes_leBytesOfNat :
    ∀ (n v : Nat),
      natOfLeBytes (leBytesOfNat n v) = v % Nat.pow 2 (8 * n)
  | 0, v => by
    change 0 = v % 1
    rw [Nat.mod_one]
  | n + 1, v => by
    unfold leBytesOfNat natOfLeBytes
    change (UInt8.ofNat (v % 256)).toNat +
        256 * natOfLeBytes (leBytesOfNat n (v / 256)) =
      v % Nat.pow 2 (8 * (n + 1))
    rw [uint8_ofNat_toNat_mod v, natOfLeBytes_leBytesOfNat n (v / 256)]
    have hPow : Nat.pow 2 (8 * (n + 1)) = 256 * Nat.pow 2 (8 * n) := by
      rw [Nat.mul_succ, nat_pow_add 2 (8 * n) 8,
        Nat.mul_comm (Nat.pow 2 (8 * n)) (Nat.pow 2 8)]
    rw [hPow]
    exact mod_256_add_mul_mod v (Nat.pow 2 (8 * n)) (Nat.pow_pos (by decide))

private theorem decodeUInt_encodeUInt (e : TargetEndian) (n value : Nat) :
    decodeUInt e (encodeUInt e n value) = value % Nat.pow 2 (8 * n) := by
  cases e with
  | little => exact natOfLeBytes_leBytesOfNat n value
  | big =>
    unfold decodeUInt encodeUInt
    rw [reverse_reverse]
    exact natOfLeBytes_leBytesOfNat n value

private theorem nonZeroIntoBytes_sound (endian : TargetEndian) (signed : Bool)
    (w : IntWidth) : Spec.NonZeroIntoBytesSound endian signed w := by
  intro sv hcv hNe
  let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp hcv
  cases hEq
  have hModPos : 0 < intWidthModulus w := by cases w <;> decide
  have hBitsLt : bits.toNat < intWidthModulus w := by
    rw [← hTrunc, toNat_truncateBits]
    exact Nat.mod_lt bits.toNat hModPos
  let raw := encodeUInt endian w.byteSize bits.toNat
  let bs := raw.map (fun b => AllocByte.init b none)
  have hEnc : encodeVal endian (.int w signed) (.scalar ⟨w, signed, bits⟩) =
      .ok bs := by
    unfold encodeVal
    rw [hcv]
    rfl
  have hbsLen : bs.length = w.byteSize := by
    rw [list_length_map, encodeUInt_length]
  have hraw : initBytes? bs = some raw := initBytes?_map_init raw
  have hDecNat : decodeUInt endian raw = bits.toNat := by
    rw [decodeUInt_encodeUInt endian w.byteSize bits.toNat,
      two_pow_eight_mul_byteSize w]
    exact Nat.mod_eq_of_lt hBitsLt
  have hBitsEq : BitVec.ofNat 128 (decodeUInt endian raw) = bits :=
    bitVec_eq_of_toNat_eq (by rw [hDecNat]; exact Nat.mod_eq_of_lt bits.isLt)
  have hLenEqTrue : Nat.beq bs.length w.byteSize = true := by
    rw [hbsLen, Anneal.InitLemmas.nat_beq_refl]
  have hDecZ : Spec.decodeIntBytes endian signed w bs =
      some (decodeScalar ⟨w, signed, bits⟩) := by
    unfold Spec.decodeIntBytes
    rw [ite_bool_true hLenEqTrue, hraw]
    dsimp only
    rw [hBitsEq]
  exact ⟨intLayout w, bs, rfl, hEnc,
    hbsLen.trans (intLayout_size_eq_byteSize w).symm,
    not_mem_uninit_of_initBytes? hraw,
    ⟨⟨hbsLen, raw, hraw⟩, _, hDecZ, hNe⟩, hDecZ⟩

private theorem nonZeroIntoBytes_witness (signed : Bool) (w : IntWidth) :
    checkVal (.scalar ⟨w, signed, BitVec.ofNat 128 1⟩) (.int w signed) =
      true ∧
    decodeScalar ⟨w, signed, BitVec.ofNat 128 1⟩ ≠ 0 := by
  have hOne : decodeScalar ⟨w, signed, BitVec.ofNat 128 1⟩ = 1 := by
    cases signed <;> cases w <;> rfl
  refine ⟨checkVal_scalar_of_toNat_lt (by cases w <;> decide), fun h => ?_⟩
  rw [hOne] at h
  cases h

private theorem optionNonZero_niche_partition (endian : TargetEndian)
    (signed : Bool) (w : IntWidth) :
    Spec.OptionNonZeroNichePartition endian signed w := by
  intro bs
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hInit
      let ⟨hbs, raw, hraw⟩ := hInit
      have hLenEqTrue : Nat.beq bs.length w.byteSize = true := by
        rw [hbs, Anneal.InitLemmas.nat_beq_refl]
      let z :=
        decodeScalar ⟨w, signed, BitVec.ofNat 128 (decodeUInt endian raw)⟩
      have hDecZ : Spec.decodeIntBytes endian signed w bs = some z := by
        unfold Spec.decodeIntBytes
        rw [ite_bool_true hLenEqTrue, hraw]
      cases hz : z with
      | ofNat n =>
        cases n with
        | zero =>
          have hz0 : z = 0 := hz
          rw [hz0] at hDecZ
          exact Or.inl
            ((decodeIntBytes_zero_iff endian signed w hInit).mp hDecZ)
        | succ _ =>
          refine Or.inr ⟨hInit, z, hDecZ, fun hz0 => ?_⟩
          rw [hz] at hz0
          cases hz0
      | negSucc _ =>
        refine Or.inr ⟨hInit, z, hDecZ, fun hz0 => ?_⟩
        rw [hz] at hz0
        cases hz0
    · intro hOr
      cases hOr with
      | inl hNiche => exact ⟨hNiche.1, _, hNiche.2⟩
      | inr hValid => exact hValid.1
  · intro ⟨hNiche, hValid⟩
    have hPair := (nonZeroValid_iff_not_niche endian signed w bs).mp hValid
    exact hPair.2 hNiche
  · intro hUninit
    exact ⟨fun ⟨_, hNiche⟩ => not_mem_uninit_of_initBytes? hNiche hUninit,
      fun ⟨⟨_, _, hraw⟩, _⟩ => not_mem_uninit_of_initBytes? hraw hUninit⟩

/-! ### Alignment Proofs and Multi-Byte Alignment Refutations -/

private theorem multibyte_alignLog2 (w : IntWidth) (hw : w ≠ .i8) :
    0 < (intLayout w).alignLog2 := by
  cases w with
  | i8 => exact False.elim (hw rfl)
  | i16 => decide
  | i32 => decide
  | i64 => decide
  | i128 => decide
  | isize => decide

private theorem nonzero_niche_bit_validity : Spec.NonZeroNicheBitValiditySpec :=
  ⟨fun endian signed w =>
    ⟨rfl,
      intLayout_size_eq_byteSize w,
      fun _ hInit => decodeVal_bridge endian signed w hInit,
      fun _ hInit => decodeIntBytes_zero_iff endian signed w hInit,
      nonZeroValid_iff_not_niche endian signed w,
      fun _ hLen => nonZeroValid_plain_iff endian signed w hLen,
      nonZeroValid_unit_one endian signed w,
      zeroAllocBytes_allInit w.byteSize,
      zeroAllocBytes_isNiche w.byteSize,
      zeroAllocBytes_not_nonZeroValid endian signed w,
      nonZeroIntoBytes_sound endian signed w,
      (nonZeroIntoBytes_witness signed w).1,
      (nonZeroIntoBytes_witness signed w).2,
      optionNonZero_niche_partition endian signed w⟩,
    rfl,
    multibyte_alignLog2⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem all_bodies_verified defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, nonzero_niche_bit_validity⟩
    intro defId identity found
    have hSub := allMarkersAt_getElem all_markers_at defId identity found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
