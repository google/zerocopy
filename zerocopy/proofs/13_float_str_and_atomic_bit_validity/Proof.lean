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
      (idAt 0 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_0, Captured.Shard_000.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m01 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.UnitMarkerAt Captured.program 1
      (idAt 1 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_1, Captured.Shard_000.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m02 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.UnitMarkerAt Captured.program 2
      (idAt 2 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_2, Captured.Shard_000.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m03 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.UnitMarkerAt Captured.program 3
      (idAt 3 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_3, Captured.Shard_000.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m04 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.UnitMarkerAt Captured.program 4
      (idAt 4 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_4, Captured.Shard_000.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m05 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.UnitMarkerAt Captured.program 5
      (idAt 5 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_5, Captured.Shard_000.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m06 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.UnitMarkerAt Captured.program 6
      (idAt 6 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_6, Captured.Shard_000.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m07 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.UnitMarkerAt Captured.program 7
      (idAt 7 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_7, Captured.Shard_000.body_7, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m08 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.UnitMarkerAt Captured.program 8
      (idAt 8 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_8, Captured.Shard_000.body_8, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m09 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.UnitMarkerAt Captured.program 9
      (idAt 9 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_9, Captured.Shard_000.body_9, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.UnitMarkerAt Captured.program 10
      (idAt 10 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_10, Captured.Shard_000.body_10, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.UnitMarkerAt Captured.program 11
      (idAt 11 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_11, Captured.Shard_001.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.UnitMarkerAt Captured.program 12
      (idAt 12 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_12, Captured.Shard_001.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.UnitMarkerAt Captured.program 13
      (idAt 13 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_13, Captured.Shard_001.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.UnitMarkerAt Captured.program 14
      (idAt 14 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_14, Captured.Shard_001.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.UnitMarkerAt Captured.program 15
      (idAt 15 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_15, Captured.Shard_001.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.UnitMarkerAt Captured.program 16
      (idAt 16 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_16, Captured.Shard_001.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.UnitMarkerAt Captured.program 17
      (idAt 17 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_17, Captured.Shard_001.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.UnitMarkerAt Captured.program 18
      (idAt 18 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_18, Captured.Shard_001.body_7, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.UnitMarkerAt Captured.program 19
      (idAt 19 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_19, Captured.Shard_001.body_8, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.UnitMarkerAt Captured.program 20
      (idAt 20 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_20, Captured.Shard_002.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.UnitMarkerAt Captured.program 21
      (idAt 21 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_21, Captured.Shard_002.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.UnitMarkerAt Captured.program 22
      (idAt 22 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_22, Captured.Shard_002.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.UnitMarkerAt Captured.program 23
      (idAt 23 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_23, Captured.Shard_002.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.UnitMarkerAt Captured.program 24
      (idAt 24 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_24, Captured.Shard_002.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.UnitMarkerAt Captured.program 25
      (idAt 25 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_25, Captured.Shard_002.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.UnitMarkerAt Captured.program 26
      (idAt 26 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_26, Captured.Shard_002.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.UnitMarkerAt Captured.program 27
      (idAt 27 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_27, Captured.Shard_003.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.UnitMarkerAt Captured.program 28
      (idAt 28 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_28, Captured.Shard_003.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.UnitMarkerAt Captured.program 29
      (idAt 29 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_29, Captured.Shard_003.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.UnitMarkerAt Captured.program 30
      (idAt 30 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_30, Captured.Shard_003.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.UnitMarkerAt Captured.program 31
      (idAt 31 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_31, Captured.Shard_003.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.UnitMarkerAt Captured.program 32
      (idAt 32 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_32, Captured.Shard_003.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.UnitMarkerAt Captured.program 33
      (idAt 33 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_33, Captured.Shard_003.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.UnitMarkerAt Captured.program 34
      (idAt 34 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_34, Captured.Shard_004.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.UnitMarkerAt Captured.program 35
      (idAt 35 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_35, Captured.Shard_004.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.UnitMarkerAt Captured.program 36
      (idAt 36 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_36, Captured.Shard_004.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.UnitMarkerAt Captured.program 37
      (idAt 37 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_37, Captured.Shard_004.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.UnitMarkerAt Captured.program 38
      (idAt 38 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_38, Captured.Shard_004.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.UnitMarkerAt Captured.program 39
      (idAt 39 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_39, Captured.Shard_004.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.UnitMarkerAt Captured.program 40
      (idAt 40 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_40, Captured.Shard_004.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.UnitMarkerAt Captured.program 41
      (idAt 41 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_41, Captured.Shard_005.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.UnitMarkerAt Captured.program 42
      (idAt 42 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_42, Captured.Shard_005.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.UnitMarkerAt Captured.program 43
      (idAt 43 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_43, Captured.Shard_005.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.UnitMarkerAt Captured.program 44
      (idAt 44 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_44, Captured.Shard_005.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.UnitMarkerAt Captured.program 45
      (idAt 45 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_45, Captured.Shard_005.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.UnitMarkerAt Captured.program 46
      (idAt 46 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_46, Captured.Shard_005.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.UnitMarkerAt Captured.program 47
      (idAt 47 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_47, Captured.Shard_005.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.UnitMarkerAt Captured.program 48
      (idAt 48 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_48, Captured.Shard_005.body_7, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.UnitMarkerAt Captured.program 49
      (idAt 49 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_49, Captured.Shard_006.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.UnitMarkerAt Captured.program 50
      (idAt 50 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_50, Captured.Shard_006.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.UnitMarkerAt Captured.program 51
      (idAt 51 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_51, Captured.Shard_006.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.UnitMarkerAt Captured.program 52
      (idAt 52 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_52, Captured.Shard_006.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.UnitMarkerAt Captured.program 53
      (idAt 53 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_53, Captured.Shard_006.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.UnitMarkerAt Captured.program 54
      (idAt 54 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_54, Captured.Shard_006.body_5, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.UnitMarkerAt Captured.program 55
      (idAt 55 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_55, Captured.Shard_006.body_6, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.UnitMarkerAt Captured.program 56
      (idAt 56 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_56, Captured.Shard_007.body_0, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.UnitMarkerAt Captured.program 57
      (idAt 57 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_57, Captured.Shard_007.body_1, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.UnitMarkerAt Captured.program 58
      (idAt 58 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_58, Captured.Shard_007.body_2, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.UnitMarkerAt Captured.program 59
      (idAt 59 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_59, Captured.Shard_007.body_3, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.UnitMarkerAt Captured.program 60
      (idAt 60 Spec.floatStrAtomicMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_60, Captured.Shard_007.body_4, Spec.floatStrAtomicMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private noncomputable def BodiesVerifiedFrom (program : Program) :
    Nat → List Body → Prop
  | _, [] => True
  | idx, body :: rest =>
    BodyVerified program idx body (Spec.specs.safety body.identity) ∧
      BodiesVerifiedFrom program (idx + 1) rest

private theorem bodiesVerified_nil (idx : Nat) :
    BodiesVerifiedFrom Captured.program idx [] := trivial

private theorem bodiesVerified_cons {idx : Nat} {body : Body}
    {rest : List Body}
    (hHead :
      BodyVerified Captured.program idx body
        (Spec.specs.safety body.identity))
    (hTail : BodiesVerifiedFrom Captured.program (idx + 1) rest) :
    BodiesVerifiedFrom Captured.program idx (body :: rest) :=
  ⟨hHead, hTail⟩

private theorem bodiesVerified_getElem :
    ∀ {bs : List Body} {base : Nat} (i : Nat) (body : Body),
      BodiesVerifiedFrom Captured.program base bs →
      Trusted.MirSemantics.getElem? bs i = some body →
      BodyVerified Captured.program (base + i) body
        (Spec.specs.safety body.identity)
  | [], _, _, _, _, h => by cases h
  | b :: _, base, 0, body, ⟨hHead, _⟩, h => by
    injection h with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hHead
  | _ :: rest, base, i + 1, body, ⟨_, hTail⟩, h => by
    have hSub := bodiesVerified_getElem i body hTail h
    have hIdx : (base + 1) + i = base + (i + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hIdx] at hSub
    exact hSub

private noncomputable def AllMarkersAtFrom (program : Program) :
    Nat → List String → Prop
  | _, [] => True
  | idx, identity :: rest =>
    Spec.UnitMarkerAt program idx identity ∧
      AllMarkersAtFrom program (idx + 1) rest

private theorem allMarkersAt_nil (idx : Nat) :
    AllMarkersAtFrom Captured.program idx [] := trivial

private theorem allMarkersAt_cons {idx : Nat} {identity : String}
    {rest : List String}
    (hHead : Spec.UnitMarkerAt Captured.program idx identity)
    (hTail : AllMarkersAtFrom Captured.program (idx + 1) rest) :
    AllMarkersAtFrom Captured.program idx (identity :: rest) :=
  ⟨hHead, hTail⟩

private theorem allMarkersAt_getElem :
    ∀ {ids : List String} {base : Nat} (i : Nat) (identity : String),
      AllMarkersAtFrom Captured.program base ids →
      Trusted.MirSemantics.getElem? ids i = some identity →
      Spec.UnitMarkerAt Captured.program (base + i) identity
  | [], _, _, _, _, h => by cases h
  | id0 :: _, base, 0, identity, ⟨hHead, _⟩, h => by
    injection h with hEq
    subst hEq
    rw [Nat.add_zero]
    exact hHead
  | _ :: rest, base, i + 1, identity, ⟨_, hTail⟩, h => by
    have hSub := allMarkersAt_getElem i identity hTail h
    have hIdx : (base + 1) + i = base + (i + 1) := by
      rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hIdx] at hSub
    exact hSub

private theorem all_bodies_verified :
    BodiesVerifiedFrom Captured.program 0 Captured.program.bodies := by
  refine bodiesVerified_cons m00.1 ?_
  refine bodiesVerified_cons m01.1 ?_
  refine bodiesVerified_cons m02.1 ?_
  refine bodiesVerified_cons m03.1 ?_
  refine bodiesVerified_cons m04.1 ?_
  refine bodiesVerified_cons m05.1 ?_
  refine bodiesVerified_cons m06.1 ?_
  refine bodiesVerified_cons m07.1 ?_
  refine bodiesVerified_cons m08.1 ?_
  refine bodiesVerified_cons m09.1 ?_
  refine bodiesVerified_cons m10.1 ?_
  refine bodiesVerified_cons m11.1 ?_
  refine bodiesVerified_cons m12.1 ?_
  refine bodiesVerified_cons m13.1 ?_
  refine bodiesVerified_cons m14.1 ?_
  refine bodiesVerified_cons m15.1 ?_
  refine bodiesVerified_cons m16.1 ?_
  refine bodiesVerified_cons m17.1 ?_
  refine bodiesVerified_cons m18.1 ?_
  refine bodiesVerified_cons m19.1 ?_
  refine bodiesVerified_cons m20.1 ?_
  refine bodiesVerified_cons m21.1 ?_
  refine bodiesVerified_cons m22.1 ?_
  refine bodiesVerified_cons m23.1 ?_
  refine bodiesVerified_cons m24.1 ?_
  refine bodiesVerified_cons m25.1 ?_
  refine bodiesVerified_cons m26.1 ?_
  refine bodiesVerified_cons m27.1 ?_
  refine bodiesVerified_cons m28.1 ?_
  refine bodiesVerified_cons m29.1 ?_
  refine bodiesVerified_cons m30.1 ?_
  refine bodiesVerified_cons m31.1 ?_
  refine bodiesVerified_cons m32.1 ?_
  refine bodiesVerified_cons m33.1 ?_
  refine bodiesVerified_cons m34.1 ?_
  refine bodiesVerified_cons m35.1 ?_
  refine bodiesVerified_cons m36.1 ?_
  refine bodiesVerified_cons m37.1 ?_
  refine bodiesVerified_cons m38.1 ?_
  refine bodiesVerified_cons m39.1 ?_
  refine bodiesVerified_cons m40.1 ?_
  refine bodiesVerified_cons m41.1 ?_
  refine bodiesVerified_cons m42.1 ?_
  refine bodiesVerified_cons m43.1 ?_
  refine bodiesVerified_cons m44.1 ?_
  refine bodiesVerified_cons m45.1 ?_
  refine bodiesVerified_cons m46.1 ?_
  refine bodiesVerified_cons m47.1 ?_
  refine bodiesVerified_cons m48.1 ?_
  refine bodiesVerified_cons m49.1 ?_
  refine bodiesVerified_cons m50.1 ?_
  refine bodiesVerified_cons m51.1 ?_
  refine bodiesVerified_cons m52.1 ?_
  refine bodiesVerified_cons m53.1 ?_
  refine bodiesVerified_cons m54.1 ?_
  refine bodiesVerified_cons m55.1 ?_
  refine bodiesVerified_cons m56.1 ?_
  refine bodiesVerified_cons m57.1 ?_
  refine bodiesVerified_cons m58.1 ?_
  refine bodiesVerified_cons m59.1 ?_
  refine bodiesVerified_cons m60.1 ?_
  exact bodiesVerified_nil _

private theorem all_markers_at :
    AllMarkersAtFrom Captured.program 0
      Spec.floatStrAtomicMarkerIdentities := by
  refine allMarkersAt_cons m00.2 ?_
  refine allMarkersAt_cons m01.2 ?_
  refine allMarkersAt_cons m02.2 ?_
  refine allMarkersAt_cons m03.2 ?_
  refine allMarkersAt_cons m04.2 ?_
  refine allMarkersAt_cons m05.2 ?_
  refine allMarkersAt_cons m06.2 ?_
  refine allMarkersAt_cons m07.2 ?_
  refine allMarkersAt_cons m08.2 ?_
  refine allMarkersAt_cons m09.2 ?_
  refine allMarkersAt_cons m10.2 ?_
  refine allMarkersAt_cons m11.2 ?_
  refine allMarkersAt_cons m12.2 ?_
  refine allMarkersAt_cons m13.2 ?_
  refine allMarkersAt_cons m14.2 ?_
  refine allMarkersAt_cons m15.2 ?_
  refine allMarkersAt_cons m16.2 ?_
  refine allMarkersAt_cons m17.2 ?_
  refine allMarkersAt_cons m18.2 ?_
  refine allMarkersAt_cons m19.2 ?_
  refine allMarkersAt_cons m20.2 ?_
  refine allMarkersAt_cons m21.2 ?_
  refine allMarkersAt_cons m22.2 ?_
  refine allMarkersAt_cons m23.2 ?_
  refine allMarkersAt_cons m24.2 ?_
  refine allMarkersAt_cons m25.2 ?_
  refine allMarkersAt_cons m26.2 ?_
  refine allMarkersAt_cons m27.2 ?_
  refine allMarkersAt_cons m28.2 ?_
  refine allMarkersAt_cons m29.2 ?_
  refine allMarkersAt_cons m30.2 ?_
  refine allMarkersAt_cons m31.2 ?_
  refine allMarkersAt_cons m32.2 ?_
  refine allMarkersAt_cons m33.2 ?_
  refine allMarkersAt_cons m34.2 ?_
  refine allMarkersAt_cons m35.2 ?_
  refine allMarkersAt_cons m36.2 ?_
  refine allMarkersAt_cons m37.2 ?_
  refine allMarkersAt_cons m38.2 ?_
  refine allMarkersAt_cons m39.2 ?_
  refine allMarkersAt_cons m40.2 ?_
  refine allMarkersAt_cons m41.2 ?_
  refine allMarkersAt_cons m42.2 ?_
  refine allMarkersAt_cons m43.2 ?_
  refine allMarkersAt_cons m44.2 ?_
  refine allMarkersAt_cons m45.2 ?_
  refine allMarkersAt_cons m46.2 ?_
  refine allMarkersAt_cons m47.2 ?_
  refine allMarkersAt_cons m48.2 ?_
  refine allMarkersAt_cons m49.2 ?_
  refine allMarkersAt_cons m50.2 ?_
  refine allMarkersAt_cons m51.2 ?_
  refine allMarkersAt_cons m52.2 ?_
  refine allMarkersAt_cons m53.2 ?_
  refine allMarkersAt_cons m54.2 ?_
  refine allMarkersAt_cons m55.2 ?_
  refine allMarkersAt_cons m56.2 ?_
  refine allMarkersAt_cons m57.2 ?_
  refine allMarkersAt_cons m58.2 ?_
  refine allMarkersAt_cons m59.2 ?_
  refine allMarkersAt_cons m60.2 ?_
  exact allMarkersAt_nil _

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: Model-Side Float, UTF-8 `str`, and `Atomic*` Proofs -/

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

private theorem initBytes?_replicate_init (b : UInt8) :
    ∀ (n : Nat),
      initBytes? (List.replicate n (AllocByte.init b none)) =
        some (List.replicate n b)
  | 0 => rfl
  | n + 1 => by
    unfold List.replicate initBytes?
    rw [initBytes?_replicate_init b n]

private theorem not_mem_uninit_of_initBytes? :
    ∀ {bs : List AllocByte} {raw : List UInt8},
      initBytes? bs = some raw → AllocByte.uninit ∉ bs
  | [], _, _, hMem => by cases hMem
  | .uninit :: _, _, h, _ => by cases h
  | .init _ _ :: rest, _, h, hMem => by
    unfold initBytes? at h
    cases hRest : initBytes? rest with
    | none => rw [hRest] at h; cases h
    | some _ =>
      cases hMem with
      | tail _ hTail => exact not_mem_uninit_of_initBytes? hRest hTail

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

/-! ### Section 2B Proofs: RFC 3629 UTF-8 DFA, Grammar, and Refutations -/

private theorem nat_eq_of_beq :
    ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by cases h
  | _ + 1, 0, h => by cases h
  | a + 1, b + 1, h => congrArg Nat.succ (nat_eq_of_beq h)

private theorem nat_le_of_ble :
    ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | a + 1, b + 1, h => Nat.succ_le_succ (nat_le_of_ble h)

private theorem bool_and_true_iff {a b : Bool} :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem bool_or_true_iff {a b : Bool} :
    (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

private theorem inByteRange_lo {lo hi : Nat} {b : UInt8}
    (h : Spec.inByteRange lo hi b = true) : lo ≤ b.toNat :=
  nat_le_of_ble (bool_and_true_iff.mp h).1

private theorem inByteRange_hi {lo hi : Nat} {b : UInt8}
    (h : Spec.inByteRange lo hi b = true) : b.toNat ≤ hi :=
  nat_le_of_ble (bool_and_true_iff.mp h).2

private theorem nat_ble_false_of_lt {a b : Nat} (hLt : b < a) :
    Nat.ble a b = false := by
  cases h : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_le_of_gt hLt (nat_le_of_ble h))

private theorem nat_beq_false_of_ne {a b : Nat} (hNe : a ≠ b) :
    Nat.beq a b = false := by
  cases h : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (hNe (nat_eq_of_beq h))

private theorem inByteRange_false_of_gt_hi {lo hi : Nat} {b : UInt8}
    (hGt : hi < b.toNat) : Spec.inByteRange lo hi b = false := by
  unfold Spec.inByteRange
  rw [nat_ble_false_of_lt hGt]
  cases Nat.ble lo b.toNat <;> rfl

private theorem uint8_eq_of_toNat_beq {b : UInt8} {k : Nat}
    (hk : k < 256) (hBeq : Nat.beq b.toNat k = true) :
    b = UInt8.ofNat k := by
  have hEq : b.toNat = k := nat_eq_of_beq hBeq
  cases b with
  | ofBitVec bv =>
    cases bv with
    | ofFin fn =>
      apply congrArg UInt8.ofBitVec
      apply congrArg BitVec.ofFin
      apply Fin.eq_of_val_eq
      change fn.val = (UInt8.ofNat k).toNat
      rw [show fn.val = k from hEq]
      exact (Nat.mod_eq_of_lt hk).symm

private theorem utf8Step_0_twoByte {b₀ : UInt8}
    (h0 : Spec.inByteRange 0xC2 0xDF b₀ = true) :
    Spec.utf8Step 0 b₀ = 1 := by
  have hLo := inByteRange_lo h0
  have hGt7F : 0x7F < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0x7F < 0xC2) hLo
  have hStep : Spec.utf8Step 0 b₀ =
      (if Nat.ble b₀.toNat 0x7F then 0
      else if Spec.inByteRange 0xC2 0xDF b₀ then 1
      else if Nat.beq b₀.toNat 0xE0 then 2
      else if Spec.inByteRange 0xE1 0xEC b₀ ||
          Spec.inByteRange 0xEE 0xEF b₀ then 3
      else if Nat.beq b₀.toNat 0xED then 4
      else if Nat.beq b₀.toNat 0xF0 then 5
      else if Spec.inByteRange 0xF1 0xF3 b₀ then 6
      else if Nat.beq b₀.toNat 0xF4 then 7
      else 8) := rfl
  rw [hStep, ite_bool_false (nat_ble_false_of_lt hGt7F), ite_bool_true h0]

private theorem utf8Step_0_threeStd {b₀ : UInt8}
    (h0 : (Spec.inByteRange 0xE1 0xEC b₀ ||
      Spec.inByteRange 0xEE 0xEF b₀) = true) :
    Spec.utf8Step 0 b₀ = 3 := by
  have hGeE1 : 0xE1 ≤ b₀.toNat := by
    cases bool_or_true_iff.mp h0 with
    | inl hL => exact inByteRange_lo hL
    | inr hR =>
      exact Nat.le_trans (by decide : 0xE1 ≤ 0xEE) (inByteRange_lo hR)
  have hGt7F : 0x7F < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0x7F < 0xE1) hGeE1
  have hGtDF : 0xDF < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0xDF < 0xE1) hGeE1
  have hNeE0 : b₀.toNat ≠ 0xE0 := fun hEq => by
    rw [hEq] at hGeE1
    exact Nat.not_le_of_gt (by decide : 0xE0 < 0xE1) hGeE1
  have hStep : Spec.utf8Step 0 b₀ =
      (if Nat.ble b₀.toNat 0x7F then 0
      else if Spec.inByteRange 0xC2 0xDF b₀ then 1
      else if Nat.beq b₀.toNat 0xE0 then 2
      else if Spec.inByteRange 0xE1 0xEC b₀ ||
          Spec.inByteRange 0xEE 0xEF b₀ then 3
      else if Nat.beq b₀.toNat 0xED then 4
      else if Nat.beq b₀.toNat 0xF0 then 5
      else if Spec.inByteRange 0xF1 0xF3 b₀ then 6
      else if Nat.beq b₀.toNat 0xF4 then 7
      else 8) := rfl
  rw [hStep,
    ite_bool_false (nat_ble_false_of_lt hGt7F),
    ite_bool_false (inByteRange_false_of_gt_hi hGtDF),
    ite_bool_false (nat_beq_false_of_ne hNeE0),
    ite_bool_true h0]

private theorem utf8Step_0_fourStd {b₀ : UInt8}
    (h0 : Spec.inByteRange 0xF1 0xF3 b₀ = true) :
    Spec.utf8Step 0 b₀ = 6 := by
  have hLo := inByteRange_lo h0
  have hGt7F : 0x7F < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0x7F < 0xF1) hLo
  have hGtDF : 0xDF < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0xDF < 0xF1) hLo
  have hGtEC : 0xEC < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0xEC < 0xF1) hLo
  have hGtEF : 0xEF < b₀.toNat :=
    Nat.lt_of_lt_of_le (by decide : 0xEF < 0xF1) hLo
  have hNeE0 : b₀.toNat ≠ 0xE0 := fun hEq => by
    rw [hEq] at hLo
    exact Nat.not_le_of_gt (by decide : 0xE0 < 0xF1) hLo
  have hNeED : b₀.toNat ≠ 0xED := fun hEq => by
    rw [hEq] at hLo
    exact Nat.not_le_of_gt (by decide : 0xED < 0xF1) hLo
  have hNeF0 : b₀.toNat ≠ 0xF0 := fun hEq => by
    rw [hEq] at hLo
    exact Nat.not_le_of_gt (by decide : 0xF0 < 0xF1) hLo
  have hThreeStd : (Spec.inByteRange 0xE1 0xEC b₀ ||
      Spec.inByteRange 0xEE 0xEF b₀) = false := by
    rw [inByteRange_false_of_gt_hi hGtEC, inByteRange_false_of_gt_hi hGtEF]
    rfl
  have hStep : Spec.utf8Step 0 b₀ =
      (if Nat.ble b₀.toNat 0x7F then 0
      else if Spec.inByteRange 0xC2 0xDF b₀ then 1
      else if Nat.beq b₀.toNat 0xE0 then 2
      else if Spec.inByteRange 0xE1 0xEC b₀ ||
          Spec.inByteRange 0xEE 0xEF b₀ then 3
      else if Nat.beq b₀.toNat 0xED then 4
      else if Nat.beq b₀.toNat 0xF0 then 5
      else if Spec.inByteRange 0xF1 0xF3 b₀ then 6
      else if Nat.beq b₀.toNat 0xF4 then 7
      else 8) := rfl
  rw [hStep,
    ite_bool_false (nat_ble_false_of_lt hGt7F),
    ite_bool_false (inByteRange_false_of_gt_hi hGtDF),
    ite_bool_false (nat_beq_false_of_ne hNeE0),
    ite_bool_false hThreeStd,
    ite_bool_false (nat_beq_false_of_ne hNeED),
    ite_bool_false (nat_beq_false_of_ne hNeF0),
    ite_bool_true h0]

private theorem foldl_utf8Step_invalid :
    ∀ (raw : List UInt8), raw.foldl Spec.utf8Step 8 = 8
  | [] => rfl
  | _ :: rest => foldl_utf8Step_invalid rest

private theorem peel_state_1 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 1) 0 = true) :
    ∃ b rest, xs = b :: rest ∧ Spec.inByteRange 0x80 0xBF b = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b rest =>
    have h1 : Spec.utf8Step 1 b =
        (if Spec.inByteRange 0x80 0xBF b then 0 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h1] at h
    cases hb : Spec.inByteRange 0x80 0xBF b with
    | false =>
      rw [ite_bool_false hb, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb] at h
      exact ⟨b, rest, rfl, hb, h⟩

private theorem peel_state_3 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 3) 0 = true) :
    ∃ b₁ b₂ rest, xs = b₁ :: b₂ :: rest ∧
      Spec.inByteRange 0x80 0xBF b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h3 : Spec.utf8Step 3 b₁ =
        (if Spec.inByteRange 0x80 0xBF b₁ then 1 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h3] at h
    cases hb1 : Spec.inByteRange 0x80 0xBF b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, rest, hEq, hb2, hRest⟩ := peel_state_1 h
      subst hEq
      exact ⟨b₁, b₂, rest, rfl, hb1, hb2, hRest⟩

private theorem peel_state_2 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 2) 0 = true) :
    ∃ b₁ b₂ rest, xs = b₁ :: b₂ :: rest ∧
      Spec.inByteRange 0xA0 0xBF b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h2 : Spec.utf8Step 2 b₁ =
        (if Spec.inByteRange 0xA0 0xBF b₁ then 1 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h2] at h
    cases hb1 : Spec.inByteRange 0xA0 0xBF b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, rest, hEq, hb2, hRest⟩ := peel_state_1 h
      subst hEq
      exact ⟨b₁, b₂, rest, rfl, hb1, hb2, hRest⟩

private theorem peel_state_4 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 4) 0 = true) :
    ∃ b₁ b₂ rest, xs = b₁ :: b₂ :: rest ∧
      Spec.inByteRange 0x80 0x9F b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h4 : Spec.utf8Step 4 b₁ =
        (if Spec.inByteRange 0x80 0x9F b₁ then 1 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h4] at h
    cases hb1 : Spec.inByteRange 0x80 0x9F b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, rest, hEq, hb2, hRest⟩ := peel_state_1 h
      subst hEq
      exact ⟨b₁, b₂, rest, rfl, hb1, hb2, hRest⟩

private theorem peel_state_5 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 5) 0 = true) :
    ∃ b₁ b₂ b₃ rest, xs = b₁ :: b₂ :: b₃ :: rest ∧
      Spec.inByteRange 0x90 0xBF b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.inByteRange 0x80 0xBF b₃ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h5 : Spec.utf8Step 5 b₁ =
        (if Spec.inByteRange 0x90 0xBF b₁ then 3 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h5] at h
    cases hb1 : Spec.inByteRange 0x90 0xBF b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, b₃, rest, hEq, hb2, hb3, hRest⟩ := peel_state_3 h
      subst hEq
      exact ⟨b₁, b₂, b₃, rest, rfl, hb1, hb2, hb3, hRest⟩

private theorem peel_state_6 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 6) 0 = true) :
    ∃ b₁ b₂ b₃ rest, xs = b₁ :: b₂ :: b₃ :: rest ∧
      Spec.inByteRange 0x80 0xBF b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.inByteRange 0x80 0xBF b₃ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h6 : Spec.utf8Step 6 b₁ =
        (if Spec.inByteRange 0x80 0xBF b₁ then 3 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h6] at h
    cases hb1 : Spec.inByteRange 0x80 0xBF b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, b₃, rest, hEq, hb2, hb3, hRest⟩ := peel_state_3 h
      subst hEq
      exact ⟨b₁, b₂, b₃, rest, rfl, hb1, hb2, hb3, hRest⟩

private theorem peel_state_7 {xs : List UInt8}
    (h : Nat.beq (xs.foldl Spec.utf8Step 7) 0 = true) :
    ∃ b₁ b₂ b₃ rest, xs = b₁ :: b₂ :: b₃ :: rest ∧
      Spec.inByteRange 0x80 0x8F b₁ = true ∧
      Spec.inByteRange 0x80 0xBF b₂ = true ∧
      Spec.inByteRange 0x80 0xBF b₃ = true ∧
      Spec.IsValidUtf8Bytes rest = true := by
  cases xs with
  | nil => cases h
  | cons b₁ rest₁ =>
    have h7 : Spec.utf8Step 7 b₁ =
        (if Spec.inByteRange 0x80 0x8F b₁ then 3 else 8) := rfl
    dsimp only [List.foldl] at h
    rw [h7] at h
    cases hb1 : Spec.inByteRange 0x80 0x8F b₁ with
    | false =>
      rw [ite_bool_false hb1, foldl_utf8Step_invalid] at h
      cases h
    | true =>
      rw [ite_bool_true hb1] at h
      let ⟨b₂, b₃, rest, hEq, hb2, hb3, hRest⟩ := peel_state_3 h
      subst hEq
      exact ⟨b₁, b₂, b₃, rest, rfl, hb1, hb2, hb3, hRest⟩

private theorem utf8Step_1_true {b : UInt8}
    (h : Spec.inByteRange 0x80 0xBF b = true) :
    Spec.utf8Step 1 b = 0 := by
  have hs : Spec.utf8Step 1 b =
      (if Spec.inByteRange 0x80 0xBF b then 0 else 8) := rfl
  rw [hs, ite_bool_true h]

private theorem utf8Step_3_true {b : UInt8}
    (h : Spec.inByteRange 0x80 0xBF b = true) :
    Spec.utf8Step 3 b = 1 := by
  have hs : Spec.utf8Step 3 b =
      (if Spec.inByteRange 0x80 0xBF b then 1 else 8) := rfl
  rw [hs, ite_bool_true h]

private theorem validUtf8_iff_stepDecomp (raw : List UInt8) :
    Spec.IsValidUtf8Bytes raw = true ↔ Spec.ValidUtf8StepDecomp raw := by
  constructor
  · intro hValid
    cases raw with
    | nil => exact Or.inl rfl
    | cons b₀ xs =>
      unfold Spec.IsValidUtf8Bytes at hValid
      dsimp only [List.foldl] at hValid
      have h0Step : Spec.utf8Step 0 b₀ =
          (if Nat.ble b₀.toNat 0x7F then 0
          else if Spec.inByteRange 0xC2 0xDF b₀ then 1
          else if Nat.beq b₀.toNat 0xE0 then 2
          else if Spec.inByteRange 0xE1 0xEC b₀ ||
              Spec.inByteRange 0xEE 0xEF b₀ then 3
          else if Nat.beq b₀.toNat 0xED then 4
          else if Nat.beq b₀.toNat 0xF0 then 5
          else if Spec.inByteRange 0xF1 0xF3 b₀ then 6
          else if Nat.beq b₀.toNat 0xF4 then 7
          else 8) := rfl
      rw [h0Step] at hValid
      cases c1 : Nat.ble b₀.toNat 0x7F with
      | true =>
        rw [ite_bool_true c1] at hValid
        exact Or.inr (Or.inl ⟨b₀, xs, rfl, c1, hValid⟩)
      | false =>
        rw [ite_bool_false c1] at hValid
        cases c2 : Spec.inByteRange 0xC2 0xDF b₀ with
        | true =>
          rw [ite_bool_true c2] at hValid
          let ⟨b₁, rest, hEq, hb1, hRest⟩ := peel_state_1 hValid
          subst hEq
          exact Or.inr (Or.inr (Or.inl ⟨b₀, b₁, rest, rfl, c2, hb1, hRest⟩))
        | false =>
          rw [ite_bool_false c2] at hValid
          cases c3 : Nat.beq b₀.toNat 0xE0 with
          | true =>
            rw [ite_bool_true c3] at hValid
            have hb0 := uint8_eq_of_toNat_beq (by decide : 0xE0 < 256) c3
            subst hb0
            let ⟨b₁, b₂, rest, hEq, hb1, hb2, hRest⟩ := peel_state_2 hValid
            subst hEq
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨b₁, b₂, rest, rfl, hb1, hb2, hRest⟩)))
          | false =>
            rw [ite_bool_false c3] at hValid
            cases c4 : (Spec.inByteRange 0xE1 0xEC b₀ ||
                Spec.inByteRange 0xEE 0xEF b₀) with
            | true =>
              rw [ite_bool_true c4] at hValid
              let ⟨b₁, b₂, rest, hEq, hb1, hb2, hRest⟩ := peel_state_3 hValid
              subst hEq
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨b₀, b₁, b₂, rest, rfl, c4, hb1, hb2, hRest⟩))))
            | false =>
              rw [ite_bool_false c4] at hValid
              cases c5 : Nat.beq b₀.toNat 0xED with
              | true =>
                rw [ite_bool_true c5] at hValid
                have hb0 := uint8_eq_of_toNat_beq (by decide : 0xED < 256) c5
                subst hb0
                let ⟨b₁, b₂, rest, hEq, hb1, hb2, hRest⟩ := peel_state_4 hValid
                subst hEq
                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨b₁, b₂, rest, rfl, hb1, hb2, hRest⟩)))))
              | false =>
                rw [ite_bool_false c5] at hValid
                cases c6 : Nat.beq b₀.toNat 0xF0 with
                | true =>
                  rw [ite_bool_true c6] at hValid
                  have hb0 := uint8_eq_of_toNat_beq (by decide : 0xF0 < 256) c6
                  subst hb0
                  let ⟨b₁, b₂, b₃, rest, hEq, hb1, hb2, hb3, hRest⟩ :=
                    peel_state_5 hValid
                  subst hEq
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨b₁, b₂, b₃, rest, rfl, hb1, hb2, hb3, hRest⟩))))))
                | false =>
                  rw [ite_bool_false c6] at hValid
                  cases c7 : Spec.inByteRange 0xF1 0xF3 b₀ with
                  | true =>
                    rw [ite_bool_true c7] at hValid
                    let ⟨b₁, b₂, b₃, rest, hEq, hb1, hb2, hb3, hRest⟩ :=
                      peel_state_6 hValid
                    subst hEq
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inl
                        ⟨b₀, b₁, b₂, b₃, rest, rfl, c7, hb1, hb2, hb3,
                          hRest⟩)))))))
                  | false =>
                    rw [ite_bool_false c7] at hValid
                    cases c8 : Nat.beq b₀.toNat 0xF4 with
                    | true =>
                      rw [ite_bool_true c8] at hValid
                      have hb0 :=
                        uint8_eq_of_toNat_beq (by decide : 0xF4 < 256) c8
                      subst hb0
                      let ⟨b₁, b₂, b₃, rest, hEq, hb1, hb2, hb3, hRest⟩ :=
                        peel_state_7 hValid
                      subst hEq
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr
                          ⟨b₁, b₂, b₃, rest, rfl, hb1, hb2, hb3, hRest⟩)))))))
                    | false =>
                      rw [ite_bool_false c8, foldl_utf8Step_invalid] at hValid
                      cases hValid
  · intro hDecomp
    cases hDecomp with
    | inl hNil => subst hNil; rfl
    | inr h1 =>
      cases h1 with
      | inl hAscii =>
        let ⟨b₀, rest, hEq, h0, hRest⟩ := hAscii
        subst hEq
        unfold Spec.IsValidUtf8Bytes
        dsimp only [List.foldl]
        have hs : Spec.utf8Step 0 b₀ = 0 := by
          have hStep : Spec.utf8Step 0 b₀ =
              (if Nat.ble b₀.toNat 0x7F then 0
              else if Spec.inByteRange 0xC2 0xDF b₀ then 1
              else if Nat.beq b₀.toNat 0xE0 then 2
              else if Spec.inByteRange 0xE1 0xEC b₀ ||
                  Spec.inByteRange 0xEE 0xEF b₀ then 3
              else if Nat.beq b₀.toNat 0xED then 4
              else if Nat.beq b₀.toNat 0xF0 then 5
              else if Spec.inByteRange 0xF1 0xF3 b₀ then 6
              else if Nat.beq b₀.toNat 0xF4 then 7
              else 8) := rfl
          rw [hStep, ite_bool_true h0]
        rw [hs]
        exact hRest
      | inr h2 =>
        cases h2 with
        | inl hTwo =>
          let ⟨b₀, b₁, rest, hEq, h0, h1, hRest⟩ := hTwo
          subst hEq
          unfold Spec.IsValidUtf8Bytes
          dsimp only [List.foldl]
          rw [utf8Step_0_twoByte h0, utf8Step_1_true h1]
          exact hRest
        | inr h3 =>
          cases h3 with
          | inl hE0 =>
            let ⟨b₁, b₂, rest, hEq, h1, h2, hRest⟩ := hE0
            subst hEq
            unfold Spec.IsValidUtf8Bytes
            dsimp only [List.foldl]
            have hs0 : Spec.utf8Step 0 0xE0 = 2 := rfl
            have hs1 : Spec.utf8Step 2 b₁ = 1 := by
              have hStep : Spec.utf8Step 2 b₁ =
                  (if Spec.inByteRange 0xA0 0xBF b₁ then 1 else 8) := rfl
              rw [hStep, ite_bool_true h1]
            rw [hs0, hs1, utf8Step_1_true h2]
            exact hRest
          | inr h4 =>
            cases h4 with
            | inl hThreeStd =>
              let ⟨b₀, b₁, b₂, rest, hEq, h0, h1, h2, hRest⟩ := hThreeStd
              subst hEq
              unfold Spec.IsValidUtf8Bytes
              dsimp only [List.foldl]
              rw [utf8Step_0_threeStd h0, utf8Step_3_true h1,
                utf8Step_1_true h2]
              exact hRest
            | inr h5 =>
              cases h5 with
              | inl hEd =>
                let ⟨b₁, b₂, rest, hEq, h1, h2, hRest⟩ := hEd
                subst hEq
                unfold Spec.IsValidUtf8Bytes
                dsimp only [List.foldl]
                have hs0 : Spec.utf8Step 0 0xED = 4 := rfl
                have hs1 : Spec.utf8Step 4 b₁ = 1 := by
                  have hStep : Spec.utf8Step 4 b₁ =
                      (if Spec.inByteRange 0x80 0x9F b₁ then 1 else 8) := rfl
                  rw [hStep, ite_bool_true h1]
                rw [hs0, hs1, utf8Step_1_true h2]
                exact hRest
              | inr h6 =>
                cases h6 with
                | inl hF0 =>
                  let ⟨b₁, b₂, b₃, rest, hEq, h1, h2, h3, hRest⟩ := hF0
                  subst hEq
                  unfold Spec.IsValidUtf8Bytes
                  dsimp only [List.foldl]
                  have hs0 : Spec.utf8Step 0 0xF0 = 5 := rfl
                  have hs1 : Spec.utf8Step 5 b₁ = 3 := by
                    have hStep : Spec.utf8Step 5 b₁ =
                        (if Spec.inByteRange 0x90 0xBF b₁ then 3 else 8) := rfl
                    rw [hStep, ite_bool_true h1]
                  rw [hs0, hs1, utf8Step_3_true h2, utf8Step_1_true h3]
                  exact hRest
                | inr h7 =>
                  cases h7 with
                  | inl hFourStd =>
                    let ⟨b₀, b₁, b₂, b₃, rest, hEq, h0, h1, h2, h3, hRest⟩ :=
                      hFourStd
                    subst hEq
                    unfold Spec.IsValidUtf8Bytes
                    dsimp only [List.foldl]
                    have hs1 : Spec.utf8Step 6 b₁ = 3 := by
                      have hStep : Spec.utf8Step 6 b₁ =
                          (if Spec.inByteRange 0x80 0xBF b₁ then 3
                            else 8) := rfl
                      rw [hStep, ite_bool_true h1]
                    rw [utf8Step_0_fourStd h0, hs1, utf8Step_3_true h2,
                      utf8Step_1_true h3]
                    exact hRest
                  | inr hF4 =>
                    let ⟨b₁, b₂, b₃, rest, hEq, h1, h2, h3, hRest⟩ := hF4
                    subst hEq
                    unfold Spec.IsValidUtf8Bytes
                    dsimp only [List.foldl]
                    have hs0 : Spec.utf8Step 0 0xF4 = 7 := rfl
                    have hs1 : Spec.utf8Step 7 b₁ = 3 := by
                      have hStep : Spec.utf8Step 7 b₁ =
                          (if Spec.inByteRange 0x80 0x8F b₁ then 3
                            else 8) := rfl
                      rw [hStep, ite_bool_true h1]
                    rw [hs0, hs1, utf8Step_3_true h2, utf8Step_1_true h3]
                    exact hRest

private theorem foldl_append {α β : Type} (f : α → β → α) :
    ∀ (xs ys : List β) (init : α),
      (xs ++ ys).foldl f init = ys.foldl f (xs.foldl f init)
  | [], _, _ => rfl
  | x :: xs, ys, init => foldl_append f xs ys (f init x)

private theorem validUtf8_append (raw₁ raw₂ : List UInt8)
    (h₁ : Spec.IsValidUtf8Bytes raw₁ = true)
    (h₂ : Spec.IsValidUtf8Bytes raw₂ = true) :
    Spec.IsValidUtf8Bytes (raw₁ ++ raw₂) = true := by
  have hR₁ : raw₁.foldl Spec.utf8Step 0 = 0 := nat_eq_of_beq h₁
  unfold Spec.IsValidUtf8Bytes
  rw [foldl_append, hR₁]
  exact h₂

private theorem foldl_replicate_zero :
    ∀ (n : Nat),
      (List.replicate n (0 : UInt8)).foldl Spec.utf8Step 0 = 0
  | 0 => rfl
  | n + 1 => foldl_replicate_zero n

private theorem str_fromZeros_sound : Spec.StrFromZerosSound := by
  intro n
  refine ⟨List.replicate n 0, initBytes?_replicate_init 0 n, ?_⟩
  unfold Spec.IsValidUtf8Bytes
  rw [foldl_replicate_zero n]
  rfl

private theorem initBytes?_inj {bs : List AllocByte} {r₁ r₂ : List UInt8}
    (h₁ : initBytes? bs = some r₁) (h₂ : initBytes? bs = some r₂) :
    r₁ = r₂ := by
  rw [h₁] at h₂
  injection h₂

private theorem str_not_fromBytes_replicate_ff (n : Nat) :
    Spec.AllInitBytes (n + 1)
        (List.replicate (n + 1) (AllocByte.init 0xFF none)) ∧
    ¬ Spec.IsValidUtf8AllocBytes
        (List.replicate (n + 1) (AllocByte.init 0xFF none)) := by
  have hInit := initBytes?_replicate_init 0xFF (n + 1)
  refine ⟨⟨list_length_replicate (n + 1) (AllocByte.init 0xFF none),
      List.replicate (n + 1) 0xFF, hInit⟩,
    fun ⟨raw, hraw, hValid⟩ => ?_⟩
  have hEq : raw = List.replicate (n + 1) 0xFF := initBytes?_inj hraw hInit
  subst hEq
  unfold Spec.IsValidUtf8Bytes at hValid
  have hFold :
      (List.replicate (n + 1) (0xFF : UInt8)).foldl Spec.utf8Step 0 =
        (List.replicate n (0xFF : UInt8)).foldl Spec.utf8Step 8 := rfl
  rw [hFold, foldl_utf8Step_invalid] at hValid
  cases hValid

/-! ### Section 2C Proofs: `Atomic*` Backing Scalars & `UnsafeCell` Laws -/

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

private theorem decodeUInt_singleton (endian : TargetEndian) (b : UInt8) :
    decodeUInt endian [b] = b.toNat := by
  cases endian <;> (
    dsimp only [decodeUInt, List.reverse, List.reverseAux, natOfLeBytes]
    rw [Nat.mul_zero, Nat.add_zero]
  )

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

private theorem checkVal_bool_inv {v : Val} (h : checkVal v .bool = true) :
    ∃ b : Bool, v = .bool b := by
  have hTy := checkVal_iff_ty?.mp h
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | unit | char _ | ordering _ | ptr _ | slicePtr _ _ | rangeTo _
  | rangeFrom _ | range _ _ | optionVal _ | array _ | bytes _ => cases hTy
  | scalar sv =>
    dsimp only [Val.ty?] at hTy
    cases hWf : sv.wf <;> rw [hWf] at hTy <;> cases hTy
  | enumVal ety idx =>
    dsimp only [Val.ty?] at hTy
    cases hE : (enumAdmitted ety && Nat.blt idx ety.discriminants.length) <;>
      rw [hE] at hTy <;> cases hTy
  | tuple fs =>
    let ⟨_, hEq⟩ := Val.ty?_tuple_some hTy
    cases hEq

private theorem bool_fromZeros (endian : TargetEndian) :
    Spec.IsFromZeros endian .bool :=
  ⟨⟨1, 0⟩, .bool false, rfl, by cases endian <;> rfl, rfl⟩

private theorem bool_intoBytes (endian : TargetEndian) :
    Spec.IsIntoBytes endian .bool := by
  refine ⟨⟨1, 0⟩, rfl, ?_, ?_⟩
  · intro v hv
    let ⟨b, hb⟩ := checkVal_bool_inv hv
    subst hb
    exact ⟨[AllocByte.init (if b then 1 else 0) none], rfl⟩
  · intro v bs hEnc
    unfold encodeVal at hEnc
    cases hcv : checkVal v .bool with
    | false => rw [hcv] at hEnc; cases hEnc
    | true =>
      rw [hcv] at hEnc
      let ⟨b, hb⟩ := checkVal_bool_inv hcv
      subst hb
      dsimp only at hEnc
      injection hEnc with hBs
      subst hBs
      exact ⟨rfl, [if b then 1 else 0], rfl, rfl⟩

private theorem bool_tryFromBytes_sound (endian : TargetEndian) :
    Spec.BoolTryFromBytesSound endian := by
  intro bs raw hbs hraw
  have hrawLen : raw.length = 1 := (initBytes?_length hraw).trans hbs
  cases raw with
  | nil => cases hrawLen
  | cons b rest =>
    cases rest with
    | cons _ _ => cases hrawLen
    | nil =>
      have hDec : decodeUInt endian [b] = b.toNat :=
        decodeUInt_singleton endian b
      have hb256 : b.toNat < 256 := b.toBitVec.isLt
      have hb128 : b.toNat < Nat.pow 2 128 :=
        Nat.lt_trans hb256 (by decide)
      let bits : BitVec 128 := BitVec.ofNat 128 b.toNat
      have hBitsNat : bits.toNat = b.toNat := Nat.mod_eq_of_lt hb128
      have hBitsLt : bits.toNat < intWidthModulus .i8 := by
        rw [hBitsNat]; exact hb256
      have hTrunc : truncateBits .i8 bits = bits :=
        truncateBits_of_toNat_lt hBitsLt
      have hLenBeq : (!Nat.beq bs.length 1) = false := by
        rw [hbs]; rfl
      constructor
      · intro hLt2
        rw [hDec] at hLt2
        unfold decodeVal
        dsimp only [layoutOfTy]
        rw [ite_bool_false hLenBeq, ite_bool_false (rfl : Nat.beq 1 0 = false),
          hraw]
        dsimp only [evalConstLit]
        rw [hDec, show BitVec.ofNat 128 b.toNat = bits from rfl,
          hTrunc, ite_bool_false (bne_self_eq_false bits), hBitsNat]
        cases hb0 : b.toNat with
        | zero => exact ⟨false, rfl, rfl⟩
        | succ k =>
          rw [hb0] at hLt2
          cases hk : k with
          | zero => exact ⟨true, rfl, rfl⟩
          | succ m =>
            rw [hk] at hLt2
            exact False.elim
              (Nat.not_lt_zero m
                (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hLt2)))
      · intro hGe2
        rw [hDec] at hGe2
        unfold decodeVal
        dsimp only [layoutOfTy]
        rw [ite_bool_false hLenBeq, ite_bool_false (rfl : Nat.beq 1 0 = false),
          hraw]
        dsimp only [evalConstLit]
        rw [hDec, show BitVec.ofNat 128 b.toNat = bits from rfl,
          hTrunc, ite_bool_false (bne_self_eq_false bits), hBitsNat]
        have hU8Nat : (UInt8.ofNat b.toNat).toNat = b.toNat :=
          Nat.mod_eq_of_lt hb256
        have hNe0 : (UInt8.ofNat b.toNat == 0) = false := by
          cases hEq0 : (UInt8.ofNat b.toNat == 0) with
          | false => rfl
          | true =>
            have hNat0 : b.toNat = 0 := by
              rw [← hU8Nat]
              exact congrArg UInt8.toNat (eq_of_beq hEq0)
            rw [hNat0] at hGe2
            exact False.elim (Nat.not_le_of_gt (by decide : 0 < 2) hGe2)
        have hNe1 : (UInt8.ofNat b.toNat == 1) = false := by
          cases hEq1 : (UInt8.ofNat b.toNat == 1) with
          | false => rfl
          | true =>
            have hNat1 : b.toNat = 1 := by
              rw [← hU8Nat]
              exact congrArg UInt8.toNat (eq_of_beq hEq1)
            rw [hNat1] at hGe2
            exact False.elim (Nat.not_le_of_gt (by decide : 1 < 2) hGe2)
        rw [ite_bool_false hNe0, ite_bool_false hNe1]

private theorem bool_not_fromBytes (endian : TargetEndian) :
    decodeVal endian .bool [.init 0x02 none] = .error .undefined ∧
    ¬ Spec.IsFromBytes endian .bool := by
  have hBad : decodeVal endian .bool [.init 0x02 none] = .error .undefined := by
    cases endian <;> rfl
  refine ⟨hBad, fun ⟨layout, hLay, hAll⟩ => ?_⟩
  injection hLay with hLayEq
  subst hLayEq
  let ⟨_, hOk, _⟩ := hAll [.init 0x02 none] [0x02] rfl rfl
  rw [hBad] at hOk
  cases hOk

private theorem int_fromBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : Spec.IsFromBytes endian (.int w s) := by
  refine ⟨intLayout w, rfl, fun bs raw hbs hraw => ?_⟩
  have hrawLen : raw.length = w.byteSize :=
    (initBytes?_length hraw).trans (hbs.trans (intLayout_size_eq_byteSize w))
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
    rw [hbs, Anneal.InitLemmas.nat_beq_refl]
    rfl
  unfold decodeVal
  dsimp only [layoutOfTy]
  rw [ite_bool_false hLenBeq, ite_bool_false (intLayout_size_beq_zero w),
    hraw]
  dsimp only [evalConstLit]
  rw [show BitVec.ofNat 128 (decodeUInt endian raw) = bits from rfl,
    hTrunc, ite_bool_false (bne_self_eq_false bits)]
  exact ⟨.scalar ⟨w, s, bits⟩, rfl, checkVal_scalar_of_toNat_lt hBitsLt⟩

private theorem int_fromZeros (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : Spec.IsFromZeros endian (.int w s) := by
  let ⟨layout, hLay, hAll⟩ := int_fromBytes endian w s
  let ⟨v, hDec, hCv⟩ :=
    hAll (List.replicate layout.size (AllocByte.init 0 none))
      (List.replicate layout.size 0)
      (list_length_replicate layout.size (AllocByte.init 0 none))
      (initBytes?_replicate_init 0 layout.size)
  exact ⟨layout, v, hLay, hDec, hCv⟩

private theorem int_intoBytes (endian : TargetEndian) (w : IntWidth)
    (s : Bool) : Spec.IsIntoBytes endian (.int w s) := by
  refine ⟨intLayout w, rfl, ?_, ?_⟩
  · intro v hv
    let ⟨bits, hvEq, _⟩ := checkVal_int_iff.mp hv
    subst hvEq
    refine ⟨(encodeUInt endian w.byteSize bits.toNat).map
      (fun b => AllocByte.init b none), ?_⟩
    unfold encodeVal
    rw [hv]
    rfl
  · intro v bs hEnc
    unfold encodeVal at hEnc
    cases hcv : checkVal v (.int w s) with
    | false => rw [hcv] at hEnc; cases hEnc
    | true =>
      rw [hcv] at hEnc
      let ⟨bits, hvEq, _⟩ := checkVal_int_iff.mp hcv
      subst hvEq
      dsimp only at hEnc
      injection hEnc with hBs
      subst hBs
      refine ⟨?_, encodeUInt endian w.byteSize bits.toNat,
        initBytes?_map_init (encodeUInt endian w.byteSize bits.toNat), rfl⟩
      rw [list_length_map, encodeUInt_length, intLayout_size_eq_byteSize w]

/-- The `impls.rs:468-492` argument: a 1-byte layout whose size is a multiple
of its alignment has alignment 1, since `1 % 2 ^ (a + 1) = 1`. -/
private theorem one_byte_align_one (l : LayoutData) (hs : l.size = 1)
    (hm : Spec.SizeMultipleOfAlign l) : l.alignLog2 = 0 := by
  unfold Spec.SizeMultipleOfAlign at hm
  rw [hs] at hm
  cases ha : l.alignLog2 with
  | zero => rfl
  | succ a =>
    rw [ha] at hm
    have hpos : 0 < Nat.pow 2 a := Nat.two_pow_pos a
    have h2 : 1 < Nat.pow 2 (a + 1) := by
      change 1 < Nat.pow 2 a * 2
      rw [Nat.mul_two]
      exact Nat.lt_of_lt_of_le (by decide : 1 < 1 + 1)
        (Nat.add_le_add hpos hpos)
    have h1 : 1 % Nat.pow 2 (a + 1) = 1 := Nat.mod_eq_of_lt h2
    exact absurd (h1.symm.trans hm) (by decide)

private theorem int_multibyte_not_unaligned (w : IntWidth) (s : Bool)
    (hw : w ≠ .i8) :
    (∃ layout, layoutOfTy (.int w s) = some layout ∧ 0 < layout.alignLog2) ∧
    ¬ Spec.IsUnaligned (.int w s) := by
  cases w with
  | i8 => exact False.elim (hw rfl)
  | i16 =>
    refine ⟨⟨⟨2, 1⟩, rfl, by decide⟩, fun ⟨_, hLay, hZ⟩ => ?_⟩
    injection hLay with hEq; subst hEq; cases hZ
  | i32 =>
    refine ⟨⟨⟨4, 2⟩, rfl, by decide⟩, fun ⟨_, hLay, hZ⟩ => ?_⟩
    injection hLay with hEq; subst hEq; cases hZ
  | i64 =>
    refine ⟨⟨⟨8, 3⟩, rfl, by decide⟩, fun ⟨_, hLay, hZ⟩ => ?_⟩
    injection hLay with hEq; subst hEq; cases hZ
  | i128 =>
    refine ⟨⟨⟨16, 4⟩, rfl, by decide⟩, fun ⟨_, hLay, hZ⟩ => ?_⟩
    injection hLay with hEq; subst hEq; cases hZ
  | isize =>
    refine ⟨⟨⟨8, 3⟩, rfl, by decide⟩, fun ⟨_, hLay, hZ⟩ => ?_⟩
    injection hLay with hEq; subst hEq; cases hZ

/-! ### Byte-Codec Round-Trip Lemmas -/

private theorem reverseAux_reverseAux {α : Type} :
    ∀ (xs acc : List α),
      List.reverseAux (List.reverseAux xs acc) [] = List.reverseAux acc xs
  | [], _ => rfl
  | x :: rest, acc => reverseAux_reverseAux rest (x :: acc)

private theorem list_reverse_reverse {α : Type} (xs : List α) :
    xs.reverse.reverse = xs :=
  reverseAux_reverseAux xs []

private theorem encodeUInt_singleton (endian : TargetEndian) (v : Nat) :
    encodeUInt endian 1 v = [UInt8.ofNat (v % 256)] := by
  cases endian <;> rfl

private theorem uint8_ofNat_toNat_mod (x : Nat) :
    (UInt8.ofNat (x % 256)).toNat = x % 256 := by
  change ((x % 256) % 256) = x % 256
  exact Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))

private theorem uint8_ofNat_toNat (b : UInt8) : UInt8.ofNat b.toNat = b := by
  cases b with
  | ofBitVec bv =>
    exact congrArg UInt8.ofBitVec
      (bitVec_eq_of_toNat_eq (Nat.mod_eq_of_lt bv.isLt))

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

private theorem leBytesOfNat_natOfLeBytes :
    ∀ (bs : List UInt8), leBytesOfNat bs.length (natOfLeBytes bs) = bs
  | [] => rfl
  | b :: rest => by
    unfold List.length natOfLeBytes leBytesOfNat
    change UInt8.ofNat ((b.toNat + 256 * natOfLeBytes rest) % 256) ::
        leBytesOfNat rest.length
          ((b.toNat + 256 * natOfLeBytes rest) / 256) =
      b :: rest
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hMod : (b.toNat + 256 * natOfLeBytes rest) % 256 = b.toNat := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have hDiv : (b.toNat + 256 * natOfLeBytes rest) / 256 =
        natOfLeBytes rest := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb,
        Nat.zero_add]
    rw [hMod, hDiv, uint8_ofNat_toNat b, leBytesOfNat_natOfLeBytes rest]

private theorem decodeUInt_encodeUInt (e : TargetEndian) (n value : Nat) :
    decodeUInt e (encodeUInt e n value) = value % Nat.pow 2 (8 * n) := by
  cases e with
  | little => exact natOfLeBytes_leBytesOfNat n value
  | big =>
    unfold decodeUInt encodeUInt
    rw [list_reverse_reverse]
    exact natOfLeBytes_leBytesOfNat n value

private theorem encodeUInt_decodeUInt (e : TargetEndian) (bs : List UInt8) :
    encodeUInt e bs.length (decodeUInt e bs) = bs := by
  cases e with
  | little => exact leBytesOfNat_natOfLeBytes bs
  | big =>
    unfold encodeUInt decodeUInt
    rw [← list_length_reverse bs, leBytesOfNat_natOfLeBytes bs.reverse,
      list_reverse_reverse]

/-! ### Section 2A Proofs: IEEE `f32`/`f64` Byte Validity & Alignment -/

private theorem float_fromBytes (fw : Spec.FloatWidth) :
    Spec.FloatFromBytesSound fw := by
  intro endian bs raw hbs hraw
  have hrawLen : raw.length = (Spec.floatLayout fw).size :=
    (initBytes?_length hraw).trans hbs
  refine ⟨⟨hbs, raw, hraw⟩, ?_, ?_⟩
  · have h := decodeUInt_lt endian raw
    rw [hrawLen] at h
    exact h
  · have h := encodeUInt_decodeUInt endian raw
    rw [hrawLen] at h
    exact h

private theorem float_intoBytes (fw : Spec.FloatWidth) :
    Spec.FloatIntoBytesSound fw := by
  intro endian bits hLt
  refine ⟨⟨?_, _, initBytes?_map_init _⟩, ?_⟩
  · rw [list_length_map, encodeUInt_length]
  · rw [decodeUInt_encodeUInt]
    exact Nat.mod_eq_of_lt hLt

private theorem float_laws (fw : Spec.FloatWidth) :
    Spec.FloatValidBytes fw (Spec.zeroAllocBytes (Spec.floatLayout fw).size) ∧
    Spec.FloatFromBytesSound fw ∧
    (∀ endian : TargetEndian,
      Spec.FloatValidBytes fw
        ((encodeUInt endian (Spec.floatLayout fw).size
          (Spec.floatQuietNanBits fw)).map
          (fun b => AllocByte.init b none)) ∧
      Spec.FloatValidBytes fw
        ((encodeUInt endian (Spec.floatLayout fw).size
          (Spec.floatSignalingNanBits fw)).map
          (fun b => AllocByte.init b none))) ∧
    Spec.FloatIntoBytesSound fw ∧
    Spec.floatQuietNanBits fw <
      Nat.pow 2 (8 * (Spec.floatLayout fw).size) ∧
    Spec.floatSignalingNanBits fw <
      Nat.pow 2 (8 * (Spec.floatLayout fw).size) ∧
    (∀ bs : List AllocByte,
      AllocByte.uninit ∈ bs → ¬ Spec.FloatValidBytes fw bs) ∧
    0 < (Spec.floatLayout fw).alignLog2 := by
  refine ⟨?_, float_fromBytes fw, ?_, float_intoBytes fw, ?_, ?_, ?_, ?_⟩
  · exact ⟨list_length_replicate (Spec.floatLayout fw).size
        (AllocByte.init 0 none),
      List.replicate (Spec.floatLayout fw).size 0,
      initBytes?_replicate_init 0 (Spec.floatLayout fw).size⟩
  · intro endian
    constructor
    · refine ⟨?_, _, initBytes?_map_init _⟩
      rw [list_length_map, encodeUInt_length]
    · refine ⟨?_, _, initBytes?_map_init _⟩
      rw [list_length_map, encodeUInt_length]
  · cases fw <;> decide
  · cases fw <;> decide
  · intro bs hMem ⟨_, _, hraw⟩
    exact not_mem_uninit_of_initBytes? hraw hMem
  · cases fw <;> decide

/-! ### Section 2B Proofs: `str` `IntoBytes` via `u8` `encodeVal` -/

private theorem u8_encodeVal (endian : TargetEndian) (b : UInt8) :
    encodeVal endian (.int .i8 false)
        (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩) =
      .ok [AllocByte.init b none] := by
  have hb : b.toNat < 256 := b.toBitVec.isLt
  have hb128 : b.toNat < Nat.pow 2 128 := Nat.lt_trans hb (by decide)
  have hBits : (BitVec.ofNat 128 b.toNat).toNat = b.toNat :=
    Nat.mod_eq_of_lt hb128
  have hcv : checkVal (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)
      (.int .i8 false) = true :=
    checkVal_scalar_of_toNat_lt (by rw [hBits]; exact hb)
  have hNot : (!checkVal (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)
      (.int .i8 false)) = false := by
    rw [hcv]
    rfl
  unfold encodeVal
  rw [ite_bool_false hNot]
  change (Except.ok ((encodeUInt endian 1 (BitVec.ofNat 128 b.toNat).toNat).map
      (fun b => AllocByte.init b none)) : Except FaultKind (List AllocByte)) = _
  rw [hBits, encodeUInt_singleton, Nat.mod_eq_of_lt hb, uint8_ofNat_toNat]
  rfl

private theorem str_intoBytes_sound : Spec.StrIntoBytesSound :=
  ⟨u8_encodeVal,
    fun raw hValid => ⟨raw, initBytes?_map_init raw, hValid⟩,
    ⟨⟨1, 0⟩, rfl, rfl⟩⟩

private theorem float_str_atomic_bit_validity :
    Spec.FloatStrAtomicBitValiditySpec :=
  ⟨rfl,
    fun _ _ => rfl,
    rfl,
    rfl,
    float_laws,
    validUtf8_iff_stepDecomp,
    validUtf8_append,
    str_fromZeros_sound,
    str_intoBytes_sound,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      str_not_fromBytes_replicate_ff,
      fun endian =>
        ⟨bool_fromZeros endian,
          bool_intoBytes endian,
          bool_tryFromBytes_sound endian,
          bool_not_fromBytes endian,
          fun w s =>
            ⟨int_fromZeros endian w s,
              int_fromBytes endian w s,
              int_intoBytes endian w s⟩⟩,
      rfl,
      fun _ => rfl,
      one_byte_align_one,
      rfl,
      int_multibyte_not_unaligned,
      rfl, rfl, rfl, rfl, rfl,
      ⟨fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h,
        fun h => Bool.noConfusion h⟩⟩⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem defId body all_bodies_verified found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, float_str_atomic_bit_validity⟩
    intro defId identity found
    have hSub := allMarkersAt_getElem defId identity all_markers_at found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
