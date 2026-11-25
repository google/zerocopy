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
        { frames :=
            [{ defId := defId, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }],
           callerMem := ⟨[]⟩, mem := mem } =
      .step
        { frames :=
            [{ defId := defId, blockIdx := 0, stmtIdx := 1, locals := [.immediate (some .unit)] }],
           callerMem := ⟨[]⟩, mem := mem })
    (h_step2 : ∀ mem : MemoryState,
      evalStep Captured.program 0
        { frames :=
            [{ defId := defId, blockIdx := 0, stmtIdx := 1, locals := [.immediate (some .unit)] }],
           callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨.unit, ⟨[]⟩⟩)) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.UnitMarkerAt Captured.program defId identity := by
  refine ⟨?_, ⟨body, h_body, h_id, h_safe, h_argc,
    total_of_runs h_body h_adm h_args h_runs, fun mem =>
      ⟨{ frames :=
           [{ defId := defId, blockIdx := 0, stmtIdx := 1, locals := [.immediate (some .unit)] }],
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

private theorem m000 :
    BodyVerified Captured.program 0 Captured.body_0
      (Spec.specs.safety Captured.body_0.identity) ∧
    Spec.UnitMarkerAt Captured.program 0
      (idAt 0 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_0, Captured.Shard_000.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m001 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.UnitMarkerAt Captured.program 1
      (idAt 1 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_1, Captured.Shard_000.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m002 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.UnitMarkerAt Captured.program 2
      (idAt 2 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_2, Captured.Shard_000.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m003 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.UnitMarkerAt Captured.program 3
      (idAt 3 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_3, Captured.Shard_000.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m004 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.UnitMarkerAt Captured.program 4
      (idAt 4 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_4, Captured.Shard_000.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m005 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.UnitMarkerAt Captured.program 5
      (idAt 5 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_5, Captured.Shard_000.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m006 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.UnitMarkerAt Captured.program 6
      (idAt 6 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_6, Captured.Shard_000.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m007 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.UnitMarkerAt Captured.program 7
      (idAt 7 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_7, Captured.Shard_000.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m008 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.UnitMarkerAt Captured.program 8
      (idAt 8 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_8, Captured.Shard_001.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m009 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.UnitMarkerAt Captured.program 9
      (idAt 9 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_9, Captured.Shard_001.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m010 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.UnitMarkerAt Captured.program 10
      (idAt 10 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_10, Captured.Shard_001.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m011 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.UnitMarkerAt Captured.program 11
      (idAt 11 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_11, Captured.Shard_001.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m012 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.UnitMarkerAt Captured.program 12
      (idAt 12 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_12, Captured.Shard_001.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m013 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.UnitMarkerAt Captured.program 13
      (idAt 13 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_13, Captured.Shard_001.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m014 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.UnitMarkerAt Captured.program 14
      (idAt 14 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_14, Captured.Shard_001.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m015 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.UnitMarkerAt Captured.program 15
      (idAt 15 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_15, Captured.Shard_001.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m016 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.UnitMarkerAt Captured.program 16
      (idAt 16 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_16, Captured.Shard_002.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m017 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.UnitMarkerAt Captured.program 17
      (idAt 17 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_17, Captured.Shard_002.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m018 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.UnitMarkerAt Captured.program 18
      (idAt 18 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_18, Captured.Shard_002.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m019 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.UnitMarkerAt Captured.program 19
      (idAt 19 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_19, Captured.Shard_002.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m020 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.UnitMarkerAt Captured.program 20
      (idAt 20 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_20, Captured.Shard_002.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m021 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.UnitMarkerAt Captured.program 21
      (idAt 21 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_21, Captured.Shard_002.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m022 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.UnitMarkerAt Captured.program 22
      (idAt 22 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_22, Captured.Shard_002.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m023 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.UnitMarkerAt Captured.program 23
      (idAt 23 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_23, Captured.Shard_002.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m024 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.UnitMarkerAt Captured.program 24
      (idAt 24 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_24, Captured.Shard_003.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m025 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.UnitMarkerAt Captured.program 25
      (idAt 25 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_25, Captured.Shard_003.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m026 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.UnitMarkerAt Captured.program 26
      (idAt 26 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_26, Captured.Shard_003.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m027 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.UnitMarkerAt Captured.program 27
      (idAt 27 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_27, Captured.Shard_003.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m028 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.UnitMarkerAt Captured.program 28
      (idAt 28 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_28, Captured.Shard_003.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m029 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.UnitMarkerAt Captured.program 29
      (idAt 29 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_29, Captured.Shard_003.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m030 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.UnitMarkerAt Captured.program 30
      (idAt 30 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_30, Captured.Shard_003.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m031 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.UnitMarkerAt Captured.program 31
      (idAt 31 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_31, Captured.Shard_003.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m032 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.UnitMarkerAt Captured.program 32
      (idAt 32 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_32, Captured.Shard_004.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m033 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.UnitMarkerAt Captured.program 33
      (idAt 33 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_33, Captured.Shard_004.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m034 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.UnitMarkerAt Captured.program 34
      (idAt 34 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_34, Captured.Shard_004.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m035 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.UnitMarkerAt Captured.program 35
      (idAt 35 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_35, Captured.Shard_004.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m036 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.UnitMarkerAt Captured.program 36
      (idAt 36 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_36, Captured.Shard_004.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m037 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.UnitMarkerAt Captured.program 37
      (idAt 37 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_37, Captured.Shard_004.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m038 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.UnitMarkerAt Captured.program 38
      (idAt 38 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_38, Captured.Shard_004.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m039 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.UnitMarkerAt Captured.program 39
      (idAt 39 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_39, Captured.Shard_004.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m040 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.UnitMarkerAt Captured.program 40
      (idAt 40 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_40, Captured.Shard_005.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m041 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.UnitMarkerAt Captured.program 41
      (idAt 41 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_41, Captured.Shard_005.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m042 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.UnitMarkerAt Captured.program 42
      (idAt 42 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_42, Captured.Shard_005.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m043 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.UnitMarkerAt Captured.program 43
      (idAt 43 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_43, Captured.Shard_005.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m044 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.UnitMarkerAt Captured.program 44
      (idAt 44 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_44, Captured.Shard_005.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m045 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.UnitMarkerAt Captured.program 45
      (idAt 45 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_45, Captured.Shard_005.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m046 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.UnitMarkerAt Captured.program 46
      (idAt 46 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_46, Captured.Shard_005.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m047 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.UnitMarkerAt Captured.program 47
      (idAt 47 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_47, Captured.Shard_005.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m048 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.UnitMarkerAt Captured.program 48
      (idAt 48 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_48, Captured.Shard_006.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m049 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.UnitMarkerAt Captured.program 49
      (idAt 49 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_49, Captured.Shard_006.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m050 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.UnitMarkerAt Captured.program 50
      (idAt 50 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_50, Captured.Shard_006.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m051 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.UnitMarkerAt Captured.program 51
      (idAt 51 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_51, Captured.Shard_006.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m052 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.UnitMarkerAt Captured.program 52
      (idAt 52 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_52, Captured.Shard_006.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m053 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.UnitMarkerAt Captured.program 53
      (idAt 53 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_53, Captured.Shard_006.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m054 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.UnitMarkerAt Captured.program 54
      (idAt 54 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_54, Captured.Shard_006.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m055 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.UnitMarkerAt Captured.program 55
      (idAt 55 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_55, Captured.Shard_006.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m056 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.UnitMarkerAt Captured.program 56
      (idAt 56 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_56, Captured.Shard_007.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m057 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.UnitMarkerAt Captured.program 57
      (idAt 57 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_57, Captured.Shard_007.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m058 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.UnitMarkerAt Captured.program 58
      (idAt 58 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_58, Captured.Shard_007.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m059 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.UnitMarkerAt Captured.program 59
      (idAt 59 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_59, Captured.Shard_007.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m060 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.UnitMarkerAt Captured.program 60
      (idAt 60 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_60, Captured.Shard_007.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m061 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.UnitMarkerAt Captured.program 61
      (idAt 61 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_61, Captured.Shard_007.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m062 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.UnitMarkerAt Captured.program 62
      (idAt 62 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_62, Captured.Shard_007.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m063 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.UnitMarkerAt Captured.program 63
      (idAt 63 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_63, Captured.Shard_007.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m064 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.UnitMarkerAt Captured.program 64
      (idAt 64 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_64, Captured.Shard_008.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m065 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.UnitMarkerAt Captured.program 65
      (idAt 65 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_65, Captured.Shard_008.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m066 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.UnitMarkerAt Captured.program 66
      (idAt 66 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_66, Captured.Shard_008.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m067 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.UnitMarkerAt Captured.program 67
      (idAt 67 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_67, Captured.Shard_008.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m068 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.UnitMarkerAt Captured.program 68
      (idAt 68 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_68, Captured.Shard_008.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m069 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.UnitMarkerAt Captured.program 69
      (idAt 69 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_69, Captured.Shard_008.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m070 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.UnitMarkerAt Captured.program 70
      (idAt 70 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_70, Captured.Shard_008.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m071 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.UnitMarkerAt Captured.program 71
      (idAt 71 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_71, Captured.Shard_008.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m072 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.UnitMarkerAt Captured.program 72
      (idAt 72 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_72, Captured.Shard_009.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m073 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.UnitMarkerAt Captured.program 73
      (idAt 73 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_73, Captured.Shard_009.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m074 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.UnitMarkerAt Captured.program 74
      (idAt 74 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_74, Captured.Shard_009.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m075 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.UnitMarkerAt Captured.program 75
      (idAt 75 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_75, Captured.Shard_009.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m076 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.UnitMarkerAt Captured.program 76
      (idAt 76 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_76, Captured.Shard_009.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m077 :
    BodyVerified Captured.program 77 Captured.body_77
      (Spec.specs.safety Captured.body_77.identity) ∧
    Spec.UnitMarkerAt Captured.program 77
      (idAt 77 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_77, Captured.Shard_009.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m078 :
    BodyVerified Captured.program 78 Captured.body_78
      (Spec.specs.safety Captured.body_78.identity) ∧
    Spec.UnitMarkerAt Captured.program 78
      (idAt 78 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_78, Captured.Shard_009.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m079 :
    BodyVerified Captured.program 79 Captured.body_79
      (Spec.specs.safety Captured.body_79.identity) ∧
    Spec.UnitMarkerAt Captured.program 79
      (idAt 79 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_79, Captured.Shard_009.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m080 :
    BodyVerified Captured.program 80 Captured.body_80
      (Spec.specs.safety Captured.body_80.identity) ∧
    Spec.UnitMarkerAt Captured.program 80
      (idAt 80 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_80, Captured.Shard_010.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m081 :
    BodyVerified Captured.program 81 Captured.body_81
      (Spec.specs.safety Captured.body_81.identity) ∧
    Spec.UnitMarkerAt Captured.program 81
      (idAt 81 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_81, Captured.Shard_010.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m082 :
    BodyVerified Captured.program 82 Captured.body_82
      (Spec.specs.safety Captured.body_82.identity) ∧
    Spec.UnitMarkerAt Captured.program 82
      (idAt 82 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_82, Captured.Shard_010.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m083 :
    BodyVerified Captured.program 83 Captured.body_83
      (Spec.specs.safety Captured.body_83.identity) ∧
    Spec.UnitMarkerAt Captured.program 83
      (idAt 83 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_83, Captured.Shard_010.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m084 :
    BodyVerified Captured.program 84 Captured.body_84
      (Spec.specs.safety Captured.body_84.identity) ∧
    Spec.UnitMarkerAt Captured.program 84
      (idAt 84 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_84, Captured.Shard_010.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m085 :
    BodyVerified Captured.program 85 Captured.body_85
      (Spec.specs.safety Captured.body_85.identity) ∧
    Spec.UnitMarkerAt Captured.program 85
      (idAt 85 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_85, Captured.Shard_010.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m086 :
    BodyVerified Captured.program 86 Captured.body_86
      (Spec.specs.safety Captured.body_86.identity) ∧
    Spec.UnitMarkerAt Captured.program 86
      (idAt 86 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_86, Captured.Shard_010.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m087 :
    BodyVerified Captured.program 87 Captured.body_87
      (Spec.specs.safety Captured.body_87.identity) ∧
    Spec.UnitMarkerAt Captured.program 87
      (idAt 87 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_87, Captured.Shard_010.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m088 :
    BodyVerified Captured.program 88 Captured.body_88
      (Spec.specs.safety Captured.body_88.identity) ∧
    Spec.UnitMarkerAt Captured.program 88
      (idAt 88 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_88, Captured.Shard_011.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m089 :
    BodyVerified Captured.program 89 Captured.body_89
      (Spec.specs.safety Captured.body_89.identity) ∧
    Spec.UnitMarkerAt Captured.program 89
      (idAt 89 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_89, Captured.Shard_011.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m090 :
    BodyVerified Captured.program 90 Captured.body_90
      (Spec.specs.safety Captured.body_90.identity) ∧
    Spec.UnitMarkerAt Captured.program 90
      (idAt 90 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_90, Captured.Shard_011.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m091 :
    BodyVerified Captured.program 91 Captured.body_91
      (Spec.specs.safety Captured.body_91.identity) ∧
    Spec.UnitMarkerAt Captured.program 91
      (idAt 91 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_91, Captured.Shard_011.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m092 :
    BodyVerified Captured.program 92 Captured.body_92
      (Spec.specs.safety Captured.body_92.identity) ∧
    Spec.UnitMarkerAt Captured.program 92
      (idAt 92 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_92, Captured.Shard_011.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m093 :
    BodyVerified Captured.program 93 Captured.body_93
      (Spec.specs.safety Captured.body_93.identity) ∧
    Spec.UnitMarkerAt Captured.program 93
      (idAt 93 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_93, Captured.Shard_011.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m094 :
    BodyVerified Captured.program 94 Captured.body_94
      (Spec.specs.safety Captured.body_94.identity) ∧
    Spec.UnitMarkerAt Captured.program 94
      (idAt 94 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_94, Captured.Shard_011.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m095 :
    BodyVerified Captured.program 95 Captured.body_95
      (Spec.specs.safety Captured.body_95.identity) ∧
    Spec.UnitMarkerAt Captured.program 95
      (idAt 95 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_95, Captured.Shard_011.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m096 :
    BodyVerified Captured.program 96 Captured.body_96
      (Spec.specs.safety Captured.body_96.identity) ∧
    Spec.UnitMarkerAt Captured.program 96
      (idAt 96 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_96, Captured.Shard_012.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m097 :
    BodyVerified Captured.program 97 Captured.body_97
      (Spec.specs.safety Captured.body_97.identity) ∧
    Spec.UnitMarkerAt Captured.program 97
      (idAt 97 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_97, Captured.Shard_012.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m098 :
    BodyVerified Captured.program 98 Captured.body_98
      (Spec.specs.safety Captured.body_98.identity) ∧
    Spec.UnitMarkerAt Captured.program 98
      (idAt 98 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_98, Captured.Shard_012.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m099 :
    BodyVerified Captured.program 99 Captured.body_99
      (Spec.specs.safety Captured.body_99.identity) ∧
    Spec.UnitMarkerAt Captured.program 99
      (idAt 99 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_99, Captured.Shard_012.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m100 :
    BodyVerified Captured.program 100 Captured.body_100
      (Spec.specs.safety Captured.body_100.identity) ∧
    Spec.UnitMarkerAt Captured.program 100
      (idAt 100 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_100, Captured.Shard_012.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m101 :
    BodyVerified Captured.program 101 Captured.body_101
      (Spec.specs.safety Captured.body_101.identity) ∧
    Spec.UnitMarkerAt Captured.program 101
      (idAt 101 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_101, Captured.Shard_012.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m102 :
    BodyVerified Captured.program 102 Captured.body_102
      (Spec.specs.safety Captured.body_102.identity) ∧
    Spec.UnitMarkerAt Captured.program 102
      (idAt 102 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_102, Captured.Shard_012.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m103 :
    BodyVerified Captured.program 103 Captured.body_103
      (Spec.specs.safety Captured.body_103.identity) ∧
    Spec.UnitMarkerAt Captured.program 103
      (idAt 103 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_103, Captured.Shard_012.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m104 :
    BodyVerified Captured.program 104 Captured.body_104
      (Spec.specs.safety Captured.body_104.identity) ∧
    Spec.UnitMarkerAt Captured.program 104
      (idAt 104 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_104, Captured.Shard_013.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m105 :
    BodyVerified Captured.program 105 Captured.body_105
      (Spec.specs.safety Captured.body_105.identity) ∧
    Spec.UnitMarkerAt Captured.program 105
      (idAt 105 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_105, Captured.Shard_013.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m106 :
    BodyVerified Captured.program 106 Captured.body_106
      (Spec.specs.safety Captured.body_106.identity) ∧
    Spec.UnitMarkerAt Captured.program 106
      (idAt 106 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_106, Captured.Shard_013.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m107 :
    BodyVerified Captured.program 107 Captured.body_107
      (Spec.specs.safety Captured.body_107.identity) ∧
    Spec.UnitMarkerAt Captured.program 107
      (idAt 107 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_107, Captured.Shard_013.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m108 :
    BodyVerified Captured.program 108 Captured.body_108
      (Spec.specs.safety Captured.body_108.identity) ∧
    Spec.UnitMarkerAt Captured.program 108
      (idAt 108 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_108, Captured.Shard_013.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m109 :
    BodyVerified Captured.program 109 Captured.body_109
      (Spec.specs.safety Captured.body_109.identity) ∧
    Spec.UnitMarkerAt Captured.program 109
      (idAt 109 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_109, Captured.Shard_013.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m110 :
    BodyVerified Captured.program 110 Captured.body_110
      (Spec.specs.safety Captured.body_110.identity) ∧
    Spec.UnitMarkerAt Captured.program 110
      (idAt 110 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_110, Captured.Shard_013.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m111 :
    BodyVerified Captured.program 111 Captured.body_111
      (Spec.specs.safety Captured.body_111.identity) ∧
    Spec.UnitMarkerAt Captured.program 111
      (idAt 111 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_111, Captured.Shard_013.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m112 :
    BodyVerified Captured.program 112 Captured.body_112
      (Spec.specs.safety Captured.body_112.identity) ∧
    Spec.UnitMarkerAt Captured.program 112
      (idAt 112 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_112, Captured.Shard_014.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m113 :
    BodyVerified Captured.program 113 Captured.body_113
      (Spec.specs.safety Captured.body_113.identity) ∧
    Spec.UnitMarkerAt Captured.program 113
      (idAt 113 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_113, Captured.Shard_014.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m114 :
    BodyVerified Captured.program 114 Captured.body_114
      (Spec.specs.safety Captured.body_114.identity) ∧
    Spec.UnitMarkerAt Captured.program 114
      (idAt 114 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_114, Captured.Shard_014.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m115 :
    BodyVerified Captured.program 115 Captured.body_115
      (Spec.specs.safety Captured.body_115.identity) ∧
    Spec.UnitMarkerAt Captured.program 115
      (idAt 115 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_115, Captured.Shard_014.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m116 :
    BodyVerified Captured.program 116 Captured.body_116
      (Spec.specs.safety Captured.body_116.identity) ∧
    Spec.UnitMarkerAt Captured.program 116
      (idAt 116 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_116, Captured.Shard_014.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m117 :
    BodyVerified Captured.program 117 Captured.body_117
      (Spec.specs.safety Captured.body_117.identity) ∧
    Spec.UnitMarkerAt Captured.program 117
      (idAt 117 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_117, Captured.Shard_014.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m118 :
    BodyVerified Captured.program 118 Captured.body_118
      (Spec.specs.safety Captured.body_118.identity) ∧
    Spec.UnitMarkerAt Captured.program 118
      (idAt 118 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_118, Captured.Shard_014.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m119 :
    BodyVerified Captured.program 119 Captured.body_119
      (Spec.specs.safety Captured.body_119.identity) ∧
    Spec.UnitMarkerAt Captured.program 119
      (idAt 119 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_119, Captured.Shard_014.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m120 :
    BodyVerified Captured.program 120 Captured.body_120
      (Spec.specs.safety Captured.body_120.identity) ∧
    Spec.UnitMarkerAt Captured.program 120
      (idAt 120 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_120, Captured.Shard_015.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m121 :
    BodyVerified Captured.program 121 Captured.body_121
      (Spec.specs.safety Captured.body_121.identity) ∧
    Spec.UnitMarkerAt Captured.program 121
      (idAt 121 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_121, Captured.Shard_015.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m122 :
    BodyVerified Captured.program 122 Captured.body_122
      (Spec.specs.safety Captured.body_122.identity) ∧
    Spec.UnitMarkerAt Captured.program 122
      (idAt 122 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_122, Captured.Shard_015.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m123 :
    BodyVerified Captured.program 123 Captured.body_123
      (Spec.specs.safety Captured.body_123.identity) ∧
    Spec.UnitMarkerAt Captured.program 123
      (idAt 123 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_123, Captured.Shard_015.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m124 :
    BodyVerified Captured.program 124 Captured.body_124
      (Spec.specs.safety Captured.body_124.identity) ∧
    Spec.UnitMarkerAt Captured.program 124
      (idAt 124 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_124, Captured.Shard_015.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m125 :
    BodyVerified Captured.program 125 Captured.body_125
      (Spec.specs.safety Captured.body_125.identity) ∧
    Spec.UnitMarkerAt Captured.program 125
      (idAt 125 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_125, Captured.Shard_015.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m126 :
    BodyVerified Captured.program 126 Captured.body_126
      (Spec.specs.safety Captured.body_126.identity) ∧
    Spec.UnitMarkerAt Captured.program 126
      (idAt 126 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_126, Captured.Shard_015.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m127 :
    BodyVerified Captured.program 127 Captured.body_127
      (Spec.specs.safety Captured.body_127.identity) ∧
    Spec.UnitMarkerAt Captured.program 127
      (idAt 127 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_127, Captured.Shard_015.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m128 :
    BodyVerified Captured.program 128 Captured.body_128
      (Spec.specs.safety Captured.body_128.identity) ∧
    Spec.UnitMarkerAt Captured.program 128
      (idAt 128 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_128, Captured.Shard_016.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m129 :
    BodyVerified Captured.program 129 Captured.body_129
      (Spec.specs.safety Captured.body_129.identity) ∧
    Spec.UnitMarkerAt Captured.program 129
      (idAt 129 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_129, Captured.Shard_016.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m130 :
    BodyVerified Captured.program 130 Captured.body_130
      (Spec.specs.safety Captured.body_130.identity) ∧
    Spec.UnitMarkerAt Captured.program 130
      (idAt 130 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_130, Captured.Shard_016.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m131 :
    BodyVerified Captured.program 131 Captured.body_131
      (Spec.specs.safety Captured.body_131.identity) ∧
    Spec.UnitMarkerAt Captured.program 131
      (idAt 131 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_131, Captured.Shard_016.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m132 :
    BodyVerified Captured.program 132 Captured.body_132
      (Spec.specs.safety Captured.body_132.identity) ∧
    Spec.UnitMarkerAt Captured.program 132
      (idAt 132 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_132, Captured.Shard_016.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m133 :
    BodyVerified Captured.program 133 Captured.body_133
      (Spec.specs.safety Captured.body_133.identity) ∧
    Spec.UnitMarkerAt Captured.program 133
      (idAt 133 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_133, Captured.Shard_016.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m134 :
    BodyVerified Captured.program 134 Captured.body_134
      (Spec.specs.safety Captured.body_134.identity) ∧
    Spec.UnitMarkerAt Captured.program 134
      (idAt 134 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_134, Captured.Shard_016.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m135 :
    BodyVerified Captured.program 135 Captured.body_135
      (Spec.specs.safety Captured.body_135.identity) ∧
    Spec.UnitMarkerAt Captured.program 135
      (idAt 135 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_135, Captured.Shard_016.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m136 :
    BodyVerified Captured.program 136 Captured.body_136
      (Spec.specs.safety Captured.body_136.identity) ∧
    Spec.UnitMarkerAt Captured.program 136
      (idAt 136 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_136, Captured.Shard_017.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m137 :
    BodyVerified Captured.program 137 Captured.body_137
      (Spec.specs.safety Captured.body_137.identity) ∧
    Spec.UnitMarkerAt Captured.program 137
      (idAt 137 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_137, Captured.Shard_017.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m138 :
    BodyVerified Captured.program 138 Captured.body_138
      (Spec.specs.safety Captured.body_138.identity) ∧
    Spec.UnitMarkerAt Captured.program 138
      (idAt 138 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_138, Captured.Shard_017.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m139 :
    BodyVerified Captured.program 139 Captured.body_139
      (Spec.specs.safety Captured.body_139.identity) ∧
    Spec.UnitMarkerAt Captured.program 139
      (idAt 139 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_139, Captured.Shard_017.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m140 :
    BodyVerified Captured.program 140 Captured.body_140
      (Spec.specs.safety Captured.body_140.identity) ∧
    Spec.UnitMarkerAt Captured.program 140
      (idAt 140 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_140, Captured.Shard_017.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m141 :
    BodyVerified Captured.program 141 Captured.body_141
      (Spec.specs.safety Captured.body_141.identity) ∧
    Spec.UnitMarkerAt Captured.program 141
      (idAt 141 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_141, Captured.Shard_017.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m142 :
    BodyVerified Captured.program 142 Captured.body_142
      (Spec.specs.safety Captured.body_142.identity) ∧
    Spec.UnitMarkerAt Captured.program 142
      (idAt 142 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_142, Captured.Shard_017.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m143 :
    BodyVerified Captured.program 143 Captured.body_143
      (Spec.specs.safety Captured.body_143.identity) ∧
    Spec.UnitMarkerAt Captured.program 143
      (idAt 143 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_143, Captured.Shard_017.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m144 :
    BodyVerified Captured.program 144 Captured.body_144
      (Spec.specs.safety Captured.body_144.identity) ∧
    Spec.UnitMarkerAt Captured.program 144
      (idAt 144 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_144, Captured.Shard_018.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m145 :
    BodyVerified Captured.program 145 Captured.body_145
      (Spec.specs.safety Captured.body_145.identity) ∧
    Spec.UnitMarkerAt Captured.program 145
      (idAt 145 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_145, Captured.Shard_018.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m146 :
    BodyVerified Captured.program 146 Captured.body_146
      (Spec.specs.safety Captured.body_146.identity) ∧
    Spec.UnitMarkerAt Captured.program 146
      (idAt 146 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_146, Captured.Shard_018.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m147 :
    BodyVerified Captured.program 147 Captured.body_147
      (Spec.specs.safety Captured.body_147.identity) ∧
    Spec.UnitMarkerAt Captured.program 147
      (idAt 147 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_147, Captured.Shard_018.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m148 :
    BodyVerified Captured.program 148 Captured.body_148
      (Spec.specs.safety Captured.body_148.identity) ∧
    Spec.UnitMarkerAt Captured.program 148
      (idAt 148 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_148, Captured.Shard_018.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m149 :
    BodyVerified Captured.program 149 Captured.body_149
      (Spec.specs.safety Captured.body_149.identity) ∧
    Spec.UnitMarkerAt Captured.program 149
      (idAt 149 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_149, Captured.Shard_018.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m150 :
    BodyVerified Captured.program 150 Captured.body_150
      (Spec.specs.safety Captured.body_150.identity) ∧
    Spec.UnitMarkerAt Captured.program 150
      (idAt 150 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_150, Captured.Shard_018.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m151 :
    BodyVerified Captured.program 151 Captured.body_151
      (Spec.specs.safety Captured.body_151.identity) ∧
    Spec.UnitMarkerAt Captured.program 151
      (idAt 151 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_151, Captured.Shard_018.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m152 :
    BodyVerified Captured.program 152 Captured.body_152
      (Spec.specs.safety Captured.body_152.identity) ∧
    Spec.UnitMarkerAt Captured.program 152
      (idAt 152 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_152, Captured.Shard_019.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m153 :
    BodyVerified Captured.program 153 Captured.body_153
      (Spec.specs.safety Captured.body_153.identity) ∧
    Spec.UnitMarkerAt Captured.program 153
      (idAt 153 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_153, Captured.Shard_019.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m154 :
    BodyVerified Captured.program 154 Captured.body_154
      (Spec.specs.safety Captured.body_154.identity) ∧
    Spec.UnitMarkerAt Captured.program 154
      (idAt 154 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_154, Captured.Shard_019.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m155 :
    BodyVerified Captured.program 155 Captured.body_155
      (Spec.specs.safety Captured.body_155.identity) ∧
    Spec.UnitMarkerAt Captured.program 155
      (idAt 155 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_155, Captured.Shard_019.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m156 :
    BodyVerified Captured.program 156 Captured.body_156
      (Spec.specs.safety Captured.body_156.identity) ∧
    Spec.UnitMarkerAt Captured.program 156
      (idAt 156 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_156, Captured.Shard_019.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m157 :
    BodyVerified Captured.program 157 Captured.body_157
      (Spec.specs.safety Captured.body_157.identity) ∧
    Spec.UnitMarkerAt Captured.program 157
      (idAt 157 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_157, Captured.Shard_019.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m158 :
    BodyVerified Captured.program 158 Captured.body_158
      (Spec.specs.safety Captured.body_158.identity) ∧
    Spec.UnitMarkerAt Captured.program 158
      (idAt 158 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_158, Captured.Shard_019.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m159 :
    BodyVerified Captured.program 159 Captured.body_159
      (Spec.specs.safety Captured.body_159.identity) ∧
    Spec.UnitMarkerAt Captured.program 159
      (idAt 159 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_159, Captured.Shard_019.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m160 :
    BodyVerified Captured.program 160 Captured.body_160
      (Spec.specs.safety Captured.body_160.identity) ∧
    Spec.UnitMarkerAt Captured.program 160
      (idAt 160 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_160, Captured.Shard_020.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m161 :
    BodyVerified Captured.program 161 Captured.body_161
      (Spec.specs.safety Captured.body_161.identity) ∧
    Spec.UnitMarkerAt Captured.program 161
      (idAt 161 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_161, Captured.Shard_020.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m162 :
    BodyVerified Captured.program 162 Captured.body_162
      (Spec.specs.safety Captured.body_162.identity) ∧
    Spec.UnitMarkerAt Captured.program 162
      (idAt 162 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_162, Captured.Shard_020.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m163 :
    BodyVerified Captured.program 163 Captured.body_163
      (Spec.specs.safety Captured.body_163.identity) ∧
    Spec.UnitMarkerAt Captured.program 163
      (idAt 163 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_163, Captured.Shard_020.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m164 :
    BodyVerified Captured.program 164 Captured.body_164
      (Spec.specs.safety Captured.body_164.identity) ∧
    Spec.UnitMarkerAt Captured.program 164
      (idAt 164 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_164, Captured.Shard_020.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m165 :
    BodyVerified Captured.program 165 Captured.body_165
      (Spec.specs.safety Captured.body_165.identity) ∧
    Spec.UnitMarkerAt Captured.program 165
      (idAt 165 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_165, Captured.Shard_020.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m166 :
    BodyVerified Captured.program 166 Captured.body_166
      (Spec.specs.safety Captured.body_166.identity) ∧
    Spec.UnitMarkerAt Captured.program 166
      (idAt 166 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_166, Captured.Shard_020.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m167 :
    BodyVerified Captured.program 167 Captured.body_167
      (Spec.specs.safety Captured.body_167.identity) ∧
    Spec.UnitMarkerAt Captured.program 167
      (idAt 167 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_167, Captured.Shard_020.body_7,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m168 :
    BodyVerified Captured.program 168 Captured.body_168
      (Spec.specs.safety Captured.body_168.identity) ∧
    Spec.UnitMarkerAt Captured.program 168
      (idAt 168 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_168, Captured.Shard_021.body_0,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m169 :
    BodyVerified Captured.program 169 Captured.body_169
      (Spec.specs.safety Captured.body_169.identity) ∧
    Spec.UnitMarkerAt Captured.program 169
      (idAt 169 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_169, Captured.Shard_021.body_1,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m170 :
    BodyVerified Captured.program 170 Captured.body_170
      (Spec.specs.safety Captured.body_170.identity) ∧
    Spec.UnitMarkerAt Captured.program 170
      (idAt 170 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_170, Captured.Shard_021.body_2,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m171 :
    BodyVerified Captured.program 171 Captured.body_171
      (Spec.specs.safety Captured.body_171.identity) ∧
    Spec.UnitMarkerAt Captured.program 171
      (idAt 171 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_171, Captured.Shard_021.body_3,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m172 :
    BodyVerified Captured.program 172 Captured.body_172
      (Spec.specs.safety Captured.body_172.identity) ∧
    Spec.UnitMarkerAt Captured.program 172
      (idAt 172 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_172, Captured.Shard_021.body_4,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m173 :
    BodyVerified Captured.program 173 Captured.body_173
      (Spec.specs.safety Captured.body_173.identity) ∧
    Spec.UnitMarkerAt Captured.program 173
      (idAt 173 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_173, Captured.Shard_021.body_5,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private theorem m174 :
    BodyVerified Captured.program 174 Captured.body_174
      (Spec.specs.safety Captured.body_174.identity) ∧
    Spec.UnitMarkerAt Captured.program 174
      (idAt 174 Spec.byteorderMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_174, Captured.Shard_021.body_6,
      Spec.byteorderMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

private noncomputable def BodiesVerifiedFrom (program : Program)
    (idx : Nat) : List Body → Prop
  | [] => True
  | b :: rest =>
    BodyVerified program idx b (Spec.specs.safety b.identity) ∧
      BodiesVerifiedFrom program (idx + 1) rest

private theorem bodiesVerified_nil (idx : Nat) :
    BodiesVerifiedFrom Captured.program idx [] := trivial

private theorem bodiesVerified_cons {idx : Nat} {b : Body} {rest : List Body}
    (hHead :
      BodyVerified Captured.program idx b (Spec.specs.safety b.identity))
    (hTail : BodiesVerifiedFrom Captured.program (idx + 1) rest) :
    BodiesVerifiedFrom Captured.program idx (b :: rest) :=
  ⟨hHead, hTail⟩

private theorem bodiesVerified_getElem :
    ∀ {bs : List Body} {base : Nat} (i : Nat) (body : Body),
      BodiesVerifiedFrom Captured.program base bs →
      Trusted.MirSemantics.getElem? bs i = some body →
      BodyVerified Captured.program (base + i) body
        (Spec.specs.safety body.identity)
  | [], _, _, _, _, h => by cases h
  | b0 :: _, base, 0, body, ⟨hHead, _⟩, h => by
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

private noncomputable def AllMarkersAtFrom (program : Program)
    (idx : Nat) : List String → Prop
  | [] => True
  | identity :: rest =>
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
  | _ :: _, base, 0, _, ⟨hHead, _⟩, h => by
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
  refine bodiesVerified_cons m000.1 ?_
  refine bodiesVerified_cons m001.1 ?_
  refine bodiesVerified_cons m002.1 ?_
  refine bodiesVerified_cons m003.1 ?_
  refine bodiesVerified_cons m004.1 ?_
  refine bodiesVerified_cons m005.1 ?_
  refine bodiesVerified_cons m006.1 ?_
  refine bodiesVerified_cons m007.1 ?_
  refine bodiesVerified_cons m008.1 ?_
  refine bodiesVerified_cons m009.1 ?_
  refine bodiesVerified_cons m010.1 ?_
  refine bodiesVerified_cons m011.1 ?_
  refine bodiesVerified_cons m012.1 ?_
  refine bodiesVerified_cons m013.1 ?_
  refine bodiesVerified_cons m014.1 ?_
  refine bodiesVerified_cons m015.1 ?_
  refine bodiesVerified_cons m016.1 ?_
  refine bodiesVerified_cons m017.1 ?_
  refine bodiesVerified_cons m018.1 ?_
  refine bodiesVerified_cons m019.1 ?_
  refine bodiesVerified_cons m020.1 ?_
  refine bodiesVerified_cons m021.1 ?_
  refine bodiesVerified_cons m022.1 ?_
  refine bodiesVerified_cons m023.1 ?_
  refine bodiesVerified_cons m024.1 ?_
  refine bodiesVerified_cons m025.1 ?_
  refine bodiesVerified_cons m026.1 ?_
  refine bodiesVerified_cons m027.1 ?_
  refine bodiesVerified_cons m028.1 ?_
  refine bodiesVerified_cons m029.1 ?_
  refine bodiesVerified_cons m030.1 ?_
  refine bodiesVerified_cons m031.1 ?_
  refine bodiesVerified_cons m032.1 ?_
  refine bodiesVerified_cons m033.1 ?_
  refine bodiesVerified_cons m034.1 ?_
  refine bodiesVerified_cons m035.1 ?_
  refine bodiesVerified_cons m036.1 ?_
  refine bodiesVerified_cons m037.1 ?_
  refine bodiesVerified_cons m038.1 ?_
  refine bodiesVerified_cons m039.1 ?_
  refine bodiesVerified_cons m040.1 ?_
  refine bodiesVerified_cons m041.1 ?_
  refine bodiesVerified_cons m042.1 ?_
  refine bodiesVerified_cons m043.1 ?_
  refine bodiesVerified_cons m044.1 ?_
  refine bodiesVerified_cons m045.1 ?_
  refine bodiesVerified_cons m046.1 ?_
  refine bodiesVerified_cons m047.1 ?_
  refine bodiesVerified_cons m048.1 ?_
  refine bodiesVerified_cons m049.1 ?_
  refine bodiesVerified_cons m050.1 ?_
  refine bodiesVerified_cons m051.1 ?_
  refine bodiesVerified_cons m052.1 ?_
  refine bodiesVerified_cons m053.1 ?_
  refine bodiesVerified_cons m054.1 ?_
  refine bodiesVerified_cons m055.1 ?_
  refine bodiesVerified_cons m056.1 ?_
  refine bodiesVerified_cons m057.1 ?_
  refine bodiesVerified_cons m058.1 ?_
  refine bodiesVerified_cons m059.1 ?_
  refine bodiesVerified_cons m060.1 ?_
  refine bodiesVerified_cons m061.1 ?_
  refine bodiesVerified_cons m062.1 ?_
  refine bodiesVerified_cons m063.1 ?_
  refine bodiesVerified_cons m064.1 ?_
  refine bodiesVerified_cons m065.1 ?_
  refine bodiesVerified_cons m066.1 ?_
  refine bodiesVerified_cons m067.1 ?_
  refine bodiesVerified_cons m068.1 ?_
  refine bodiesVerified_cons m069.1 ?_
  refine bodiesVerified_cons m070.1 ?_
  refine bodiesVerified_cons m071.1 ?_
  refine bodiesVerified_cons m072.1 ?_
  refine bodiesVerified_cons m073.1 ?_
  refine bodiesVerified_cons m074.1 ?_
  refine bodiesVerified_cons m075.1 ?_
  refine bodiesVerified_cons m076.1 ?_
  refine bodiesVerified_cons m077.1 ?_
  refine bodiesVerified_cons m078.1 ?_
  refine bodiesVerified_cons m079.1 ?_
  refine bodiesVerified_cons m080.1 ?_
  refine bodiesVerified_cons m081.1 ?_
  refine bodiesVerified_cons m082.1 ?_
  refine bodiesVerified_cons m083.1 ?_
  refine bodiesVerified_cons m084.1 ?_
  refine bodiesVerified_cons m085.1 ?_
  refine bodiesVerified_cons m086.1 ?_
  refine bodiesVerified_cons m087.1 ?_
  refine bodiesVerified_cons m088.1 ?_
  refine bodiesVerified_cons m089.1 ?_
  refine bodiesVerified_cons m090.1 ?_
  refine bodiesVerified_cons m091.1 ?_
  refine bodiesVerified_cons m092.1 ?_
  refine bodiesVerified_cons m093.1 ?_
  refine bodiesVerified_cons m094.1 ?_
  refine bodiesVerified_cons m095.1 ?_
  refine bodiesVerified_cons m096.1 ?_
  refine bodiesVerified_cons m097.1 ?_
  refine bodiesVerified_cons m098.1 ?_
  refine bodiesVerified_cons m099.1 ?_
  refine bodiesVerified_cons m100.1 ?_
  refine bodiesVerified_cons m101.1 ?_
  refine bodiesVerified_cons m102.1 ?_
  refine bodiesVerified_cons m103.1 ?_
  refine bodiesVerified_cons m104.1 ?_
  refine bodiesVerified_cons m105.1 ?_
  refine bodiesVerified_cons m106.1 ?_
  refine bodiesVerified_cons m107.1 ?_
  refine bodiesVerified_cons m108.1 ?_
  refine bodiesVerified_cons m109.1 ?_
  refine bodiesVerified_cons m110.1 ?_
  refine bodiesVerified_cons m111.1 ?_
  refine bodiesVerified_cons m112.1 ?_
  refine bodiesVerified_cons m113.1 ?_
  refine bodiesVerified_cons m114.1 ?_
  refine bodiesVerified_cons m115.1 ?_
  refine bodiesVerified_cons m116.1 ?_
  refine bodiesVerified_cons m117.1 ?_
  refine bodiesVerified_cons m118.1 ?_
  refine bodiesVerified_cons m119.1 ?_
  refine bodiesVerified_cons m120.1 ?_
  refine bodiesVerified_cons m121.1 ?_
  refine bodiesVerified_cons m122.1 ?_
  refine bodiesVerified_cons m123.1 ?_
  refine bodiesVerified_cons m124.1 ?_
  refine bodiesVerified_cons m125.1 ?_
  refine bodiesVerified_cons m126.1 ?_
  refine bodiesVerified_cons m127.1 ?_
  refine bodiesVerified_cons m128.1 ?_
  refine bodiesVerified_cons m129.1 ?_
  refine bodiesVerified_cons m130.1 ?_
  refine bodiesVerified_cons m131.1 ?_
  refine bodiesVerified_cons m132.1 ?_
  refine bodiesVerified_cons m133.1 ?_
  refine bodiesVerified_cons m134.1 ?_
  refine bodiesVerified_cons m135.1 ?_
  refine bodiesVerified_cons m136.1 ?_
  refine bodiesVerified_cons m137.1 ?_
  refine bodiesVerified_cons m138.1 ?_
  refine bodiesVerified_cons m139.1 ?_
  refine bodiesVerified_cons m140.1 ?_
  refine bodiesVerified_cons m141.1 ?_
  refine bodiesVerified_cons m142.1 ?_
  refine bodiesVerified_cons m143.1 ?_
  refine bodiesVerified_cons m144.1 ?_
  refine bodiesVerified_cons m145.1 ?_
  refine bodiesVerified_cons m146.1 ?_
  refine bodiesVerified_cons m147.1 ?_
  refine bodiesVerified_cons m148.1 ?_
  refine bodiesVerified_cons m149.1 ?_
  refine bodiesVerified_cons m150.1 ?_
  refine bodiesVerified_cons m151.1 ?_
  refine bodiesVerified_cons m152.1 ?_
  refine bodiesVerified_cons m153.1 ?_
  refine bodiesVerified_cons m154.1 ?_
  refine bodiesVerified_cons m155.1 ?_
  refine bodiesVerified_cons m156.1 ?_
  refine bodiesVerified_cons m157.1 ?_
  refine bodiesVerified_cons m158.1 ?_
  refine bodiesVerified_cons m159.1 ?_
  refine bodiesVerified_cons m160.1 ?_
  refine bodiesVerified_cons m161.1 ?_
  refine bodiesVerified_cons m162.1 ?_
  refine bodiesVerified_cons m163.1 ?_
  refine bodiesVerified_cons m164.1 ?_
  refine bodiesVerified_cons m165.1 ?_
  refine bodiesVerified_cons m166.1 ?_
  refine bodiesVerified_cons m167.1 ?_
  refine bodiesVerified_cons m168.1 ?_
  refine bodiesVerified_cons m169.1 ?_
  refine bodiesVerified_cons m170.1 ?_
  refine bodiesVerified_cons m171.1 ?_
  refine bodiesVerified_cons m172.1 ?_
  refine bodiesVerified_cons m173.1 ?_
  refine bodiesVerified_cons m174.1 ?_
  exact bodiesVerified_nil _

private theorem all_markers_at :
    AllMarkersAtFrom Captured.program 0 Spec.byteorderMarkerIdentities := by
  refine allMarkersAt_cons m000.2 ?_
  refine allMarkersAt_cons m001.2 ?_
  refine allMarkersAt_cons m002.2 ?_
  refine allMarkersAt_cons m003.2 ?_
  refine allMarkersAt_cons m004.2 ?_
  refine allMarkersAt_cons m005.2 ?_
  refine allMarkersAt_cons m006.2 ?_
  refine allMarkersAt_cons m007.2 ?_
  refine allMarkersAt_cons m008.2 ?_
  refine allMarkersAt_cons m009.2 ?_
  refine allMarkersAt_cons m010.2 ?_
  refine allMarkersAt_cons m011.2 ?_
  refine allMarkersAt_cons m012.2 ?_
  refine allMarkersAt_cons m013.2 ?_
  refine allMarkersAt_cons m014.2 ?_
  refine allMarkersAt_cons m015.2 ?_
  refine allMarkersAt_cons m016.2 ?_
  refine allMarkersAt_cons m017.2 ?_
  refine allMarkersAt_cons m018.2 ?_
  refine allMarkersAt_cons m019.2 ?_
  refine allMarkersAt_cons m020.2 ?_
  refine allMarkersAt_cons m021.2 ?_
  refine allMarkersAt_cons m022.2 ?_
  refine allMarkersAt_cons m023.2 ?_
  refine allMarkersAt_cons m024.2 ?_
  refine allMarkersAt_cons m025.2 ?_
  refine allMarkersAt_cons m026.2 ?_
  refine allMarkersAt_cons m027.2 ?_
  refine allMarkersAt_cons m028.2 ?_
  refine allMarkersAt_cons m029.2 ?_
  refine allMarkersAt_cons m030.2 ?_
  refine allMarkersAt_cons m031.2 ?_
  refine allMarkersAt_cons m032.2 ?_
  refine allMarkersAt_cons m033.2 ?_
  refine allMarkersAt_cons m034.2 ?_
  refine allMarkersAt_cons m035.2 ?_
  refine allMarkersAt_cons m036.2 ?_
  refine allMarkersAt_cons m037.2 ?_
  refine allMarkersAt_cons m038.2 ?_
  refine allMarkersAt_cons m039.2 ?_
  refine allMarkersAt_cons m040.2 ?_
  refine allMarkersAt_cons m041.2 ?_
  refine allMarkersAt_cons m042.2 ?_
  refine allMarkersAt_cons m043.2 ?_
  refine allMarkersAt_cons m044.2 ?_
  refine allMarkersAt_cons m045.2 ?_
  refine allMarkersAt_cons m046.2 ?_
  refine allMarkersAt_cons m047.2 ?_
  refine allMarkersAt_cons m048.2 ?_
  refine allMarkersAt_cons m049.2 ?_
  refine allMarkersAt_cons m050.2 ?_
  refine allMarkersAt_cons m051.2 ?_
  refine allMarkersAt_cons m052.2 ?_
  refine allMarkersAt_cons m053.2 ?_
  refine allMarkersAt_cons m054.2 ?_
  refine allMarkersAt_cons m055.2 ?_
  refine allMarkersAt_cons m056.2 ?_
  refine allMarkersAt_cons m057.2 ?_
  refine allMarkersAt_cons m058.2 ?_
  refine allMarkersAt_cons m059.2 ?_
  refine allMarkersAt_cons m060.2 ?_
  refine allMarkersAt_cons m061.2 ?_
  refine allMarkersAt_cons m062.2 ?_
  refine allMarkersAt_cons m063.2 ?_
  refine allMarkersAt_cons m064.2 ?_
  refine allMarkersAt_cons m065.2 ?_
  refine allMarkersAt_cons m066.2 ?_
  refine allMarkersAt_cons m067.2 ?_
  refine allMarkersAt_cons m068.2 ?_
  refine allMarkersAt_cons m069.2 ?_
  refine allMarkersAt_cons m070.2 ?_
  refine allMarkersAt_cons m071.2 ?_
  refine allMarkersAt_cons m072.2 ?_
  refine allMarkersAt_cons m073.2 ?_
  refine allMarkersAt_cons m074.2 ?_
  refine allMarkersAt_cons m075.2 ?_
  refine allMarkersAt_cons m076.2 ?_
  refine allMarkersAt_cons m077.2 ?_
  refine allMarkersAt_cons m078.2 ?_
  refine allMarkersAt_cons m079.2 ?_
  refine allMarkersAt_cons m080.2 ?_
  refine allMarkersAt_cons m081.2 ?_
  refine allMarkersAt_cons m082.2 ?_
  refine allMarkersAt_cons m083.2 ?_
  refine allMarkersAt_cons m084.2 ?_
  refine allMarkersAt_cons m085.2 ?_
  refine allMarkersAt_cons m086.2 ?_
  refine allMarkersAt_cons m087.2 ?_
  refine allMarkersAt_cons m088.2 ?_
  refine allMarkersAt_cons m089.2 ?_
  refine allMarkersAt_cons m090.2 ?_
  refine allMarkersAt_cons m091.2 ?_
  refine allMarkersAt_cons m092.2 ?_
  refine allMarkersAt_cons m093.2 ?_
  refine allMarkersAt_cons m094.2 ?_
  refine allMarkersAt_cons m095.2 ?_
  refine allMarkersAt_cons m096.2 ?_
  refine allMarkersAt_cons m097.2 ?_
  refine allMarkersAt_cons m098.2 ?_
  refine allMarkersAt_cons m099.2 ?_
  refine allMarkersAt_cons m100.2 ?_
  refine allMarkersAt_cons m101.2 ?_
  refine allMarkersAt_cons m102.2 ?_
  refine allMarkersAt_cons m103.2 ?_
  refine allMarkersAt_cons m104.2 ?_
  refine allMarkersAt_cons m105.2 ?_
  refine allMarkersAt_cons m106.2 ?_
  refine allMarkersAt_cons m107.2 ?_
  refine allMarkersAt_cons m108.2 ?_
  refine allMarkersAt_cons m109.2 ?_
  refine allMarkersAt_cons m110.2 ?_
  refine allMarkersAt_cons m111.2 ?_
  refine allMarkersAt_cons m112.2 ?_
  refine allMarkersAt_cons m113.2 ?_
  refine allMarkersAt_cons m114.2 ?_
  refine allMarkersAt_cons m115.2 ?_
  refine allMarkersAt_cons m116.2 ?_
  refine allMarkersAt_cons m117.2 ?_
  refine allMarkersAt_cons m118.2 ?_
  refine allMarkersAt_cons m119.2 ?_
  refine allMarkersAt_cons m120.2 ?_
  refine allMarkersAt_cons m121.2 ?_
  refine allMarkersAt_cons m122.2 ?_
  refine allMarkersAt_cons m123.2 ?_
  refine allMarkersAt_cons m124.2 ?_
  refine allMarkersAt_cons m125.2 ?_
  refine allMarkersAt_cons m126.2 ?_
  refine allMarkersAt_cons m127.2 ?_
  refine allMarkersAt_cons m128.2 ?_
  refine allMarkersAt_cons m129.2 ?_
  refine allMarkersAt_cons m130.2 ?_
  refine allMarkersAt_cons m131.2 ?_
  refine allMarkersAt_cons m132.2 ?_
  refine allMarkersAt_cons m133.2 ?_
  refine allMarkersAt_cons m134.2 ?_
  refine allMarkersAt_cons m135.2 ?_
  refine allMarkersAt_cons m136.2 ?_
  refine allMarkersAt_cons m137.2 ?_
  refine allMarkersAt_cons m138.2 ?_
  refine allMarkersAt_cons m139.2 ?_
  refine allMarkersAt_cons m140.2 ?_
  refine allMarkersAt_cons m141.2 ?_
  refine allMarkersAt_cons m142.2 ?_
  refine allMarkersAt_cons m143.2 ?_
  refine allMarkersAt_cons m144.2 ?_
  refine allMarkersAt_cons m145.2 ?_
  refine allMarkersAt_cons m146.2 ?_
  refine allMarkersAt_cons m147.2 ?_
  refine allMarkersAt_cons m148.2 ?_
  refine allMarkersAt_cons m149.2 ?_
  refine allMarkersAt_cons m150.2 ?_
  refine allMarkersAt_cons m151.2 ?_
  refine allMarkersAt_cons m152.2 ?_
  refine allMarkersAt_cons m153.2 ?_
  refine allMarkersAt_cons m154.2 ?_
  refine allMarkersAt_cons m155.2 ?_
  refine allMarkersAt_cons m156.2 ?_
  refine allMarkersAt_cons m157.2 ?_
  refine allMarkersAt_cons m158.2 ?_
  refine allMarkersAt_cons m159.2 ?_
  refine allMarkersAt_cons m160.2 ?_
  refine allMarkersAt_cons m161.2 ?_
  refine allMarkersAt_cons m162.2 ?_
  refine allMarkersAt_cons m163.2 ?_
  refine allMarkersAt_cons m164.2 ?_
  refine allMarkersAt_cons m165.2 ?_
  refine allMarkersAt_cons m166.2 ?_
  refine allMarkersAt_cons m167.2 ?_
  refine allMarkersAt_cons m168.2 ?_
  refine allMarkersAt_cons m169.2 ?_
  refine allMarkersAt_cons m170.2 ?_
  refine allMarkersAt_cons m171.2 ?_
  refine allMarkersAt_cons m172.2 ?_
  refine allMarkersAt_cons m173.2 ?_
  refine allMarkersAt_cons m174.2 ?_
  exact allMarkersAt_nil _

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: Model-Side Endian Codec, Alignment, and Bit-Validity Proofs -/

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
  | cons x rest ih =>
    unfold List.reverseAux
    rw [ih (x :: acc)]
    change rest.length + (acc.length + 1) = (rest.length + 1) + acc.length
    rw [Nat.add_assoc, Nat.add_comm acc.length 1, ← Nat.add_assoc]

private theorem list_length_reverse {α : Type} (xs : List α) :
    xs.reverse.length = xs.length :=
  list_length_reverseAux xs []

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).length = xs.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (list_length_map f rest)

private theorem list_reverseAux_eq {α : Type} :
    ∀ (xs acc : List α),
      List.reverseAux xs acc = List.reverseAux xs [] ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
    unfold List.reverseAux
    rw [list_reverseAux_eq xs (x :: acc), list_reverseAux_eq xs [x],
      List.append_assoc]
    rfl

private theorem list_reverse_cons {α : Type} (x : α) (xs : List α) :
    (x :: xs).reverse = xs.reverse ++ [x] := by
  change List.reverseAux xs [x] = List.reverseAux xs [] ++ [x]
  exact list_reverseAux_eq xs [x]

private theorem list_reverse_append {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).reverse = ys.reverse ++ xs.reverse
  | [], ys => by
    rw [List.nil_append]
    change ys.reverse = ys.reverse ++ []
    exact (List.append_nil ys.reverse).symm
  | x :: xs, ys => by
    change (x :: (xs ++ ys)).reverse = ys.reverse ++ (x :: xs).reverse
    rw [list_reverse_cons x (xs ++ ys), list_reverse_cons x xs,
      list_reverse_append xs ys, List.append_assoc]

private theorem list_reverse_reverse {α : Type} :
    ∀ (xs : List α), xs.reverse.reverse = xs
  | [] => rfl
  | x :: xs => by
    rw [list_reverse_cons x xs, list_reverse_append xs.reverse [x],
      list_reverse_reverse xs]
    rfl

private theorem nat_pow_add (a m : Nat) :
    ∀ (n : Nat), Nat.pow a (m + n) = Nat.pow a m * Nat.pow a n
  | 0 => by
    rw [Nat.add_zero]
    change Nat.pow a m = Nat.pow a m * 1
    rw [Nat.mul_one]
  | n + 1 => by
    change Nat.pow a (m + n) * a = Nat.pow a m * (Nat.pow a n * a)
    rw [nat_pow_add a m n, Nat.mul_assoc]

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

private theorem swapEndian_involutive (e : TargetEndian) :
    Spec.swapEndian (Spec.swapEndian e) = e := by
  cases e <;> rfl

private theorem encodeUInt_swapEndian (e : TargetEndian) (n value : Nat) :
    encodeUInt (Spec.swapEndian e) n value =
      (encodeUInt e n value).reverse := by
  cases e with
  | little => rfl
  | big =>
    unfold encodeUInt Spec.swapEndian
    exact (list_reverse_reverse (leBytesOfNat n value)).symm

private theorem decodeUInt_reverse (e : TargetEndian) (bs : List UInt8) :
    decodeUInt e bs.reverse = decodeUInt (Spec.swapEndian e) bs := by
  cases e with
  | little => rfl
  | big =>
    unfold decodeUInt Spec.swapEndian
    rw [list_reverse_reverse]

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

private theorem encodeUInt_decodeUInt_swap (e : TargetEndian)
    (bs : List UInt8) :
    encodeUInt e bs.length (decodeUInt (Spec.swapEndian e) bs) =
      bs.reverse := by
  rw [← decodeUInt_reverse e bs, ← list_length_reverse bs]
  exact encodeUInt_decodeUInt e bs.reverse

private theorem initBytes?_length :
    ∀ {bs : List AllocByte} {raw : List UInt8},
      initBytes? bs = some raw → raw.length = bs.length
  | [], _, h => by cases h; rfl
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

private theorem u8_foundation
    (e1 e2 : TargetEndian) (b : UInt8) (v : Nat) :
    decodeUInt e1 [b] = b.toNat ∧
    decodeUInt e1 [b] = decodeUInt e2 [b] ∧
    encodeUInt e1 1 v = [UInt8.ofNat (v % 256)] ∧
    decodeVal e1 (.int .i8 false) [AllocByte.init b none] =
      .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)) := by
  have h1 := decodeUInt_singleton e1 b
  have h2 := decodeUInt_singleton e2 b
  have h3 := encodeUInt_singleton e1 v
  have hb128 : b.toNat < 2 ^ 128 :=
    Nat.lt_trans b.toBitVec.isLt (by decide)
  let bits : BitVec 128 := BitVec.ofNat 128 b.toNat
  have hbLt : bits.toNat < intWidthModulus .i8 := by
    change b.toNat % 2 ^ 128 < 256
    rw [Nat.mod_eq_of_lt hb128]
    exact b.toBitVec.isLt
  have hTrunc : truncateBits .i8 bits = bits :=
    truncateBits_of_toNat_lt hbLt
  have hDec :
      decodeVal e1 (.int .i8 false) [AllocByte.init b none] =
        .ok (some (.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩)) := by
    have hInit : initBytes? [AllocByte.init b none] = some [b] := rfl
    unfold decodeVal
    dsimp only [layoutOfTy, intLayout, List.length]
    rw [ite_bool_false (rfl : (!Nat.beq 1 1) = false),
      ite_bool_false (rfl : Nat.beq 1 0 = false), hInit]
    dsimp only [evalConstLit]
    rw [h1, show BitVec.ofNat 128 b.toNat = bits from rfl, hTrunc,
      ite_bool_false (bne_self_eq_false bits)]
  exact ⟨h1, h1.trans h2.symm, h3, hDec⟩

private theorem int_fromBytes (e : TargetEndian) (signed : Bool)
    (w : IntWidth) : Spec.IntFromBytesEndianSound e signed w := by
  intro bs ⟨hbsLen, raw, hraw⟩
  have hrawLen : raw.length = w.byteSize :=
    (initBytes?_length hraw).trans hbsLen
  have hDecLt : decodeUInt e raw < intWidthModulus w := by
    have h := decodeUInt_lt e raw
    rw [hrawLen, two_pow_eight_mul_byteSize w] at h
    exact h
  have hDec128 : decodeUInt e raw < Nat.pow 2 128 :=
    Nat.lt_of_lt_of_le hDecLt (intWidthModulus_le_128 w)
  let bits : BitVec 128 := BitVec.ofNat 128 (decodeUInt e raw)
  have hBitsNat : bits.toNat = decodeUInt e raw :=
    Nat.mod_eq_of_lt hDec128
  have hBitsLt : bits.toNat < intWidthModulus w := by
    rw [hBitsNat]; exact hDecLt
  have hTrunc : truncateBits w bits = bits :=
    truncateBits_of_toNat_lt hBitsLt
  have hLenBeq : (!Nat.beq bs.length (intLayout w).size) = false := by
    rw [hbsLen, intLayout_size_eq_byteSize w, Nat.beq_refl]
    rfl
  unfold decodeVal
  dsimp only [layoutOfTy]
  rw [ite_bool_false hLenBeq, ite_bool_false (intLayout_size_beq_zero w), hraw]
  dsimp only [evalConstLit]
  rw [show BitVec.ofNat 128 (decodeUInt e raw) = bits from rfl, hTrunc,
    ite_bool_false (bne_self_eq_false bits)]
  exact ⟨⟨w, signed, bits⟩, rfl, checkVal_scalar_of_toNat_lt hBitsLt⟩

private theorem int_intoBytes (e : TargetEndian) (signed : Bool)
    (w : IntWidth) : Spec.IntIntoBytesEndianSound e signed w := by
  intro sv hcv
  let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp hcv
  cases hEq
  have hModPos : 0 < intWidthModulus w := by cases w <;> decide
  have hBitsLt : bits.toNat < intWidthModulus w := by
    rw [← hTrunc, toNat_truncateBits]
    exact Nat.mod_lt bits.toNat hModPos
  let raw := encodeUInt e w.byteSize bits.toNat
  let bs := raw.map (fun b => AllocByte.init b none)
  have hEnc : encodeVal e (.int w signed) (.scalar ⟨w, signed, bits⟩) =
      .ok bs := by
    unfold encodeVal
    rw [hcv]
    rfl
  have hbsLen : bs.length = w.byteSize := by
    rw [list_length_map, encodeUInt_length]
  have hraw : initBytes? bs = some raw := initBytes?_map_init raw
  have hDecNat : decodeUInt e raw = bits.toNat := by
    rw [decodeUInt_encodeUInt e w.byteSize bits.toNat,
      two_pow_eight_mul_byteSize w]
    exact Nat.mod_eq_of_lt hBitsLt
  have hBitsEq : BitVec.ofNat 128 (decodeUInt e raw) = bits :=
    bitVec_eq_of_toNat_eq (by rw [hDecNat]; exact Nat.mod_eq_of_lt bits.isLt)
  have hLenBeq : (!Nat.beq bs.length (intLayout w).size) = false := by
    rw [hbsLen, intLayout_size_eq_byteSize w, Nat.beq_refl]
    rfl
  have hDec : decodeVal e (.int w signed) bs =
      .ok (some (.scalar ⟨w, signed, bits⟩)) := by
    unfold decodeVal
    dsimp only [layoutOfTy]
    rw [ite_bool_false hLenBeq, ite_bool_false (intLayout_size_beq_zero w),
      hraw]
    dsimp only [evalConstLit]
    rw [hBitsEq, hTrunc, ite_bool_false (bne_self_eq_false bits)]
  exact ⟨bs, hEnc, hbsLen, ⟨raw, hraw, rfl⟩, hDec⟩

private theorem multibyte_alignment (w : IntWidth) (signed : Bool)
    (hw : w ≠ .i8) :
    ∃ l : LayoutData,
      layoutOfTy (.int w signed) = some l ∧
      l.size = w.byteSize ∧
      0 < l.alignLog2 := by
  cases w with
  | i8 => exact False.elim (hw rfl)
  | i16 => exact ⟨⟨2, 1⟩, rfl, rfl, by decide⟩
  | i32 => exact ⟨⟨4, 2⟩, rfl, rfl, by decide⟩
  | i64 => exact ⟨⟨8, 3⟩, rfl, rfl, by decide⟩
  | i128 => exact ⟨⟨16, 4⟩, rfl, rfl, by decide⟩
  | isize => exact ⟨⟨8, 3⟩, rfl, rfl, by decide⟩

private theorem raw_bits_codec_roundtrip (n bound : Nat)
    (hBound : bound = Nat.pow 2 (8 * n))
    (e : TargetEndian) (bits : Nat) (hLt : bits < bound) :
    decodeUInt e (encodeUInt e n bits) = bits ∧
    decodeUInt (Spec.swapEndian e) (encodeUInt e n bits).reverse = bits ∧
    (encodeUInt e n bits).length = n := by
  have hDec : decodeUInt e (encodeUInt e n bits) = bits := by
    rw [decodeUInt_encodeUInt e n bits, ← hBound]
    exact Nat.mod_eq_of_lt hLt
  have hSwap :
      decodeUInt (Spec.swapEndian e) (encodeUInt e n bits).reverse = bits := by
    rw [decodeUInt_reverse, swapEndian_involutive, hDec]
  exact ⟨hDec, hSwap, encodeUInt_length e n bits⟩

private theorem concrete_endian_witnesses :
    encodeUInt .big 2 0x0102 = [0x01, 0x02] ∧
    encodeUInt .little 2 0x0102 = [0x02, 0x01] ∧
    encodeUInt .big 2 0x0102 ≠ encodeUInt .little 2 0x0102 ∧
    decodeUInt .big [0x01, 0x02] = 0x0102 ∧
    decodeUInt .little [0x01, 0x02] = 0x0201 ∧
    decodeUInt .big [0x01, 0x02] ≠ decodeUInt .little [0x01, 0x02] ∧
    encodeUInt .big 4 0x01020304 = [0x01, 0x02, 0x03, 0x04] ∧
    encodeUInt .little 4 0x01020304 = [0x04, 0x03, 0x02, 0x01] ∧
    decodeUInt .big [0x01, 0x02, 0x03, 0x04] = 0x01020304 ∧
    decodeUInt .little [0x01, 0x02, 0x03, 0x04] = 0x04030201 ∧
    decodeUInt .big (encodeUInt .little 8 0x0123456789ABCDEF).reverse =
      0x0123456789ABCDEF ∧
    decodeUInt .little (encodeUInt .big 16 0x0123456789ABCDEF).reverse =
      0x0123456789ABCDEF := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide
  · rw [decodeUInt_reverse]
    dsimp only [Spec.swapEndian]
    rw [decodeUInt_encodeUInt]
  · rw [decodeUInt_reverse]
    dsimp only [Spec.swapEndian]
    rw [decodeUInt_encodeUInt]

private theorem byteorder_model_spec : Spec.ByteorderModelSpec := by
  refine ⟨rfl, u8_foundation, swapEndian_involutive, ?_,
    decodeUInt_reverse, decodeUInt_encodeUInt, ?_, ?_,
    concrete_endian_witnesses, ?_, multibyte_alignment, ?_⟩
  · intro e n value
    exact ⟨encodeUInt_length e n value, encodeUInt_swapEndian e n value⟩
  · intro e n value hLt
    rw [decodeUInt_encodeUInt e n value]
    exact Nat.mod_eq_of_lt hLt
  · intro e bs
    exact ⟨encodeUInt_decodeUInt e bs, encodeUInt_decodeUInt_swap e bs⟩
  · intro e signed w
    exact ⟨int_fromBytes e signed w, int_intoBytes e signed w⟩
  · exact ⟨rfl, fun _ _ => rfl,
      raw_bits_codec_roundtrip 4 (Nat.pow 2 32) rfl,
      raw_bits_codec_roundtrip 8 (Nat.pow 2 64) rfl⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem defId body all_bodies_verified found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, byteorder_model_spec⟩
    intro defId identity found
    have hSub := allMarkersAt_getElem defId identity all_markers_at found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
