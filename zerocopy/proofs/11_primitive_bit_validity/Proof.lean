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

/-! ## Part 1: Captured MIR Sealing-Marker Verification -/

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
    (h_runs : Runs body 2 [] .unit) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    Spec.UnitMarkerAt Captured.program defId identity := by
  refine ⟨?_, ⟨body, h_body, h_id, h_safe, h_argc,
    total_of_runs h_body h_adm h_args h_runs⟩⟩
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
      (idAt 0 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_0, Captured.Shard_000.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m01 :
    BodyVerified Captured.program 1 Captured.body_1
      (Spec.specs.safety Captured.body_1.identity) ∧
    Spec.UnitMarkerAt Captured.program 1
      (idAt 1 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_1, Captured.Shard_000.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m02 :
    BodyVerified Captured.program 2 Captured.body_2
      (Spec.specs.safety Captured.body_2.identity) ∧
    Spec.UnitMarkerAt Captured.program 2
      (idAt 2 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_2, Captured.Shard_000.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m03 :
    BodyVerified Captured.program 3 Captured.body_3
      (Spec.specs.safety Captured.body_3.identity) ∧
    Spec.UnitMarkerAt Captured.program 3
      (idAt 3 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_3, Captured.Shard_000.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m04 :
    BodyVerified Captured.program 4 Captured.body_4
      (Spec.specs.safety Captured.body_4.identity) ∧
    Spec.UnitMarkerAt Captured.program 4
      (idAt 4 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_4, Captured.Shard_000.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m05 :
    BodyVerified Captured.program 5 Captured.body_5
      (Spec.specs.safety Captured.body_5.identity) ∧
    Spec.UnitMarkerAt Captured.program 5
      (idAt 5 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_5, Captured.Shard_000.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m06 :
    BodyVerified Captured.program 6 Captured.body_6
      (Spec.specs.safety Captured.body_6.identity) ∧
    Spec.UnitMarkerAt Captured.program 6
      (idAt 6 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_6, Captured.Shard_000.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m07 :
    BodyVerified Captured.program 7 Captured.body_7
      (Spec.specs.safety Captured.body_7.identity) ∧
    Spec.UnitMarkerAt Captured.program 7
      (idAt 7 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_7, Captured.Shard_000.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m08 :
    BodyVerified Captured.program 8 Captured.body_8
      (Spec.specs.safety Captured.body_8.identity) ∧
    Spec.UnitMarkerAt Captured.program 8
      (idAt 8 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_8, Captured.Shard_000.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m09 :
    BodyVerified Captured.program 9 Captured.body_9
      (Spec.specs.safety Captured.body_9.identity) ∧
    Spec.UnitMarkerAt Captured.program 9
      (idAt 9 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_9, Captured.Shard_000.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m10 :
    BodyVerified Captured.program 10 Captured.body_10
      (Spec.specs.safety Captured.body_10.identity) ∧
    Spec.UnitMarkerAt Captured.program 10
      (idAt 10 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_10, Captured.Shard_000.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m11 :
    BodyVerified Captured.program 11 Captured.body_11
      (Spec.specs.safety Captured.body_11.identity) ∧
    Spec.UnitMarkerAt Captured.program 11
      (idAt 11 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_11, Captured.Shard_001.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m12 :
    BodyVerified Captured.program 12 Captured.body_12
      (Spec.specs.safety Captured.body_12.identity) ∧
    Spec.UnitMarkerAt Captured.program 12
      (idAt 12 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_12, Captured.Shard_001.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m13 :
    BodyVerified Captured.program 13 Captured.body_13
      (Spec.specs.safety Captured.body_13.identity) ∧
    Spec.UnitMarkerAt Captured.program 13
      (idAt 13 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_13, Captured.Shard_001.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m14 :
    BodyVerified Captured.program 14 Captured.body_14
      (Spec.specs.safety Captured.body_14.identity) ∧
    Spec.UnitMarkerAt Captured.program 14
      (idAt 14 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_14, Captured.Shard_001.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m15 :
    BodyVerified Captured.program 15 Captured.body_15
      (Spec.specs.safety Captured.body_15.identity) ∧
    Spec.UnitMarkerAt Captured.program 15
      (idAt 15 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_15, Captured.Shard_001.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m16 :
    BodyVerified Captured.program 16 Captured.body_16
      (Spec.specs.safety Captured.body_16.identity) ∧
    Spec.UnitMarkerAt Captured.program 16
      (idAt 16 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_16, Captured.Shard_001.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m17 :
    BodyVerified Captured.program 17 Captured.body_17
      (Spec.specs.safety Captured.body_17.identity) ∧
    Spec.UnitMarkerAt Captured.program 17
      (idAt 17 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_17, Captured.Shard_001.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m18 :
    BodyVerified Captured.program 18 Captured.body_18
      (Spec.specs.safety Captured.body_18.identity) ∧
    Spec.UnitMarkerAt Captured.program 18
      (idAt 18 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_18, Captured.Shard_001.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m19 :
    BodyVerified Captured.program 19 Captured.body_19
      (Spec.specs.safety Captured.body_19.identity) ∧
    Spec.UnitMarkerAt Captured.program 19
      (idAt 19 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_19, Captured.Shard_001.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m20 :
    BodyVerified Captured.program 20 Captured.body_20
      (Spec.specs.safety Captured.body_20.identity) ∧
    Spec.UnitMarkerAt Captured.program 20
      (idAt 20 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_20, Captured.Shard_001.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m21 :
    BodyVerified Captured.program 21 Captured.body_21
      (Spec.specs.safety Captured.body_21.identity) ∧
    Spec.UnitMarkerAt Captured.program 21
      (idAt 21 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_21, Captured.Shard_001.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m22 :
    BodyVerified Captured.program 22 Captured.body_22
      (Spec.specs.safety Captured.body_22.identity) ∧
    Spec.UnitMarkerAt Captured.program 22
      (idAt 22 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_22, Captured.Shard_002.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m23 :
    BodyVerified Captured.program 23 Captured.body_23
      (Spec.specs.safety Captured.body_23.identity) ∧
    Spec.UnitMarkerAt Captured.program 23
      (idAt 23 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_23, Captured.Shard_002.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m24 :
    BodyVerified Captured.program 24 Captured.body_24
      (Spec.specs.safety Captured.body_24.identity) ∧
    Spec.UnitMarkerAt Captured.program 24
      (idAt 24 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_24, Captured.Shard_002.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m25 :
    BodyVerified Captured.program 25 Captured.body_25
      (Spec.specs.safety Captured.body_25.identity) ∧
    Spec.UnitMarkerAt Captured.program 25
      (idAt 25 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_25, Captured.Shard_002.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m26 :
    BodyVerified Captured.program 26 Captured.body_26
      (Spec.specs.safety Captured.body_26.identity) ∧
    Spec.UnitMarkerAt Captured.program 26
      (idAt 26 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_26, Captured.Shard_002.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m27 :
    BodyVerified Captured.program 27 Captured.body_27
      (Spec.specs.safety Captured.body_27.identity) ∧
    Spec.UnitMarkerAt Captured.program 27
      (idAt 27 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_27, Captured.Shard_002.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m28 :
    BodyVerified Captured.program 28 Captured.body_28
      (Spec.specs.safety Captured.body_28.identity) ∧
    Spec.UnitMarkerAt Captured.program 28
      (idAt 28 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_28, Captured.Shard_002.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m29 :
    BodyVerified Captured.program 29 Captured.body_29
      (Spec.specs.safety Captured.body_29.identity) ∧
    Spec.UnitMarkerAt Captured.program 29
      (idAt 29 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_29, Captured.Shard_002.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m30 :
    BodyVerified Captured.program 30 Captured.body_30
      (Spec.specs.safety Captured.body_30.identity) ∧
    Spec.UnitMarkerAt Captured.program 30
      (idAt 30 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_30, Captured.Shard_002.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m31 :
    BodyVerified Captured.program 31 Captured.body_31
      (Spec.specs.safety Captured.body_31.identity) ∧
    Spec.UnitMarkerAt Captured.program 31
      (idAt 31 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_31, Captured.Shard_002.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m32 :
    BodyVerified Captured.program 32 Captured.body_32
      (Spec.specs.safety Captured.body_32.identity) ∧
    Spec.UnitMarkerAt Captured.program 32
      (idAt 32 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_32, Captured.Shard_002.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m33 :
    BodyVerified Captured.program 33 Captured.body_33
      (Spec.specs.safety Captured.body_33.identity) ∧
    Spec.UnitMarkerAt Captured.program 33
      (idAt 33 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_33, Captured.Shard_003.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m34 :
    BodyVerified Captured.program 34 Captured.body_34
      (Spec.specs.safety Captured.body_34.identity) ∧
    Spec.UnitMarkerAt Captured.program 34
      (idAt 34 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_34, Captured.Shard_003.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m35 :
    BodyVerified Captured.program 35 Captured.body_35
      (Spec.specs.safety Captured.body_35.identity) ∧
    Spec.UnitMarkerAt Captured.program 35
      (idAt 35 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_35, Captured.Shard_003.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m36 :
    BodyVerified Captured.program 36 Captured.body_36
      (Spec.specs.safety Captured.body_36.identity) ∧
    Spec.UnitMarkerAt Captured.program 36
      (idAt 36 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_36, Captured.Shard_003.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m37 :
    BodyVerified Captured.program 37 Captured.body_37
      (Spec.specs.safety Captured.body_37.identity) ∧
    Spec.UnitMarkerAt Captured.program 37
      (idAt 37 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_37, Captured.Shard_003.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m38 :
    BodyVerified Captured.program 38 Captured.body_38
      (Spec.specs.safety Captured.body_38.identity) ∧
    Spec.UnitMarkerAt Captured.program 38
      (idAt 38 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_38, Captured.Shard_003.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m39 :
    BodyVerified Captured.program 39 Captured.body_39
      (Spec.specs.safety Captured.body_39.identity) ∧
    Spec.UnitMarkerAt Captured.program 39
      (idAt 39 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_39, Captured.Shard_003.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m40 :
    BodyVerified Captured.program 40 Captured.body_40
      (Spec.specs.safety Captured.body_40.identity) ∧
    Spec.UnitMarkerAt Captured.program 40
      (idAt 40 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_40, Captured.Shard_003.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m41 :
    BodyVerified Captured.program 41 Captured.body_41
      (Spec.specs.safety Captured.body_41.identity) ∧
    Spec.UnitMarkerAt Captured.program 41
      (idAt 41 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_41, Captured.Shard_003.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m42 :
    BodyVerified Captured.program 42 Captured.body_42
      (Spec.specs.safety Captured.body_42.identity) ∧
    Spec.UnitMarkerAt Captured.program 42
      (idAt 42 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_42, Captured.Shard_003.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m43 :
    BodyVerified Captured.program 43 Captured.body_43
      (Spec.specs.safety Captured.body_43.identity) ∧
    Spec.UnitMarkerAt Captured.program 43
      (idAt 43 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_43, Captured.Shard_003.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m44 :
    BodyVerified Captured.program 44 Captured.body_44
      (Spec.specs.safety Captured.body_44.identity) ∧
    Spec.UnitMarkerAt Captured.program 44
      (idAt 44 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_44, Captured.Shard_004.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m45 :
    BodyVerified Captured.program 45 Captured.body_45
      (Spec.specs.safety Captured.body_45.identity) ∧
    Spec.UnitMarkerAt Captured.program 45
      (idAt 45 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_45, Captured.Shard_004.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m46 :
    BodyVerified Captured.program 46 Captured.body_46
      (Spec.specs.safety Captured.body_46.identity) ∧
    Spec.UnitMarkerAt Captured.program 46
      (idAt 46 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_46, Captured.Shard_004.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m47 :
    BodyVerified Captured.program 47 Captured.body_47
      (Spec.specs.safety Captured.body_47.identity) ∧
    Spec.UnitMarkerAt Captured.program 47
      (idAt 47 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_47, Captured.Shard_004.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m48 :
    BodyVerified Captured.program 48 Captured.body_48
      (Spec.specs.safety Captured.body_48.identity) ∧
    Spec.UnitMarkerAt Captured.program 48
      (idAt 48 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_48, Captured.Shard_004.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m49 :
    BodyVerified Captured.program 49 Captured.body_49
      (Spec.specs.safety Captured.body_49.identity) ∧
    Spec.UnitMarkerAt Captured.program 49
      (idAt 49 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_49, Captured.Shard_004.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m50 :
    BodyVerified Captured.program 50 Captured.body_50
      (Spec.specs.safety Captured.body_50.identity) ∧
    Spec.UnitMarkerAt Captured.program 50
      (idAt 50 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_50, Captured.Shard_004.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m51 :
    BodyVerified Captured.program 51 Captured.body_51
      (Spec.specs.safety Captured.body_51.identity) ∧
    Spec.UnitMarkerAt Captured.program 51
      (idAt 51 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_51, Captured.Shard_004.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m52 :
    BodyVerified Captured.program 52 Captured.body_52
      (Spec.specs.safety Captured.body_52.identity) ∧
    Spec.UnitMarkerAt Captured.program 52
      (idAt 52 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_52, Captured.Shard_004.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m53 :
    BodyVerified Captured.program 53 Captured.body_53
      (Spec.specs.safety Captured.body_53.identity) ∧
    Spec.UnitMarkerAt Captured.program 53
      (idAt 53 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_53, Captured.Shard_004.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m54 :
    BodyVerified Captured.program 54 Captured.body_54
      (Spec.specs.safety Captured.body_54.identity) ∧
    Spec.UnitMarkerAt Captured.program 54
      (idAt 54 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_54, Captured.Shard_004.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m55 :
    BodyVerified Captured.program 55 Captured.body_55
      (Spec.specs.safety Captured.body_55.identity) ∧
    Spec.UnitMarkerAt Captured.program 55
      (idAt 55 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_55, Captured.Shard_005.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m56 :
    BodyVerified Captured.program 56 Captured.body_56
      (Spec.specs.safety Captured.body_56.identity) ∧
    Spec.UnitMarkerAt Captured.program 56
      (idAt 56 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_56, Captured.Shard_005.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m57 :
    BodyVerified Captured.program 57 Captured.body_57
      (Spec.specs.safety Captured.body_57.identity) ∧
    Spec.UnitMarkerAt Captured.program 57
      (idAt 57 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_57, Captured.Shard_005.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m58 :
    BodyVerified Captured.program 58 Captured.body_58
      (Spec.specs.safety Captured.body_58.identity) ∧
    Spec.UnitMarkerAt Captured.program 58
      (idAt 58 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_58, Captured.Shard_005.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m59 :
    BodyVerified Captured.program 59 Captured.body_59
      (Spec.specs.safety Captured.body_59.identity) ∧
    Spec.UnitMarkerAt Captured.program 59
      (idAt 59 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_59, Captured.Shard_005.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m60 :
    BodyVerified Captured.program 60 Captured.body_60
      (Spec.specs.safety Captured.body_60.identity) ∧
    Spec.UnitMarkerAt Captured.program 60
      (idAt 60 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_60, Captured.Shard_005.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m61 :
    BodyVerified Captured.program 61 Captured.body_61
      (Spec.specs.safety Captured.body_61.identity) ∧
    Spec.UnitMarkerAt Captured.program 61
      (idAt 61 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_61, Captured.Shard_005.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m62 :
    BodyVerified Captured.program 62 Captured.body_62
      (Spec.specs.safety Captured.body_62.identity) ∧
    Spec.UnitMarkerAt Captured.program 62
      (idAt 62 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_62, Captured.Shard_005.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m63 :
    BodyVerified Captured.program 63 Captured.body_63
      (Spec.specs.safety Captured.body_63.identity) ∧
    Spec.UnitMarkerAt Captured.program 63
      (idAt 63 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_63, Captured.Shard_005.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m64 :
    BodyVerified Captured.program 64 Captured.body_64
      (Spec.specs.safety Captured.body_64.identity) ∧
    Spec.UnitMarkerAt Captured.program 64
      (idAt 64 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_64, Captured.Shard_005.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m65 :
    BodyVerified Captured.program 65 Captured.body_65
      (Spec.specs.safety Captured.body_65.identity) ∧
    Spec.UnitMarkerAt Captured.program 65
      (idAt 65 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_65, Captured.Shard_005.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m66 :
    BodyVerified Captured.program 66 Captured.body_66
      (Spec.specs.safety Captured.body_66.identity) ∧
    Spec.UnitMarkerAt Captured.program 66
      (idAt 66 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_66, Captured.Shard_006.body_0, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m67 :
    BodyVerified Captured.program 67 Captured.body_67
      (Spec.specs.safety Captured.body_67.identity) ∧
    Spec.UnitMarkerAt Captured.program 67
      (idAt 67 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_67, Captured.Shard_006.body_1, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m68 :
    BodyVerified Captured.program 68 Captured.body_68
      (Spec.specs.safety Captured.body_68.identity) ∧
    Spec.UnitMarkerAt Captured.program 68
      (idAt 68 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_68, Captured.Shard_006.body_2, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m69 :
    BodyVerified Captured.program 69 Captured.body_69
      (Spec.specs.safety Captured.body_69.identity) ∧
    Spec.UnitMarkerAt Captured.program 69
      (idAt 69 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_69, Captured.Shard_006.body_3, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m70 :
    BodyVerified Captured.program 70 Captured.body_70
      (Spec.specs.safety Captured.body_70.identity) ∧
    Spec.UnitMarkerAt Captured.program 70
      (idAt 70 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_70, Captured.Shard_006.body_4, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m71 :
    BodyVerified Captured.program 71 Captured.body_71
      (Spec.specs.safety Captured.body_71.identity) ∧
    Spec.UnitMarkerAt Captured.program 71
      (idAt 71 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_71, Captured.Shard_006.body_5, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m72 :
    BodyVerified Captured.program 72 Captured.body_72
      (Spec.specs.safety Captured.body_72.identity) ∧
    Spec.UnitMarkerAt Captured.program 72
      (idAt 72 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_72, Captured.Shard_006.body_6, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m73 :
    BodyVerified Captured.program 73 Captured.body_73
      (Spec.specs.safety Captured.body_73.identity) ∧
    Spec.UnitMarkerAt Captured.program 73
      (idAt 73 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_73, Captured.Shard_006.body_7, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m74 :
    BodyVerified Captured.program 74 Captured.body_74
      (Spec.specs.safety Captured.body_74.identity) ∧
    Spec.UnitMarkerAt Captured.program 74
      (idAt 74 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_74, Captured.Shard_006.body_8, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m75 :
    BodyVerified Captured.program 75 Captured.body_75
      (Spec.specs.safety Captured.body_75.identity) ∧
    Spec.UnitMarkerAt Captured.program 75
      (idAt 75 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_75, Captured.Shard_006.body_9, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem m76 :
    BodyVerified Captured.program 76 Captured.body_76
      (Spec.specs.safety Captured.body_76.identity) ∧
    Spec.UnitMarkerAt Captured.program 76
      (idAt 76 Spec.primitiveMarkerIdentities) :=
  marker_safe_and_at rfl rfl
    (by simp only [Captured.body_76, Captured.Shard_006.body_10, Spec.primitiveMarkerIdentities,
      idAt, stringAppend_ofList, List.cons_append, List.nil_append])
    rfl rfl rfl rfl rfl

private theorem all_bodies_verified :
    BodiesVerified Captured.program Spec.specs 0 Captured.program.bodies :=
    ⟨m00.1, m01.1, m02.1, m03.1, m04.1, m05.1, m06.1, m07.1, m08.1, m09.1,
     m10.1, m11.1, m12.1, m13.1, m14.1, m15.1, m16.1, m17.1, m18.1, m19.1,
     m20.1, m21.1, m22.1, m23.1, m24.1, m25.1, m26.1, m27.1, m28.1, m29.1,
     m30.1, m31.1, m32.1, m33.1, m34.1, m35.1, m36.1, m37.1, m38.1, m39.1,
     m40.1, m41.1, m42.1, m43.1, m44.1, m45.1, m46.1, m47.1, m48.1, m49.1,
     m50.1, m51.1, m52.1, m53.1, m54.1, m55.1, m56.1, m57.1, m58.1, m59.1,
     m60.1, m61.1, m62.1, m63.1, m64.1, m65.1, m66.1, m67.1, m68.1, m69.1,
     m70.1, m71.1, m72.1, m73.1, m74.1, m75.1, m76.1, True.intro⟩

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
    AllMarkersAt Captured.program 0 Spec.primitiveMarkerIdentities :=
    ⟨m00.2, m01.2, m02.2, m03.2, m04.2, m05.2, m06.2, m07.2, m08.2, m09.2,
     m10.2, m11.2, m12.2, m13.2, m14.2, m15.2, m16.2, m17.2, m18.2, m19.2,
     m20.2, m21.2, m22.2, m23.2, m24.2, m25.2, m26.2, m27.2, m28.2, m29.2,
     m30.2, m31.2, m32.2, m33.2, m34.2, m35.2, m36.2, m37.2, m38.2, m39.2,
     m40.2, m41.2, m42.2, m43.2, m44.2, m45.2, m46.2, m47.2, m48.2, m49.2,
     m50.2, m51.2, m52.2, m53.2, m54.2, m55.2, m56.2, m57.2, m58.2, m59.2,
     m60.2, m61.2, m62.2, m63.2, m64.2, m65.2, m66.2, m67.2, m68.2, m69.2,
     m70.2, m71.2, m72.2, m73.2, m74.2, m75.2, m76.2, True.intro⟩

private theorem bodies_unique_identities :
    bodiesHaveUniqueIdentities Captured.program.bodies = true := rfl

/-! ## Part 2: Endian-Parametric `Trusted.MirSemantics.Bytes` Proofs -/

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

private theorem initBytes?_replicate_zero :
    ∀ (n : Nat),
      initBytes? (List.replicate n (AllocByte.init 0 none)) =
        some (List.replicate n 0)
  | 0 => rfl
  | n + 1 => by
    unfold List.replicate initBytes?
    rw [initBytes?_replicate_zero n]

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
  | rangeFrom _ | array _ | bytes _ => cases hTy
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

private theorem checkVal_char_inv {v : Val} (h : checkVal v .char = true) :
    ∃ c : Char, v = .char c := by
  have hTy := checkVal_iff_ty?.mp h
  cases v with
  | char c => exact ⟨c, rfl⟩
  | unit | bool _ | ordering _ | ptr _ | slicePtr _ _ | rangeTo _
  | rangeFrom _ | array _ | bytes _ => cases hTy
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

private theorem checkVal_unit_inv {v : Val} (h : checkVal v .unit = true) :
    v = .unit :=
  checkVal_unit_iff.mp h

/-! ### `()` Proofs -/

private theorem unit_fromZeros (endian : TargetEndian) :
    Spec.IsFromZeros endian .unit :=
  ⟨⟨0, 0⟩, .unit, rfl, by cases endian <;> rfl, rfl⟩

private theorem unit_fromBytes (endian : TargetEndian) :
    Spec.IsFromBytes endian .unit := by
  refine ⟨⟨0, 0⟩, rfl, fun bs _ hbs _ => ?_⟩
  cases bs with
  | nil => exact ⟨.unit, by cases endian <;> rfl, rfl⟩
  | cons _ _ => cases hbs

private theorem unit_intoBytes (endian : TargetEndian) :
    Spec.IsIntoBytes endian .unit := by
  refine ⟨⟨0, 0⟩, rfl, ?_, ?_⟩
  · intro v hv
    have hu := checkVal_unit_inv hv
    subst hu
    exact ⟨[], rfl⟩
  · intro v bs hEnc
    unfold encodeVal at hEnc
    cases hcv : checkVal v .unit with
    | false => rw [hcv] at hEnc; cases hEnc
    | true =>
      rw [hcv] at hEnc
      have hu := checkVal_unit_inv hcv
      subst hu
      dsimp only at hEnc
      injection hEnc with hBs
      subst hBs
      exact ⟨rfl, [], rfl, rfl⟩

private theorem unit_unaligned : Spec.IsUnaligned .unit :=
  ⟨⟨0, 0⟩, rfl, rfl⟩

/-! ### `bool` Proofs and Refutation -/

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

private theorem bool_unaligned : Spec.IsUnaligned .bool :=
  ⟨⟨1, 0⟩, rfl, rfl⟩

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
        | zero =>
          exact ⟨false, rfl, rfl⟩
        | succ k =>
          rw [hb0] at hLt2
          cases hk : k with
          | zero =>
            exact ⟨true, rfl, rfl⟩
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

/-! ### `char` Proofs and Refutations -/

private theorem char_fromZeros (endian : TargetEndian) :
    Spec.IsFromZeros endian .char :=
  ⟨⟨4, 2⟩, .char (Char.ofNat 0), rfl, by cases endian <;> rfl, rfl⟩

private theorem char_intoBytes (endian : TargetEndian) :
    Spec.IsIntoBytes endian .char := by
  refine ⟨⟨4, 2⟩, rfl, ?_, ?_⟩
  · intro v hv
    let ⟨c, hc⟩ := checkVal_char_inv hv
    subst hc
    exact ⟨(encodeUInt endian 4 c.toNat).map
      (fun b => AllocByte.init b none), rfl⟩
  · intro v bs hEnc
    unfold encodeVal at hEnc
    cases hcv : checkVal v .char with
    | false => rw [hcv] at hEnc; cases hEnc
    | true =>
      rw [hcv] at hEnc
      let ⟨c, hc⟩ := checkVal_char_inv hcv
      subst hc
      dsimp only at hEnc
      injection hEnc with hBs
      subst hBs
      refine ⟨?_, encodeUInt endian 4 c.toNat,
        initBytes?_map_init (encodeUInt endian 4 c.toNat), rfl⟩
      rw [list_length_map, encodeUInt_length]

private theorem char_tryFromBytes_sound (endian : TargetEndian) :
    Spec.CharTryFromBytesSound endian := by
  intro bs raw hbs hraw
  have hrawLen : raw.length = 4 := (initBytes?_length hraw).trans hbs
  have hDecLt32 : decodeUInt endian raw < Nat.pow 2 32 := by
    have h := decodeUInt_lt endian raw
    rw [hrawLen] at h
    exact h
  have hDecLt128 : decodeUInt endian raw < Nat.pow 2 128 :=
    Nat.lt_trans hDecLt32 (by decide)
  let bits : BitVec 128 := BitVec.ofNat 128 (decodeUInt endian raw)
  have hBitsNat : bits.toNat = decodeUInt endian raw :=
    Nat.mod_eq_of_lt hDecLt128
  have hBitsLt : bits.toNat < intWidthModulus .i32 := by
    rw [hBitsNat]; exact hDecLt32
  have hTrunc : truncateBits .i32 bits = bits :=
    truncateBits_of_toNat_lt hBitsLt
  have hLenBeq : (!Nat.beq bs.length 4) = false := by
    rw [hbs]; rfl
  constructor
  · intro hU
    unfold decodeVal
    dsimp only [layoutOfTy]
    rw [ite_bool_false hLenBeq, ite_bool_false (rfl : Nat.beq 4 0 = false),
      hraw]
    dsimp only [evalConstLit]
    rw [show BitVec.ofNat 128 (decodeUInt endian raw) = bits from rfl,
      hTrunc, ite_bool_false (bne_self_eq_false bits), hBitsNat,
      ite_bool_true hU]
    exact ⟨Char.ofNat (decodeUInt endian raw), rfl, rfl⟩
  · intro hNotU
    unfold decodeVal
    dsimp only [layoutOfTy]
    rw [ite_bool_false hLenBeq, ite_bool_false (rfl : Nat.beq 4 0 = false),
      hraw]
    dsimp only [evalConstLit]
    rw [show BitVec.ofNat 128 (decodeUInt endian raw) = bits from rfl,
      hTrunc, ite_bool_false (bne_self_eq_false bits), hBitsNat,
      ite_bool_false hNotU]

private theorem char_not_fromBytes (endian : TargetEndian) :
    decodeVal endian .char
      ((encodeUInt endian 4 0xD800).map (fun b => .init b none)) =
      .error .undefined ∧
    ¬ Spec.IsFromBytes endian .char := by
  have hBad :
      decodeVal endian .char
        ((encodeUInt endian 4 0xD800).map (fun b => .init b none)) =
        .error .undefined := by
    cases endian <;> rfl
  refine ⟨hBad, fun ⟨layout, hLay, hAll⟩ => ?_⟩
  injection hLay with hLayEq
  subst hLayEq
  have hLen :
      ((encodeUInt endian 4 0xD800).map
        (fun b => AllocByte.init b none)).length = 4 := by
    rw [list_length_map, encodeUInt_length]
  let ⟨_, hOk, _⟩ :=
    hAll _ (encodeUInt endian 4 0xD800) hLen
      (initBytes?_map_init (encodeUInt endian 4 0xD800))
  rw [hBad] at hOk
  cases hOk

private theorem char_not_unaligned :
    (∃ layout, layoutOfTy .char = some layout ∧ 0 < layout.alignLog2) ∧
    ¬ Spec.IsUnaligned .char := by
  refine ⟨⟨⟨4, 2⟩, rfl, by decide⟩, fun ⟨layout, hLay, hZero⟩ => ?_⟩
  injection hLay with hEq
  subst hEq
  cases hZero

/-! ### Integer (`u8`..`isize` = `IntWidth × Bool`) Proofs and Refutations -/

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
      (initBytes?_replicate_zero layout.size)
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

private theorem int_i8_unaligned (s : Bool) :
    Spec.IsUnaligned (.int .i8 s) :=
  ⟨⟨1, 0⟩, rfl, rfl⟩

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

private theorem primitive_bit_validity : Spec.PrimitiveBitValiditySpec :=
  ⟨fun endian =>
    ⟨unit_fromZeros endian,
      unit_fromBytes endian,
      unit_intoBytes endian,
      unit_unaligned,
      bool_fromZeros endian,
      bool_intoBytes endian,
      bool_unaligned,
      bool_tryFromBytes_sound endian,
      char_fromZeros endian,
      char_intoBytes endian,
      char_tryFromBytes_sound endian,
      fun w s => ⟨int_fromZeros endian w s, int_fromBytes endian w s,
        int_intoBytes endian w s⟩,
      int_i8_unaligned,
      bool_not_fromBytes endian,
      char_not_fromBytes endian⟩,
    char_not_unaligned,
    int_multibyte_not_unaligned⟩

/-! ## Top-Level Proof-Unit Theorem -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, bodies_unique_identities, ?_, ?_⟩
  · intro defId body found
    have hSub := bodiesVerified_getElem all_bodies_verified defId body found
    rw [Nat.zero_add] at hSub
    exact hSub
  · refine ⟨⟨rfl, ?_⟩, primitive_bit_validity⟩
    intro defId identity found
    have hSub := allMarkersAt_getElem all_markers_at defId identity found
    rw [Nat.zero_add] at hSub
    exact hSub

end Proof
